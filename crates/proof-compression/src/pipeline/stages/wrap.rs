use super::{KzgVerifier, Prepared, Result, scalar_statement};
use crate::kzg::{KzgConfig, Scalar, Srs};
use crate::recursive::native_verifier;
use ark_bls12_381::{Bls12_381, G1Affine, G2Affine};
use ark_ec::{AffineRepr, pairing::Pairing};
use ark_ff::Zero;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use multi_stark::prover::Proof;
use multi_stark::traits::Algebra;
use multi_stark::types::Val;
use std::sync::Arc;

/// Recursive proof and its public pairing operands. Certificate claim values
/// are supplied independently to RecursiveVerifier::verify.
pub struct RecursiveProof {
  pub proof: Proof<KzgConfig>,
  pub pairing_values: Vec<Scalar>,
}

struct Pairings {
  degree_count: usize,
  keys: Vec<G2Affine>,
}

impl Pairings {
  fn encode(&self, values: &[Scalar]) -> Result<Vec<u8>> {
    if values.len() != 2 * self.keys.len()
      || self.keys.len() != self.degree_count + 2
    {
      return Err("incorrect pairing operand count".into());
    }
    let mut bytes = Vec::with_capacity(values.len() * 24);
    for value in values {
      let limbs = value.canonical_limbs_le();
      if limbs[3] != 0 {
        return Err("noncanonical packed pairing operand".into());
      }
      for limb in &limbs[..3] {
        bytes.extend(limb.to_le_bytes());
      }
    }
    Ok(bytes)
  }

  fn verify(&self, values: &[Scalar]) -> Result<()> {
    let bytes = self.encode(values)?;
    let points = bytes
      .as_chunks::<48>()
      .0
      .iter()
      .map(|bytes| G1Affine::deserialize_compressed(bytes.as_slice()))
      .collect::<std::result::Result<Vec<_>, _>>()?;
    for range in [0..self.degree_count, self.degree_count..self.keys.len()] {
      if !Bls12_381::multi_pairing(
        points[range.clone()].to_vec(),
        self.keys[range].to_vec(),
      )
      .is_zero()
      {
        return Err("external pairing equation failed".into());
      }
    }
    Ok(())
  }
}

fn build_recursive(
  verifier: &KzgVerifier,
  proof: &Proof<KzgConfig>,
  claims: &[Vec<Scalar>],
) -> Result<native_verifier::Built> {
  let plan = native_verifier::Plan::new(
    &verifier.system,
    &proof.log_degrees,
    native_verifier::ClaimSchema::from_claims(
      claims,
      &verifier.statement.locations,
    )?,
    native_verifier::LayoutPolicy {
      namespace: Scalar::ONE,
      max_computation_height: 1 << 28,
      max_table_height: 1 << 28,
    },
  )?;
  Ok(plan.build(proof, claims)?)
}

pub struct RecursiveStage {
  prepared: Prepared<Scalar>,
  pairings: Pairings,
  claim_len: usize,
}

/// Build the recursive KZG verifier. The original public statement remains
/// public; degree-check and opening-check operands are additional publics.
pub fn prepare_recursive(
  verifier: &KzgVerifier,
  proof: &Proof<KzgConfig>,
  expected: &[Val],
) -> Result<RecursiveStage> {
  let public = scalar_statement(expected);
  verifier.verify(proof, &public)?;
  let claims = verifier.statement.claims(&public)?;
  let built = build_recursive(verifier, proof, &claims)?;
  let (_, assignment) = built.check_and_assign()?;
  let pairings = Pairings { degree_count: 0, keys: built.pairing_keys };
  pairings.verify(&assignment.public_values()[public.len()..])?;
  Ok(RecursiveStage {
    prepared: Prepared { circuit: built.circuit, assignment },
    pairings,
    claim_len: public.len(),
  })
}

impl RecursiveStage {
  pub fn circuit(&self) -> &multi_stark::plonkish::Circuit<Scalar> {
    self.prepared.circuit()
  }

  pub fn prove(
    self,
    srs: Arc<Srs>,
    max_height: usize,
  ) -> Result<(RecursiveVerifier, RecursiveProof)> {
    let pairing_values =
      self.prepared.public_values()[self.claim_len..].to_vec();
    let (verifier, proof) = self.prepared.prove_kzg(srs, max_height)?;
    Ok((
      RecursiveVerifier {
        verifier,
        pairings: self.pairings,
        claim_len: self.claim_len,
      },
      RecursiveProof { proof, pairing_values },
    ))
  }
}

pub struct RecursiveVerifier {
  verifier: KzgVerifier,
  pairings: Pairings,
  claim_len: usize,
}

pub(super) fn setup_recursive(
  verifier: &KzgVerifier,
  srs: Arc<Srs>,
  height: usize,
) -> Result<RecursiveVerifier> {
  let claim_len = verifier.statement.locations.len();
  let claims = verifier.statement.claims(&vec![Scalar::ZERO; claim_len])?;
  let template = verifier.codec()?.template();
  let built = build_recursive(verifier, &template, &claims)?;
  let outer = super::setup::kzg(built.circuit, srs, height)?;
  Ok(RecursiveVerifier {
    verifier: outer,
    pairings: Pairings { degree_count: 0, keys: built.pairing_keys },
    claim_len,
  })
}

impl RecursiveVerifier {
  /// Encode all verification data, including both stages' public parameters
  /// and the pairing equations. Authenticate the complete encoding on transport.
  pub fn to_bytes(&self) -> Result<Vec<u8>> {
    let mut keys = vec![];
    for key in &self.pairings.keys {
      key.serialize_compressed(&mut keys)?;
    }
    super::codec::encode(
      b"IXRECV01",
      (
        self.verifier.to_bytes()?,
        self.claim_len,
        self.pairings.degree_count,
        keys,
      ),
    )
  }

  /// Decode an independently trusted verifier with a 64 MiB decoding budget.
  pub fn from_bytes(bytes: &[u8]) -> Result<Self> {
    let (verifier, claim_len, degree_count, keys): (
      Vec<u8>,
      usize,
      usize,
      Vec<u8>,
    ) = super::codec::decode(b"IXRECV01", bytes)?;
    let verifier = KzgVerifier::from_bytes(&verifier)?;
    let count = degree_count.checked_add(2).ok_or("pairing count overflow")?;
    if count.checked_mul(96) != Some(keys.len())
      || count.checked_mul(2).and_then(|n| n.checked_add(claim_len))
        != Some(verifier.statement.locations.len())
    {
      return Err("invalid recursive public statement dimensions".into());
    }
    let keys = keys
      .as_chunks::<96>()
      .0
      .iter()
      .map(|bytes| G2Affine::deserialize_compressed(bytes.as_slice()))
      .collect::<std::result::Result<Vec<_>, _>>()?;
    if keys.iter().any(|p| p.is_zero()) {
      return Err("identity pairing key".into());
    }
    Ok(Self { verifier, pairings: Pairings { degree_count, keys }, claim_len })
  }

  /// Pack the public pairing operands followed by the fixed-shape KZG proof.
  /// The expected certificate claim and trusted verifier are supplied separately.
  pub fn encode_proof(&self, proof: &RecursiveProof) -> Result<Vec<u8>> {
    let mut bytes = self.pairings.encode(&proof.pairing_values)?;
    bytes.extend(self.verifier.encode_proof(&proof.proof)?);
    Ok(bytes)
  }

  pub fn verify_bytes(&self, bytes: &[u8], expected: &[Val]) -> Result<()> {
    let offset = self.pairings.keys.len() * 48;
    if bytes.len() < offset {
      return Err("truncated pairing operands".into());
    }
    let pairing_values = bytes[..offset]
      .as_chunks::<24>()
      .0
      .iter()
      .map(|chunk| {
        let mut limbs = [0; 4];
        for (limb, bytes) in limbs.iter_mut().zip(chunk.as_chunks::<8>().0) {
          *limb = u64::from_le_bytes(*bytes);
        }
        Scalar::from_limbs_le(limbs)
      })
      .collect();
    let proof = self.verifier.codec()?.decode(&bytes[offset..])?;
    self.verify(&RecursiveProof { proof, pairing_values }, expected)
  }

  /// Verify the recursive proof, expected certificate statement, and both
  /// external pairing equations. No proving SRS is needed.
  pub fn verify(&self, proof: &RecursiveProof, expected: &[Val]) -> Result<()> {
    if expected.len() != self.claim_len {
      return Err("unexpected certificate claim length".into());
    }
    let mut public = scalar_statement(expected);
    public.extend_from_slice(&proof.pairing_values);
    self.verifier.verify(&proof.proof, &public)?;
    self.pairings.verify(&proof.pairing_values)
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use ark_ec::CurveGroup;
  use ark_serialize::CanonicalSerialize;
  use multi_stark::plonkish::CircuitBuilder;
  use multi_stark::traits::{Algebra, Field};

  #[test]
  fn final_verifier_requires_claim_outer_proof_and_both_pairings() -> Result<()>
  {
    let inner = Srs::unsafe_dev_setup(8, b"inner-test");
    let outer = Arc::new(Srs::unsafe_dev_setup(128, b"outer-test"));
    // Exercise the final verification boundary with small generated outer
    // circuits. Actual recursive constraints are tested by prepare_recursive
    // and the native_verifier tests, without a large recursive proving run.
    for (claim_len, degree_count) in [(2, 0), (5, 2)] {
      for invalid_pairing in [None, Some(0), Some(1)] {
        if degree_count == 0 && invalid_pairing == Some(0) {
          continue;
        }
        let mut points = vec![];
        let mut keys = vec![];
        if degree_count != 0 {
          points.extend([inner.g1[0], -inner.g1[0]]);
          keys.extend([inner.g2, inner.g2]);
        }
        points.extend([inner.g1[1], -inner.g1[0]]);
        keys.extend([inner.g2, inner.tau_g2]);
        if let Some(equation) = invalid_pairing {
          let index = if equation == 0 { 0 } else { degree_count };
          points[index] =
            (points[index] * ark_bls12_381::Fr::from(2u8)).into_affine();
        }
        let mut packed = vec![];
        for point in points {
          let mut bytes = vec![];
          point.serialize_compressed(&mut bytes)?;
          for chunk in bytes.as_chunks::<24>().0 {
            let mut limbs = [0; 4];
            for (limb, bytes) in limbs.iter_mut().zip(chunk.as_chunks::<8>().0)
            {
              *limb = u64::from_le_bytes(*bytes);
            }
            packed.push(Scalar::from_limbs_le(limbs));
          }
        }
        let expected: Vec<_> =
          (0..claim_len).map(|i| Val::from_usize(7 + i)).collect();
        let mut public = scalar_statement(&expected);
        public.extend_from_slice(&packed);
        let mut b = CircuitBuilder::new();
        let wires: Vec<_> = (0..public.len())
          .map(|i| b.public_input(format!("public{i}")))
          .collect();
        let circuit = b.finish();
        let mut witness = circuit.witness();
        for (&wire, &value) in wires.iter().zip(&public) {
          witness.set(wire, value)?;
        }
        let assignment = witness.generate()?;
        let stage = RecursiveStage {
          prepared: Prepared { circuit, assignment },
          pairings: Pairings { degree_count, keys },
          claim_len,
        };
        let (verifier, mut proof) = stage.prove(outer.clone(), 128)?;
        assert_eq!(
          verifier.verify(&proof, &expected).is_err(),
          invalid_pairing.is_some()
        );
        if invalid_pairing.is_none() {
          let key_bytes = verifier.to_bytes()?;
          let verifier = RecursiveVerifier::from_bytes(&key_bytes)?;
          assert_eq!(verifier.to_bytes()?, key_bytes);
          assert!(
            RecursiveVerifier::from_bytes(&key_bytes[..key_bytes.len() - 1])
              .is_err()
          );
          let mut extra_key = key_bytes.clone();
          extra_key.push(0);
          assert!(RecursiveVerifier::from_bytes(&extra_key).is_err());
          let bytes = verifier.encode_proof(&proof)?;
          verifier.verify_bytes(&bytes, &expected)?;
          assert!(
            verifier
              .verify_bytes(&bytes[..bytes.len() - 1], &expected)
              .is_err()
          );
          let mut extra = bytes.clone();
          extra.push(0);
          assert!(verifier.verify_bytes(&extra, &expected).is_err());
          let mut malformed = bytes.clone();
          malformed[..48].fill(0xff);
          assert!(verifier.verify_bytes(&malformed, &expected).is_err());
          let mut wrong = expected.clone();
          wrong[0] += Val::ONE;
          assert!(verifier.verify(&proof, &wrong).is_err());
          assert!(verifier.verify(&proof, &expected[..claim_len - 1]).is_err());
          proof.pairing_values[0] += Scalar::ONE;
          assert!(verifier.verify(&proof, &expected).is_err());
          proof.pairing_values[0] -= Scalar::ONE;
          proof.proof.stage_1_opened_values[0][0][0] += Scalar::ONE;
          assert!(verifier.verify(&proof, &expected).is_err());
        }
      }
    }
    Ok(())
  }
}
