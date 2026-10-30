//! The recursive KZG stage: a circuit verifying a first KZG stage proof with
//! its opening pairing deferred to public operands, the proof of it, and the
//! prepared verifier shared by local and bundled verifying keys.
use crate::kzg::{
  KzgConfig, Scalar, Srs,
  curve::{
    G1_COMPRESSED_BYTES, G1Affine, G2_COMPRESSED_BYTES, G2Affine, PairingCurve,
    read_g1_compressed,
  },
};
use crate::pipeline::{
  Result,
  claims::ClaimTemplate,
  lowering,
  stage::{self, KzgVerifier, Prepared, scalar_statement},
};
use crate::recursive::native_verifier;
use crate::recursive::pairing::{self, PUBLIC_VALUES};
use ark_ec::{AffineRepr, pairing::Pairing};
use ark_ff::Zero;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use multi_stark::{prover::Proof, system::System, types::Val};
use std::sync::Arc;

/// Recursive proof and its public pairing operands. Certificate claim values
/// are supplied independently to RecursiveVerifier::verify.
pub struct RecursiveProof {
  pub proof: Proof<KzgConfig>,
  pub pairing_values: Vec<Scalar>,
}

fn build_recursive(
  verifier: &KzgVerifier,
  proof: &Proof<KzgConfig>,
  claims: &[Vec<Scalar>],
) -> Result<native_verifier::Built> {
  let plan = lowering::recursive_plan(
    &verifier.system,
    &proof.log_degrees,
    native_verifier::ClaimSchema::from_claims(
      claims,
      &verifier.statement.locations,
    )?,
  )?;
  Ok(plan.build(proof, claims)?)
}

pub struct RecursiveStage {
  prepared: Prepared<Scalar>,
  pairings: Pairings,
  claim_len: usize,
}

/// Build the recursive KZG verifier. The original public statement remains
/// public; the opening-check operands are additional publics.
pub fn prepare_recursive(
  verifier: &KzgVerifier,
  proof: &Proof<KzgConfig>,
  expected: &[Val],
) -> Result<RecursiveStage> {
  let public = scalar_statement(expected);
  verifier.verify(proof, &public)?;
  let claims = verifier.statement.claims(&public)?;
  let built = build_recursive(verifier, proof, &claims)?;
  let assignment = built.assign()?;
  let pairings = Pairings {
    keys: built
      .pairing_keys
      .try_into()
      .map_err(|_keys| "expected two pairing keys")?,
  };
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
    let compiled =
      lowering::lower_recursive(self.prepared.circuit, max_height)?;
    let height = lowering::max_height(&compiled)?;
    if height > srs.max_len() {
      return Err("recursive trace exceeds the SRS range".into());
    }
    let config = KzgConfig::with_max_trace_len(srs, height, 2)
      .with_transcript(crate::kzg::TranscriptKind::Blake3)
      .with_streaming_lookups()
      .with_streaming_quotient();
    let (verifier, proof) = stage::prove_lowered(
      lowering::Lowered { compiled, assignment: self.prepared.assignment },
      config,
    )?;
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

const RECURSIVE_VERIFIER_MAGIC: &[u8; 8] = b"IXBNRV02";

pub(in crate::pipeline) const PAIRING_BYTES: usize = 2 * G1_COMPRESSED_BYTES;

pub(in crate::pipeline) struct Pairings {
  pub(in crate::pipeline) keys: [G2Affine; 2],
}

impl Pairings {
  pub(in crate::pipeline) fn encode(
    &self,
    values: &[Scalar],
  ) -> Result<Vec<u8>> {
    pack_pairings(values)
  }

  pub(in crate::pipeline) fn verify(&self, values: &[Scalar]) -> Result<()> {
    self.verify_points(pairing::decode(values)?)
  }
}

pub struct RecursiveVerifier {
  pub(super) verifier: KzgVerifier,
  pub(super) pairings: Pairings,
  pub(super) claim_len: usize,
}

impl RecursiveVerifier {
  /// Encode all verification data, including both stages' public parameters
  /// and the pairing equations. Authenticate the complete encoding on transport.
  pub fn to_bytes(&self) -> Result<Vec<u8>> {
    let mut keys = vec![];
    for key in &self.pairings.keys {
      key.serialize_compressed(&mut keys)?;
    }
    stage::encode_key(
      RECURSIVE_VERIFIER_MAGIC,
      (self.verifier.to_bytes()?, self.claim_len, keys),
    )
  }

  /// Decode an independently trusted verifier with a 64 MiB decoding budget.
  pub fn from_bytes(bytes: &[u8]) -> Result<Self> {
    let (verifier, claim_len, keys): (Vec<u8>, usize, Vec<u8>) =
      stage::decode_key(RECURSIVE_VERIFIER_MAGIC, bytes)?;
    let verifier = KzgVerifier::from_bytes(&verifier)?;
    if keys.len() != 2 * G2_COMPRESSED_BYTES
      || claim_len.checked_add(PUBLIC_VALUES)
        != Some(verifier.statement.locations.len())
    {
      return Err("invalid recursive public statement dimensions".into());
    }
    let encoded_keys = keys;
    let keys = encoded_keys
      .as_chunks::<G2_COMPRESSED_BYTES>()
      .0
      .iter()
      .map(|bytes| G2Affine::deserialize_compressed(bytes.as_slice()))
      .collect::<std::result::Result<Vec<_>, _>>()?;
    let mut canonical_keys = Vec::with_capacity(encoded_keys.len());
    for key in &keys {
      key.serialize_compressed(&mut canonical_keys)?;
    }
    if canonical_keys != encoded_keys {
      return Err("noncanonical recursive pairing keys".into());
    }
    Self::from_parts(verifier.system, verifier.statement, &keys, claim_len)
  }

  /// Pack the public pairing operands followed by the fixed-shape KZG proof.
  /// The expected certificate claim and trusted verifier are supplied separately.
  pub fn encode_proof(&self, proof: &RecursiveProof) -> Result<Vec<u8>> {
    let mut bytes = self.pairings.encode(&proof.pairing_values)?;
    bytes.extend(self.verifier.encode_proof(&proof.proof)?);
    Ok(bytes)
  }

  pub fn verify_bytes(&self, bytes: &[u8], expected: &[Val]) -> Result<()> {
    self.verify_scalar_bytes(bytes, &scalar_statement(expected))
  }

  /// Verify the recursive proof, expected certificate statement, and the
  /// deferred inner opening pairing. No proving SRS is needed.
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

impl RecursiveVerifier {
  pub(in crate::pipeline) fn from_parts(
    system: System<KzgConfig>,
    statement: ClaimTemplate<Scalar>,
    keys: &[G2Affine],
    claim_len: usize,
  ) -> Result<Self> {
    let keys: [G2Affine; 2] =
      keys.try_into().map_err(|_keys| "expected two pairing keys")?;
    if keys.iter().any(|p| {
      p.is_zero()
        || !p.is_on_curve()
        || !p.is_in_correct_subgroup_assuming_on_curve()
    }) || statement.locations.len()
      != claim_len.checked_add(PUBLIC_VALUES).ok_or("public count overflow")?
    {
      return Err("invalid recursive verifier parameters".into());
    }
    Ok(Self {
      verifier: KzgVerifier::new(system, statement)?,
      pairings: Pairings { keys },
      claim_len,
    })
  }

  pub(in crate::pipeline) fn verify_scalar_bytes(
    &self,
    bytes: &[u8],
    expected: &[Scalar],
  ) -> Result<()> {
    if expected.len() != self.claim_len {
      return Err("unexpected certificate claim length".into());
    }
    verify_recursive_bytes(
      &self.verifier.system,
      &self.verifier.codec,
      &self.verifier.statement,
      &self.pairings,
      bytes,
      expected,
    )
  }
}

impl Pairings {
  pub(in crate::pipeline) fn verify_bytes(&self, bytes: &[u8]) -> Result<()> {
    self.verify_points(pairing_points(bytes)?)
  }

  fn verify_points(&self, points: [G1Affine; 2]) -> Result<()> {
    if !PairingCurve::multi_pairing(points, self.keys).is_zero() {
      return Err("external opening pairing equation failed".into());
    }
    Ok(())
  }
}

fn pairing_points(mut bytes: &[u8]) -> Result<[G1Affine; 2]> {
  if bytes.len() != PAIRING_BYTES {
    return Err("pairing point count".into());
  }
  Ok([read_g1_compressed(&mut bytes)?, read_g1_compressed(&mut bytes)?])
}

#[cfg(any(test, feature = "plonk", feature = "groth16"))]
pub(in crate::pipeline) fn unpack_pairings(
  bytes: &[u8],
) -> Result<Vec<Scalar>> {
  Ok(pairing::encode(pairing_points(bytes)?).to_vec())
}

pub(in crate::pipeline) fn pack_pairings(values: &[Scalar]) -> Result<Vec<u8>> {
  let mut bytes = Vec::with_capacity(PAIRING_BYTES);
  for point in pairing::decode(values)? {
    point.serialize_compressed(&mut bytes)?;
  }
  Ok(bytes)
}

pub(in crate::pipeline) fn verify_recursive_bytes(
  system: &System<KzgConfig>,
  codec: &crate::kzg::compact::FixedProofCodec,
  statement: &ClaimTemplate<Scalar>,
  pairings: &Pairings,
  bytes: &[u8],
  expected: &[Scalar],
) -> Result<()> {
  if bytes.len() < PAIRING_BYTES {
    return Err("truncated pairing operands".into());
  }
  let points = pairing_points(&bytes[..PAIRING_BYTES])?;
  let mut public = expected.to_vec();
  public.extend(pairing::encode(points));
  let claims = statement.claims(&public)?;
  let proof = codec.decode(&bytes[PAIRING_BYTES..])?;
  system
    .verify_multiple_claims(
      &claims.iter().map(Vec::as_slice).collect::<Vec<_>>(),
      &proof,
    )
    .map_err(|e| format!("outer KZG proof: {e:?}"))?;
  pairings.verify_points(points)
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::kzg::curve::Fr;
  use crate::recursive::pairing::POINT_LIMB_BYTES;
  use ark_ec::CurveGroup;
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
    for claim_len in [2, 5] {
      for invalid_pairing in [false, true] {
        let mut points = [inner.g1[1], -inner.g1[0]];
        let keys = [inner.g2, inner.tau_g2];
        if invalid_pairing {
          points[0] = (points[0] * Fr::from(2u8)).into_affine();
        }
        let packed = pairing::encode(points);
        let expected: Vec<_> =
          (0..claim_len).map(|i| Val::from_usize(7 + i)).collect();
        let mut public = scalar_statement(&expected);
        public.extend_from_slice(&packed);
        let mut b = CircuitBuilder::new();
        let table =
          b.fixed_table("small", vec![vec![Scalar::ONE], vec![Scalar::TWO]]);
        let one = b.constant(Scalar::ONE);
        b.lookup(table, &[one]);
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
          pairings: Pairings { keys },
          claim_len,
        };
        let (verifier, mut proof) = stage.prove(outer.clone(), 128)?;
        assert_eq!(
          verifier.verify(&proof, &expected).is_err(),
          invalid_pairing
        );
        if !invalid_pairing {
          let key_bytes = verifier.to_bytes()?;
          let verifier = RecursiveVerifier::from_bytes(&key_bytes)?;
          assert_eq!(verifier.to_bytes()?, key_bytes);
          let mut wrong_magic = key_bytes.clone();
          wrong_magic[7] ^= 1;
          assert!(RecursiveVerifier::from_bytes(&wrong_magic).is_err());
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
          malformed[..G1_COMPRESSED_BYTES].fill(0xff);
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

  #[test]
  fn pairing_transport_preserves_points_and_rejects_noncanonical_values()
  -> Result<()> {
    let generator = G1Affine::generator();
    let multiple = (generator * Fr::from(7u8)).into_affine();
    for points in [
      [generator, multiple],
      [-generator, -multiple],
      [G1Affine::identity(), generator],
      [G1Affine::identity(); 2],
    ] {
      let values = pairing::encode(points);
      let encoded = pack_pairings(&values)?;
      assert_eq!(encoded.len(), PAIRING_BYTES);
      assert_eq!(pairing_points(&encoded)?, points);
      assert_eq!(unpack_pairings(&encoded)?, values);
      assert!(unpack_pairings(&encoded[..encoded.len() - 1]).is_err());
      let mut extra = encoded.clone();
      extra.push(0);
      assert!(unpack_pairings(&extra).is_err());
      let mut invalid = encoded;
      invalid[..G1_COMPRESSED_BYTES].fill(0xff);
      assert!(unpack_pairings(&invalid).is_err());
      for i in 0..PUBLIC_VALUES {
        let mut high_limb = [0; 4];
        high_limb[POINT_LIMB_BYTES / 8] = 1;
        let mut aliased = values;
        aliased[i] += Scalar::from_limbs_le(high_limb);
        assert!(pack_pairings(&aliased).is_err());
      }
      assert!(pack_pairings(&values[..PUBLIC_VALUES - 1]).is_err());
      assert!(pack_pairings(&[Scalar::ZERO; PUBLIC_VALUES + 1]).is_err());
    }
    Ok(())
  }

  #[test]
  fn pairing_transport_rejects_infinity_coordinate_aliases() -> Result<()> {
    let values = pairing::encode([G1Affine::identity(); 2]);
    let mut encoded = pack_pairings(&values)?;
    encoded[0] = 1;
    assert!(unpack_pairings(&encoded).is_err());
    let mut aliased = values;
    aliased[0] = Scalar::ONE;
    assert!(pack_pairings(&aliased).is_err());
    Ok(())
  }
}
