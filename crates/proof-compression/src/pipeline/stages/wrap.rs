use super::verification::{Pairings, RecursiveVerifier};
use super::{KzgVerifier, Prepared, Result, scalar_statement};
use crate::kzg::{KzgConfig, Scalar, Srs};
use crate::recursive::native_verifier;
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

fn build_recursive(
  verifier: &KzgVerifier,
  proof: &Proof<KzgConfig>,
  claims: &[Vec<Scalar>],
) -> Result<native_verifier::Built> {
  let plan = super::construct::recursive_plan(
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
      super::construct::lower_recursive(self.prepared.circuit, max_height)?;
    let height = super::construct::max_height(&compiled)?;
    if height > srs.max_len() {
      return Err("recursive trace exceeds the SRS range".into());
    }
    let config = KzgConfig::with_max_trace_len(srs, height, 2)
      .with_transcript(crate::kzg::TranscriptKind::Keccak256)
      .with_streaming_lookups()
      .with_streaming_quotient();
    let (verifier, proof) = super::prove_lowered(
      super::construct::Lowered {
        compiled,
        assignment: self.prepared.assignment,
      },
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

pub(super) fn setup_recursive(
  verifier: &KzgVerifier,
  srs: Arc<Srs>,
  height: usize,
) -> Result<RecursiveVerifier> {
  let claim_len = verifier.statement.locations.len();
  let claims = verifier.statement.claims(&vec![Scalar::ZERO; claim_len])?;
  let template = verifier.codec.template();
  let built = build_recursive(verifier, &template, &claims)?;
  let compiled = super::construct::lower_recursive(built.circuit, height)?;
  let height = super::construct::max_height(&compiled)?;
  if height > srs.max_len() {
    return Err("recursive trace exceeds the SRS range".into());
  }
  let config = KzgConfig::with_max_trace_len(srs, height, 2)
    .with_transcript(crate::kzg::TranscriptKind::Keccak256)
    .with_streaming_lookups()
    .with_streaming_quotient();
  let outer = super::setup::kzg_lowered(compiled, config, claim_len + 4)?;
  Ok(RecursiveVerifier {
    verifier: outer,
    pairings: Pairings {
      keys: built
        .pairing_keys
        .try_into()
        .map_err(|_keys| "expected two pairing keys")?,
    },
    claim_len,
  })
}

#[cfg(test)]
mod tests {
  use super::*;
  use ark_ec::CurveGroup;
  use ark_serialize::CanonicalSerialize;
  use multi_stark::plonkish::CircuitBuilder;
  use multi_stark::traits::Algebra;
  use multi_stark::traits::Field;

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
          points[0] = (points[0] * ark_bls12_381::Fr::from(2u8)).into_affine();
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
          let mut old_key = key_bytes.clone();
          old_key[..8].copy_from_slice(b"IXRECV01");
          assert!(RecursiveVerifier::from_bytes(&old_key).is_err());
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
