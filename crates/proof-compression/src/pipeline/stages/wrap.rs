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
  max_height: usize,
) -> Result<native_verifier::Built> {
  let plan = super::construct::recursive_plan_with_max_height(
    &verifier.system,
    &proof.log_degrees,
    native_verifier::ClaimSchema::from_claims(
      claims,
      &verifier.statement.locations,
    )?,
    max_height,
  )?;
  Ok(plan.build(proof, claims)?)
}

pub struct RecursiveStage {
  prepared: Prepared<Scalar>,
  pairings: Pairings,
  claim_len: usize,
  max_height: usize,
}

/// Build the recursive KZG verifier. The original public statement remains
/// public; the opening-check operands are additional publics.
pub fn prepare_recursive(
  verifier: &KzgVerifier,
  proof: &Proof<KzgConfig>,
  expected: &[Val],
) -> Result<RecursiveStage> {
  prepare_recursive_with_max_height(
    verifier,
    proof,
    expected,
    super::construct::RECURSIVE_HEIGHT,
  )
}

/// Prepare a recursive verifier under an explicit computation/table cap.
/// Proving may lower this cap, but cannot exceed the prepared layout's bound.
pub fn prepare_recursive_with_max_height(
  verifier: &KzgVerifier,
  proof: &Proof<KzgConfig>,
  expected: &[Val],
  max_height: usize,
) -> Result<RecursiveStage> {
  super::construct::recursive_layout_with_max_height(max_height)?;
  let public = scalar_statement(expected);
  verifier.verify(proof, &public)?;
  let claims = verifier.statement.claims(&public)?;
  let built = build_recursive(verifier, proof, &claims, max_height)?;
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
    max_height,
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
    validate_parameters(&srs, max_height)?;
    if max_height > self.max_height {
      return Err("recursive proving cap exceeds the prepared layout".into());
    }
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
  validate_parameters(&srs, height)?;
  let claim_len = verifier.statement.locations.len();
  let claims = verifier.statement.claims(&vec![Scalar::ZERO; claim_len])?;
  let template = verifier.codec.template();
  let built = build_recursive(verifier, &template, &claims, height)?;
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

pub(super) fn validate_parameters(srs: &Srs, height: usize) -> Result<()> {
  super::construct::recursive_layout_with_max_height(height)?;
  if srs.public_setup.max_degree.checked_add(1).is_none()
    || height - 1 > srs.public_setup.max_degree
  {
    return Err("recursive trace cap exceeds public setup allowance".into());
  }
  if srs.max_len() < 2
    || !srs.max_len().is_power_of_two()
    || height > srs.max_len()
    || srs.max_len() - 1 > srs.public_setup.max_degree
  {
    return Err("recursive trace cap exceeds a valid loaded SRS prefix".into());
  }
  Ok(())
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
  fn recursive_limits_respect_public_degree_and_loaded_prefix() -> Result<()> {
    assert_eq!(
      super::super::construct::recursive_layout_with_max_height(1 << 28)?
        .max_computation_height,
      1 << 28,
    );
    let filecoin = crate::kzg::srs::filecoin::filecoin_anchors();
    assert!(
      validate_parameters(&filecoin, 1 << 28)
        .unwrap_err()
        .to_string()
        .contains("public setup allowance")
    );
    let srs = Srs::unsafe_dev_setup_prefix(16, 31, b"recursive-bounds");
    for height in [2, 8, 16] {
      validate_parameters(&srs, height)?;
    }
    assert!(
      validate_parameters(&srs, 32)
        .unwrap_err()
        .to_string()
        .contains("loaded SRS")
    );
    for height in [0, 1, 3, 1 << 29] {
      assert!(validate_parameters(&srs, height).is_err());
    }
    Ok(())
  }

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
          max_height: 128,
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
