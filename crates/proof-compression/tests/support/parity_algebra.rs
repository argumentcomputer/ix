//! Host-side test adapter, NOT trusted circuit verification. Transcript
//! replay supplies witness values and differential-test oracle challenges;
//! transcript-enabled experiments constrain these values independently.

use ix_proof_compression::fri::AlgebraicInputs;
use ix_proof_compression::fri::QuadraticValue;
use multi_stark::config::StarkGenericConfig;
use multi_stark::p3_field::BasedVectorSpace;
use multi_stark::p3_field::PrimeCharacteristicRing;
use multi_stark::plonkish::CircuitBuilder;
use multi_stark::plonkish::Witness;
use multi_stark::plonkish::WitnessError;
use multi_stark::prover::Proof;
use multi_stark::system::System;
use multi_stark::types::ExtVal;
use multi_stark::types::GoldilocksBlake3Config;
use multi_stark::types::Val;
use p3_challenger::{CanObserve, FieldChallenger};

/// Native transcript replay through zeta, in the order used by System::verify.
pub(crate) fn challenges(
  system: &System<GoldilocksBlake3Config>,
  proof: &Proof<GoldilocksBlake3Config>,
  claims: &[&[Val]],
) -> [ExtVal; 4] {
  let mut challenger = system.config.initialise_challenger();
  system.observe_shape(&mut challenger);
  for &active in &proof.active {
    challenger.observe(Val::from_bool(active));
  }
  if let Some(commitment) = &system.preprocessed_commit {
    challenger.observe(commitment.clone());
  }
  challenger.observe(proof.commitments.stage_1_trace.clone());
  for &height in &proof.log_degrees {
    challenger.observe(Val::from_u8(height));
  }
  challenger.observe(Val::from_usize(claims.len()));
  for claim in claims {
    challenger.observe(Val::from_usize(claim.len()));
    challenger.observe_slice(claim);
  }
  let beta: ExtVal = challenger.sample_algebra_element();
  challenger.observe_algebra_element(beta);
  let gamma: ExtVal = challenger.sample_algebra_element();
  challenger.observe_algebra_element(gamma);
  challenger.observe(proof.commitments.stage_2_trace.clone());
  for &accumulator in &proof.intermediate_accumulators {
    challenger.observe_algebra_element(accumulator);
  }
  let alpha = challenger.sample_algebra_element();
  challenger.observe(proof.commitments.quotient_chunks.clone());
  let zeta = challenger.sample_algebra_element();
  [beta, gamma, alpha, zeta]
}

pub(crate) fn set_extension(
  witness: &mut Witness<'_, Val>,
  wire: QuadraticValue,
  value: ExtVal,
) -> Result<(), WitnessError> {
  for (wire, &value) in wire.0.iter().zip(value.as_basis_coefficients_slice()) {
    witness.set(*wire, value)?;
  }
  Ok(())
}

pub(crate) fn assign(
  witness: &mut Witness<'_, Val>,
  inputs: &AlgebraicInputs,
  proof: &Proof<GoldilocksBlake3Config>,
  claims: &[&[Val]],
  challenges: [ExtVal; 4],
) -> Result<(), WitnessError> {
  assert_eq!(claims.len(), inputs.claims.len());
  for (wires, claim) in inputs.claims.iter().zip(claims) {
    assert_eq!(wires.len(), claim.len());
    for (&wire, &value) in wires.iter().zip(*claim) {
      witness.set(wire, value)?;
    }
  }
  let c = inputs.challenges;
  for (wire, value) in
    [c.beta, c.gamma, c.alpha, c.zeta].into_iter().zip(challenges)
  {
    set_extension(witness, wire, value)?;
  }
  assert_eq!(proof.active, vec![true; inputs.openings.len()]);
  let mut preprocessed_slot = 0;
  for (i, opening) in inputs.openings.iter().enumerate() {
    let mut windows = vec![
      (&opening.main, &proof.stage_1_opened_values[i]),
      (&opening.stage2, &proof.stage_2_opened_values[i]),
    ];
    if !opening.preprocessed[0].is_empty() {
      windows.push((
        &opening.preprocessed,
        &proof.preprocessed_opened_values.as_ref().unwrap()[preprocessed_slot],
      ));
      preprocessed_slot += 1;
    }
    for (wires, values) in windows {
      assert_eq!(values.len(), 2);
      for row in 0..2 {
        assert_eq!(wires[row].len(), values[row].len());
        for (&wire, &value) in wires[row].iter().zip(&values[row]) {
          set_extension(witness, wire, value)?;
        }
      }
    }
    assert_eq!(proof.quotient_opened_values[i].len(), 1);
    assert_eq!(
      opening.quotient.len(),
      proof.quotient_opened_values[i][0].len()
    );
    for (&wire, &value) in
      opening.quotient.iter().zip(&proof.quotient_opened_values[i][0])
    {
      set_extension(witness, wire, value)?;
    }
    set_extension(
      witness,
      opening.accumulator,
      proof.intermediate_accumulators[i],
    )?;
  }
  Ok(())
}

/// Publicly bind the complete algebraic instance for this intermediate
/// experiment. A future full verifier instead authenticates these wires
/// with transcript/PCS constraints and exposes only the inner claims.
pub(crate) fn expose_boundary(
  builder: &mut CircuitBuilder<Val>,
  inputs: &AlgebraicInputs,
) {
  let c = inputs.challenges;
  let mut boundary = vec![c.beta, c.gamma, c.alpha, c.zeta];
  for o in &inputs.openings {
    boundary.extend(o.preprocessed.iter().flatten().copied());
    boundary.extend(o.main.iter().flatten().copied());
    boundary.extend(o.stage2.iter().flatten().copied());
    boundary.extend(o.quotient.iter().copied());
    boundary.push(o.accumulator);
  }
  for wire in boundary {
    for coordinate in wire.0 {
      builder.expose_public(coordinate);
    }
  }
}

/// Expected public instance obtained from the native inputs, independently
/// of the Plonkish witness assignment. Ordering matches expose_boundary().
pub(crate) fn statement(
  proof: &Proof<GoldilocksBlake3Config>,
  claims: &[&[Val]],
  challenges: [ExtVal; 4],
) -> Vec<Val> {
  let mut public: Vec<Val> =
    claims.iter().flat_map(|claim| claim.iter().copied()).collect();
  let mut extension_values = challenges.to_vec();
  // The example has preprocessing for both circuits; this helper is not
  // the general sparse-system/optional-preprocessing proof adapter.
  let preprocessed = proof.preprocessed_opened_values.as_ref().unwrap();
  for (i, preprocessed) in preprocessed.iter().enumerate() {
    extension_values.extend(preprocessed.iter().flatten().copied());
    extension_values
      .extend(proof.stage_1_opened_values[i].iter().flatten().copied());
    extension_values
      .extend(proof.stage_2_opened_values[i].iter().flatten().copied());
    extension_values.extend(proof.quotient_opened_values[i][0].iter().copied());
    extension_values.push(proof.intermediate_accumulators[i]);
  }
  for value in extension_values {
    public.extend_from_slice(value.as_basis_coefficients_slice());
  }
  public
}
