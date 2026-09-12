use crate::algebra::{
  F128AlgebraCircuitInputsV1, constrain_f128_algebra_trace,
};
use crate::f128::{alloc_f128_constant, enforce_f128_equal_constant};
use crate::{
  CanonicalR1csV1, ConstraintPhase, F128VariablesV1, R1csBuilder, R1csError,
  Witness, alloc_f128_private,
};
use ix_stage4_trace::{F128CircuitStructureMatrixIdV1, F128WiringTraceV1};
use std::fmt;

const PHASE: ConstraintPhase = ConstraintPhase::Wiring;

/// Already-constrained transcript and statement inputs for Flock's wiring
/// verifier. The two private values are the circuit-static helper evaluations
/// exported as conditional claims by this relation.
#[derive(Clone, Copy)]
pub struct F128WiringCircuitInputsV1<'a> {
  pub public_values: &'a [F128VariablesV1],
  pub observed_values: &'a [F128VariablesV1],
  pub challenges: &'a [F128VariablesV1],
  pub private_values: &'a [[u8; 16]],
}

/// One claim against Flock's digest-keyed circuit-structure matrix.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128CircuitStructureClaimVariablesV1 {
  pub matrix: F128CircuitStructureMatrixIdV1,
  pub row_point: Vec<F128VariablesV1>,
  pub column_point: Vec<F128VariablesV1>,
  pub value: F128VariablesV1,
}

/// One gather evaluation destined for Flock's merged packed-direct opening.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128PackedDirectClaimVariablesV1 {
  pub point: Vec<F128VariablesV1>,
  pub value: F128VariablesV1,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128WiringCircuitOutputV1 {
  pub topology_digest: [u8; 32],
  /// In order: `live * id`, `live`, and `live * sigma`.
  pub circuit_structure_claims: Vec<F128CircuitStructureClaimVariablesV1>,
  pub gather_claims: Vec<F128PackedDirectClaimVariablesV1>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum F128WiringCircuitError {
  InvalidTrace(String),
  R1cs(R1csError),
  Algebra(String),
  MissingInput(&'static str),
}

impl fmt::Display for F128WiringCircuitError {
  fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::InvalidTrace(error) => {
        write!(formatter, "invalid F128 wiring trace: {error}")
      },
      Self::R1cs(error) => write!(formatter, "F128 wiring R1CS: {error}"),
      Self::Algebra(error) => write!(formatter, "F128 wiring algebra: {error}"),
      Self::MissingInput(kind) => write!(formatter, "missing wiring {kind}"),
    }
  }
}

impl std::error::Error for F128WiringCircuitError {}

impl From<R1csError> for F128WiringCircuitError {
  fn from(error: R1csError) -> Self {
    Self::R1cs(error)
  }
}

/// Build a standalone materialized wiring relation.
pub fn build_f128_wiring_r1cs(
  trace: &F128WiringTraceV1,
  public_values: &[[u8; 16]],
  observed_values: &[[u8; 16]],
  challenges: &[[u8; 16]],
  private_values: &[[u8; 16]],
) -> Result<
  (CanonicalR1csV1, Witness, F128WiringCircuitOutputV1),
  F128WiringCircuitError,
> {
  let mut builder = R1csBuilder::new();
  let public_values = alloc_sources(&mut builder, public_values)?;
  let observed_values = alloc_sources(&mut builder, observed_values)?;
  let challenges = alloc_sources(&mut builder, challenges)?;
  let output = constrain_f128_wiring(
    &mut builder,
    trace,
    F128WiringCircuitInputsV1 {
      public_values: &public_values,
      observed_values: &observed_values,
      challenges: &challenges,
      private_values,
    },
  )?;
  let (r1cs, witness) = builder.finish()?;
  Ok((r1cs, witness, output))
}

/// Replay Flock's complete Product-GKR and gather recombination in canonical
/// Fr R1CS, returning only the claims that intentionally cross into the
/// circuit-structure accumulator and PCS opening.
pub fn constrain_f128_wiring(
  builder: &mut R1csBuilder,
  trace: &F128WiringTraceV1,
  inputs: F128WiringCircuitInputsV1<'_>,
) -> Result<F128WiringCircuitOutputV1, F128WiringCircuitError> {
  trace
    .validate(
      inputs.public_values.len(),
      inputs.observed_values.len(),
      inputs.challenges.len(),
      inputs.private_values.len(),
    )
    .map_err(|error| F128WiringCircuitError::InvalidTrace(error.to_string()))?;

  for (value, fixed) in
    inputs.public_values.iter().zip(&trace.fixed_public_values)
  {
    if let Some(fixed) = fixed {
      enforce_f128_equal_constant(builder, value, *fixed, PHASE);
    }
  }

  let private_values = inputs
    .private_values
    .iter()
    .copied()
    .map(|value| alloc_f128_private(builder, value, PHASE))
    .collect::<Result<Vec<_>, _>>()?;
  constrain_f128_algebra_trace(
    builder,
    &trace.algebra,
    F128AlgebraCircuitInputsV1 {
      public_values: inputs.public_values,
      observed_values: inputs.observed_values,
      challenges: inputs.challenges,
      private_values: &private_values,
    },
  )
  .map_err(|error| F128WiringCircuitError::Algebra(error.to_string()))?;

  let rho = trace
    .rho_challenges
    .iter()
    .map(|&index| {
      get(inputs.challenges, index, "Product-GKR endpoint challenge")
    })
    .collect::<Result<Vec<_>, _>>()?;
  let row_variables = usize::try_from(trace.row_variables)
    .map_err(|_| F128WiringCircuitError::MissingInput("row dimension"))?;
  let base_variables = usize::try_from(trace.structure_base_variables)
    .map_err(|_| F128WiringCircuitError::MissingInput("structure dimension"))?;
  let zero = alloc_f128_constant(builder, [0; 16], PHASE)?;
  let mut one_value = [0; 16];
  one_value[0] = 1;
  let one = alloc_f128_constant(builder, one_value, PHASE)?;

  let masked_id =
    get(&private_values, trace.masked_id_private_value, "masked-id value")?;
  let live = get(&private_values, trace.live_private_value, "live value")?;
  let sigma = get(
    inputs.observed_values,
    trace.sigma_eval_observation,
    "sigma evaluation",
  )?;
  let matrix = trace.structure_matrix();
  let mut circuit_structure_claims = Vec::with_capacity(3);
  for (plane, value) in [masked_id, live, sigma].into_iter().enumerate() {
    let mut column_point = rho[row_variables..].to_vec();
    column_point.resize(base_variables, zero.clone());
    column_point.extend((0..3).map(|bit| {
      if (plane >> bit) & 1 == 1 { one.clone() } else { zero.clone() }
    }));
    circuit_structure_claims.push(F128CircuitStructureClaimVariablesV1 {
      matrix,
      row_point: rho[..row_variables].to_vec(),
      column_point,
      value,
    });
  }

  let gather_claims = trace
    .gather_observations
    .iter()
    .zip(&trace.gather_high_bits)
    .map(|(&observation, bits)| {
      let mut point = rho[..row_variables].to_vec();
      point.extend(
        bits.iter().map(|&bit| if bit { one.clone() } else { zero.clone() }),
      );
      Ok(F128PackedDirectClaimVariablesV1 {
        point,
        value: get(inputs.observed_values, observation, "gather value")?,
      })
    })
    .collect::<Result<Vec<_>, F128WiringCircuitError>>()?;

  Ok(F128WiringCircuitOutputV1 {
    topology_digest: trace.topology_digest(),
    circuit_structure_claims,
    gather_claims,
  })
}

fn alloc_sources(
  builder: &mut R1csBuilder,
  values: &[[u8; 16]],
) -> Result<Vec<F128VariablesV1>, R1csError> {
  values
    .iter()
    .copied()
    .map(|value| alloc_f128_private(builder, value, ConstraintPhase::Statement))
    .collect()
}

fn get(
  values: &[F128VariablesV1],
  index: u64,
  kind: &'static str,
) -> Result<F128VariablesV1, F128WiringCircuitError> {
  values
    .get(
      usize::try_from(index)
        .map_err(|_| F128WiringCircuitError::MissingInput(kind))?,
    )
    .cloned()
    .ok_or(F128WiringCircuitError::MissingInput(kind))
}

#[cfg(test)]
mod tests {
  use super::*;
  use ix_stage4_trace::{
    F128AlgebraTraceV1, F128EqualityV1, F128InputSourceV1, F128ReferenceV1,
    F128VerifierPhaseV1,
  };

  fn value(low: u64) -> [u8; 16] {
    u128::from(low).to_le_bytes()
  }

  fn fixture() -> F128WiringTraceV1 {
    let public = F128ReferenceV1::Input(F128InputSourceV1::PublicValue(0));
    let gather = F128ReferenceV1::Input(F128InputSourceV1::ObservedValue(1));
    F128WiringTraceV1 {
      circuit_digest: [3; 32],
      public_value_count: 1,
      row_variables: 1,
      cell_variables: 2,
      packed_claim_variables: 2,
      structure_base_variables: 1,
      fixed_public_values: vec![Some(value(7))],
      rho_challenges: vec![0, 1],
      closing_digest_challenges: [2, 3],
      masked_id_private_value: 0,
      live_private_value: 1,
      sigma_eval_observation: 0,
      gather_observations: vec![1],
      gather_high_bits: vec![vec![false]],
      algebra: F128AlgebraTraceV1 {
        operations: Vec::new(),
        equalities: vec![F128EqualityV1 {
          phase: F128VerifierPhaseV1::Wiring,
          left: gather,
          right: public,
        }],
        deferred_matrix_claims: Vec::new(),
      },
    }
  }

  #[test]
  fn compiles_conditional_structure_and_gather_claims() {
    let trace = fixture();
    let (r1cs, witness, output) = build_f128_wiring_r1cs(
      &trace,
      &[value(7)],
      &[value(11), value(7)],
      &[value(2), value(3), value(4), value(5)],
      &[value(13), value(17)],
    )
    .unwrap();
    r1cs.check(&witness).unwrap();
    assert_eq!(output.circuit_structure_claims.len(), 3);
    assert_eq!(output.gather_claims.len(), 1);
    assert_eq!(output.gather_claims[0].point.len(), 2);
    assert_eq!(output.gather_claims[0].value.value(), &value(7));
  }

  #[test]
  fn fixed_public_and_gather_recombination_are_enforced() {
    let trace = fixture();
    let result = build_f128_wiring_r1cs(
      &trace,
      &[value(9)],
      &[value(11), value(9)],
      &[value(2), value(3), value(4), value(5)],
      &[value(13), value(17)],
    );
    assert!(matches!(
      result,
      Err(F128WiringCircuitError::R1cs(R1csError::Unsatisfied { .. }))
    ));
  }
}
