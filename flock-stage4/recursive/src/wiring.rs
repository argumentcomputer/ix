//! Native-field lowering of the verifier relation in `../../circuit/src/wiring.rs`.
//! The protocol equations and transcript topology are shared by specification;
//! arithmetic and hashing below use the Flock backend defined in this crate.

use crate::algebra::{
  F128AlgebraCircuitInputsV1, constrain_f128_algebra_trace,
};
use crate::f128::{alloc_f128_constant, enforce_f128_equal_constant};
use crate::{
  ConstraintPhase, F128VariablesV1, R1csBuilder, R1csError, alloc_f128_private,
};
use ix_stage4_trace::{F128CircuitStructureMatrixIdV1, F128WiringTraceV1};
use std::fmt;

const PHASE: ConstraintPhase = ConstraintPhase::Wiring;

/// Already-constrained transcript and statement inputs for Flock's wiring
/// verifier. The two private values are the circuit-static helper evaluations
/// exported as conditional claims by this relation.
#[derive(Clone, Copy)]
pub(crate) struct F128WiringCircuitInputsV1<'a> {
  pub(crate) public_values: &'a [F128VariablesV1],
  pub(crate) observed_values: &'a [F128VariablesV1],
  pub(crate) challenges: &'a [F128VariablesV1],
  pub(crate) private_values: &'a [[u8; 16]],
}

/// One claim against Flock's digest-keyed circuit-structure matrix.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct F128CircuitStructureClaimVariablesV1 {
  pub(crate) matrix: F128CircuitStructureMatrixIdV1,
  pub(crate) row_point: Vec<F128VariablesV1>,
  pub(crate) column_point: Vec<F128VariablesV1>,
  pub(crate) value: F128VariablesV1,
}

/// One gather evaluation destined for Flock's merged packed-direct opening.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct F128PackedDirectClaimVariablesV1 {
  pub(crate) point: Vec<F128VariablesV1>,
  pub(crate) value: F128VariablesV1,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct F128WiringCircuitOutputV1 {
  pub(crate) topology_digest: [u8; 32],
  /// In order: `live * id`, `live`, and `live * sigma`.
  pub(crate) circuit_structure_claims:
    Vec<F128CircuitStructureClaimVariablesV1>,
  pub(crate) gather_claims: Vec<F128PackedDirectClaimVariablesV1>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum F128WiringCircuitError {
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

/// Replay Flock's complete Product-GKR and gather recombination in native Flock
/// GF(2^128) constraints, returning only the claims that intentionally cross into the
/// circuit-structure accumulator and PCS opening.
pub(crate) fn constrain_f128_wiring(
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
