use crate::f128::{
  alloc_f128_constant, native_f128_add, native_f128_multiply,
  packed_f128_variables,
};
use crate::{
  ConstraintPhase, F128CircuitStructureClaimVariablesV1, F128TranscriptWordV1,
  F128VariablesV1, LinearCombination, R1csBuilder, R1csError,
  constrain_f128_add, constrain_f128_multiply, enforce_f128_equal,
};
use ark_bls12_381::Fr;
use ark_ff::{AdditiveGroup, Field, PrimeField};
use ix_stage4_trace::{
  F128CircuitStructureAccumulatorTraceV1, F128CircuitStructureMatrixIdV1,
  F128MatrixFoldRoundV1,
};
use std::fmt;

const PHASE: ConstraintPhase = ConstraintPhase::MatrixFold;

/// Already-constrained Product-GKR claims and auxiliary aggregate transcript.
#[derive(Clone, Copy)]
pub struct F128CircuitStructureAccumulatorCircuitInputsV1<'a> {
  pub claims: &'a [F128CircuitStructureClaimVariablesV1],
  pub observed_values: &'a [F128VariablesV1],
  pub byte_payloads: &'a [Vec<F128TranscriptWordV1>],
  pub challenges: &'a [F128VariablesV1],
}

/// One plain evaluation left after batching all circuit-structure claims.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128CircuitStructureRootClaimVariablesV1 {
  pub matrix: F128CircuitStructureMatrixIdV1,
  pub row_point: Vec<F128VariablesV1>,
  pub column_point: Vec<F128VariablesV1>,
  pub value: F128VariablesV1,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128CircuitStructureAccumulatorCircuitOutputV1 {
  pub topology_digest: [u8; 32],
  /// Conditional root. The terminal verifier must check it directly against
  /// the digest-keyed circuit-structure table.
  pub root_claim: F128CircuitStructureRootClaimVariablesV1,
}

/// Public field values for the terminal direct structure-table check.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128CircuitStructureRootClaimPublicInputV1 {
  pub matrix: F128CircuitStructureMatrixIdV1,
  pub row_point: Vec<[u8; 16]>,
  pub column_point: Vec<[u8; 16]>,
  pub value: [u8; 16],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128CircuitStructureRootClaimPublicVariablesV1 {
  matrix: F128CircuitStructureMatrixIdV1,
  row_point: Vec<crate::Variable>,
  column_point: Vec<crate::Variable>,
  value: crate::Variable,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum F128CircuitStructureAccumulatorCircuitError {
  InvalidTrace(String),
  R1cs(R1csError),
  MissingInput(&'static str),
  DigestPayloadShape {
    expected: usize,
    actual: usize,
  },
  DigestPayloadMismatch {
    word: usize,
  },
  MatrixMismatch {
    claim: usize,
  },
  PointShape {
    claim: usize,
    side: &'static str,
    expected: usize,
    actual: usize,
  },
  BindingMismatch {
    claim: usize,
    component: &'static str,
    element: usize,
  },
  ConsistencyMismatch {
    which: &'static str,
  },
  PublicRootPointShape {
    side: &'static str,
    expected: usize,
    actual: usize,
  },
  PublicRootMatrixMismatch,
}

impl fmt::Display for F128CircuitStructureAccumulatorCircuitError {
  fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::InvalidTrace(error) => {
        write!(
          formatter,
          "invalid circuit-structure accumulator trace: {error}"
        )
      },
      Self::R1cs(error) => {
        write!(formatter, "circuit-structure fold R1CS: {error}")
      },
      Self::MissingInput(kind) => {
        write!(formatter, "missing circuit-structure {kind}")
      },
      Self::DigestPayloadShape { expected, actual } => write!(
        formatter,
        "circuit-structure digest payload has {actual} words; expected {expected}",
      ),
      Self::DigestPayloadMismatch { word } => write!(
        formatter,
        "circuit-structure digest payload word {word} is inconsistent",
      ),
      Self::MatrixMismatch { claim } => write!(
        formatter,
        "circuit-structure input claim {claim} names a different matrix",
      ),
      Self::PointShape { claim, side, expected, actual } => write!(
        formatter,
        "circuit-structure claim {claim} has {actual} {side} coordinates; expected {expected}",
      ),
      Self::BindingMismatch { claim, component, element } => write!(
        formatter,
        "circuit-structure claim {claim} {component} binding {element} is inconsistent",
      ),
      Self::ConsistencyMismatch { which } => write!(
        formatter,
        "circuit-structure fold failed its {which} consistency equation",
      ),
      Self::PublicRootPointShape { side, expected, actual } => write!(
        formatter,
        "public circuit-structure root has {actual} {side} coordinates; expected {expected}",
      ),
      Self::PublicRootMatrixMismatch => write!(
        formatter,
        "public circuit-structure root names a different matrix",
      ),
    }
  }
}

impl std::error::Error for F128CircuitStructureAccumulatorCircuitError {}

impl From<R1csError> for F128CircuitStructureAccumulatorCircuitError {
  fn from(error: R1csError) -> Self {
    Self::R1cs(error)
  }
}

/// Allocate the one terminal structure root before any private witness.
pub fn alloc_f128_circuit_structure_root_public_input(
  builder: &mut R1csBuilder,
  root: &F128CircuitStructureRootClaimPublicInputV1,
) -> Result<
  F128CircuitStructureRootClaimPublicVariablesV1,
  F128CircuitStructureAccumulatorCircuitError,
> {
  validate_point_shape("row", root.matrix.row_variables, root.row_point.len())?;
  validate_point_shape(
    "column",
    root.matrix.column_variables,
    root.column_point.len(),
  )?;
  let row_point = root
    .row_point
    .iter()
    .map(|value| builder.alloc_public(fr_from_f128(*value)))
    .collect::<Result<Vec<_>, _>>()?;
  let column_point = root
    .column_point
    .iter()
    .map(|value| builder.alloc_public(fr_from_f128(*value)))
    .collect::<Result<Vec<_>, _>>()?;
  let value = builder.alloc_public(fr_from_f128(root.value))?;
  Ok(F128CircuitStructureRootClaimPublicVariablesV1 {
    matrix: root.matrix,
    row_point,
    column_point,
    value,
  })
}

/// Bind the derived fold output to the public root discharged by the terminal
/// verifier against the digest-keyed static table.
pub fn constrain_f128_circuit_structure_root_public_input(
  builder: &mut R1csBuilder,
  public: &F128CircuitStructureRootClaimPublicVariablesV1,
  derived: &F128CircuitStructureRootClaimVariablesV1,
) -> Result<(), F128CircuitStructureAccumulatorCircuitError> {
  if public.matrix != derived.matrix {
    return Err(
      F128CircuitStructureAccumulatorCircuitError::PublicRootMatrixMismatch,
    );
  }
  validate_public_binding_shape("row", &public.row_point, &derived.row_point)?;
  validate_public_binding_shape(
    "column",
    &public.column_point,
    &derived.column_point,
  )?;
  for (variable, value) in public.row_point.iter().zip(&derived.row_point) {
    constrain_public_f128(builder, *variable, value);
  }
  for (variable, value) in public.column_point.iter().zip(&derived.column_point)
  {
    constrain_public_f128(builder, *variable, value);
  }
  constrain_public_f128(builder, public.value, &derived.value);
  Ok(())
}

/// Replay the batched circuit-structure fold without reading the matrix.
pub fn constrain_f128_circuit_structure_accumulator(
  builder: &mut R1csBuilder,
  trace: &F128CircuitStructureAccumulatorTraceV1,
  inputs: F128CircuitStructureAccumulatorCircuitInputsV1<'_>,
) -> Result<
  F128CircuitStructureAccumulatorCircuitOutputV1,
  F128CircuitStructureAccumulatorCircuitError,
> {
  trace
    .validate(
      inputs.claims.len(),
      inputs.observed_values.len(),
      inputs.byte_payloads.len(),
      inputs.challenges.len(),
    )
    .map_err(|error| {
      F128CircuitStructureAccumulatorCircuitError::InvalidTrace(
        error.to_string(),
      )
    })?;
  bind_circuit_digest(builder, trace, inputs.byte_payloads)?;

  let zero = alloc_f128_constant(builder, [0; 16], PHASE)?;
  let mut one_value = [0; 16];
  one_value[0] = 1;
  let one = alloc_f128_constant(builder, one_value, PHASE)?;
  let row_variables =
    usize::try_from(trace.matrix.row_variables).map_err(|_| {
      F128CircuitStructureAccumulatorCircuitError::MissingInput("row dimension")
    })?;
  let column_variables = usize::try_from(trace.matrix.column_variables)
    .map_err(|_| {
      F128CircuitStructureAccumulatorCircuitError::MissingInput(
        "column dimension",
      )
    })?;

  let mut claims = Vec::with_capacity(trace.claims.len());
  for (position, binding) in trace.claims.iter().enumerate() {
    let claim = inputs
      .claims
      .get(to_usize(binding.claim, "input claim")?)
      .ok_or(F128CircuitStructureAccumulatorCircuitError::MissingInput(
        "input claim",
      ))?;
    if claim.matrix != trace.matrix {
      return Err(
        F128CircuitStructureAccumulatorCircuitError::MatrixMismatch {
          claim: position,
        },
      );
    }
    validate_claim_point_shape(
      position,
      "row",
      row_variables,
      claim.row_point.len(),
    )?;
    validate_claim_point_shape(
      position,
      "column",
      column_variables,
      claim.column_point.len(),
    )?;
    bind_observed(
      builder,
      &one,
      binding.row_low_observations[0],
      inputs.observed_values,
      position,
      "row-low",
      0,
    )?;
    bind_component(
      builder,
      &claim.row_point,
      &binding.row_point_observations,
      inputs.observed_values,
      position,
      "row-point",
    )?;
    bind_observed(
      builder,
      &one,
      binding.column_low_observations[0],
      inputs.observed_values,
      position,
      "column-low",
      0,
    )?;
    bind_component(
      builder,
      &claim.column_point,
      &binding.column_point_observations,
      inputs.observed_values,
      position,
      "column-point",
    )?;
    bind_observed(
      builder,
      &claim.value,
      binding.value_observation,
      inputs.observed_values,
      position,
      "value",
      0,
    )?;
    claims.push(claim);
  }

  let lambdas = resolve_indices(
    &trace.lambda_challenges,
    inputs.challenges,
    "lambda challenge",
  )?;
  let claim_values =
    claims.iter().map(|claim| &claim.value).collect::<Vec<_>>();
  let target = weighted_sum(builder, &claim_values, &lambdas, &zero)?;
  let (column_running, column_point) = replay_rounds(
    builder,
    &trace.column_rounds,
    target,
    inputs.observed_values,
    inputs.challenges,
  )?;
  let bridge = resolve_indices(
    &trace.bridge_observations,
    inputs.observed_values,
    "bridge observation",
  )?;
  let mut column_expected = zero.clone();
  for ((claim, lambda), bridge) in claims.iter().zip(&lambdas).zip(&bridge) {
    let evaluation =
      evaluate_eq(builder, &claim.column_point, &column_point, &one)?;
    let scaled = multiply(builder, lambda, &evaluation)?;
    let term = multiply(builder, &scaled, bridge)?;
    column_expected = add(builder, &column_expected, &term)?;
  }
  enforce_consistency(builder, &column_running, &column_expected, "column")?;

  let mus =
    resolve_indices(&trace.mu_challenges, inputs.challenges, "mu challenge")?;
  let bridge_refs = bridge.iter().collect::<Vec<_>>();
  let target = weighted_sum(builder, &bridge_refs, &mus, &zero)?;
  let (row_running, row_point) = replay_rounds(
    builder,
    &trace.row_rounds,
    target,
    inputs.observed_values,
    inputs.challenges,
  )?;
  let mut row_weight = zero;
  for (claim, mu) in claims.iter().zip(&mus) {
    let evaluation = evaluate_eq(builder, &claim.row_point, &row_point, &one)?;
    let term = multiply(builder, mu, &evaluation)?;
    row_weight = add(builder, &row_weight, &term)?;
  }
  let value = resolve_index(
    trace.value_observation,
    inputs.observed_values,
    "root-value observation",
  )?;
  let row_expected = multiply(builder, &row_weight, &value)?;
  enforce_consistency(builder, &row_running, &row_expected, "row")?;

  Ok(F128CircuitStructureAccumulatorCircuitOutputV1 {
    topology_digest: trace.topology_digest(),
    root_claim: F128CircuitStructureRootClaimVariablesV1 {
      matrix: trace.matrix,
      row_point,
      column_point,
      value,
    },
  })
}

fn bind_circuit_digest(
  builder: &mut R1csBuilder,
  trace: &F128CircuitStructureAccumulatorTraceV1,
  payloads: &[Vec<F128TranscriptWordV1>],
) -> Result<(), F128CircuitStructureAccumulatorCircuitError> {
  let payload = payloads
    .get(to_usize(trace.circuit_digest_payload, "digest payload")?)
    .ok_or(F128CircuitStructureAccumulatorCircuitError::MissingInput(
      "digest payload",
    ))?;
  let expected = [
    trace.matrix.circuit_digest[..16]
      .try_into()
      .expect("circuit digest half has 16 bytes"),
    trace.matrix.circuit_digest[16..]
      .try_into()
      .expect("circuit digest half has 16 bytes"),
  ];
  if payload.len() != expected.len() {
    return Err(
      F128CircuitStructureAccumulatorCircuitError::DigestPayloadShape {
        expected: expected.len(),
        actual: payload.len(),
      },
    );
  }
  for (word, (actual, expected)) in payload.iter().zip(expected).enumerate() {
    if actual.value() != &expected {
      return Err(
        F128CircuitStructureAccumulatorCircuitError::DigestPayloadMismatch {
          word,
        },
      );
    }
    let mut coefficient = Fr::ONE;
    let packed = LinearCombination::from_terms(
      actual.bit_expressions().iter().flat_map(|expression| {
        let scaled = expression.clone().scale(coefficient);
        coefficient.double_in_place();
        scaled.terms().to_vec()
      }),
    );
    let encoded = u128::from_le_bytes(expected);
    let low = u64::try_from(encoded & u128::from(u64::MAX))
      .expect("masked payload word fits u64");
    let high =
      u64::try_from(encoded >> 64).expect("payload high half fits u64");
    let constant =
      Fr::from(low) + Fr::from(high) * Fr::from(u128::from(1_u64) << 64);
    builder.enforce_zero(
      PHASE,
      packed.minus(&LinearCombination::from_constant(constant)),
    );
  }
  Ok(())
}

fn bind_component(
  builder: &mut R1csBuilder,
  values: &[F128VariablesV1],
  observations: &[u64],
  sources: &[F128VariablesV1],
  claim: usize,
  component: &'static str,
) -> Result<(), F128CircuitStructureAccumulatorCircuitError> {
  for (element, (value, &observation)) in
    values.iter().zip(observations).enumerate()
  {
    bind_observed(
      builder,
      value,
      observation,
      sources,
      claim,
      component,
      element,
    )?;
  }
  Ok(())
}

#[allow(clippy::too_many_arguments)]
fn bind_observed(
  builder: &mut R1csBuilder,
  value: &F128VariablesV1,
  observation: u64,
  sources: &[F128VariablesV1],
  claim: usize,
  component: &'static str,
  element: usize,
) -> Result<(), F128CircuitStructureAccumulatorCircuitError> {
  let observed = resolve_index(observation, sources, "claim observation")?;
  if value.value() != observed.value() {
    return Err(F128CircuitStructureAccumulatorCircuitError::BindingMismatch {
      claim,
      component,
      element,
    });
  }
  enforce_f128_equal(builder, value, &observed, PHASE);
  Ok(())
}

fn replay_rounds(
  builder: &mut R1csBuilder,
  rounds: &[F128MatrixFoldRoundV1],
  mut running: F128VariablesV1,
  observations: &[F128VariablesV1],
  challenges: &[F128VariablesV1],
) -> Result<
  (F128VariablesV1, Vec<F128VariablesV1>),
  F128CircuitStructureAccumulatorCircuitError,
> {
  let mut point = Vec::with_capacity(rounds.len());
  for round in rounds {
    let q_one = resolve_index(
      round.one_observation,
      observations,
      "round-one observation",
    )?;
    let q_infinity = resolve_index(
      round.infinity_observation,
      observations,
      "round-infinity observation",
    )?;
    let challenge =
      resolve_index(round.challenge, challenges, "round challenge")?;
    let q_zero = add(builder, &running, &q_one)?;
    let q_zero_plus_one = add(builder, &q_zero, &q_one)?;
    let linear_coefficient = add(builder, &q_zero_plus_one, &q_infinity)?;
    let infinity_times_r = multiply(builder, &q_infinity, &challenge)?;
    let quadratic = multiply(builder, &infinity_times_r, &challenge)?;
    let linear = multiply(builder, &linear_coefficient, &challenge)?;
    let nonconstant = add(builder, &quadratic, &linear)?;
    running = add(builder, &nonconstant, &q_zero)?;
    point.push(challenge);
  }
  Ok((running, point))
}

fn evaluate_eq(
  builder: &mut R1csBuilder,
  claim_point: &[F128VariablesV1],
  evaluation_point: &[F128VariablesV1],
  one: &F128VariablesV1,
) -> Result<F128VariablesV1, F128CircuitStructureAccumulatorCircuitError> {
  let mut output = one.clone();
  for (coordinate, challenge) in claim_point.iter().zip(evaluation_point) {
    let one_plus_coordinate = add(builder, one, coordinate)?;
    let factor = add(builder, &one_plus_coordinate, challenge)?;
    output = multiply(builder, &output, &factor)?;
  }
  Ok(output)
}

fn weighted_sum(
  builder: &mut R1csBuilder,
  values: &[&F128VariablesV1],
  coefficients: &[F128VariablesV1],
  zero: &F128VariablesV1,
) -> Result<F128VariablesV1, F128CircuitStructureAccumulatorCircuitError> {
  let mut output = zero.clone();
  for (value, coefficient) in values.iter().zip(coefficients) {
    let term = multiply(builder, value, coefficient)?;
    output = add(builder, &output, &term)?;
  }
  Ok(output)
}

fn enforce_consistency(
  builder: &mut R1csBuilder,
  actual: &F128VariablesV1,
  expected: &F128VariablesV1,
  which: &'static str,
) -> Result<(), F128CircuitStructureAccumulatorCircuitError> {
  if actual.value() != expected.value() {
    return Err(
      F128CircuitStructureAccumulatorCircuitError::ConsistencyMismatch {
        which,
      },
    );
  }
  enforce_f128_equal(builder, actual, expected, PHASE);
  Ok(())
}

fn add(
  builder: &mut R1csBuilder,
  left: &F128VariablesV1,
  right: &F128VariablesV1,
) -> Result<F128VariablesV1, F128CircuitStructureAccumulatorCircuitError> {
  let output = constrain_f128_add(builder, left, right, PHASE)?;
  debug_assert_eq!(
    output.value(),
    &native_f128_add(*left.value(), *right.value())
  );
  Ok(output)
}

fn multiply(
  builder: &mut R1csBuilder,
  left: &F128VariablesV1,
  right: &F128VariablesV1,
) -> Result<F128VariablesV1, F128CircuitStructureAccumulatorCircuitError> {
  let output = constrain_f128_multiply(builder, left, right, PHASE)?;
  debug_assert_eq!(
    output.value(),
    &native_f128_multiply(*left.value(), *right.value()),
  );
  Ok(output)
}

fn resolve_indices(
  indices: &[u64],
  values: &[F128VariablesV1],
  kind: &'static str,
) -> Result<Vec<F128VariablesV1>, F128CircuitStructureAccumulatorCircuitError> {
  indices.iter().map(|&index| resolve_index(index, values, kind)).collect()
}

fn resolve_index(
  index: u64,
  values: &[F128VariablesV1],
  kind: &'static str,
) -> Result<F128VariablesV1, F128CircuitStructureAccumulatorCircuitError> {
  values
    .get(to_usize(index, kind)?)
    .cloned()
    .ok_or(F128CircuitStructureAccumulatorCircuitError::MissingInput(kind))
}

fn to_usize(
  value: u64,
  kind: &'static str,
) -> Result<usize, F128CircuitStructureAccumulatorCircuitError> {
  usize::try_from(value).map_err(|_| {
    F128CircuitStructureAccumulatorCircuitError::MissingInput(kind)
  })
}

fn validate_claim_point_shape(
  claim: usize,
  side: &'static str,
  expected: usize,
  actual: usize,
) -> Result<(), F128CircuitStructureAccumulatorCircuitError> {
  if actual != expected {
    return Err(F128CircuitStructureAccumulatorCircuitError::PointShape {
      claim,
      side,
      expected,
      actual,
    });
  }
  Ok(())
}

fn validate_point_shape(
  side: &'static str,
  variables: u32,
  actual: usize,
) -> Result<(), F128CircuitStructureAccumulatorCircuitError> {
  let expected = usize::try_from(variables).expect("u32 fits usize");
  if actual != expected {
    return Err(
      F128CircuitStructureAccumulatorCircuitError::PublicRootPointShape {
        side,
        expected,
        actual,
      },
    );
  }
  Ok(())
}

fn validate_public_binding_shape(
  side: &'static str,
  public: &[crate::Variable],
  derived: &[F128VariablesV1],
) -> Result<(), F128CircuitStructureAccumulatorCircuitError> {
  if public.len() != derived.len() {
    return Err(
      F128CircuitStructureAccumulatorCircuitError::PublicRootPointShape {
        side,
        expected: derived.len(),
        actual: public.len(),
      },
    );
  }
  Ok(())
}

fn constrain_public_f128(
  builder: &mut R1csBuilder,
  public: crate::Variable,
  derived: &F128VariablesV1,
) {
  builder.enforce_zero(
    PHASE,
    packed_f128_variables(derived)
      .minus(&LinearCombination::from_variable(public)),
  );
}

fn fr_from_f128(value: [u8; 16]) -> Fr {
  Fr::from_le_bytes_mod_order(&value)
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::alloc_f128_private;
  use ix_stage4_trace::{
    F128CircuitStructureAccumulatorTraceV1, F128MatrixFoldClaimBindingV1,
  };

  struct Fixture {
    trace: F128CircuitStructureAccumulatorTraceV1,
    row_point: [u8; 16],
    column_point: [u8; 16],
    claim_value: [u8; 16],
    observations: Vec<[u8; 16]>,
    challenges: Vec<[u8; 16]>,
  }

  fn scalar(value: u64) -> [u8; 16] {
    u128::from(value).to_le_bytes()
  }

  fn add_native(left: [u8; 16], right: [u8; 16]) -> [u8; 16] {
    native_f128_add(left, right)
  }

  fn mul_native(left: [u8; 16], right: [u8; 16]) -> [u8; 16] {
    native_f128_multiply(left, right)
  }

  fn fold_pair(pair: [[u8; 16]; 2], challenge: [u8; 16]) -> [u8; 16] {
    add_native(pair[0], mul_native(add_native(pair[0], pair[1]), challenge))
  }

  fn eq_pair(point: [u8; 16]) -> [[u8; 16]; 2] {
    [add_native(scalar(1), point), point]
  }

  fn fixture() -> Fixture {
    let row_point = scalar(2);
    let column_point = scalar(3);
    let row_weight = eq_pair(row_point);
    let column_weight = eq_pair(column_point);
    let matrix = [[scalar(5), scalar(7)], [scalar(11), scalar(13)]];
    let comb = [
      add_native(
        mul_native(row_weight[0], matrix[0][0]),
        mul_native(row_weight[1], matrix[1][0]),
      ),
      add_native(
        mul_native(row_weight[0], matrix[0][1]),
        mul_native(row_weight[1], matrix[1][1]),
      ),
    ];
    let claim_value = add_native(
      mul_native(column_weight[0], comb[0]),
      mul_native(column_weight[1], comb[1]),
    );
    let lambda = scalar(17);
    let column_challenge = scalar(19);
    let column_one = mul_native(lambda, mul_native(column_weight[1], comb[1]));
    let column_infinity = mul_native(
      lambda,
      mul_native(
        add_native(column_weight[0], column_weight[1]),
        add_native(comb[0], comb[1]),
      ),
    );
    let bridge = fold_pair(comb, column_challenge);
    let column_eval = eq_pair(column_challenge);
    let h = [
      add_native(
        mul_native(matrix[0][0], column_eval[0]),
        mul_native(matrix[0][1], column_eval[1]),
      ),
      add_native(
        mul_native(matrix[1][0], column_eval[0]),
        mul_native(matrix[1][1], column_eval[1]),
      ),
    ];
    let mu = scalar(23);
    let row_challenge = scalar(29);
    let weighted_row =
      [mul_native(mu, row_weight[0]), mul_native(mu, row_weight[1])];
    let row_one = mul_native(weighted_row[1], h[1]);
    let row_infinity = mul_native(
      add_native(weighted_row[0], weighted_row[1]),
      add_native(h[0], h[1]),
    );
    let root_value = fold_pair(h, row_challenge);
    let observations = vec![
      scalar(1),
      row_point,
      scalar(1),
      column_point,
      claim_value,
      column_one,
      column_infinity,
      bridge,
      row_one,
      row_infinity,
      root_value,
    ];
    let challenges = vec![lambda, column_challenge, mu, row_challenge];
    let matrix_id = F128CircuitStructureMatrixIdV1 {
      circuit_digest: [4; 32],
      row_variables: 1,
      column_variables: 1,
    };
    let trace = F128CircuitStructureAccumulatorTraceV1 {
      matrix: matrix_id,
      circuit_digest_payload: 0,
      claims: vec![F128MatrixFoldClaimBindingV1 {
        claim: 0,
        row_low_observations: vec![0],
        row_point_observations: vec![1],
        column_low_observations: vec![2],
        column_point_observations: vec![3],
        value_observation: 4,
      }],
      lambda_challenges: vec![0],
      column_rounds: vec![F128MatrixFoldRoundV1 {
        one_observation: 5,
        infinity_observation: 6,
        challenge: 1,
      }],
      bridge_observations: vec![7],
      mu_challenges: vec![2],
      row_rounds: vec![F128MatrixFoldRoundV1 {
        one_observation: 8,
        infinity_observation: 9,
        challenge: 3,
      }],
      value_observation: 10,
    };
    Fixture {
      trace,
      row_point,
      column_point,
      claim_value,
      observations,
      challenges,
    }
  }

  fn compile(
    fixture: &Fixture,
  ) -> Result<
    (
      crate::CanonicalR1csV1,
      crate::Witness,
      F128CircuitStructureAccumulatorCircuitOutputV1,
    ),
    F128CircuitStructureAccumulatorCircuitError,
  > {
    let mut builder = R1csBuilder::new();
    let public_root = alloc_f128_circuit_structure_root_public_input(
      &mut builder,
      &F128CircuitStructureRootClaimPublicInputV1 {
        matrix: fixture.trace.matrix,
        row_point: vec![fixture.challenges[3]],
        column_point: vec![fixture.challenges[1]],
        value: fixture.observations[10],
      },
    )?;
    let claim = F128CircuitStructureClaimVariablesV1 {
      matrix: fixture.trace.matrix,
      row_point: vec![alloc_f128_private(
        &mut builder,
        fixture.row_point,
        PHASE,
      )?],
      column_point: vec![alloc_f128_private(
        &mut builder,
        fixture.column_point,
        PHASE,
      )?],
      value: alloc_f128_private(&mut builder, fixture.claim_value, PHASE)?,
    };
    let observations = fixture
      .observations
      .iter()
      .copied()
      .map(|value| alloc_f128_private(&mut builder, value, PHASE))
      .collect::<Result<Vec<_>, _>>()?;
    let challenges = fixture
      .challenges
      .iter()
      .copied()
      .map(|value| alloc_f128_private(&mut builder, value, PHASE))
      .collect::<Result<Vec<_>, _>>()?;
    let digest_words = [
      alloc_f128_private(&mut builder, [4; 16], PHASE)?,
      alloc_f128_private(&mut builder, [4; 16], PHASE)?,
    ];
    let payloads = vec![
      digest_words
        .iter()
        .map(F128TranscriptWordV1::from_f128_variables)
        .collect(),
    ];
    let output = constrain_f128_circuit_structure_accumulator(
      &mut builder,
      &fixture.trace,
      F128CircuitStructureAccumulatorCircuitInputsV1 {
        claims: &[claim],
        observed_values: &observations,
        byte_payloads: &payloads,
        challenges: &challenges,
      },
    )?;
    constrain_f128_circuit_structure_root_public_input(
      &mut builder,
      &public_root,
      &output.root_claim,
    )?;
    let (r1cs, witness) = builder.finish()?;
    Ok((r1cs, witness, output))
  }

  #[test]
  fn replays_rectangular_structure_fold_and_binds_public_root() {
    let fixture = fixture();
    let (r1cs, witness, output) = compile(&fixture).unwrap();
    r1cs.check(&witness).unwrap();
    assert_eq!(r1cs.census().public_variables, 3);
    assert_eq!(output.root_claim.row_point[0].value(), &fixture.challenges[3]);
    assert_eq!(
      output.root_claim.column_point[0].value(),
      &fixture.challenges[1],
    );
    assert_eq!(output.root_claim.value.value(), &fixture.observations[10]);
  }

  #[test]
  fn rejects_mutated_claim_binding_and_public_root() {
    let mut mutated = fixture();
    mutated.observations[4] = scalar(31);
    assert!(matches!(
      compile(&mutated),
      Err(F128CircuitStructureAccumulatorCircuitError::BindingMismatch { .. })
    ));

    let fixture = fixture();
    let (r1cs, mut witness, _) = compile(&fixture).unwrap();
    witness.set(crate::Variable::from_index(1), Fr::ZERO).unwrap();
    assert!(matches!(r1cs.check(&witness), Err(R1csError::Unsatisfied { .. })));
  }
}
