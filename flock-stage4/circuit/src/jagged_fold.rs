use crate::f128::{alloc_f128_constant, packed_f128_variables};
use crate::{
  ConstraintPhase, F128JaggedAssertionVariablesV1, F128JaggedClaimVariablesV1,
  F128JaggedRowWeightVariablesV1, F128TranscriptWordV1, F128VariablesV1,
  LinearCombination, R1csBuilder, R1csError, constrain_f128_add,
  constrain_f128_multiply, enforce_f128_equal,
};
use ark_bls12_381::Fr;
use ark_ff::{AdditiveGroup, Field};
use ix_stage4_trace::{
  F128JaggedAccumulatorTraceV1, F128JaggedMatrixIdV1, F128JaggedRowBindingV1,
  F128MatrixFoldRoundV1,
};
use std::fmt;

const PHASE: ConstraintPhase = ConstraintPhase::MatrixFold;

#[derive(Clone, Copy)]
pub struct F128JaggedAccumulatorCircuitInputsV1<'a> {
  pub assertion: &'a F128JaggedAssertionVariablesV1,
  pub observed_values: &'a [F128VariablesV1],
  pub byte_payloads: &'a [Vec<F128TranscriptWordV1>],
  pub challenges: &'a [F128VariablesV1],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128JaggedRootClaimVariablesV1 {
  pub matrix: F128JaggedMatrixIdV1,
  pub row_point: Vec<F128VariablesV1>,
  pub column_point: Vec<F128VariablesV1>,
  pub value: F128VariablesV1,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128JaggedAccumulatorCircuitOutputV1 {
  pub topology_digest: [u8; 32],
  pub root_claim: F128JaggedRootClaimVariablesV1,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128JaggedRootClaimPublicInputV1 {
  pub matrix: F128JaggedMatrixIdV1,
  pub row_point: Vec<[u8; 16]>,
  pub column_point: Vec<[u8; 16]>,
  pub value: [u8; 16],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128JaggedRootClaimPublicVariablesV1 {
  matrix: F128JaggedMatrixIdV1,
  row_point: Vec<crate::Variable>,
  column_point: Vec<crate::Variable>,
  value: crate::Variable,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum F128JaggedAccumulatorCircuitError {
  InvalidTrace(String),
  R1cs(R1csError),
  MissingInput(&'static str),
  MatrixMismatch,
  ClaimMismatch { claim: usize, component: &'static str },
  DigestPayloadShape { expected: usize, actual: usize },
  DigestPayloadMismatch { word: usize },
  PublicRootShape { side: &'static str, expected: usize, actual: usize },
  PublicRootMatrixMismatch,
}

impl fmt::Display for F128JaggedAccumulatorCircuitError {
  fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::InvalidTrace(error) => {
        write!(formatter, "invalid jagged accumulator trace: {error}")
      },
      Self::R1cs(error) => write!(formatter, "jagged fold R1CS: {error}"),
      Self::MissingInput(kind) => {
        write!(formatter, "missing jagged fold {kind}")
      },
      Self::MatrixMismatch => {
        write!(formatter, "jagged assertion names a different matrix")
      },
      Self::ClaimMismatch { claim, component } => write!(
        formatter,
        "jagged claim {claim} has an inconsistent {component} binding",
      ),
      Self::DigestPayloadShape { expected, actual } => write!(
        formatter,
        "jagged digest payload has {actual} words; expected {expected}",
      ),
      Self::DigestPayloadMismatch { word } => {
        write!(formatter, "jagged digest payload word {word} is inconsistent")
      },
      Self::PublicRootShape { side, expected, actual } => write!(
        formatter,
        "public jagged root has {actual} {side} coordinates; expected {expected}",
      ),
      Self::PublicRootMatrixMismatch => {
        write!(formatter, "public jagged root names a different matrix")
      },
    }
  }
}

impl std::error::Error for F128JaggedAccumulatorCircuitError {}

impl From<R1csError> for F128JaggedAccumulatorCircuitError {
  fn from(error: R1csError) -> Self {
    Self::R1cs(error)
  }
}

pub fn alloc_f128_jagged_root_public_input(
  builder: &mut R1csBuilder,
  root: &F128JaggedRootClaimPublicInputV1,
) -> Result<
  F128JaggedRootClaimPublicVariablesV1,
  F128JaggedAccumulatorCircuitError,
> {
  validate_public_shape(
    "row",
    root.matrix.row_variables,
    root.row_point.len(),
  )?;
  validate_public_shape(
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
  Ok(F128JaggedRootClaimPublicVariablesV1 {
    matrix: root.matrix,
    row_point,
    column_point,
    value,
  })
}

pub fn constrain_f128_jagged_root_public_input(
  builder: &mut R1csBuilder,
  public: &F128JaggedRootClaimPublicVariablesV1,
  derived: &F128JaggedRootClaimVariablesV1,
) -> Result<(), F128JaggedAccumulatorCircuitError> {
  if public.matrix != derived.matrix {
    return Err(F128JaggedAccumulatorCircuitError::PublicRootMatrixMismatch);
  }
  if public.row_point.len() != derived.row_point.len() {
    return Err(F128JaggedAccumulatorCircuitError::PublicRootShape {
      side: "row",
      expected: public.row_point.len(),
      actual: derived.row_point.len(),
    });
  }
  if public.column_point.len() != derived.column_point.len() {
    return Err(F128JaggedAccumulatorCircuitError::PublicRootShape {
      side: "column",
      expected: public.column_point.len(),
      actual: derived.column_point.len(),
    });
  }
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

/// Replay the jagged-layout fold without reading the layout table.
pub fn constrain_f128_jagged_accumulator(
  builder: &mut R1csBuilder,
  trace: &F128JaggedAccumulatorTraceV1,
  inputs: F128JaggedAccumulatorCircuitInputsV1<'_>,
) -> Result<
  F128JaggedAccumulatorCircuitOutputV1,
  F128JaggedAccumulatorCircuitError,
> {
  trace
    .validate(
      inputs.assertion.claims.len(),
      inputs.observed_values.len(),
      inputs.byte_payloads.len(),
      inputs.challenges.len(),
    )
    .map_err(|error| {
      F128JaggedAccumulatorCircuitError::InvalidTrace(error.to_string())
    })?;
  if inputs.assertion.matrix != trace.matrix {
    return Err(F128JaggedAccumulatorCircuitError::MatrixMismatch);
  }
  bind_digest(builder, trace, inputs.byte_payloads)?;

  let zero = alloc_f128_constant(builder, [0; 16], PHASE)?;
  let mut one_value = [0u8; 16];
  one_value[0] = 1;
  let one = alloc_f128_constant(builder, one_value, PHASE)?;
  let shape_value = f128_from_u64s(
    u64::from(trace.matrix.row_variables),
    u64::try_from(trace.claims.len()).expect("claim count fits u64"),
  );
  let shape = alloc_f128_constant(builder, shape_value, PHASE)?;
  bind_observed(
    builder,
    &shape,
    trace.shape_observation,
    inputs.observed_values,
    0,
    "shape",
  )?;

  let mut claims = Vec::with_capacity(trace.claims.len());
  for (position, binding) in trace.claims.iter().enumerate() {
    let claim = inputs
      .assertion
      .claims
      .get(to_usize(binding.claim, "input claim")?)
      .ok_or(F128JaggedAccumulatorCircuitError::MissingInput("input claim"))?;
    bind_row(builder, position, &binding.row, claim, inputs.observed_values)?;
    bind_component(
      builder,
      position,
      "column point",
      &claim.column_point,
      &binding.column_point_observations,
      inputs.observed_values,
    )?;
    bind_observed(
      builder,
      &claim.value,
      binding.value_observation,
      inputs.observed_values,
      position,
      "value",
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
    let weighted = multiply(builder, lambda, &evaluation)?;
    let term = multiply(builder, &weighted, bridge)?;
    column_expected = add(builder, &column_expected, &term)?;
  }
  enforce_f128_equal(builder, &column_running, &column_expected, PHASE);

  let mus =
    resolve_indices(&trace.mu_challenges, inputs.challenges, "mu challenge")?;
  let bridge_values = bridge.iter().collect::<Vec<_>>();
  let target = weighted_sum(builder, &bridge_values, &mus, &zero)?;
  let (row_running, row_point) = replay_rounds(
    builder,
    &trace.row_rounds,
    target,
    inputs.observed_values,
    inputs.challenges,
  )?;
  let mut row_weight = zero.clone();
  for (claim, mu) in claims.iter().zip(&mus) {
    let evaluation =
      evaluate_row(builder, &claim.row, &row_point, &zero, &one)?;
    let term = multiply(builder, mu, &evaluation)?;
    row_weight = add(builder, &row_weight, &term)?;
  }
  let value = resolve_index(
    trace.value_observation,
    inputs.observed_values,
    "root value observation",
  )?;
  let row_expected = multiply(builder, &row_weight, &value)?;
  enforce_f128_equal(builder, &row_running, &row_expected, PHASE);

  Ok(F128JaggedAccumulatorCircuitOutputV1 {
    topology_digest: trace.topology_digest(),
    root_claim: F128JaggedRootClaimVariablesV1 {
      matrix: trace.matrix,
      row_point,
      column_point,
      value,
    },
  })
}

fn bind_row(
  builder: &mut R1csBuilder,
  position: usize,
  binding: &F128JaggedRowBindingV1,
  claim: &F128JaggedClaimVariablesV1,
  observations: &[F128VariablesV1],
) -> Result<(), F128JaggedAccumulatorCircuitError> {
  match (binding, &claim.row) {
    (
      F128JaggedRowBindingV1::Eq {
        header_observation,
        scale_observation,
        point_observations,
      },
      F128JaggedRowWeightVariablesV1::Eq { scale, point },
    ) => {
      let header = alloc_f128_constant(
        builder,
        f128_from_u64s(
          0,
          u64::try_from(point.len()).expect("point length fits u64"),
        ),
        PHASE,
      )?;
      bind_observed(
        builder,
        &header,
        *header_observation,
        observations,
        position,
        "row header",
      )?;
      bind_observed(
        builder,
        scale,
        *scale_observation,
        observations,
        position,
        "row scale",
      )?;
      bind_component(
        builder,
        position,
        "row point",
        point,
        point_observations,
        observations,
      )
    },
    (
      F128JaggedRowBindingV1::Combo { header_observation, terms: bindings },
      F128JaggedRowWeightVariablesV1::Combo { terms },
    ) => {
      if bindings.len() != terms.len() {
        return Err(F128JaggedAccumulatorCircuitError::ClaimMismatch {
          claim: position,
          component: "combo length",
        });
      }
      let header = alloc_f128_constant(
        builder,
        f128_from_u64s(
          1,
          u64::try_from(terms.len()).expect("term count fits u64"),
        ),
        PHASE,
      )?;
      bind_observed(
        builder,
        &header,
        *header_observation,
        observations,
        position,
        "row header",
      )?;
      for (binding, term) in bindings.iter().zip(terms) {
        if binding.address != term.address {
          return Err(F128JaggedAccumulatorCircuitError::ClaimMismatch {
            claim: position,
            component: "combo address",
          });
        }
        bind_observed(
          builder,
          &term.coefficient,
          binding.coefficient_observation,
          observations,
          position,
          "combo coefficient",
        )?;
        let address = alloc_f128_constant(
          builder,
          f128_from_u64s(u64::from(term.address), 0),
          PHASE,
        )?;
        bind_observed(
          builder,
          &address,
          binding.address_observation,
          observations,
          position,
          "combo address",
        )?;
      }
      Ok(())
    },
    _ => Err(F128JaggedAccumulatorCircuitError::ClaimMismatch {
      claim: position,
      component: "row-weight kind",
    }),
  }
}

fn bind_digest(
  builder: &mut R1csBuilder,
  trace: &F128JaggedAccumulatorTraceV1,
  payloads: &[Vec<F128TranscriptWordV1>],
) -> Result<(), F128JaggedAccumulatorCircuitError> {
  let payload = payloads
    .get(to_usize(trace.circuit_digest_payload, "digest payload")?)
    .ok_or(F128JaggedAccumulatorCircuitError::MissingInput("digest payload"))?;
  let expected = [
    trace.matrix.circuit_digest[..16]
      .try_into()
      .expect("digest half has 16 bytes"),
    trace.matrix.circuit_digest[16..]
      .try_into()
      .expect("digest half has 16 bytes"),
  ];
  if payload.len() != expected.len() {
    return Err(F128JaggedAccumulatorCircuitError::DigestPayloadShape {
      expected: expected.len(),
      actual: payload.len(),
    });
  }
  for (word, (actual, expected)) in payload.iter().zip(expected).enumerate() {
    if actual.value() != &expected {
      return Err(F128JaggedAccumulatorCircuitError::DigestPayloadMismatch {
        word,
      });
    }
    let mut coefficient = Fr::ONE;
    let packed = LinearCombination::from_terms(
      actual.bit_expressions().iter().flat_map(|expression| {
        let scaled = expression.clone().scale(coefficient);
        coefficient.double_in_place();
        scaled.terms().to_vec()
      }),
    );
    builder.enforce_zero(
      PHASE,
      packed.minus(&LinearCombination::from_constant(fr_from_f128(expected))),
    );
  }
  Ok(())
}

fn bind_component(
  builder: &mut R1csBuilder,
  claim: usize,
  component: &'static str,
  values: &[F128VariablesV1],
  indices: &[u64],
  observations: &[F128VariablesV1],
) -> Result<(), F128JaggedAccumulatorCircuitError> {
  if values.len() != indices.len() {
    return Err(F128JaggedAccumulatorCircuitError::ClaimMismatch {
      claim,
      component,
    });
  }
  for (value, &index) in values.iter().zip(indices) {
    bind_observed(builder, value, index, observations, claim, component)?;
  }
  Ok(())
}

fn bind_observed(
  builder: &mut R1csBuilder,
  value: &F128VariablesV1,
  index: u64,
  observations: &[F128VariablesV1],
  claim: usize,
  component: &'static str,
) -> Result<(), F128JaggedAccumulatorCircuitError> {
  let observed = resolve_index(index, observations, "claim observation")?;
  if value.value() != observed.value() {
    return Err(F128JaggedAccumulatorCircuitError::ClaimMismatch {
      claim,
      component,
    });
  }
  enforce_f128_equal(builder, value, &observed, PHASE);
  Ok(())
}

fn evaluate_row(
  builder: &mut R1csBuilder,
  row: &F128JaggedRowWeightVariablesV1,
  point: &[F128VariablesV1],
  zero: &F128VariablesV1,
  one: &F128VariablesV1,
) -> Result<F128VariablesV1, F128JaggedAccumulatorCircuitError> {
  match row {
    F128JaggedRowWeightVariablesV1::Eq { scale, point: claim_point } => {
      let evaluation = evaluate_eq(builder, claim_point, point, one)?;
      multiply(builder, scale, &evaluation)
    },
    F128JaggedRowWeightVariablesV1::Combo { terms } => {
      let mut output = zero.clone();
      for term in terms {
        let mut evaluation = one.clone();
        for (bit, coordinate) in point.iter().enumerate() {
          let factor =
            if bit < u32::BITS as usize && (term.address >> bit) & 1 == 1 {
              coordinate.clone()
            } else {
              add(builder, one, coordinate)?
            };
          evaluation = multiply(builder, &evaluation, &factor)?;
        }
        let contribution = multiply(builder, &term.coefficient, &evaluation)?;
        output = add(builder, &output, &contribution)?;
      }
      Ok(output)
    },
  }
}

fn evaluate_eq(
  builder: &mut R1csBuilder,
  claim_point: &[F128VariablesV1],
  evaluation_point: &[F128VariablesV1],
  one: &F128VariablesV1,
) -> Result<F128VariablesV1, F128JaggedAccumulatorCircuitError> {
  if claim_point.len() != evaluation_point.len() {
    return Err(F128JaggedAccumulatorCircuitError::MissingInput(
      "evaluation point",
    ));
  }
  let mut output = one.clone();
  for (coordinate, challenge) in claim_point.iter().zip(evaluation_point) {
    let zero_branch = add(builder, one, coordinate)?;
    let factor = add(builder, &zero_branch, challenge)?;
    output = multiply(builder, &output, &factor)?;
  }
  Ok(output)
}

fn replay_rounds(
  builder: &mut R1csBuilder,
  rounds: &[F128MatrixFoldRoundV1],
  mut running: F128VariablesV1,
  observations: &[F128VariablesV1],
  challenges: &[F128VariablesV1],
) -> Result<
  (F128VariablesV1, Vec<F128VariablesV1>),
  F128JaggedAccumulatorCircuitError,
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
    let linear = add(builder, &q_zero, &q_one)?;
    let linear = add(builder, &linear, &q_infinity)?;
    let infinity_times_r = multiply(builder, &q_infinity, &challenge)?;
    let quadratic = multiply(builder, &infinity_times_r, &challenge)?;
    let linear = multiply(builder, &linear, &challenge)?;
    let nonconstant = add(builder, &quadratic, &linear)?;
    running = add(builder, &q_zero, &nonconstant)?;
    point.push(challenge);
  }
  Ok((running, point))
}

fn weighted_sum(
  builder: &mut R1csBuilder,
  values: &[&F128VariablesV1],
  coefficients: &[F128VariablesV1],
  zero: &F128VariablesV1,
) -> Result<F128VariablesV1, F128JaggedAccumulatorCircuitError> {
  if values.len() != coefficients.len() {
    return Err(F128JaggedAccumulatorCircuitError::MissingInput(
      "weighted-sum coefficient",
    ));
  }
  let mut output = zero.clone();
  for (value, coefficient) in values.iter().zip(coefficients) {
    let term = multiply(builder, value, coefficient)?;
    output = add(builder, &output, &term)?;
  }
  Ok(output)
}

fn resolve_indices(
  indices: &[u64],
  values: &[F128VariablesV1],
  kind: &'static str,
) -> Result<Vec<F128VariablesV1>, F128JaggedAccumulatorCircuitError> {
  indices.iter().map(|&index| resolve_index(index, values, kind)).collect()
}

fn resolve_index(
  index: u64,
  values: &[F128VariablesV1],
  kind: &'static str,
) -> Result<F128VariablesV1, F128JaggedAccumulatorCircuitError> {
  values
    .get(to_usize(index, kind)?)
    .cloned()
    .ok_or(F128JaggedAccumulatorCircuitError::MissingInput(kind))
}

fn to_usize(
  index: u64,
  kind: &'static str,
) -> Result<usize, F128JaggedAccumulatorCircuitError> {
  usize::try_from(index)
    .map_err(|_| F128JaggedAccumulatorCircuitError::MissingInput(kind))
}

fn add(
  builder: &mut R1csBuilder,
  left: &F128VariablesV1,
  right: &F128VariablesV1,
) -> Result<F128VariablesV1, F128JaggedAccumulatorCircuitError> {
  Ok(constrain_f128_add(builder, left, right, PHASE)?)
}

fn multiply(
  builder: &mut R1csBuilder,
  left: &F128VariablesV1,
  right: &F128VariablesV1,
) -> Result<F128VariablesV1, F128JaggedAccumulatorCircuitError> {
  Ok(constrain_f128_multiply(builder, left, right, PHASE)?)
}

fn validate_public_shape(
  side: &'static str,
  expected: u32,
  actual: usize,
) -> Result<(), F128JaggedAccumulatorCircuitError> {
  let expected = usize::try_from(expected).map_err(|_| {
    F128JaggedAccumulatorCircuitError::PublicRootShape {
      side,
      expected: usize::MAX,
      actual,
    }
  })?;
  if expected != actual {
    return Err(F128JaggedAccumulatorCircuitError::PublicRootShape {
      side,
      expected,
      actual,
    });
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
    LinearCombination::from_variable(public)
      .minus(&packed_f128_variables(derived)),
  );
}

fn fr_from_f128(value: [u8; 16]) -> Fr {
  let encoded = u128::from_le_bytes(value);
  let low = u64::try_from(encoded & u128::from(u64::MAX))
    .expect("masked value fits u64");
  let high = u64::try_from(encoded >> 64).expect("high half fits u64");
  Fr::from(low) + Fr::from(high) * Fr::from(u128::from(1u64) << 64)
}

fn f128_from_u64s(low: u64, high: u64) -> [u8; 16] {
  (u128::from(low) | (u128::from(high) << 64)).to_le_bytes()
}
