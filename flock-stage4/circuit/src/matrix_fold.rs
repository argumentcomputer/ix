use crate::algebra::{
  F128DeferredMatrixClaimVariablesV1, F128StructuredWeightVariablesV1,
};
use crate::f128::{
  alloc_f128_constant, native_f128_add, native_f128_multiply,
  packed_f128_variables,
};
use crate::{
  ConstraintPhase, F128TranscriptWordV1, F128VariablesV1, LinearCombination,
  R1csBuilder, R1csError, constrain_f128_add, constrain_f128_multiply,
  enforce_f128_equal,
};
use ark_bls12_381::Fr;
use ark_ff::{AdditiveGroup, Field, PrimeField};
use ix_stage4_trace::{
  F128MatrixAccumulatorTraceV1, F128MatrixFoldRoundV1, F128StaticMatrixIdV1,
};
use std::fmt;

const PHASE: ConstraintPhase = ConstraintPhase::MatrixFold;

/// Already-constrained inputs shared with the deferred verifier algebra and
/// the accumulator's chained-BLAKE3 transcript.
#[derive(Clone, Copy)]
pub struct F128MatrixAccumulatorCircuitInputsV1<'a> {
  pub claims: &'a [F128DeferredMatrixClaimVariablesV1],
  pub observed_values: &'a [F128VariablesV1],
  pub byte_payloads: &'a [Vec<F128TranscriptWordV1>],
  pub challenges: &'a [F128VariablesV1],
}

/// One plain `eq(row_point) ⊗ eq(column_point)` root claim.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128RootMatrixClaimVariablesV1 {
  pub matrix: F128StaticMatrixIdV1,
  pub row_point: Vec<F128VariablesV1>,
  pub column_point: Vec<F128VariablesV1>,
  pub value: F128VariablesV1,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128MatrixAccumulatorCircuitOutputV1 {
  pub topology_digest: [u8; 32],
  /// Conditional accumulator outputs. A terminal verifier must publish and
  /// directly discharge these claims against the named registry matrices.
  pub root_claims: Vec<F128RootMatrixClaimVariablesV1>,
}

/// Public values for one terminal matrix root claim.
///
/// The field-element order is row point, column point, then value. Every
/// `GF(2^128)` element is interpreted as a little-endian integer below
/// `2^128`, making its embedding in BLS12-381 `Fr` injective.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128RootMatrixClaimPublicInputV1 {
  pub matrix: F128StaticMatrixIdV1,
  pub row_point: Vec<[u8; 16]>,
  pub column_point: Vec<[u8; 16]>,
  pub value: [u8; 16],
}

/// Public `Fr` wires allocated for one terminal matrix root claim.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128RootMatrixClaimPublicVariablesV1 {
  matrix: F128StaticMatrixIdV1,
  row_point: Vec<crate::Variable>,
  column_point: Vec<crate::Variable>,
  value: crate::Variable,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum F128MatrixAccumulatorCircuitError {
  InvalidTrace(String),
  R1cs(R1csError),
  MissingInput(&'static str),
  RegistryPayloadShape {
    kind: &'static str,
    expected: usize,
    actual: usize,
  },
  RegistryPayloadMismatch {
    kind: &'static str,
    word: usize,
  },
  MatrixMismatch {
    fold: usize,
    claim: usize,
  },
  WeightShape {
    fold: usize,
    claim: usize,
    side: &'static str,
  },
  BindingShape {
    fold: usize,
    claim: usize,
    component: &'static str,
    expected: usize,
    actual: usize,
  },
  BindingMismatch {
    fold: usize,
    claim: usize,
    component: &'static str,
    element: usize,
  },
  ConsistencyMismatch {
    fold: usize,
    which: &'static str,
  },
  PublicRootCount {
    expected: usize,
    actual: usize,
  },
  PublicRootPointShape {
    claim: usize,
    side: &'static str,
    expected: usize,
    actual: usize,
  },
  PublicRootMatrixMismatch {
    claim: usize,
  },
}

impl fmt::Display for F128MatrixAccumulatorCircuitError {
  fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::InvalidTrace(error) => {
        write!(formatter, "invalid F128 matrix-accumulator trace: {error}")
      },
      Self::R1cs(error) => write!(formatter, "F128 matrix-fold R1CS: {error}"),
      Self::MissingInput(kind) => {
        write!(formatter, "missing matrix-fold {kind}")
      },
      Self::RegistryPayloadShape { kind, expected, actual } => write!(
        formatter,
        "matrix-accumulator {kind} payload has {actual} words; expected {expected}",
      ),
      Self::RegistryPayloadMismatch { kind, word } => write!(
        formatter,
        "matrix-accumulator {kind} payload word {word} is inconsistent",
      ),
      Self::MatrixMismatch { fold, claim } => write!(
        formatter,
        "matrix fold {fold} input claim {claim} names a different matrix",
      ),
      Self::WeightShape { fold, claim, side } => write!(
        formatter,
        "matrix fold {fold} input claim {claim} has a malformed {side} weight",
      ),
      Self::BindingShape { fold, claim, component, expected, actual } => {
        write!(
          formatter,
          "matrix fold {fold} claim {claim} {component} binding has {actual} values; expected {expected}",
        )
      },
      Self::BindingMismatch { fold, claim, component, element } => write!(
        formatter,
        "matrix fold {fold} claim {claim} {component} binding {element} is inconsistent",
      ),
      Self::ConsistencyMismatch { fold, which } => write!(
        formatter,
        "matrix fold {fold} failed its {which} consistency equation",
      ),
      Self::PublicRootCount { expected, actual } => write!(
        formatter,
        "matrix accumulator has {actual} public root claims; expected {expected}",
      ),
      Self::PublicRootPointShape { claim, side, expected, actual } => write!(
        formatter,
        "public matrix root {claim} has {actual} {side} coordinates; expected {expected}",
      ),
      Self::PublicRootMatrixMismatch { claim } => write!(
        formatter,
        "public matrix root {claim} names a different registry matrix",
      ),
    }
  }
}

impl std::error::Error for F128MatrixAccumulatorCircuitError {}

impl From<R1csError> for F128MatrixAccumulatorCircuitError {
  fn from(error: R1csError) -> Self {
    Self::R1cs(error)
  }
}

/// Allocate the terminal matrix roots as public `Fr` inputs.
///
/// This must run before any private allocation because canonical Stage 4 R1CS
/// numbers every public variable before its witness variables. Matrix IDs and
/// point lengths remain circuit topology; only coordinates and evaluations
/// consume public fields.
pub fn alloc_f128_matrix_root_public_inputs(
  builder: &mut R1csBuilder,
  roots: &[F128RootMatrixClaimPublicInputV1],
) -> Result<
  Vec<F128RootMatrixClaimPublicVariablesV1>,
  F128MatrixAccumulatorCircuitError,
> {
  for (claim, root) in roots.iter().enumerate() {
    validate_public_root_point_shape(
      claim,
      "row",
      root.matrix.variables,
      root.row_point.len(),
    )?;
    validate_public_root_point_shape(
      claim,
      "column",
      root.matrix.variables,
      root.column_point.len(),
    )?;
  }

  roots
    .iter()
    .map(|root| {
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
      Ok(F128RootMatrixClaimPublicVariablesV1 {
        matrix: root.matrix,
        row_point,
        column_point,
        value,
      })
    })
    .collect()
}

/// Bind derived fold outputs to their public terminal root claims.
pub fn constrain_f128_matrix_root_public_inputs(
  builder: &mut R1csBuilder,
  public_roots: &[F128RootMatrixClaimPublicVariablesV1],
  derived_roots: &[F128RootMatrixClaimVariablesV1],
) -> Result<(), F128MatrixAccumulatorCircuitError> {
  if public_roots.len() != derived_roots.len() {
    return Err(F128MatrixAccumulatorCircuitError::PublicRootCount {
      expected: derived_roots.len(),
      actual: public_roots.len(),
    });
  }
  for (claim, (public, derived)) in
    public_roots.iter().zip(derived_roots).enumerate()
  {
    if public.matrix != derived.matrix {
      return Err(
        F128MatrixAccumulatorCircuitError::PublicRootMatrixMismatch { claim },
      );
    }
    validate_public_root_binding_shape(
      claim,
      "row",
      &public.row_point,
      &derived.row_point,
    )?;
    validate_public_root_binding_shape(
      claim,
      "column",
      &public.column_point,
      &derived.column_point,
    )?;
    for (variable, value) in public.row_point.iter().zip(&derived.row_point) {
      constrain_public_f128(builder, *variable, value);
    }
    for (variable, value) in
      public.column_point.iter().zip(&derived.column_point)
    {
      constrain_public_f128(builder, *variable, value);
    }
    constrain_public_f128(builder, public.value, &derived.value);
  }
  Ok(())
}

fn validate_public_root_point_shape(
  claim: usize,
  side: &'static str,
  variables: u32,
  actual: usize,
) -> Result<(), F128MatrixAccumulatorCircuitError> {
  let expected = usize::try_from(variables).expect("u32 fits usize");
  if actual != expected {
    return Err(F128MatrixAccumulatorCircuitError::PublicRootPointShape {
      claim,
      side,
      expected,
      actual,
    });
  }
  Ok(())
}

fn validate_public_root_binding_shape(
  claim: usize,
  side: &'static str,
  public: &[crate::Variable],
  derived: &[F128VariablesV1],
) -> Result<(), F128MatrixAccumulatorCircuitError> {
  if public.len() != derived.len() {
    return Err(F128MatrixAccumulatorCircuitError::PublicRootPointShape {
      claim,
      side,
      expected: derived.len(),
      actual: public.len(),
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
    packed_f128_variables(derived)
      .minus(&LinearCombination::from_variable(public)),
  );
}

fn fr_from_f128(value: [u8; 16]) -> Fr {
  Fr::from_le_bytes_mod_order(&value)
}

/// Replay all matrix folds without reading a matrix.
///
/// The trace validates total input-claim coverage, binds each claim to the
/// observations that precede its Fiat-Shamir challenges, and checks both
/// sumchecks. The returned roots are still conditional: sound terminal use
/// publishes them and performs the registry-static direct checks outside the
/// recursive circuit.
pub fn constrain_f128_matrix_accumulator(
  builder: &mut R1csBuilder,
  trace: &F128MatrixAccumulatorTraceV1,
  inputs: F128MatrixAccumulatorCircuitInputsV1<'_>,
) -> Result<
  F128MatrixAccumulatorCircuitOutputV1,
  F128MatrixAccumulatorCircuitError,
> {
  trace
    .validate(
      inputs.claims.len(),
      inputs.observed_values.len(),
      inputs.byte_payloads.len(),
      inputs.challenges.len(),
    )
    .map_err(|error| {
      F128MatrixAccumulatorCircuitError::InvalidTrace(error.to_string())
    })?;

  bind_protocol_payloads(builder, trace, inputs.byte_payloads)?;
  let zero = alloc_f128_constant(builder, [0; 16], PHASE)?;
  let mut one_value = [0; 16];
  one_value[0] = 1;
  let one = alloc_f128_constant(builder, one_value, PHASE)?;

  let mut root_claims = Vec::with_capacity(trace.folds.len());
  for (fold_index, fold) in trace.folds.iter().enumerate() {
    let mut claims = Vec::with_capacity(fold.claims.len());
    for (claim_position, binding) in fold.claims.iter().enumerate() {
      let claim =
        inputs.claims.get(to_usize(binding.claim, "input claim")?).ok_or(
          F128MatrixAccumulatorCircuitError::MissingInput("input claim"),
        )?;
      if claim.matrix != fold.matrix {
        return Err(F128MatrixAccumulatorCircuitError::MatrixMismatch {
          fold: fold_index,
          claim: claim_position,
        });
      }
      validate_weight_shape(
        &claim.row,
        fold.matrix.variables,
        fold_index,
        claim_position,
        "row",
      )?;
      validate_weight_shape(
        &claim.column,
        fold.matrix.variables,
        fold_index,
        claim_position,
        "column",
      )?;
      bind_claim(
        builder,
        claim,
        binding,
        inputs.observed_values,
        fold_index,
        claim_position,
      )?;
      claims.push(claim);
    }

    let lambdas = resolve_indices(
      &fold.lambda_challenges,
      inputs.challenges,
      "lambda challenge",
    )?;
    let claim_values =
      claims.iter().map(|claim| &claim.value).collect::<Vec<_>>();
    let target = weighted_sum(builder, &claim_values, &lambdas, &zero)?;
    let (column_running, column_point) = replay_rounds(
      builder,
      &fold.column_rounds,
      target,
      inputs.observed_values,
      inputs.challenges,
    )?;
    let bridge = resolve_indices(
      &fold.bridge_observations,
      inputs.observed_values,
      "bridge observation",
    )?;
    let mut column_expected = zero.clone();
    for ((claim, lambda), bridge) in claims.iter().zip(&lambdas).zip(&bridge) {
      let evaluation =
        evaluate_weight(builder, &claim.column, &column_point, &one)?;
      let scaled = multiply(builder, lambda, &evaluation)?;
      let term = multiply(builder, &scaled, bridge)?;
      column_expected = add(builder, &column_expected, &term)?;
    }
    enforce_consistency(
      builder,
      &column_running,
      &column_expected,
      fold_index,
      "column",
    )?;

    let mus =
      resolve_indices(&fold.mu_challenges, inputs.challenges, "mu challenge")?;
    let bridge_refs = bridge.iter().collect::<Vec<_>>();
    let target = weighted_sum(builder, &bridge_refs, &mus, &zero)?;
    let (row_running, row_point) = replay_rounds(
      builder,
      &fold.row_rounds,
      target,
      inputs.observed_values,
      inputs.challenges,
    )?;
    let mut row_weight = zero.clone();
    for (claim, mu) in claims.iter().zip(&mus) {
      let evaluation = evaluate_weight(builder, &claim.row, &row_point, &one)?;
      let term = multiply(builder, mu, &evaluation)?;
      row_weight = add(builder, &row_weight, &term)?;
    }
    let value = resolve_index(
      fold.value_observation,
      inputs.observed_values,
      "root-value observation",
    )?;
    let row_expected = multiply(builder, &row_weight, &value)?;
    enforce_consistency(
      builder,
      &row_running,
      &row_expected,
      fold_index,
      "row",
    )?;

    root_claims.push(F128RootMatrixClaimVariablesV1 {
      matrix: fold.matrix,
      row_point,
      column_point,
      value,
    });
  }

  Ok(F128MatrixAccumulatorCircuitOutputV1 {
    topology_digest: trace.topology_digest(),
    root_claims,
  })
}

fn bind_protocol_payloads(
  builder: &mut R1csBuilder,
  trace: &F128MatrixAccumulatorTraceV1,
  payloads: &[Vec<F128TranscriptWordV1>],
) -> Result<(), F128MatrixAccumulatorCircuitError> {
  let digest_payload = payloads
    .get(to_usize(trace.registry_digest_payload, "registry payload")?)
    .ok_or(F128MatrixAccumulatorCircuitError::MissingInput(
      "registry payload",
    ))?;
  let expected_digest = [
    trace.registry_digest[..16]
      .try_into()
      .expect("registry digest half has 16 bytes"),
    trace.registry_digest[16..]
      .try_into()
      .expect("registry digest half has 16 bytes"),
  ];
  bind_payload(builder, digest_payload, &expected_digest, "registry digest")?;

  let prior_payload = payloads
    .get(to_usize(trace.prior_count_payload, "prior-count payload")?)
    .ok_or(F128MatrixAccumulatorCircuitError::MissingInput(
      "prior-count payload",
    ))?;
  let mut expected_prior = [0; 16];
  expected_prior[0] = trace.prior_accumulators;
  bind_payload(builder, prior_payload, &[expected_prior], "prior count")
}

fn bind_payload(
  builder: &mut R1csBuilder,
  actual: &[F128TranscriptWordV1],
  expected: &[[u8; 16]],
  kind: &'static str,
) -> Result<(), F128MatrixAccumulatorCircuitError> {
  if actual.len() != expected.len() {
    return Err(F128MatrixAccumulatorCircuitError::RegistryPayloadShape {
      kind,
      expected: expected.len(),
      actual: actual.len(),
    });
  }
  for (word, (actual, expected)) in actual.iter().zip(expected).enumerate() {
    if actual.value() != expected {
      return Err(F128MatrixAccumulatorCircuitError::RegistryPayloadMismatch {
        kind,
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
    let encoded = u128::from_le_bytes(*expected);
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

fn bind_claim(
  builder: &mut R1csBuilder,
  claim: &F128DeferredMatrixClaimVariablesV1,
  binding: &ix_stage4_trace::F128MatrixFoldClaimBindingV1,
  observations: &[F128VariablesV1],
  fold: usize,
  claim_index: usize,
) -> Result<(), F128MatrixAccumulatorCircuitError> {
  bind_component(
    builder,
    &claim.row.low,
    &binding.row_low_observations,
    observations,
    fold,
    claim_index,
    "row-low",
  )?;
  bind_component(
    builder,
    &claim.row.point,
    &binding.row_point_observations,
    observations,
    fold,
    claim_index,
    "row-point",
  )?;
  bind_component(
    builder,
    &claim.column.low,
    &binding.column_low_observations,
    observations,
    fold,
    claim_index,
    "column-low",
  )?;
  bind_component(
    builder,
    &claim.column.point,
    &binding.column_point_observations,
    observations,
    fold,
    claim_index,
    "column-point",
  )?;
  let observed = resolve_index(
    binding.value_observation,
    observations,
    "claim-value observation",
  )?;
  bind_equal(builder, &claim.value, &observed, fold, claim_index, "value", 0)
}

#[allow(clippy::too_many_arguments)]
fn bind_component(
  builder: &mut R1csBuilder,
  values: &[F128VariablesV1],
  indices: &[u64],
  observations: &[F128VariablesV1],
  fold: usize,
  claim: usize,
  component: &'static str,
) -> Result<(), F128MatrixAccumulatorCircuitError> {
  if values.len() != indices.len() {
    return Err(F128MatrixAccumulatorCircuitError::BindingShape {
      fold,
      claim,
      component,
      expected: values.len(),
      actual: indices.len(),
    });
  }
  for (element, (value, &index)) in values.iter().zip(indices).enumerate() {
    let observed = resolve_index(index, observations, "claim observation")?;
    bind_equal(builder, value, &observed, fold, claim, component, element)?;
  }
  Ok(())
}

#[allow(clippy::too_many_arguments)]
fn bind_equal(
  builder: &mut R1csBuilder,
  value: &F128VariablesV1,
  observed: &F128VariablesV1,
  fold: usize,
  claim: usize,
  component: &'static str,
  element: usize,
) -> Result<(), F128MatrixAccumulatorCircuitError> {
  if value.value() != observed.value() {
    return Err(F128MatrixAccumulatorCircuitError::BindingMismatch {
      fold,
      claim,
      component,
      element,
    });
  }
  enforce_f128_equal(builder, value, observed, PHASE);
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
  F128MatrixAccumulatorCircuitError,
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

fn evaluate_weight(
  builder: &mut R1csBuilder,
  weight: &F128StructuredWeightVariablesV1,
  point: &[F128VariablesV1],
  one: &F128VariablesV1,
) -> Result<F128VariablesV1, F128MatrixAccumulatorCircuitError> {
  let low_variables = weight.low.len().trailing_zeros() as usize;
  let mut low = weight.low.clone();
  for challenge in &point[..low_variables] {
    let half = low.len() / 2;
    let mut folded = Vec::with_capacity(half);
    for pair in low.as_chunks::<2>().0 {
      // a(1-r) + b r = a + (a+b)r in characteristic two.
      let difference = add(builder, &pair[0], &pair[1])?;
      let correction = multiply(builder, &difference, challenge)?;
      folded.push(add(builder, &pair[0], &correction)?);
    }
    low = folded;
  }
  let mut output = low.into_iter().next().ok_or(
    F128MatrixAccumulatorCircuitError::MissingInput("weight low factor"),
  )?;
  for (coordinate, challenge) in
    weight.point.iter().zip(&point[low_variables..])
  {
    // p r + (1+p)(1+r) = 1+p+r in characteristic two.
    let one_plus_coordinate = add(builder, one, coordinate)?;
    let factor = add(builder, &one_plus_coordinate, challenge)?;
    output = multiply(builder, &output, &factor)?;
  }
  Ok(output)
}

fn validate_weight_shape(
  weight: &F128StructuredWeightVariablesV1,
  variables: u32,
  fold: usize,
  claim: usize,
  side: &'static str,
) -> Result<(), F128MatrixAccumulatorCircuitError> {
  let valid = !weight.low.is_empty()
    && weight.low.len().is_power_of_two()
    && weight.low.len().checked_ilog2().and_then(|low| {
      u32::try_from(weight.point.len())
        .ok()
        .and_then(|point| low.checked_add(point))
    }) == Some(variables);
  if !valid {
    return Err(F128MatrixAccumulatorCircuitError::WeightShape {
      fold,
      claim,
      side,
    });
  }
  Ok(())
}

fn weighted_sum(
  builder: &mut R1csBuilder,
  values: &[&F128VariablesV1],
  coefficients: &[F128VariablesV1],
  zero: &F128VariablesV1,
) -> Result<F128VariablesV1, F128MatrixAccumulatorCircuitError> {
  let mut result = zero.clone();
  for (value, coefficient) in values.iter().zip(coefficients) {
    let term = multiply(builder, value, coefficient)?;
    result = add(builder, &result, &term)?;
  }
  Ok(result)
}

fn enforce_consistency(
  builder: &mut R1csBuilder,
  actual: &F128VariablesV1,
  expected: &F128VariablesV1,
  fold: usize,
  which: &'static str,
) -> Result<(), F128MatrixAccumulatorCircuitError> {
  if actual.value() != expected.value() {
    return Err(F128MatrixAccumulatorCircuitError::ConsistencyMismatch {
      fold,
      which,
    });
  }
  enforce_f128_equal(builder, actual, expected, PHASE);
  Ok(())
}

fn add(
  builder: &mut R1csBuilder,
  left: &F128VariablesV1,
  right: &F128VariablesV1,
) -> Result<F128VariablesV1, F128MatrixAccumulatorCircuitError> {
  let output = constrain_f128_add(builder, left, right, PHASE)?;
  debug_assert_eq!(
    output.value(),
    &native_f128_add(*left.value(), *right.value()),
  );
  Ok(output)
}

fn multiply(
  builder: &mut R1csBuilder,
  left: &F128VariablesV1,
  right: &F128VariablesV1,
) -> Result<F128VariablesV1, F128MatrixAccumulatorCircuitError> {
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
) -> Result<Vec<F128VariablesV1>, F128MatrixAccumulatorCircuitError> {
  indices.iter().map(|&index| resolve_index(index, values, kind)).collect()
}

fn resolve_index(
  index: u64,
  values: &[F128VariablesV1],
  kind: &'static str,
) -> Result<F128VariablesV1, F128MatrixAccumulatorCircuitError> {
  values
    .get(to_usize(index, kind)?)
    .cloned()
    .ok_or(F128MatrixAccumulatorCircuitError::MissingInput(kind))
}

fn to_usize(
  value: u64,
  kind: &'static str,
) -> Result<usize, F128MatrixAccumulatorCircuitError> {
  usize::try_from(value)
    .map_err(|_| F128MatrixAccumulatorCircuitError::MissingInput(kind))
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::alloc_f128_private;
  use ix_stage4_trace::{
    F128MatrixFoldClaimBindingV1, F128MatrixFoldTraceV1, F128MatrixSideV1,
  };

  struct Fixture {
    trace: F128MatrixAccumulatorTraceV1,
    row: [[u8; 16]; 2],
    column: [[u8; 16]; 2],
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

  fn multiply_native(left: [u8; 16], right: [u8; 16]) -> [u8; 16] {
    native_f128_multiply(left, right)
  }

  fn fold_value(pair: [[u8; 16]; 2], challenge: [u8; 16]) -> [u8; 16] {
    add_native(
      pair[0],
      multiply_native(add_native(pair[0], pair[1]), challenge),
    )
  }

  fn fixture() -> Fixture {
    let one = scalar(1);
    let row = [scalar(2), scalar(5)];
    let column = [scalar(7), scalar(11)];
    let lambda = scalar(13);
    let column_challenge = scalar(17);
    let mu = scalar(19);
    let row_challenge = scalar(23);
    let claim_value = add_native(
      multiply_native(row[0], column[0]),
      multiply_native(row[1], column[1]),
    );

    let column_one =
      multiply_native(lambda, multiply_native(column[1], row[1]));
    let column_infinity = multiply_native(
      lambda,
      multiply_native(
        add_native(column[0], column[1]),
        add_native(row[0], row[1]),
      ),
    );
    let bridge = fold_value(row, column_challenge);

    let h = [add_native(one, column_challenge), column_challenge];
    let weighted_row =
      [multiply_native(mu, row[0]), multiply_native(mu, row[1])];
    let row_one = multiply_native(weighted_row[1], h[1]);
    let row_infinity = multiply_native(
      add_native(weighted_row[0], weighted_row[1]),
      add_native(h[0], h[1]),
    );
    let root_value = fold_value(h, row_challenge);

    let observations = vec![
      row[0],
      row[1],
      column[0],
      column[1],
      claim_value,
      column_one,
      column_infinity,
      bridge,
      row_one,
      row_infinity,
      root_value,
    ];
    let challenges = vec![lambda, column_challenge, mu, row_challenge];
    let matrix = F128StaticMatrixIdV1 {
      registry_digest: [7; 32],
      table: 0,
      side: F128MatrixSideV1::A,
      variables: 1,
    };
    let trace = F128MatrixAccumulatorTraceV1 {
      registry_digest: matrix.registry_digest,
      registry_digest_payload: 0,
      prior_count_payload: 1,
      prior_accumulators: 0,
      folds: vec![F128MatrixFoldTraceV1 {
        matrix,
        claims: vec![F128MatrixFoldClaimBindingV1 {
          claim: 0,
          row_low_observations: vec![0, 1],
          row_point_observations: Vec::new(),
          column_low_observations: vec![2, 3],
          column_point_observations: Vec::new(),
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
      }],
    };
    Fixture { trace, row, column, claim_value, observations, challenges }
  }

  fn compile(
    fixture: &Fixture,
  ) -> Result<
    (
      crate::CanonicalR1csV1,
      crate::Witness,
      F128MatrixAccumulatorCircuitOutputV1,
    ),
    F128MatrixAccumulatorCircuitError,
  > {
    let mut builder = R1csBuilder::new();
    let matrix = fixture.trace.folds[0].matrix;
    let public_roots = alloc_f128_matrix_root_public_inputs(
      &mut builder,
      &[F128RootMatrixClaimPublicInputV1 {
        matrix,
        row_point: vec![fixture.challenges[3]],
        column_point: vec![fixture.challenges[1]],
        value: fixture.observations[10],
      }],
    )?;
    let row = fixture
      .row
      .iter()
      .copied()
      .map(|value| alloc_f128_private(&mut builder, value, PHASE))
      .collect::<Result<Vec<_>, _>>()?;
    let column = fixture
      .column
      .iter()
      .copied()
      .map(|value| alloc_f128_private(&mut builder, value, PHASE))
      .collect::<Result<Vec<_>, _>>()?;
    let claim_value =
      alloc_f128_private(&mut builder, fixture.claim_value, PHASE)?;
    let claim = F128DeferredMatrixClaimVariablesV1 {
      matrix: fixture.trace.folds[0].matrix,
      row: F128StructuredWeightVariablesV1 { low: row, point: Vec::new() },
      column: F128StructuredWeightVariablesV1 {
        low: column,
        point: Vec::new(),
      },
      value: claim_value,
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
    let registry_words = [
      alloc_f128_private(&mut builder, [7; 16], PHASE)?,
      alloc_f128_private(&mut builder, [7; 16], PHASE)?,
    ];
    let prior = [alloc_f128_private(&mut builder, [0; 16], PHASE)?];
    let payloads = vec![
      registry_words
        .iter()
        .map(F128TranscriptWordV1::from_f128_variables)
        .collect(),
      prior.iter().map(F128TranscriptWordV1::from_f128_variables).collect(),
    ];
    let output = constrain_f128_matrix_accumulator(
      &mut builder,
      &fixture.trace,
      F128MatrixAccumulatorCircuitInputsV1 {
        claims: &[claim],
        observed_values: &observations,
        byte_payloads: &payloads,
        challenges: &challenges,
      },
    )?;
    constrain_f128_matrix_root_public_inputs(
      &mut builder,
      &public_roots,
      &output.root_claims,
    )?;
    let (r1cs, witness) = builder.finish()?;
    Ok((r1cs, witness, output))
  }

  #[test]
  fn replays_nonzero_fold_and_returns_plain_root_claim() {
    let fixture = fixture();
    let (r1cs, witness, output) = compile(&fixture).unwrap();
    r1cs.check(&witness).unwrap();
    assert_eq!(r1cs.census().public_variables, 3);
    assert_eq!(output.root_claims.len(), 1);
    assert_eq!(output.root_claims[0].column_point[0].value(), &scalar(17));
    assert_eq!(output.root_claims[0].row_point[0].value(), &scalar(23));
    assert_eq!(output.root_claims[0].value.value(), &fixture.observations[10],);
    assert_eq!(output.topology_digest, fixture.trace.topology_digest());
  }

  #[test]
  fn public_root_binding_rejects_mutation() {
    let fixture = fixture();
    let (r1cs, mut witness, _) = compile(&fixture).unwrap();
    witness.set(crate::Variable::from_index(1), Fr::from(0u64)).unwrap();
    assert!(matches!(r1cs.check(&witness), Err(R1csError::Unsatisfied { .. })));
  }

  #[test]
  fn rejects_unbound_claim_and_invalid_sumcheck() {
    let mut unbound = fixture();
    unbound.observations[0] = scalar(31);
    assert!(matches!(
      compile(&unbound),
      Err(F128MatrixAccumulatorCircuitError::BindingMismatch { .. })
    ));

    let mut invalid = fixture();
    invalid.observations[5] = add_native(invalid.observations[5], scalar(1));
    assert!(matches!(
      compile(&invalid),
      Err(F128MatrixAccumulatorCircuitError::ConsistencyMismatch {
        which: "column",
        ..
      })
    ));
  }
}
