use crate::f128::{alloc_f128_constant, native_f128_multiply};
use crate::merged_pcs::{constrain_eq_table, constrain_fold_round};
use crate::{
  ConstraintPhase, F128MergedPcsFrontendCircuitOutputV1, F128VariablesV1,
  R1csBuilder, R1csError, alloc_f128_private, constrain_f128_add,
  constrain_f128_frobenius, constrain_f128_multiply,
  constrain_f128_multiply_constant, enforce_f128_equal,
};
use ix_stage4_trace::{
  F128_MULTIPOINT_DUAL_VALUES, F128_MULTIPOINT_JAGGED_CLAIMS,
  F128JaggedMatrixIdV1, F128MultipointRoundV1,
  F128MultipointTwistedAssistTraceV1,
};
use std::fmt;

const PHASE: ConstraintPhase = ConstraintPhase::Pcs;

/// Already-constrained main transcript and merged-PCS frontend wires.
#[derive(Clone, Copy)]
pub struct F128MultipointTwistedAssistCircuitInputsV1<'a> {
  pub observed_values: &'a [F128VariablesV1],
  pub challenges: &'a [F128VariablesV1],
  /// The raw jagged-layout evaluations, accepted only conditionally here.
  pub private_values: &'a [[u8; 16]],
  pub frontend: &'a F128MergedPcsFrontendCircuitOutputV1,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128JaggedComboTermVariablesV1 {
  pub coefficient: F128VariablesV1,
  pub address: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum F128JaggedRowWeightVariablesV1 {
  Eq { scale: Box<F128VariablesV1>, point: Vec<F128VariablesV1> },
  Combo { terms: Vec<F128JaggedComboTermVariablesV1> },
}

/// One conditional claim on Flock's count-dependent layout table.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128JaggedClaimVariablesV1 {
  pub row: F128JaggedRowWeightVariablesV1,
  pub column_point: Vec<F128VariablesV1>,
  pub value: F128VariablesV1,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128JaggedAssertionVariablesV1 {
  pub matrix: F128JaggedMatrixIdV1,
  /// Native flattened order: RS0, RS1, packed-direct combo.
  pub claims: Vec<F128JaggedClaimVariablesV1>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128MultipointTwistedAssistCircuitOutputV1 {
  pub topology_digest: [u8; 32],
  /// The recombined twisted evaluation used by the outer merged opening.
  pub v: F128VariablesV1,
  /// Endpoint of the multipoint product sumcheck (`rho''`).
  pub point: Vec<F128VariablesV1>,
  /// Endpoint of the untwisted anchor (`sigma`).
  pub sigma: Vec<F128VariablesV1>,
  pub jagged_assertion: F128JaggedAssertionVariablesV1,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum F128MultipointCircuitError {
  InvalidTrace(String),
  FrontendMismatch(&'static str),
  MissingInput(&'static str),
  R1cs(R1csError),
}

impl fmt::Display for F128MultipointCircuitError {
  fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::InvalidTrace(error) => {
        write!(formatter, "invalid multipoint assist trace: {error}")
      },
      Self::FrontendMismatch(reason) => {
        write!(formatter, "multipoint/frontend mismatch: {reason}")
      },
      Self::MissingInput(kind) => {
        write!(formatter, "missing multipoint assist {kind}")
      },
      Self::R1cs(error) => write!(formatter, "multipoint assist R1CS: {error}"),
    }
  }
}

impl std::error::Error for F128MultipointCircuitError {}

impl From<R1csError> for F128MultipointCircuitError {
  fn from(error: R1csError) -> Self {
    Self::R1cs(error)
  }
}

/// Replay Flock's complete forked multipoint-twisted assist.
///
/// This closes the merged frontend identity `running = q_eval * v`, replays
/// both child sumchecks, and binds the anchor endpoint to three raw claims on
/// the jagged layout. The claims themselves remain conditional until the
/// digest-keyed jagged accumulator is folded and discharged.
pub fn constrain_f128_multipoint_twisted_assist(
  builder: &mut R1csBuilder,
  trace: &F128MultipointTwistedAssistTraceV1,
  inputs: F128MultipointTwistedAssistCircuitInputsV1<'_>,
) -> Result<
  F128MultipointTwistedAssistCircuitOutputV1,
  F128MultipointCircuitError,
> {
  trace
    .validate(
      inputs.observed_values.len(),
      inputs.challenges.len(),
      inputs.private_values.len(),
    )
    .map_err(|error| {
      F128MultipointCircuitError::InvalidTrace(error.to_string())
    })?;
  validate_frontend(trace, inputs.frontend)?;

  let zero = alloc_f128_constant(builder, [0; 16], PHASE)?;
  let mut one_value = [0u8; 16];
  one_value[0] = 1;
  let one = alloc_f128_constant(builder, one_value, PHASE)?;
  let private_values = inputs
    .private_values
    .iter()
    .copied()
    .map(|value| alloc_f128_private(builder, value, PHASE))
    .collect::<Result<Vec<_>, _>>()?;
  let jagged_values = get_many(
    &private_values,
    &trace.jagged_claim_private_values,
    "jagged claim value",
  )?;
  debug_assert_eq!(jagged_values.len(), F128_MULTIPOINT_JAGGED_CLAIMS);

  let dual_values = trace
    .dual_value_observations
    .iter()
    .map(|indices| get_many(inputs.observed_values, indices, "dual-form value"))
    .collect::<Result<Vec<_>, _>>()?;
  let group_values = get_many(
    inputs.observed_values,
    &trace.group_value_observations,
    "scalar-group value",
  )?;

  // Family H: derive the two ring-switch linearized-polynomial coefficient
  // vectors from the same equality weights and outer batching coefficients
  // used by the native verifier.
  let coefficients = inputs
    .frontend
    .ring_switches
    .iter()
    .zip(&inputs.frontend.batching_challenges)
    .map(|(ring, gamma)| {
      constrain_family_h_coefficients(
        builder,
        &ring.r_dprime,
        &ring.eq_r_dprime,
        gamma,
        trace,
        &one,
      )
    })
    .collect::<Result<Vec<_>, _>>()?;

  // Recombine the claimed dual values into the exact twisted evaluation V.
  let mut v = zero.clone();
  for (claim_coefficients, claim_values) in
    coefficients.iter().zip(&dual_values)
  {
    for (power, (coefficient, value)) in
      claim_coefficients.iter().zip(claim_values).enumerate()
    {
      let powered = constrain_f128_frobenius(builder, value, power, PHASE)?;
      let contribution =
        constrain_f128_multiply(builder, coefficient, &powered, PHASE)?;
      v = constrain_f128_add(builder, &v, &contribution, PHASE)?;
    }
  }
  for value in &group_values {
    v = constrain_f128_add(builder, &v, value, PHASE)?;
  }
  let outer_product =
    constrain_f128_multiply(builder, &inputs.frontend.q_eval, &v, PHASE)?;
  enforce_f128_equal(builder, &inputs.frontend.running, &outer_product, PHASE);

  // Child batching coefficient and its powers bind every sent dual/group
  // value to one dense-domain product sumcheck.
  let gamma = get(
    inputs.challenges,
    trace.gamma_challenge,
    "multipoint gamma challenge",
  )?;
  let power_count = dual_values
    .iter()
    .map(Vec::len)
    .sum::<usize>()
    .checked_add(group_values.len())
    .ok_or(F128MultipointCircuitError::FrontendMismatch(
      "multipoint power count overflow",
    ))?;
  let gamma_powers = constrain_powers(builder, &gamma, power_count, &one)?;
  let mut running = zero.clone();
  for (power, value) in
    gamma_powers.iter().zip(dual_values.iter().flatten().chain(&group_values))
  {
    let term = constrain_f128_multiply(builder, power, value, PHASE)?;
    running = constrain_f128_add(builder, &running, &term, PHASE)?;
  }
  let mut point = Vec::with_capacity(trace.multipoint_rounds.len());
  for round in &trace.multipoint_rounds {
    let (next, challenge) = constrain_round(
      builder,
      &running,
      round,
      inputs.observed_values,
      inputs.challenges,
    )?;
    running = next;
    point.push(challenge);
  }
  let anchor_value = get(
    inputs.observed_values,
    trace.anchor_value_observation,
    "anchor value",
  )?;
  enforce_f128_equal(builder, &running, &anchor_value, PHASE);

  let mut anchor_running = anchor_value;
  let mut sigma = Vec::with_capacity(trace.anchor_rounds.len());
  for round in &trace.anchor_rounds {
    let (next, challenge) = constrain_round(
      builder,
      &anchor_running,
      round,
      inputs.observed_values,
      inputs.challenges,
    )?;
    anchor_running = next;
    sigma.push(challenge);
  }

  // Closed-form endpoint coefficients for the untwisted anchor.
  let g_at = constrain_twisted_eq(
    builder,
    &gamma_powers[..F128_MULTIPOINT_DUAL_VALUES],
    &inputs.frontend.rho,
    &point,
    &one,
    &zero,
  )?;
  let e_at = constrain_eq_at(builder, &inputs.frontend.rho, &point, &one)?;
  let rs_coefficients = [
    constrain_f128_multiply(builder, &gamma_powers[0], &g_at, PHASE)?,
    constrain_f128_multiply(
      builder,
      &gamma_powers[F128_MULTIPOINT_DUAL_VALUES],
      &g_at,
      PHASE,
    )?,
  ];
  let group_coefficient = constrain_f128_multiply(
    builder,
    gamma_powers.last().ok_or(F128MultipointCircuitError::FrontendMismatch(
      "missing scalar-group gamma power",
    ))?,
    &e_at,
    PHASE,
  )?;

  let witness_row_variables = usize::try_from(trace.witness_row_variables)
    .map_err(|_| {
      F128MultipointCircuitError::FrontendMismatch(
        "witness row dimension overflow",
      )
    })?;
  let matrix_row_variables = usize::try_from(trace.matrix.row_variables)
    .map_err(|_| {
      F128MultipointCircuitError::FrontendMismatch(
        "layout row dimension overflow",
      )
    })?;
  let ring_rows = inputs
    .frontend
    .ring_switches
    .iter()
    .map(|ring| {
      ring
        .x_outer
        .get(1..1 + witness_row_variables)
        .ok_or(F128MultipointCircuitError::FrontendMismatch(
          "ring-switch row point is truncated",
        ))
        .map(<[F128VariablesV1]>::to_vec)
    })
    .collect::<Result<Vec<_>, _>>()?;
  let group_row = inputs.frontend.packed_direct_claims[0]
    .point
    .get(..witness_row_variables)
    .ok_or(F128MultipointCircuitError::FrontendMismatch(
      "scalar-group row point is truncated",
    ))?
    .to_vec();

  // Bind the trace's Boolean addresses and the single shared row point to
  // every packed-direct member before exposing the combo weight.
  for (claim, &address) in inputs
    .frontend
    .packed_direct_claims
    .iter()
    .zip(&trace.group_column_addresses)
  {
    for (left, right) in
      claim.point[..witness_row_variables].iter().zip(&group_row)
    {
      enforce_f128_equal(builder, left, right, PHASE);
    }
    for (bit, coordinate) in
      claim.point[witness_row_variables..].iter().enumerate()
    {
      let expected = if bit < u32::BITS as usize && (address >> bit) & 1 == 1 {
        &one
      } else {
        &zero
      };
      enforce_f128_equal(builder, coordinate, expected, PHASE);
    }
  }

  let sigma_eq_tables = sigma
    .as_chunks::<2>()
    .0
    .iter()
    .map(|pair| constrain_eq_table(builder, pair, &zero, &one))
    .collect::<Result<Vec<_>, _>>()?;
  let mut endpoint_expectation = zero.clone();
  for ((row, coefficient), value) in
    ring_rows.iter().zip(&rs_coefficients).zip(&jagged_values[..2])
  {
    let boundary = constrain_boundary_factor(
      builder,
      row,
      &point,
      &sigma_eq_tables,
      &zero,
      &one,
    )?;
    let weighted = constrain_f128_multiply(builder, coefficient, value, PHASE)?;
    let contribution =
      constrain_f128_multiply(builder, &weighted, &boundary, PHASE)?;
    endpoint_expectation =
      constrain_f128_add(builder, &endpoint_expectation, &contribution, PHASE)?;
  }
  let group_boundary = constrain_boundary_factor(
    builder,
    &group_row,
    &point,
    &sigma_eq_tables,
    &zero,
    &one,
  )?;
  let group_weighted = constrain_f128_multiply(
    builder,
    &group_coefficient,
    &jagged_values[2],
    PHASE,
  )?;
  let group_contribution =
    constrain_f128_multiply(builder, &group_weighted, &group_boundary, PHASE)?;
  endpoint_expectation = constrain_f128_add(
    builder,
    &endpoint_expectation,
    &group_contribution,
    PHASE,
  )?;
  enforce_f128_equal(builder, &anchor_running, &endpoint_expectation, PHASE);

  let mut jagged_claims = Vec::with_capacity(F128_MULTIPOINT_JAGGED_CLAIMS);
  for (ring, value) in
    inputs.frontend.ring_switches.iter().zip(&jagged_values[..2])
  {
    let point_start = 1 + witness_row_variables;
    let row_point = ring
      .x_outer
      .get(point_start..point_start + matrix_row_variables)
      .ok_or(F128MultipointCircuitError::FrontendMismatch(
        "ring-switch column point is truncated",
      ))?
      .to_vec();
    jagged_claims.push(F128JaggedClaimVariablesV1 {
      row: F128JaggedRowWeightVariablesV1::Eq {
        scale: Box::new(one.clone()),
        point: row_point,
      },
      column_point: sigma.clone(),
      value: value.clone(),
    });
  }
  let combo_terms = inputs
    .frontend
    .batching_challenges
    .iter()
    .skip(inputs.frontend.ring_switches.len())
    .zip(&trace.group_column_addresses)
    .map(|(coefficient, &address)| F128JaggedComboTermVariablesV1 {
      coefficient: coefficient.clone(),
      address,
    })
    .collect();
  jagged_claims.push(F128JaggedClaimVariablesV1 {
    row: F128JaggedRowWeightVariablesV1::Combo { terms: combo_terms },
    column_point: sigma.clone(),
    value: jagged_values[2].clone(),
  });

  Ok(F128MultipointTwistedAssistCircuitOutputV1 {
    topology_digest: trace.topology_digest(),
    v,
    point,
    sigma,
    jagged_assertion: F128JaggedAssertionVariablesV1 {
      matrix: trace.matrix,
      claims: jagged_claims,
    },
  })
}

fn validate_frontend(
  trace: &F128MultipointTwistedAssistTraceV1,
  frontend: &F128MergedPcsFrontendCircuitOutputV1,
) -> Result<(), F128MultipointCircuitError> {
  let witness_row_variables = usize::try_from(trace.witness_row_variables)
    .map_err(|_| {
      F128MultipointCircuitError::FrontendMismatch(
        "witness row dimension overflow",
      )
    })?;
  let matrix_row_variables = usize::try_from(trace.matrix.row_variables)
    .map_err(|_| {
      F128MultipointCircuitError::FrontendMismatch(
        "layout row dimension overflow",
      )
    })?;
  let dense_variables =
    usize::try_from(trace.dense_variables).map_err(|_| {
      F128MultipointCircuitError::FrontendMismatch("dense dimension overflow")
    })?;
  if trace.frontend_topology_digest != frontend.topology_digest {
    return Err(F128MultipointCircuitError::FrontendMismatch(
      "topology digest differs",
    ));
  }
  if frontend.ring_switches.len() != 2
    || frontend.rho.len() != dense_variables
    || frontend.packed_direct_claims.len() != trace.group_column_addresses.len()
    || frontend.batching_challenges.len()
      != 2 + trace.group_column_addresses.len()
  {
    return Err(F128MultipointCircuitError::FrontendMismatch(
      "claim or challenge counts differ",
    ));
  }
  let expected_ring_variables = 1usize
    .checked_add(witness_row_variables)
    .and_then(|value| value.checked_add(matrix_row_variables))
    .ok_or(F128MultipointCircuitError::FrontendMismatch(
      "ring-switch point dimension overflow",
    ))?;
  if frontend.ring_switches.iter().any(|ring| {
    ring.x_outer.len() != expected_ring_variables
      || ring.eq_r_dprime.len() != F128_MULTIPOINT_DUAL_VALUES
  }) || frontend.packed_direct_claims.iter().any(|claim| {
    claim.point.len() != witness_row_variables + matrix_row_variables
  }) {
    return Err(F128MultipointCircuitError::FrontendMismatch(
      "claim point dimensions differ",
    ));
  }
  Ok(())
}

fn constrain_family_h_coefficients(
  builder: &mut R1csBuilder,
  ring_point: &[F128VariablesV1],
  equality_weights: &[F128VariablesV1],
  gamma: &F128VariablesV1,
  trace: &F128MultipointTwistedAssistTraceV1,
  one: &F128VariablesV1,
) -> Result<Vec<F128VariablesV1>, F128MultipointCircuitError> {
  if ring_point.len() != 7
    || equality_weights.len() != F128_MULTIPOINT_DUAL_VALUES
  {
    return Err(F128MultipointCircuitError::FrontendMismatch(
      "family-H equality table has the wrong width",
    ));
  }
  let mut geometric_origin = trace.family_h.geometric_origin;
  let mut geometric_ratio = trace.family_h.geometric_ratio;
  let mut corrections = trace.family_h.low_corrections;
  let mut coefficients = Vec::with_capacity(F128_MULTIPOINT_DUAL_VALUES);
  for _ in 0..F128_MULTIPOINT_DUAL_VALUES {
    let mut ratio_power = geometric_ratio;
    let mut factors = Vec::with_capacity(ring_point.len());
    for coordinate in ring_point {
      let scaled = constrain_f128_multiply_constant(
        builder,
        coordinate,
        ratio_power,
        PHASE,
      )?;
      let zero_branch = constrain_f128_add(builder, one, coordinate, PHASE)?;
      factors.push(constrain_f128_add(builder, &zero_branch, &scaled, PHASE)?);
      ratio_power = square_bytes(ratio_power);
    }
    let mut geometric = factors.first().cloned().ok_or(
      F128MultipointCircuitError::FrontendMismatch("family-H point is empty"),
    )?;
    for factor in &factors[1..] {
      geometric = constrain_f128_multiply(builder, &geometric, factor, PHASE)?;
    }
    let mut mle = constrain_f128_multiply_constant(
      builder,
      &geometric,
      geometric_origin,
      PHASE,
    )?;
    for (correction, weight) in corrections.iter().zip(equality_weights) {
      let term =
        constrain_f128_multiply_constant(builder, weight, *correction, PHASE)?;
      mle = constrain_f128_add(builder, &mle, &term, PHASE)?;
    }
    coefficients.push(constrain_f128_multiply(builder, gamma, &mle, PHASE)?);
    geometric_origin = square_bytes(geometric_origin);
    geometric_ratio = square_bytes(geometric_ratio);
    for correction in &mut corrections {
      *correction = square_bytes(*correction);
    }
  }
  Ok(coefficients)
}

fn constrain_powers(
  builder: &mut R1csBuilder,
  value: &F128VariablesV1,
  count: usize,
  one: &F128VariablesV1,
) -> Result<Vec<F128VariablesV1>, R1csError> {
  let mut powers = Vec::with_capacity(count);
  let mut power = one.clone();
  for index in 0..count {
    powers.push(power.clone());
    if index + 1 < count {
      power = constrain_f128_multiply(builder, &power, value, PHASE)?;
    }
  }
  Ok(powers)
}

fn constrain_twisted_eq(
  builder: &mut R1csBuilder,
  powers: &[F128VariablesV1],
  rho: &[F128VariablesV1],
  point: &[F128VariablesV1],
  one: &F128VariablesV1,
  zero: &F128VariablesV1,
) -> Result<F128VariablesV1, R1csError> {
  if powers.len() != F128_MULTIPOINT_DUAL_VALUES || rho.len() != point.len() {
    return Err(R1csError::InternalShape);
  }
  let mut total = zero.clone();
  for (inverse_power, coefficient) in powers.iter().enumerate() {
    let frobenius_power = if inverse_power == 0 {
      0
    } else {
      F128_MULTIPOINT_DUAL_VALUES - inverse_power
    };
    let mut term = coefficient.clone();
    for (rho_coordinate, point_coordinate) in rho.iter().zip(point) {
      let inverse = constrain_f128_frobenius(
        builder,
        rho_coordinate,
        frobenius_power,
        PHASE,
      )?;
      let one_plus_inverse = constrain_f128_add(builder, one, &inverse, PHASE)?;
      let factor = constrain_f128_add(
        builder,
        &one_plus_inverse,
        point_coordinate,
        PHASE,
      )?;
      term = constrain_f128_multiply(builder, &term, &factor, PHASE)?;
    }
    total = constrain_f128_add(builder, &total, &term, PHASE)?;
  }
  Ok(total)
}

fn constrain_eq_at(
  builder: &mut R1csBuilder,
  left: &[F128VariablesV1],
  right: &[F128VariablesV1],
  one: &F128VariablesV1,
) -> Result<F128VariablesV1, R1csError> {
  if left.len() != right.len() {
    return Err(R1csError::InternalShape);
  }
  let mut product = one.clone();
  for (left, right) in left.iter().zip(right) {
    let one_plus_left = constrain_f128_add(builder, one, left, PHASE)?;
    let factor = constrain_f128_add(builder, &one_plus_left, right, PHASE)?;
    product = constrain_f128_multiply(builder, &product, &factor, PHASE)?;
  }
  Ok(product)
}

fn constrain_boundary_factor(
  builder: &mut R1csBuilder,
  row_point: &[F128VariablesV1],
  index_point: &[F128VariablesV1],
  sigma_eq_tables: &[Vec<F128VariablesV1>],
  zero: &F128VariablesV1,
  one: &F128VariablesV1,
) -> Result<F128VariablesV1, R1csError> {
  if sigma_eq_tables.len() != index_point.len() + 1
    || sigma_eq_tables.iter().any(|table| table.len() != 4)
  {
    return Err(R1csError::InternalShape);
  }
  let transitions = sparse_transitions();
  let mut state = [zero.clone(), zero.clone(), one.clone(), zero.clone()];
  for layer in (0..=index_point.len()).rev() {
    let row = row_point.get(layer).unwrap_or(zero);
    let index = index_point.get(layer).unwrap_or(zero);
    let eq4 =
      constrain_eq_table(builder, &[row.clone(), index.clone()], zero, one)?;
    let mut next = Vec::with_capacity(4);
    for (state_in, _) in transitions[0].iter().enumerate() {
      let mut accumulator = zero.clone();
      for cd in 0..4 {
        let [(first_index, first_out), (second_index, second_out)] =
          transitions[cd][state_in];
        let first = constrain_f128_multiply(
          builder,
          &eq4[first_index],
          &state[first_out],
          PHASE,
        )?;
        let second = constrain_f128_multiply(
          builder,
          &eq4[second_index],
          &state[second_out],
          PHASE,
        )?;
        let pair = constrain_f128_add(builder, &first, &second, PHASE)?;
        let weighted = constrain_f128_multiply(
          builder,
          &sigma_eq_tables[layer][cd],
          &pair,
          PHASE,
        )?;
        accumulator =
          constrain_f128_add(builder, &accumulator, &weighted, PHASE)?;
      }
      next.push(accumulator);
    }
    state = next.try_into().map_err(|_| R1csError::InternalShape)?;
  }
  Ok(state[0].clone())
}

fn sparse_transitions() -> [[[(usize, usize); 2]; 4]; 4] {
  let mut table = [[[(0usize, 0usize); 2]; 4]; 4];
  for (cd, rows) in table.iter_mut().enumerate() {
    let (current, next) = (cd & 1 != 0, cd & 2 != 0);
    for (state, row) in rows.iter_mut().enumerate() {
      for (row_bit, entry) in row.iter_mut().enumerate() {
        let index_bit = (row_bit + (state & 1) + usize::from(current)) & 1 == 1;
        let out = transition(row_bit == 1, index_bit, current, next, state)
          .expect("the forced index bit never rejects");
        *entry = (row_bit + 2 * usize::from(index_bit), out);
      }
    }
  }
  table
}

fn transition(
  row: bool,
  index: bool,
  current: bool,
  next: bool,
  state: usize,
) -> Option<usize> {
  let carry = state & 1;
  let comparison = (state >> 1) & 1;
  let sum = usize::from(row) + carry + usize::from(current);
  if usize::from(index) != sum & 1 {
    return None;
  }
  let new_carry = sum >> 1;
  let new_comparison =
    if index == next { comparison } else { usize::from(next) };
  Some(new_carry + (new_comparison << 1))
}

fn constrain_round(
  builder: &mut R1csBuilder,
  running: &F128VariablesV1,
  round: &F128MultipointRoundV1,
  observed_values: &[F128VariablesV1],
  challenges: &[F128VariablesV1],
) -> Result<(F128VariablesV1, F128VariablesV1), F128MultipointCircuitError> {
  let one =
    get(observed_values, round.one_observation, "round one evaluation")?;
  let infinity = get(
    observed_values,
    round.infinity_observation,
    "round infinity coefficient",
  )?;
  let challenge = get(challenges, round.challenge, "round challenge")?;
  let next =
    constrain_fold_round(builder, running, &one, &infinity, &challenge)?;
  Ok((next, challenge))
}

fn get_many(
  values: &[F128VariablesV1],
  indices: &[u64],
  kind: &'static str,
) -> Result<Vec<F128VariablesV1>, F128MultipointCircuitError> {
  indices.iter().map(|&index| get(values, index, kind)).collect()
}

fn get(
  values: &[F128VariablesV1],
  index: u64,
  kind: &'static str,
) -> Result<F128VariablesV1, F128MultipointCircuitError> {
  values
    .get(
      usize::try_from(index)
        .map_err(|_| F128MultipointCircuitError::MissingInput(kind))?,
    )
    .cloned()
    .ok_or(F128MultipointCircuitError::MissingInput(kind))
}

fn square_bytes(value: [u8; 16]) -> [u8; 16] {
  native_f128_multiply(value, value)
}
