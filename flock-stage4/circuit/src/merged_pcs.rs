use crate::algebra::{F128AlgebraCircuitInputsV1, resolve_reference};
use crate::f128::{alloc_f128_constant, transpose_f128_variables};
use crate::{
  ConstraintPhase, F128PackedDirectClaimVariablesV1, F128TranscriptWordV1,
  F128VariablesV1, R1csBuilder, R1csError, constrain_f128_add,
  constrain_f128_multiply, enforce_f128_equal,
};
use ix_stage4_trace::{
  F128_RING_SWITCH_SKIP_WEIGHTS, F128MergedPcsBooleanClaimV1,
  F128MergedPcsFrontendTraceV1,
};
use std::collections::BTreeMap;
use std::fmt;

const PHASE: ConstraintPhase = ConstraintPhase::Pcs;

/// Already-constrained sources shared with the main transcript, Boolean
/// algebra replay, and Product-GKR wiring replay.
#[derive(Clone, Copy)]
pub struct F128MergedPcsFrontendCircuitInputsV1<'a> {
  pub public_values: &'a [F128VariablesV1],
  pub observed_values: &'a [F128VariablesV1],
  pub challenges: &'a [F128VariablesV1],
  pub private_values: &'a [F128VariablesV1],
  pub algebra_operations: &'a [F128VariablesV1],
  pub byte_payloads: &'a [Vec<F128TranscriptWordV1>],
  pub packed_direct_claims: &'a [F128PackedDirectClaimVariablesV1],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128RingSwitchCircuitOutputV1 {
  /// Native merged-opening suffix, including the seventh packed coordinate.
  pub x_outer: Vec<F128VariablesV1>,
  /// The seven transcript challenges whose equality table defines the fold.
  pub r_dprime: Vec<F128VariablesV1>,
  pub eq_r_dprime: Vec<F128VariablesV1>,
  pub sumcheck_claim: F128VariablesV1,
}

/// Constrained outputs handed to the two remaining merged-opening checks.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128MergedPcsFrontendCircuitOutputV1 {
  pub topology_digest: [u8; 32],
  pub commitment_cap: Vec<F128TranscriptWordV1>,
  pub ring_switches: Vec<F128RingSwitchCircuitOutputV1>,
  pub packed_direct_claims: Vec<F128PackedDirectClaimVariablesV1>,
  pub batching_challenges: Vec<F128VariablesV1>,
  /// Dense sumcheck endpoint used by the multipoint-twisted assist.
  pub rho: Vec<F128VariablesV1>,
  pub running: F128VariablesV1,
  /// Inner Ligerito must authenticate `q_hat(rho) = q_eval` against the CAP.
  pub q_eval: F128VariablesV1,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum F128MergedPcsFrontendCircuitError {
  InvalidTrace(String),
  R1cs(R1csError),
  Algebra(String),
  MissingInput(&'static str),
  CommitmentCapShape,
}

impl fmt::Display for F128MergedPcsFrontendCircuitError {
  fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::InvalidTrace(error) => {
        write!(formatter, "invalid merged PCS frontend: {error}")
      },
      Self::R1cs(error) => write!(formatter, "merged PCS R1CS: {error}"),
      Self::Algebra(error) => {
        write!(formatter, "merged PCS reference: {error}")
      },
      Self::MissingInput(kind) => {
        write!(formatter, "missing merged PCS {kind}")
      },
      Self::CommitmentCapShape => {
        write!(formatter, "merged PCS commitment CAP has the wrong shape")
      },
    }
  }
}

impl std::error::Error for F128MergedPcsFrontendCircuitError {}

impl From<R1csError> for F128MergedPcsFrontendCircuitError {
  fn from(error: R1csError) -> Self {
    Self::R1cs(error)
  }
}

/// Replay the two succinct ring switches, mixed claim batching, and every
/// degree-two round of Flock's dense merged sumcheck.
///
/// The returned relation is deliberately conditional: `running` still has
/// to equal `q_eval * v` for the multipoint assist's `v`, and the inner
/// Ligerito proof still has to authenticate `q_eval` at `rho`.
pub fn constrain_f128_merged_pcs_frontend(
  builder: &mut R1csBuilder,
  trace: &F128MergedPcsFrontendTraceV1,
  inputs: F128MergedPcsFrontendCircuitInputsV1<'_>,
) -> Result<
  F128MergedPcsFrontendCircuitOutputV1,
  F128MergedPcsFrontendCircuitError,
> {
  let payload_lengths = inputs
    .byte_payloads
    .iter()
    .map(|payload| payload.len().saturating_mul(16))
    .collect::<Vec<_>>();
  let packed_direct_point_variables = inputs
    .packed_direct_claims
    .iter()
    .map(|claim| claim.point.len())
    .collect::<Vec<_>>();
  trace
    .validate(
      inputs.public_values.len(),
      inputs.observed_values.len(),
      inputs.challenges.len(),
      inputs.private_values.len(),
      inputs.algebra_operations.len(),
      &payload_lengths,
      &packed_direct_point_variables,
    )
    .map_err(|error| {
      F128MergedPcsFrontendCircuitError::InvalidTrace(error.to_string())
    })?;

  let cap_index = to_usize(trace.commitment_cap_payload, "CAP payload")?;
  let commitment_cap = inputs
    .byte_payloads
    .get(cap_index)
    .cloned()
    .ok_or(F128MergedPcsFrontendCircuitError::MissingInput("CAP payload"))?;
  let cap_words = usize::try_from(trace.commitment_cap_nodes)
    .map_err(|_| F128MergedPcsFrontendCircuitError::CommitmentCapShape)?
    .checked_mul(2)
    .ok_or(F128MergedPcsFrontendCircuitError::CommitmentCapShape)?;
  if commitment_cap.len() != cap_words {
    return Err(F128MergedPcsFrontendCircuitError::CommitmentCapShape);
  }

  let algebra_inputs = F128AlgebraCircuitInputsV1 {
    public_values: inputs.public_values,
    observed_values: inputs.observed_values,
    challenges: inputs.challenges,
    private_values: inputs.private_values,
  };
  let mut constants = BTreeMap::new();
  let claims = trace
    .boolean_claims
    .iter()
    .map(|claim| {
      resolve_boolean_claim(
        builder,
        claim,
        algebra_inputs,
        inputs.algebra_operations,
        &mut constants,
      )
    })
    .collect::<Result<Vec<_>, _>>()?;
  let zero = alloc_f128_constant(builder, [0; 16], PHASE)?;
  let mut one_value = [0; 16];
  one_value[0] = 1;
  let one = alloc_f128_constant(builder, one_value, PHASE)?;

  let mut ring_switches = Vec::with_capacity(trace.ring_switches.len());
  for (claim, ring_trace) in claims.iter().zip(&trace.ring_switches) {
    let s_hat_v = get_many(
      inputs.observed_values,
      &ring_trace.s_hat_v_observations,
      "ring-switch slice",
    )?;
    let prefix_zero =
      constrain_f128_add(builder, &one, &claim.x_outer[0], PHASE)?;
    let mut claim_check = zero.clone();
    for (slice, s_hat) in s_hat_v.iter().enumerate() {
      let prefix =
        if slice >> 6 == 0 { &prefix_zero } else { &claim.x_outer[0] };
      let weight = constrain_f128_multiply(
        builder,
        &claim.skip_weights[slice & (F128_RING_SWITCH_SKIP_WEIGHTS - 1)],
        prefix,
        PHASE,
      )?;
      let term = constrain_f128_multiply(builder, &weight, s_hat, PHASE)?;
      claim_check = constrain_f128_add(builder, &claim_check, &term, PHASE)?;
    }
    enforce_f128_equal(builder, &claim_check, &claim.value, PHASE);

    let r_dprime = get_many(
      inputs.challenges,
      &ring_trace.r_dprime_challenges,
      "ring-switch randomizer",
    )?;
    let eq_r_dprime = constrain_eq_table(builder, &r_dprime, &zero, &one)?;
    let s_hat_u = transpose_f128_variables(&s_hat_v)?;
    let sumcheck_claim =
      constrain_inner_product(builder, &s_hat_u, &eq_r_dprime, &zero)?;
    ring_switches.push(F128RingSwitchCircuitOutputV1 {
      x_outer: claim.x_outer.clone(),
      r_dprime,
      eq_r_dprime,
      sumcheck_claim,
    });
  }

  for (&observation, packed) in
    trace.packed_direct_observations.iter().zip(inputs.packed_direct_claims)
  {
    let observed =
      get(inputs.observed_values, observation, "packed-direct value")?;
    enforce_f128_equal(builder, &observed, &packed.value, PHASE);
  }
  let batching_challenges = get_many(
    inputs.challenges,
    &trace.batching_challenges,
    "batching challenge",
  )?;
  let mut running = zero.clone();
  for (gamma, ring_switch) in batching_challenges.iter().zip(&ring_switches) {
    let term = constrain_f128_multiply(
      builder,
      gamma,
      &ring_switch.sumcheck_claim,
      PHASE,
    )?;
    running = constrain_f128_add(builder, &running, &term, PHASE)?;
  }
  for (gamma, packed) in batching_challenges
    .iter()
    .skip(ring_switches.len())
    .zip(inputs.packed_direct_claims)
  {
    let term = constrain_f128_multiply(builder, gamma, &packed.value, PHASE)?;
    running = constrain_f128_add(builder, &running, &term, PHASE)?;
  }

  let mut rho = Vec::with_capacity(trace.merged_rounds.len());
  for round in &trace.merged_rounds {
    let g_one = get(
      inputs.observed_values,
      round.one_observation,
      "merged-round one evaluation",
    )?;
    let g_infinity = get(
      inputs.observed_values,
      round.infinity_observation,
      "merged-round infinity coefficient",
    )?;
    let challenge =
      get(inputs.challenges, round.challenge, "merged-round challenge")?;
    running =
      constrain_fold_round(builder, &running, &g_one, &g_infinity, &challenge)?;
    rho.push(challenge);
  }
  let q_eval =
    get(inputs.observed_values, trace.q_eval_observation, "q evaluation")?;

  Ok(F128MergedPcsFrontendCircuitOutputV1 {
    topology_digest: trace.topology_digest(),
    commitment_cap,
    ring_switches,
    packed_direct_claims: inputs.packed_direct_claims.to_vec(),
    batching_challenges,
    rho,
    running,
    q_eval,
  })
}

struct ResolvedBooleanClaim {
  #[allow(dead_code)]
  z_skip: F128VariablesV1,
  skip_weights: Vec<F128VariablesV1>,
  x_outer: Vec<F128VariablesV1>,
  value: F128VariablesV1,
}

fn resolve_boolean_claim(
  builder: &mut R1csBuilder,
  claim: &F128MergedPcsBooleanClaimV1,
  inputs: F128AlgebraCircuitInputsV1<'_>,
  operations: &[F128VariablesV1],
  constants: &mut BTreeMap<[u8; 16], F128VariablesV1>,
) -> Result<ResolvedBooleanClaim, F128MergedPcsFrontendCircuitError> {
  let mut resolve = |reference| {
    resolve_reference(builder, reference, PHASE, inputs, operations, constants)
      .map_err(|error| {
        F128MergedPcsFrontendCircuitError::Algebra(error.to_string())
      })
  };
  Ok(ResolvedBooleanClaim {
    z_skip: resolve(claim.z_skip)?,
    skip_weights: claim
      .skip_weights
      .iter()
      .copied()
      .map(&mut resolve)
      .collect::<Result<Vec<_>, _>>()?,
    x_outer: claim
      .x_outer
      .iter()
      .copied()
      .map(&mut resolve)
      .collect::<Result<Vec<_>, _>>()?,
    value: resolve(claim.value)?,
  })
}

pub(crate) fn constrain_eq_table(
  builder: &mut R1csBuilder,
  point: &[F128VariablesV1],
  _zero: &F128VariablesV1,
  one: &F128VariablesV1,
) -> Result<Vec<F128VariablesV1>, R1csError> {
  let mut table = vec![one.clone()];
  for coordinate in point {
    let zero_factor = constrain_f128_add(builder, one, coordinate, PHASE)?;
    let mut next = Vec::with_capacity(2 * table.len());
    for weight in &table {
      next.push(constrain_f128_multiply(builder, weight, &zero_factor, PHASE)?);
    }
    for weight in &table {
      next.push(constrain_f128_multiply(builder, weight, coordinate, PHASE)?);
    }
    table = next;
  }
  Ok(table)
}

fn constrain_inner_product(
  builder: &mut R1csBuilder,
  left: &[F128VariablesV1],
  right: &[F128VariablesV1],
  zero: &F128VariablesV1,
) -> Result<F128VariablesV1, R1csError> {
  if left.len() != right.len() {
    return Err(R1csError::InternalShape);
  }
  left.iter().zip(right).try_fold(zero.clone(), |accumulator, (left, right)| {
    let term = constrain_f128_multiply(builder, left, right, PHASE)?;
    constrain_f128_add(builder, &accumulator, &term, PHASE)
  })
}

pub(crate) fn constrain_fold_round(
  builder: &mut R1csBuilder,
  claim: &F128VariablesV1,
  g_one: &F128VariablesV1,
  g_infinity: &F128VariablesV1,
  challenge: &F128VariablesV1,
) -> Result<F128VariablesV1, R1csError> {
  let g_zero = constrain_f128_add(builder, claim, g_one, PHASE)?;
  let one_plus_zero = constrain_f128_add(builder, g_one, &g_zero, PHASE)?;
  let linear_coefficient =
    constrain_f128_add(builder, &one_plus_zero, g_infinity, PHASE)?;
  let linear =
    constrain_f128_multiply(builder, &linear_coefficient, challenge, PHASE)?;
  let challenge_squared =
    constrain_f128_multiply(builder, challenge, challenge, PHASE)?;
  let quadratic =
    constrain_f128_multiply(builder, g_infinity, &challenge_squared, PHASE)?;
  let constant_and_linear =
    constrain_f128_add(builder, &g_zero, &linear, PHASE)?;
  constrain_f128_add(builder, &constant_and_linear, &quadratic, PHASE)
}

fn get_many(
  values: &[F128VariablesV1],
  indices: &[u64],
  kind: &'static str,
) -> Result<Vec<F128VariablesV1>, F128MergedPcsFrontendCircuitError> {
  indices.iter().map(|&index| get(values, index, kind)).collect()
}

fn get(
  values: &[F128VariablesV1],
  index: u64,
  kind: &'static str,
) -> Result<F128VariablesV1, F128MergedPcsFrontendCircuitError> {
  values
    .get(to_usize(index, kind)?)
    .cloned()
    .ok_or(F128MergedPcsFrontendCircuitError::MissingInput(kind))
}

fn to_usize(
  index: u64,
  kind: &'static str,
) -> Result<usize, F128MergedPcsFrontendCircuitError> {
  usize::try_from(index)
    .map_err(|_| F128MergedPcsFrontendCircuitError::MissingInput(kind))
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::{F128VariablesV1, alloc_f128_private};
  use ix_stage4_trace::{
    F128InputSourceV1, F128MergedPcsRoundV1, F128ReferenceV1,
    F128RingSwitchTraceV1,
  };

  fn zero() -> [u8; 16] {
    [0; 16]
  }

  fn one() -> [u8; 16] {
    let mut value = [0; 16];
    value[0] = 1;
    value
  }

  fn constant(value: [u8; 16]) -> F128ReferenceV1 {
    F128ReferenceV1::Input(F128InputSourceV1::Constant(value))
  }

  fn fixture() -> F128MergedPcsFrontendTraceV1 {
    let claim = F128MergedPcsBooleanClaimV1 {
      z_skip: constant(zero()),
      skip_weights: std::iter::once(constant(one()))
        .chain(std::iter::repeat_n(constant(zero()), 63))
        .collect(),
      x_outer: vec![constant(zero()); 3],
      value: constant(zero()),
    };
    F128MergedPcsFrontendTraceV1 {
      commitment_variables: 9,
      commitment_cap_payload: 0,
      commitment_cap_nodes: 1,
      row_variables: 1,
      column_variables: 1,
      jagged_heights: vec![1, 2],
      boolean_claims: vec![claim.clone(), claim],
      ring_switches: vec![
        F128RingSwitchTraceV1 {
          s_hat_v_observations: (0..128).collect(),
          r_dprime_challenges: (0..7).collect(),
        },
        F128RingSwitchTraceV1 {
          s_hat_v_observations: (128..256).collect(),
          r_dprime_challenges: (7..14).collect(),
        },
      ],
      packed_direct_observations: vec![256],
      batching_challenges: vec![14, 15, 16],
      merged_rounds: vec![
        F128MergedPcsRoundV1 {
          one_observation: 257,
          infinity_observation: 258,
          challenge: 17,
        },
        F128MergedPcsRoundV1 {
          one_observation: 259,
          infinity_observation: 260,
          challenge: 18,
        },
      ],
      q_eval_observation: 261,
    }
  }

  fn alloc_values(
    builder: &mut R1csBuilder,
    values: &[[u8; 16]],
  ) -> Vec<F128VariablesV1> {
    values
      .iter()
      .copied()
      .map(|value| alloc_f128_private(builder, value, PHASE).unwrap())
      .collect()
  }

  #[test]
  #[ignore = "full two-ring projection is covered by the production Stage 4 regression"]
  fn constrains_zero_frontend_and_exposes_both_deferred_checks() {
    let trace = fixture();
    let mut builder = R1csBuilder::new_projection();
    let observed = alloc_values(&mut builder, &vec![zero(); 262]);
    let challenges = alloc_values(&mut builder, &vec![zero(); 19]);
    let cap_variables = alloc_values(&mut builder, &[zero(), zero()]);
    let payloads = vec![
      cap_variables
        .iter()
        .map(F128TranscriptWordV1::from_f128_variables)
        .collect(),
    ];
    let packed_direct_claims = vec![F128PackedDirectClaimVariablesV1 {
      point: alloc_values(&mut builder, &[zero(), zero()]),
      value: alloc_f128_private(&mut builder, zero(), PHASE).unwrap(),
    }];
    let output = constrain_f128_merged_pcs_frontend(
      &mut builder,
      &trace,
      F128MergedPcsFrontendCircuitInputsV1 {
        public_values: &[],
        observed_values: &observed,
        challenges: &challenges,
        private_values: &[],
        algebra_operations: &[],
        byte_payloads: &payloads,
        packed_direct_claims: &packed_direct_claims,
      },
    )
    .expect("constrain frontend");
    assert_eq!(output.ring_switches.len(), 2);
    assert_eq!(output.rho.len(), 2);
    assert_eq!(output.running.value(), &zero());
    assert_eq!(output.q_eval.value(), &zero());
    let projection = builder.finish_projection().unwrap();
    assert!(projection.census().constraints > 0);
  }

  #[test]
  fn rejects_a_packed_direct_point_with_the_wrong_shape() {
    let trace = fixture();
    let mut builder = R1csBuilder::new_projection();
    let observed = alloc_values(&mut builder, &vec![zero(); 262]);
    let challenges = alloc_values(&mut builder, &vec![zero(); 19]);
    let cap_variables = alloc_values(&mut builder, &[zero(), zero()]);
    let payloads = vec![
      cap_variables
        .iter()
        .map(F128TranscriptWordV1::from_f128_variables)
        .collect(),
    ];
    let packed_direct_claims = vec![F128PackedDirectClaimVariablesV1 {
      point: alloc_values(&mut builder, &[zero()]),
      value: alloc_f128_private(&mut builder, zero(), PHASE).unwrap(),
    }];
    let result = constrain_f128_merged_pcs_frontend(
      &mut builder,
      &trace,
      F128MergedPcsFrontendCircuitInputsV1 {
        public_values: &[],
        observed_values: &observed,
        challenges: &challenges,
        private_values: &[],
        algebra_operations: &[],
        byte_payloads: &payloads,
        packed_direct_claims: &packed_direct_claims,
      },
    );
    assert!(matches!(
      result,
      Err(F128MergedPcsFrontendCircuitError::InvalidTrace(_))
    ));
  }
}
