use crate::blake3::{
  BLAKE3_IV, Word32, alloc_words_in_phase, constrain_compression_in_phase,
  select_word_in_phase,
};
use crate::f128::{
  alloc_f128_constant, native_f128_add, native_f128_inverse,
  native_f128_multiply,
};
use crate::merged_pcs::constrain_eq_table;
use crate::{
  ConstraintPhase, F128MergedPcsFrontendCircuitOutputV1, F128TranscriptWordV1,
  F128VariablesV1, R1csBuilder, R1csError, Variable, alloc_f128_private,
  constrain_f128_add, constrain_f128_frobenius, constrain_f128_multiply,
  constrain_f128_multiply_constant, enforce_f128_equal,
};
use ix_stage4_trace::{
  F128InnerLigeritoTraceV1, F128LigeritoLevelV1, F128LigeritoOodClaimV1,
  F256IndexPairV1, F256LigeritoMessageV1,
};
use std::{fmt, mem::size_of};

const PHASE: ConstraintPhase = ConstraintPhase::Pcs;
const F128_BYTES: usize = 16;
const WORD_BYTES: usize = 4;
const BLOCK_BYTES: usize = 64;
const BLOCK_WORDS: usize = BLOCK_BYTES / WORD_BYTES;
const MAX_CHUNK_BYTES: usize = 1024;
const CHUNK_START: u32 = 1 << 0;
const CHUNK_END: u32 = 1 << 1;
const PARENT: u32 = 1 << 2;
const QUADRATIC_NONRESIDUE: [u8; 16] =
  [0x43, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x80];

type DigestVariables = [Word32; 8];

/// Already-constrained parent transcript and merged-opening frontend wires,
/// plus the private rows and capped Merkle siblings carried by the proof.
#[derive(Clone, Copy)]
pub struct F128InnerLigeritoCircuitInputsV1<'a> {
  pub observed_values: &'a [F128VariablesV1],
  pub challenges: &'a [F128VariablesV1],
  pub byte_payloads: &'a [Vec<F128TranscriptWordV1>],
  pub private_values: &'a [[u8; 16]],
  pub private_digests: &'a [[u8; 32]],
  pub frontend: &'a F128MergedPcsFrontendCircuitOutputV1,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128InnerLigeritoCircuitOutputV1 {
  pub topology_digest: [u8; 32],
  pub authenticated_queries: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum F128InnerLigeritoCircuitError {
  InvalidTrace(String),
  FrontendMismatch(&'static str),
  MissingInput(&'static str),
  UnsupportedShape(&'static str),
  R1cs(R1csError),
}

impl fmt::Display for F128InnerLigeritoCircuitError {
  fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::InvalidTrace(error) => {
        write!(formatter, "invalid inner Ligerito trace: {error}")
      },
      Self::FrontendMismatch(reason) => {
        write!(formatter, "inner Ligerito/frontend mismatch: {reason}")
      },
      Self::MissingInput(kind) => {
        write!(formatter, "missing inner Ligerito {kind}")
      },
      Self::UnsupportedShape(reason) => {
        write!(formatter, "unsupported inner Ligerito shape: {reason}")
      },
      Self::R1cs(error) => write!(formatter, "inner Ligerito R1CS: {error}"),
    }
  }
}

impl std::error::Error for F128InnerLigeritoCircuitError {}

impl From<R1csError> for F128InnerLigeritoCircuitError {
  fn from(error: R1csError) -> Self {
    Self::R1cs(error)
  }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct F256Variables {
  c0: F128VariablesV1,
  c1: F128VariablesV1,
}

#[derive(Clone)]
struct RoundQuadVariables {
  c: F256Variables,
  b: F256Variables,
  a: F256Variables,
}

#[derive(Clone)]
struct QueryBit {
  value: bool,
  variable: Variable,
}

#[derive(Clone)]
struct QueryVariables {
  field: F128VariablesV1,
  bits: Vec<QueryBit>,
  stratum_depth: usize,
  stratum: usize,
}

#[derive(Clone)]
struct OodVariables {
  point: Vec<F128VariablesV1>,
  value: F128VariablesV1,
  intro_message: Option<F256LigeritoMessageVariables>,
  beta: F128VariablesV1,
}

#[derive(Clone)]
struct F256LigeritoMessageVariables {
  u_0: F256Variables,
  u_2: F256Variables,
}

#[derive(Clone)]
struct ConstrainedLevel {
  lane_challenges: Vec<F256Variables>,
  round_messages: Vec<F256LigeritoMessageVariables>,
  queries: Vec<QueryVariables>,
  query_weights: Vec<F128VariablesV1>,
  enforced: F256Variables,
  ood_claims: Vec<OodVariables>,
  intro_message: Option<F256LigeritoMessageVariables>,
  beta: F128VariablesV1,
}

#[derive(Clone)]
struct OodResidualContext {
  point: Vec<F128VariablesV1>,
  beta: F128VariablesV1,
  split_level: Option<usize>,
}

#[derive(Clone)]
struct ConsistencyResidualContext {
  log_columns: usize,
  queries: Vec<QueryVariables>,
  query_weights: Vec<F128VariablesV1>,
  beta: F128VariablesV1,
  start_level: usize,
}

/// Authenticate every queried row, replay the extension-field sumcheck, and
/// discharge Flock's final residual identity against the merged `q_eval`.
pub fn constrain_f128_inner_ligerito(
  builder: &mut R1csBuilder,
  trace: &F128InnerLigeritoTraceV1,
  inputs: F128InnerLigeritoCircuitInputsV1<'_>,
) -> Result<F128InnerLigeritoCircuitOutputV1, F128InnerLigeritoCircuitError> {
  let payload_lengths = inputs
    .byte_payloads
    .iter()
    .map(|payload| payload.len().saturating_mul(F128_BYTES))
    .collect::<Vec<_>>();
  trace
    .validate(
      inputs.observed_values.len(),
      inputs.challenges.len(),
      &payload_lengths,
      inputs.private_values.len(),
      inputs.private_digests.len(),
    )
    .map_err(|error| {
      F128InnerLigeritoCircuitError::InvalidTrace(error.to_string())
    })?;
  if trace.frontend_topology_digest != inputs.frontend.topology_digest {
    return Err(F128InnerLigeritoCircuitError::FrontendMismatch(
      "topology digest",
    ));
  }
  let log_n = usize::try_from(trace.commitment_variables)
    .map_err(|_| {
      F128InnerLigeritoCircuitError::UnsupportedShape(
        "commitment dimension overflow",
      )
    })?
    .checked_sub(7)
    .ok_or(F128InnerLigeritoCircuitError::UnsupportedShape(
      "commitment dimension below packing width",
    ))?;
  if inputs.frontend.rho.len() != log_n {
    return Err(F128InnerLigeritoCircuitError::FrontendMismatch(
      "evaluation-point dimension",
    ));
  }
  if trace.levels.iter().any(|level| {
    usize::try_from(level.lane_count)
      .ok()
      .and_then(|lanes| lanes.checked_mul(F128_BYTES))
      .is_none_or(|bytes| bytes > MAX_CHUNK_BYTES)
  }) {
    return Err(F128InnerLigeritoCircuitError::UnsupportedShape(
      "a committed row spans more than one BLAKE3 chunk",
    ));
  }

  let zero = alloc_f128_constant(builder, [0; 16], PHASE)?;
  let mut one_value = [0; 16];
  one_value[0] = 1;
  let one = alloc_f128_constant(builder, one_value, PHASE)?;
  let private_values = inputs
    .private_values
    .iter()
    .copied()
    .map(|value| alloc_f128_private(builder, value, PHASE))
    .collect::<Result<Vec<_>, _>>()?;
  let private_digests = inputs
    .private_digests
    .iter()
    .map(|digest| alloc_digest(builder, *digest))
    .collect::<Result<Vec<_>, _>>()?;

  bind_initial_cap(builder, trace, inputs.byte_payloads, inputs.frontend)?;
  let levels = trace
    .levels
    .iter()
    .map(|level| {
      constrain_level(
        builder,
        level,
        inputs.observed_values,
        inputs.challenges,
        inputs.byte_payloads,
        &private_values,
        &private_digests,
        &zero,
        &one,
      )
    })
    .collect::<Result<Vec<_>, _>>()?;

  let q_eval = get(
    inputs.observed_values,
    trace.q_eval_observation,
    "q-evaluation observation",
  )?;
  enforce_f128_equal(builder, &q_eval, &inputs.frontend.q_eval, PHASE);
  let gamma = get(
    inputs.challenges,
    trace.batching_challenge,
    "opening batching challenge",
  )?;
  let target = get(
    inputs.observed_values,
    trace.target_observation,
    "Ligerito target observation",
  )?;
  let expected_target =
    constrain_f128_multiply(builder, &gamma, &q_eval, PHASE)?;
  enforce_f128_equal(builder, &target, &expected_target, PHASE);

  let mut claim = f256_from_base(&target, &zero);
  let mut ood_contexts = Vec::new();
  let lane_major = usize::try_from(trace.levels[0].lane_count)
    .expect("validated lane count fits usize")
    < checked_pow2(levels[0].lane_challenges.len())?;
  for ood in &levels[0].ood_claims {
    add_base_claim(builder, &mut claim, &ood.value, &ood.beta)?;
    let mut point = ood.point.clone();
    if lane_major {
      point.rotate_left(log_n - levels[0].lane_challenges.len());
    }
    ood_contexts.push(OodResidualContext {
      point,
      beta: ood.beta.clone(),
      split_level: None,
    });
  }

  let first_message = resolve_message(
    trace.first_message,
    inputs.observed_values,
    "first sumcheck message",
  )?;
  let mut quad =
    RoundQuadVariables::from_message(builder, first_message, &claim)?;
  for (challenge, message) in
    levels[0].lane_challenges.iter().zip(&levels[0].round_messages)
  {
    claim = quad.evaluate(builder, challenge)?;
    quad = RoundQuadVariables::from_message(builder, message.clone(), &claim)?;
  }

  if levels.len() > 1 {
    introduce_oods(
      builder,
      &levels[1].ood_claims,
      0,
      &mut claim,
      &mut quad,
      &mut ood_contexts,
      &zero,
    )?;
  }
  let intro = levels[0].intro_message.clone().ok_or(
    F128InnerLigeritoCircuitError::InvalidTrace(
      "L0 has no consistency message".to_owned(),
    ),
  )?;
  let intro =
    RoundQuadVariables::from_message(builder, intro, &levels[0].enforced)?;
  quad = quad.fold(builder, &intro, &levels[0].beta)?;
  let enforced =
    f256_multiply_base(builder, &levels[0].enforced, &levels[0].beta)?;
  claim = f256_add(builder, &claim, &enforced)?;
  let mut consistency_contexts = vec![ConsistencyResidualContext {
    log_columns: usize::try_from(trace.levels[0].log_message_columns)
      .expect("validated dimension fits usize"),
    queries: levels[0].queries.clone(),
    query_weights: levels[0].query_weights.clone(),
    beta: levels[0].beta.clone(),
    start_level: 0,
  }];

  for level_index in 1..levels.len() {
    let level = &levels[level_index];
    for (challenge, message) in
      level.lane_challenges.iter().zip(&level.round_messages)
    {
      claim = quad.evaluate(builder, challenge)?;
      quad =
        RoundQuadVariables::from_message(builder, message.clone(), &claim)?;
    }
    let is_final = level_index + 1 == levels.len();
    if !is_final {
      introduce_oods(
        builder,
        &levels[level_index + 1].ood_claims,
        level_index,
        &mut claim,
        &mut quad,
        &mut ood_contexts,
        &zero,
      )?;
      let intro = level.intro_message.clone().ok_or(
        F128InnerLigeritoCircuitError::InvalidTrace(
          "recursive level has no consistency message".to_owned(),
        ),
      )?;
      let intro =
        RoundQuadVariables::from_message(builder, intro, &level.enforced)?;
      quad = quad.fold(builder, &intro, &level.beta)?;
    }
    let enforced = f256_multiply_base(builder, &level.enforced, &level.beta)?;
    claim = f256_add(builder, &claim, &enforced)?;
    consistency_contexts.push(ConsistencyResidualContext {
      log_columns: usize::try_from(
        trace.levels[level_index].log_message_columns,
      )
      .expect("validated dimension fits usize"),
      queries: level.queries.clone(),
      query_weights: level.query_weights.clone(),
      beta: level.beta.clone(),
      start_level: level_index,
    });
  }

  let recursive_challenges = levels[1..]
    .iter()
    .map(|level| level.lane_challenges.clone())
    .collect::<Vec<_>>();
  let initial_challenges = &levels[0].lane_challenges;
  let extension_log = usize::try_from(
    trace.levels.last().expect("validated levels").log_message_columns,
  )
  .expect("validated dimension fits usize");
  let original_challenges =
    residual_original_challenges(initial_challenges, &recursive_challenges, 0);
  if original_challenges.len() + extension_log != log_n {
    return Err(F128InnerLigeritoCircuitError::UnsupportedShape(
      "residual challenge dimension",
    ));
  }

  let mut rho = inputs.frontend.rho.clone();
  if lane_major {
    rho.rotate_left(log_n - initial_challenges.len());
  }
  let initial_coordinate_scale =
    coordinate_scale(builder, &recursive_challenges, 0, &zero, &one)?;
  let packed_scale =
    f256_multiply_base(builder, &initial_coordinate_scale, &gamma)?;
  let mut residual = constrain_eq_residual(
    builder,
    &rho,
    &original_challenges,
    extension_log,
    &packed_scale,
    &zero,
    &one,
  )?;

  for context in &ood_contexts {
    let (fixed, start_level) = match context.split_level {
      None => (original_challenges.clone(), 0),
      Some(split_level) => {
        let mut fixed = recursive_challenges.get(split_level).cloned().ok_or(
          F128InnerLigeritoCircuitError::UnsupportedShape("OOD split level"),
        )?;
        for later in &recursive_challenges[split_level + 1..] {
          fixed.extend_from_slice(&later[1..]);
        }
        (fixed, split_level + 1)
      },
    };
    let coordinate_scale = coordinate_scale(
      builder,
      &recursive_challenges,
      start_level,
      &zero,
      &one,
    )?;
    let scale = f256_multiply_base(builder, &coordinate_scale, &context.beta)?;
    let contribution = constrain_eq_residual(
      builder,
      &context.point,
      &fixed,
      extension_log,
      &scale,
      &zero,
      &one,
    )?;
    add_residual(builder, &mut residual, &contribution)?;
  }

  for context in &consistency_contexts {
    let fixed = residual_original_challenges(
      &[],
      &recursive_challenges,
      context.start_level,
    );
    let coordinate_scale = coordinate_scale(
      builder,
      &recursive_challenges,
      context.start_level,
      &zero,
      &one,
    )?;
    let scale = f256_multiply_base(builder, &coordinate_scale, &context.beta)?;
    let contribution = constrain_induced_basis_at_residual(
      builder,
      context.log_columns,
      &context.queries,
      &context.query_weights,
      &fixed,
      extension_log,
      &scale,
      &zero,
      &one,
    )?;
    add_residual(builder, &mut residual, &contribution)?;
  }

  let final_words = get_many(
    inputs.observed_values,
    &trace.final_yr_observations,
    "final residual word",
  )?;
  let mut final_claim = f256_zero(&zero);
  let mut split_basis = Vec::with_capacity(2 * residual.len());
  for value in &residual {
    split_basis.push(value.clone());
    split_basis.push(f256_multiply_u(builder, value)?);
  }
  if split_basis.len() != final_words.len() {
    return Err(F128InnerLigeritoCircuitError::UnsupportedShape(
      "final split basis",
    ));
  }
  for (word, weight) in final_words.iter().zip(&split_basis) {
    let term = f256_multiply_base(builder, weight, word)?;
    final_claim = f256_add(builder, &final_claim, &term)?;
  }
  enforce_f128_equal(builder, &final_claim.c0, &claim.c0, PHASE);
  enforce_f128_equal(builder, &final_claim.c1, &claim.c1, PHASE);

  Ok(F128InnerLigeritoCircuitOutputV1 {
    topology_digest: trace.topology_digest(),
    authenticated_queries: trace
      .levels
      .iter()
      .map(|level| level.query_challenges.len() as u64)
      .sum(),
  })
}

#[allow(clippy::too_many_arguments)]
fn constrain_level(
  builder: &mut R1csBuilder,
  level: &F128LigeritoLevelV1,
  observed_values: &[F128VariablesV1],
  challenges: &[F128VariablesV1],
  payloads: &[Vec<F128TranscriptWordV1>],
  private_values: &[F128VariablesV1],
  private_digests: &[DigestVariables],
  zero: &F128VariablesV1,
  one: &F128VariablesV1,
) -> Result<ConstrainedLevel, F128InnerLigeritoCircuitError> {
  let cap = resolve_cap(level, payloads)?;
  let queries = derive_queries(level, challenges, zero, one)?;
  let rows = level
    .opened_rows
    .iter()
    .map(|indices| get_many(private_values, indices, "opened-row word"))
    .collect::<Result<Vec<_>, _>>()?;
  for (((query, row), path_indices), _) in queries
    .iter()
    .zip(&rows)
    .zip(&level.merkle_paths)
    .zip(&level.query_challenges)
  {
    let path = path_indices
      .iter()
      .map(|&index| get(private_digests, index, "Merkle sibling digest"))
      .collect::<Result<Vec<_>, _>>()?;
    constrain_capped_opening(builder, level, query, row, &path, &cap)?;
  }

  let lane_challenges = level
    .lane_challenges
    .iter()
    .map(|&pair| resolve_pair(pair, challenges, "lane-fold challenge"))
    .collect::<Result<Vec<_>, _>>()?;
  let alpha =
    get_many(challenges, &level.alpha_challenges, "query-batching challenge")?;
  let query_weights = constrain_eq_table(builder, &alpha, zero, one)?
    .into_iter()
    .take(queries.len())
    .collect::<Vec<_>>();
  let enforced = constrain_enforced_sum(
    builder,
    &rows,
    &lane_challenges,
    &query_weights,
    zero,
    one,
  )?;
  let round_messages = level
    .round_messages
    .iter()
    .map(|&message| {
      resolve_message(message, observed_values, "lane-fold message")
    })
    .collect::<Result<Vec<_>, _>>()?;
  let ood_claims = level
    .ood_claims
    .iter()
    .map(|claim| resolve_ood(claim, observed_values, challenges))
    .collect::<Result<Vec<_>, _>>()?;
  let intro_message = level
    .intro_message
    .map(|message| {
      resolve_message(message, observed_values, "consistency message")
    })
    .transpose()?;
  let beta =
    get(challenges, level.beta_challenge, "consistency batching challenge")?;
  Ok(ConstrainedLevel {
    lane_challenges,
    round_messages,
    queries,
    query_weights,
    enforced,
    ood_claims,
    intro_message,
    beta,
  })
}

fn bind_initial_cap(
  builder: &mut R1csBuilder,
  trace: &F128InnerLigeritoTraceV1,
  payloads: &[Vec<F128TranscriptWordV1>],
  frontend: &F128MergedPcsFrontendCircuitOutputV1,
) -> Result<(), F128InnerLigeritoCircuitError> {
  let index = to_usize(trace.levels[0].cap_payload, "initial CAP payload")?;
  let payload = payloads.get(index).ok_or(
    F128InnerLigeritoCircuitError::MissingInput("initial CAP payload"),
  )?;
  if payload.len() != frontend.commitment_cap.len() {
    return Err(F128InnerLigeritoCircuitError::FrontendMismatch(
      "initial CAP size",
    ));
  }
  for (left, right) in payload.iter().zip(&frontend.commitment_cap) {
    for (left, right) in
      left.bit_expressions().iter().zip(right.bit_expressions())
    {
      builder.enforce_zero(PHASE, left.clone().minus(right));
    }
  }
  Ok(())
}

fn resolve_cap(
  level: &F128LigeritoLevelV1,
  payloads: &[Vec<F128TranscriptWordV1>],
) -> Result<Vec<DigestVariables>, F128InnerLigeritoCircuitError> {
  let index = to_usize(level.cap_payload, "CAP payload")?;
  let payload = payloads
    .get(index)
    .ok_or(F128InnerLigeritoCircuitError::MissingInput("CAP payload"))?;
  let nodes = usize::try_from(level.cap_nodes).map_err(|_| {
    F128InnerLigeritoCircuitError::UnsupportedShape("CAP node count")
  })?;
  if payload.len() != 2 * nodes {
    return Err(F128InnerLigeritoCircuitError::InvalidTrace(
      "CAP payload has the wrong word count".to_owned(),
    ));
  }
  payload
    .as_chunks::<2>()
    .0
    .iter()
    .map(|words| {
      words
        .iter()
        .flat_map(transcript_word32s)
        .collect::<Vec<_>>()
        .try_into()
        .map_err(|_| {
          F128InnerLigeritoCircuitError::UnsupportedShape("CAP digest")
        })
    })
    .collect()
}

fn transcript_word32s(word: &F128TranscriptWordV1) -> [Word32; 4] {
  let chunks = word.value().as_chunks::<4>().0;
  core::array::from_fn(|index| {
    Word32::from_expressions(
      u32::from_le_bytes(chunks[index]),
      word.bit_expressions()[32 * index..32 * (index + 1)]
        .to_vec()
        .try_into()
        .expect("transcript word has 32-bit limbs"),
    )
  })
}

fn derive_queries(
  level: &F128LigeritoLevelV1,
  challenges: &[F128VariablesV1],
  zero: &F128VariablesV1,
  one: &F128VariablesV1,
) -> Result<Vec<QueryVariables>, F128InnerLigeritoCircuitError> {
  let block_variables =
    usize::try_from(level.block_variables).map_err(|_| {
      F128InnerLigeritoCircuitError::UnsupportedShape("block dimension")
    })?;
  if block_variables >= usize::BITS as usize || block_variables > 128 {
    return Err(F128InnerLigeritoCircuitError::UnsupportedShape(
      "query-index dimension",
    ));
  }
  let mut strata = Vec::with_capacity(level.query_challenges.len());
  for &depth in &level.summand_depths {
    let depth = usize::try_from(depth).map_err(|_| {
      F128InnerLigeritoCircuitError::UnsupportedShape("summand depth")
    })?;
    for stratum in 0..checked_pow2(depth)? {
      strata.push((depth, stratum));
    }
  }
  if strata.len() != level.query_challenges.len() {
    return Err(F128InnerLigeritoCircuitError::InvalidTrace(
      "query schedule length".to_owned(),
    ));
  }
  level
    .query_challenges
    .iter()
    .zip(strata)
    .map(|(&challenge_index, (depth, stratum))| {
      let challenge = get(challenges, challenge_index, "query challenge")?;
      let low_bits = block_variables - depth;
      let challenge_value = u128::from_le_bytes(*challenge.value());
      let mut index = 0usize;
      let mut bits = Vec::with_capacity(block_variables);
      for bit in 0..block_variables {
        let (value, variable) = if bit < low_bits {
          ((challenge_value >> bit) & 1 == 1, challenge.bit_variables()[bit])
        } else {
          let value = (stratum >> (bit - low_bits)) & 1 == 1;
          (
            value,
            if value {
              one.bit_variables()[0]
            } else {
              zero.bit_variables()[0]
            },
          )
        };
        if value {
          index |= 1usize << bit;
        }
        bits.push(QueryBit { value, variable });
      }
      let mut field_value = [0; 16];
      field_value[..size_of::<usize>()].copy_from_slice(&index.to_le_bytes());
      let bit_variables = core::array::from_fn(|bit| {
        bits.get(bit).map_or(zero.bit_variables()[0], |source| source.variable)
      });
      Ok(QueryVariables {
        field: F128VariablesV1::from_constrained_bits(
          field_value,
          bit_variables,
        ),
        bits,
        stratum_depth: depth,
        stratum,
      })
    })
    .collect()
}

fn constrain_capped_opening(
  builder: &mut R1csBuilder,
  level: &F128LigeritoLevelV1,
  query: &QueryVariables,
  row: &[F128VariablesV1],
  path: &[DigestVariables],
  cap: &[DigestVariables],
) -> Result<(), F128InnerLigeritoCircuitError> {
  let mut current = hash_leaf(builder, row)?;
  for (depth, sibling) in path.iter().enumerate() {
    let direction = query.bits.get(depth).ok_or(
      F128InnerLigeritoCircuitError::UnsupportedShape("Merkle direction bit"),
    )?;
    let left = select_digest(builder, direction, &current, sibling)?;
    let right = select_digest(builder, direction, sibling, &current)?;
    current = hash_parent(builder, left, right)?;
  }

  let cap_depth = usize::try_from(level.summand_depths[0])
    .expect("validated cap depth fits usize");
  let selection_bits = cap_depth - query.stratum_depth;
  let range_len = checked_pow2(selection_bits)?;
  let range_start = query.stratum.checked_mul(range_len).ok_or(
    F128InnerLigeritoCircuitError::UnsupportedShape("CAP selection range"),
  )?;
  let candidates = cap.get(range_start..range_start + range_len).ok_or(
    F128InnerLigeritoCircuitError::UnsupportedShape("CAP selection range"),
  )?;
  let path_length = path.len();
  let selectors =
    query.bits.get(path_length..path_length + selection_bits).ok_or(
      F128InnerLigeritoCircuitError::UnsupportedShape("CAP selector bits"),
    )?;
  let expected = mux_digest_tree(builder, candidates, selectors)?;
  for (actual, expected) in current.iter().zip(&expected) {
    actual.enforce_equal_in_phase(builder, expected, PHASE);
  }
  Ok(())
}

/// `false_digest` is selected for a zero direction and `true_digest` for one.
fn select_digest(
  builder: &mut R1csBuilder,
  selector: &QueryBit,
  false_digest: &DigestVariables,
  true_digest: &DigestVariables,
) -> Result<DigestVariables, R1csError> {
  false_digest
    .iter()
    .zip(true_digest)
    .map(|(left, right)| {
      select_word_in_phase(
        builder,
        selector.variable,
        selector.value,
        left,
        right,
        PHASE,
      )
    })
    .collect::<Result<Vec<_>, _>>()?
    .try_into()
    .map_err(|_| R1csError::InternalShape)
}

fn mux_digest_tree(
  builder: &mut R1csBuilder,
  candidates: &[DigestVariables],
  selectors: &[QueryBit],
) -> Result<DigestVariables, F128InnerLigeritoCircuitError> {
  let mut current = candidates.to_vec();
  for selector in selectors {
    let (pairs, remainder) = current.as_chunks::<2>();
    if !remainder.is_empty() {
      return Err(F128InnerLigeritoCircuitError::UnsupportedShape(
        "CAP selector tree",
      ));
    }
    current = pairs
      .iter()
      .map(|pair| select_digest(builder, selector, &pair[0], &pair[1]))
      .collect::<Result<Vec<_>, _>>()?;
  }
  current.into_iter().next().ok_or(
    F128InnerLigeritoCircuitError::UnsupportedShape("empty CAP selector"),
  )
}

fn hash_leaf(
  builder: &mut R1csBuilder,
  row: &[F128VariablesV1],
) -> Result<DigestVariables, F128InnerLigeritoCircuitError> {
  let words = row.iter().flat_map(f128_words).collect::<Vec<_>>();
  let byte_length = row.len().checked_mul(F128_BYTES).ok_or(
    F128InnerLigeritoCircuitError::UnsupportedShape("leaf byte length"),
  )?;
  if byte_length == 0 || byte_length > MAX_CHUNK_BYTES {
    return Err(F128InnerLigeritoCircuitError::UnsupportedShape(
      "BLAKE3 leaf byte length",
    ));
  }
  let blocks = byte_length.div_ceil(BLOCK_BYTES);
  let mut chaining_value = BLAKE3_IV.map(Word32::constant);
  for block in 0..blocks {
    let start = block * BLOCK_WORDS;
    let end = (start + BLOCK_WORDS).min(words.len());
    let mut message = core::array::from_fn(|_| Word32::constant(0));
    for (target, source) in message.iter_mut().zip(&words[start..end]) {
      *target = source.clone();
    }
    let final_block = block + 1 == blocks;
    let block_length =
      if final_block { byte_length - block * BLOCK_BYTES } else { BLOCK_BYTES };
    let mut flags = 0;
    if block == 0 {
      flags |= CHUNK_START;
    }
    if final_block {
      flags |= CHUNK_END;
    }
    let output = constrain_compression_in_phase(
      builder,
      chaining_value,
      message,
      0,
      u32::try_from(block_length).expect("BLAKE3 block length fits u32"),
      flags,
      PHASE,
    )?;
    chaining_value =
      output[..8].to_vec().try_into().map_err(|_| R1csError::InternalShape)?;
  }
  Ok(chaining_value)
}

fn hash_parent(
  builder: &mut R1csBuilder,
  left: DigestVariables,
  right: DigestVariables,
) -> Result<DigestVariables, R1csError> {
  let message = left
    .into_iter()
    .chain(right)
    .collect::<Vec<_>>()
    .try_into()
    .map_err(|_| R1csError::InternalShape)?;
  let output = constrain_compression_in_phase(
    builder,
    BLAKE3_IV.map(Word32::constant),
    message,
    0,
    64,
    PARENT,
    PHASE,
  )?;
  output[..8].to_vec().try_into().map_err(|_| R1csError::InternalShape)
}

fn f128_words(value: &F128VariablesV1) -> [Word32; 4] {
  let chunks = value.value().as_chunks::<4>().0;
  core::array::from_fn(|word| {
    Word32::from_variables(
      u32::from_le_bytes(chunks[word]),
      value.bit_variables()[32 * word..32 * (word + 1)]
        .try_into()
        .expect("F128 word has 32 bits"),
    )
  })
}

fn alloc_digest(
  builder: &mut R1csBuilder,
  digest: [u8; 32],
) -> Result<DigestVariables, R1csError> {
  let chunks = digest.as_chunks::<4>().0;
  let words = core::array::from_fn(|index| u32::from_le_bytes(chunks[index]));
  alloc_words_in_phase(builder, words, PHASE)
}

fn constrain_enforced_sum(
  builder: &mut R1csBuilder,
  rows: &[Vec<F128VariablesV1>],
  lane_challenges: &[F256Variables],
  row_weights: &[F128VariablesV1],
  zero: &F128VariablesV1,
  one: &F128VariablesV1,
) -> Result<F256Variables, F128InnerLigeritoCircuitError> {
  if rows.len() != row_weights.len() {
    return Err(F128InnerLigeritoCircuitError::UnsupportedShape(
      "enforced-sum row weights",
    ));
  }
  let lane_weights = constrain_f256_eq_table(
    builder,
    lane_challenges,
    &f256_zero(zero),
    &f256_one(zero, one),
  )?;
  let mut total = f256_zero(zero);
  for (row, row_weight) in rows.iter().zip(row_weights) {
    if row.len() > lane_weights.len() {
      return Err(F128InnerLigeritoCircuitError::UnsupportedShape(
        "opened row exceeds lane equality table",
      ));
    }
    let mut evaluated = f256_zero(zero);
    for (word, weight) in row.iter().zip(&lane_weights) {
      let term = f256_multiply_base(builder, weight, word)?;
      evaluated = f256_add(builder, &evaluated, &term)?;
    }
    evaluated = f256_multiply_base(builder, &evaluated, row_weight)?;
    total = f256_add(builder, &total, &evaluated)?;
  }
  Ok(total)
}

fn resolve_ood(
  claim: &F128LigeritoOodClaimV1,
  observed_values: &[F128VariablesV1],
  challenges: &[F128VariablesV1],
) -> Result<OodVariables, F128InnerLigeritoCircuitError> {
  Ok(OodVariables {
    point: get_many(challenges, &claim.point_challenges, "OOD point")?,
    value: get(
      observed_values,
      claim.value_observation,
      "OOD value observation",
    )?,
    intro_message: claim
      .intro_message
      .map(|message| {
        resolve_message(message, observed_values, "OOD sumcheck message")
      })
      .transpose()?,
    beta: get(challenges, claim.beta_challenge, "OOD batching challenge")?,
  })
}

fn introduce_oods(
  builder: &mut R1csBuilder,
  oods: &[OodVariables],
  split_level: usize,
  claim: &mut F256Variables,
  quad: &mut RoundQuadVariables,
  contexts: &mut Vec<OodResidualContext>,
  zero: &F128VariablesV1,
) -> Result<(), F128InnerLigeritoCircuitError> {
  for ood in oods {
    let intro = ood.intro_message.clone().ok_or(
      F128InnerLigeritoCircuitError::InvalidTrace(
        "recursive OOD has no sumcheck message".to_owned(),
      ),
    )?;
    let intro = RoundQuadVariables::from_message(
      builder,
      intro,
      &f256_from_base(&ood.value, zero),
    )?;
    *quad = quad.fold(builder, &intro, &ood.beta)?;
    add_base_claim(builder, claim, &ood.value, &ood.beta)?;
    contexts.push(OodResidualContext {
      point: ood.point.clone(),
      beta: ood.beta.clone(),
      split_level: Some(split_level),
    });
  }
  Ok(())
}

fn add_base_claim(
  builder: &mut R1csBuilder,
  claim: &mut F256Variables,
  value: &F128VariablesV1,
  beta: &F128VariablesV1,
) -> Result<(), R1csError> {
  let term = constrain_f128_multiply(builder, value, beta, PHASE)?;
  claim.c0 = constrain_f128_add(builder, &claim.c0, &term, PHASE)?;
  Ok(())
}

impl RoundQuadVariables {
  fn from_message(
    builder: &mut R1csBuilder,
    message: F256LigeritoMessageVariables,
    claim: &F256Variables,
  ) -> Result<Self, R1csError> {
    Ok(Self {
      c: message.u_0,
      b: f256_add(builder, claim, &message.u_2)?,
      a: message.u_2,
    })
  }

  fn evaluate(
    &self,
    builder: &mut R1csBuilder,
    challenge: &F256Variables,
  ) -> Result<F256Variables, R1csError> {
    let linear = f256_multiply(builder, challenge, &self.b)?;
    let squared = f256_square(builder, challenge)?;
    let quadratic = f256_multiply(builder, &squared, &self.a)?;
    let constant_and_linear = f256_add(builder, &self.c, &linear)?;
    f256_add(builder, &constant_and_linear, &quadratic)
  }

  fn fold(
    &self,
    builder: &mut R1csBuilder,
    right: &Self,
    challenge: &F128VariablesV1,
  ) -> Result<Self, R1csError> {
    let right_c = f256_multiply_base(builder, &right.c, challenge)?;
    let right_b = f256_multiply_base(builder, &right.b, challenge)?;
    let right_a = f256_multiply_base(builder, &right.a, challenge)?;
    Ok(Self {
      c: f256_add(builder, &self.c, &right_c)?,
      b: f256_add(builder, &self.b, &right_b)?,
      a: f256_add(builder, &self.a, &right_a)?,
    })
  }
}

fn constrain_eq_residual(
  builder: &mut R1csBuilder,
  point: &[F128VariablesV1],
  fixed: &[F256Variables],
  residual_log: usize,
  scale: &F256Variables,
  zero: &F128VariablesV1,
  one: &F128VariablesV1,
) -> Result<Vec<F256Variables>, F128InnerLigeritoCircuitError> {
  if fixed.len() + residual_log != point.len() {
    return Err(F128InnerLigeritoCircuitError::UnsupportedShape(
      "equality residual dimension",
    ));
  }
  let mut prefix = scale.clone();
  for (coordinate, challenge) in point.iter().zip(fixed) {
    let one_plus_coordinate =
      constrain_f128_add(builder, one, coordinate, PHASE)?;
    let factor = F256Variables {
      c0: constrain_f128_add(
        builder,
        &one_plus_coordinate,
        &challenge.c0,
        PHASE,
      )?,
      c1: challenge.c1.clone(),
    };
    prefix = f256_multiply(builder, &prefix, &factor)?;
  }
  let suffix = constrain_eq_table(builder, &point[fixed.len()..], zero, one)?;
  suffix
    .iter()
    .map(|weight| f256_multiply_base(builder, &prefix, weight))
    .collect::<Result<Vec<_>, _>>()
    .map_err(Into::into)
}

#[allow(clippy::too_many_arguments)]
fn constrain_induced_basis_at_residual(
  builder: &mut R1csBuilder,
  log_columns: usize,
  queries: &[QueryVariables],
  query_weights: &[F128VariablesV1],
  fixed: &[F256Variables],
  residual_log: usize,
  scale: &F256Variables,
  zero: &F128VariablesV1,
  one: &F128VariablesV1,
) -> Result<Vec<F256Variables>, F128InnerLigeritoCircuitError> {
  if fixed.len() + residual_log != log_columns
    || queries.len() != query_weights.len()
  {
    return Err(F128InnerLigeritoCircuitError::UnsupportedShape(
      "induced residual dimension",
    ));
  }
  let (sks_vks, inverse_sks_vks) = novel_basis_constants(log_columns)?;
  let residual_len = checked_pow2(residual_log)?;
  let mut result = vec![f256_zero(zero); residual_len];
  for (query, row_weight) in queries.iter().zip(query_weights) {
    let mut raw = Vec::with_capacity(log_columns);
    if log_columns != 0 {
      raw.push(query.field.clone());
      for column in 1..log_columns {
        let prior = raw.last().expect("nonempty novel-basis recurrence");
        let squared = constrain_f128_frobenius(builder, prior, 1, PHASE)?;
        let scaled = constrain_f128_multiply_constant(
          builder,
          prior,
          sks_vks[column - 1],
          PHASE,
        )?;
        raw.push(constrain_f128_add(builder, &squared, &scaled, PHASE)?);
      }
    }
    let normalized = raw
      .iter()
      .zip(&inverse_sks_vks)
      .map(|(value, &inverse)| {
        constrain_f128_multiply_constant(builder, value, inverse, PHASE)
      })
      .collect::<Result<Vec<_>, _>>()?;

    let mut prefix = f256_one(zero, one);
    for (challenge, weight) in fixed.iter().zip(&normalized) {
      let one_plus_weight = constrain_f128_add(builder, one, weight, PHASE)?;
      let product = f256_multiply_base(builder, challenge, &one_plus_weight)?;
      let factor = f256_add(builder, &f256_one(zero, one), &product)?;
      prefix = f256_multiply(builder, &prefix, &factor)?;
    }
    prefix = f256_multiply(builder, &prefix, scale)?;
    prefix = f256_multiply_base(builder, &prefix, row_weight)?;

    let mut suffix = vec![one.clone()];
    for weight in &normalized[fixed.len()..] {
      let products = suffix
        .iter()
        .map(|value| constrain_f128_multiply(builder, value, weight, PHASE))
        .collect::<Result<Vec<_>, _>>()?;
      suffix.extend(products);
    }
    if suffix.len() != residual_len {
      return Err(F128InnerLigeritoCircuitError::UnsupportedShape(
        "induced suffix table",
      ));
    }
    for (output, suffix) in result.iter_mut().zip(&suffix) {
      let contribution = f256_multiply_base(builder, &prefix, suffix)?;
      *output = f256_add(builder, output, &contribution)?;
    }
  }
  Ok(result)
}

fn novel_basis_constants(
  log_columns: usize,
) -> Result<(Vec<[u8; 16]>, Vec<[u8; 16]>), F128InnerLigeritoCircuitError> {
  if log_columns >= 128 {
    return Err(F128InnerLigeritoCircuitError::UnsupportedShape(
      "novel-basis dimension",
    ));
  }
  let mut sks_vks = vec![[0; 16]; log_columns + 1];
  sks_vks[0][0] = 1;
  if log_columns != 0 {
    let mut layer = (1..=log_columns)
      .map(|power| (1u128 << power).to_le_bytes())
      .collect::<Vec<_>>();
    let mut current = log_columns;
    for row in 0..log_columns {
      for column in 0..current {
        let squared = native_f128_multiply(layer[column], layer[column]);
        let scaled = native_f128_multiply(layer[column], sks_vks[row]);
        let next = native_f128_add(squared, scaled);
        if column == 0 {
          sks_vks[row + 1] = next;
        } else {
          layer[column - 1] = next;
        }
      }
      current -= 1;
    }
  }
  let inverse = sks_vks[..log_columns]
    .iter()
    .map(|&value| {
      native_f128_inverse(value).ok_or(
        F128InnerLigeritoCircuitError::UnsupportedShape(
          "zero novel-basis normalization",
        ),
      )
    })
    .collect::<Result<Vec<_>, _>>()?;
  Ok((sks_vks, inverse))
}

fn coordinate_scale(
  builder: &mut R1csBuilder,
  levels: &[Vec<F256Variables>],
  start_level: usize,
  zero: &F128VariablesV1,
  one: &F128VariablesV1,
) -> Result<F256Variables, F128InnerLigeritoCircuitError> {
  if start_level > levels.len() {
    return Err(F128InnerLigeritoCircuitError::UnsupportedShape(
      "coordinate-scale start level",
    ));
  }
  levels[start_level..].iter().try_fold(
    f256_one(zero, one),
    |accumulator, level| {
      let challenge = level.first().ok_or(
        F128InnerLigeritoCircuitError::UnsupportedShape(
          "empty recursive fold level",
        ),
      )?;
      let factor = coordinate_fold_factor(builder, challenge, one)?;
      Ok(f256_multiply(builder, &accumulator, &factor)?)
    },
  )
}

fn coordinate_fold_factor(
  builder: &mut R1csBuilder,
  challenge: &F256Variables,
  one: &F128VariablesV1,
) -> Result<F256Variables, R1csError> {
  let x_inverse_c1 = constrain_f128_multiply_constant(
    builder,
    &challenge.c1,
    QUADRATIC_NONRESIDUE,
    PHASE,
  )?;
  let one_plus_c0 = constrain_f128_add(builder, one, &challenge.c0, PHASE)?;
  Ok(F256Variables {
    c0: constrain_f128_add(builder, &one_plus_c0, &x_inverse_c1, PHASE)?,
    c1: challenge.c0.clone(),
  })
}

fn residual_original_challenges(
  initial: &[F256Variables],
  levels: &[Vec<F256Variables>],
  start_level: usize,
) -> Vec<F256Variables> {
  let mut output = Vec::new();
  if start_level == 0 {
    output.extend_from_slice(initial);
  }
  for level in levels.iter().skip(start_level) {
    output.extend_from_slice(&level[1..]);
  }
  output
}

fn add_residual(
  builder: &mut R1csBuilder,
  target: &mut [F256Variables],
  source: &[F256Variables],
) -> Result<(), F128InnerLigeritoCircuitError> {
  if target.len() != source.len() {
    return Err(F128InnerLigeritoCircuitError::UnsupportedShape(
      "residual vector length",
    ));
  }
  for (target, source) in target.iter_mut().zip(source) {
    *target = f256_add(builder, target, source)?;
  }
  Ok(())
}

fn constrain_f256_eq_table(
  builder: &mut R1csBuilder,
  point: &[F256Variables],
  _zero: &F256Variables,
  one: &F256Variables,
) -> Result<Vec<F256Variables>, R1csError> {
  let mut table = vec![one.clone()];
  for coordinate in point {
    let zero_factor = f256_add(builder, one, coordinate)?;
    let mut next = Vec::with_capacity(2 * table.len());
    for weight in &table {
      next.push(f256_multiply(builder, weight, &zero_factor)?);
    }
    for weight in &table {
      next.push(f256_multiply(builder, weight, coordinate)?);
    }
    table = next;
  }
  Ok(table)
}

fn f256_zero(zero: &F128VariablesV1) -> F256Variables {
  F256Variables { c0: zero.clone(), c1: zero.clone() }
}

fn f256_one(zero: &F128VariablesV1, one: &F128VariablesV1) -> F256Variables {
  F256Variables { c0: one.clone(), c1: zero.clone() }
}

fn f256_from_base(
  value: &F128VariablesV1,
  zero: &F128VariablesV1,
) -> F256Variables {
  F256Variables { c0: value.clone(), c1: zero.clone() }
}

fn f256_add(
  builder: &mut R1csBuilder,
  left: &F256Variables,
  right: &F256Variables,
) -> Result<F256Variables, R1csError> {
  Ok(F256Variables {
    c0: constrain_f128_add(builder, &left.c0, &right.c0, PHASE)?,
    c1: constrain_f128_add(builder, &left.c1, &right.c1, PHASE)?,
  })
}

fn f256_multiply_base(
  builder: &mut R1csBuilder,
  value: &F256Variables,
  scalar: &F128VariablesV1,
) -> Result<F256Variables, R1csError> {
  Ok(F256Variables {
    c0: constrain_f128_multiply(builder, &value.c0, scalar, PHASE)?,
    c1: constrain_f128_multiply(builder, &value.c1, scalar, PHASE)?,
  })
}

fn f256_multiply(
  builder: &mut R1csBuilder,
  left: &F256Variables,
  right: &F256Variables,
) -> Result<F256Variables, R1csError> {
  let p0 = constrain_f128_multiply(builder, &left.c0, &right.c0, PHASE)?;
  let p1 = constrain_f128_multiply(builder, &left.c1, &right.c1, PHASE)?;
  let left_sum = constrain_f128_add(builder, &left.c0, &left.c1, PHASE)?;
  let right_sum = constrain_f128_add(builder, &right.c0, &right.c1, PHASE)?;
  let p2 = constrain_f128_multiply(builder, &left_sum, &right_sum, PHASE)?;
  let x_inverse_p1 = constrain_f128_multiply_constant(
    builder,
    &p1,
    QUADRATIC_NONRESIDUE,
    PHASE,
  )?;
  Ok(F256Variables {
    c0: constrain_f128_add(builder, &p0, &x_inverse_p1, PHASE)?,
    c1: constrain_f128_add(builder, &p2, &p0, PHASE)?,
  })
}

fn f256_square(
  builder: &mut R1csBuilder,
  value: &F256Variables,
) -> Result<F256Variables, R1csError> {
  let c0_squared = constrain_f128_frobenius(builder, &value.c0, 1, PHASE)?;
  let c1_squared = constrain_f128_frobenius(builder, &value.c1, 1, PHASE)?;
  let x_inverse_c1 = constrain_f128_multiply_constant(
    builder,
    &c1_squared,
    QUADRATIC_NONRESIDUE,
    PHASE,
  )?;
  Ok(F256Variables {
    c0: constrain_f128_add(builder, &c0_squared, &x_inverse_c1, PHASE)?,
    c1: c1_squared,
  })
}

fn f256_multiply_u(
  builder: &mut R1csBuilder,
  value: &F256Variables,
) -> Result<F256Variables, R1csError> {
  Ok(F256Variables {
    c0: constrain_f128_multiply_constant(
      builder,
      &value.c1,
      QUADRATIC_NONRESIDUE,
      PHASE,
    )?,
    c1: constrain_f128_add(builder, &value.c0, &value.c1, PHASE)?,
  })
}

fn resolve_message(
  message: F256LigeritoMessageV1,
  observed_values: &[F128VariablesV1],
  kind: &'static str,
) -> Result<F256LigeritoMessageVariables, F128InnerLigeritoCircuitError> {
  Ok(F256LigeritoMessageVariables {
    u_0: resolve_pair(message.u_0, observed_values, kind)?,
    u_2: resolve_pair(message.u_2, observed_values, kind)?,
  })
}

fn resolve_pair(
  pair: F256IndexPairV1,
  values: &[F128VariablesV1],
  kind: &'static str,
) -> Result<F256Variables, F128InnerLigeritoCircuitError> {
  Ok(F256Variables {
    c0: get(values, pair.c0, kind)?,
    c1: get(values, pair.c1, kind)?,
  })
}

fn get<T: Clone>(
  values: &[T],
  index: u64,
  kind: &'static str,
) -> Result<T, F128InnerLigeritoCircuitError> {
  values
    .get(to_usize(index, kind)?)
    .cloned()
    .ok_or(F128InnerLigeritoCircuitError::MissingInput(kind))
}

fn get_many<T: Clone>(
  values: &[T],
  indices: &[u64],
  kind: &'static str,
) -> Result<Vec<T>, F128InnerLigeritoCircuitError> {
  indices.iter().map(|&index| get(values, index, kind)).collect()
}

fn to_usize(
  value: u64,
  kind: &'static str,
) -> Result<usize, F128InnerLigeritoCircuitError> {
  usize::try_from(value)
    .map_err(|_| F128InnerLigeritoCircuitError::MissingInput(kind))
}

fn checked_pow2(
  exponent: usize,
) -> Result<usize, F128InnerLigeritoCircuitError> {
  1usize
    .checked_shl(u32::try_from(exponent).map_err(|_| {
      F128InnerLigeritoCircuitError::UnsupportedShape("power-of-two exponent")
    })?)
    .ok_or(F128InnerLigeritoCircuitError::UnsupportedShape(
      "power-of-two exponent",
    ))
}

#[cfg(test)]
mod tests {
  use super::*;
  use blake3::hazmat::{HasherExt, Mode, merge_subtrees_non_root};

  fn pair(start: u64) -> F256IndexPairV1 {
    F256IndexPairV1 { c0: start, c1: start + 1 }
  }

  fn message(start: u64) -> F256LigeritoMessageV1 {
    F256LigeritoMessageV1 { u_0: pair(start), u_2: pair(start + 2) }
  }

  fn fixture() -> F128InnerLigeritoTraceV1 {
    F128InnerLigeritoTraceV1 {
      frontend_topology_digest: [7; 32],
      commitment_variables: 10,
      q_eval_observation: 0,
      batching_challenge: 0,
      target_observation: 1,
      first_message: message(2),
      levels: vec![
        F128LigeritoLevelV1 {
          cap_payload: 0,
          cap_nodes: 1,
          block_variables: 2,
          lane_count: 2,
          log_message_columns: 2,
          summand_depths: vec![0],
          query_challenges: vec![1],
          opened_rows: vec![vec![0, 1]],
          merkle_paths: vec![vec![0, 1]],
          lane_challenges: vec![pair(2)],
          round_messages: vec![message(6)],
          alpha_challenges: vec![],
          ood_claims: vec![],
          intro_message: Some(message(10)),
          beta_challenge: 4,
        },
        F128LigeritoLevelV1 {
          cap_payload: 1,
          cap_nodes: 1,
          block_variables: 2,
          lane_count: 4,
          log_message_columns: 1,
          summand_depths: vec![0],
          query_challenges: vec![5],
          opened_rows: vec![vec![2, 3, 4, 5]],
          merkle_paths: vec![vec![2, 3]],
          lane_challenges: vec![pair(6), pair(8)],
          round_messages: vec![message(14), message(18)],
          alpha_challenges: vec![],
          ood_claims: vec![],
          intro_message: None,
          beta_challenge: 10,
        },
      ],
      final_yr_observations: vec![22, 23, 24, 25],
    }
  }

  fn cap_and_path(row_bytes: usize) -> ([u8; 32], [[u8; 32]; 2]) {
    let leaf =
      blake3::Hasher::new().update(&vec![0; row_bytes]).finalize_non_root();
    let parent = merge_subtrees_non_root(&leaf, &leaf, Mode::Hash);
    let root = merge_subtrees_non_root(&parent, &parent, Mode::Hash);
    (root, [leaf, parent])
  }

  fn allocate_values(
    builder: &mut R1csBuilder,
    values: &[[u8; 16]],
  ) -> Vec<F128VariablesV1> {
    values
      .iter()
      .copied()
      .map(|value| alloc_f128_private(builder, value, PHASE).unwrap())
      .collect()
  }

  fn constrain_fixture(
    builder: &mut R1csBuilder,
    query_word: [u8; 16],
  ) -> F128InnerLigeritoCircuitOutputV1 {
    let trace = fixture();
    let observed = allocate_values(builder, &vec![[0; 16]; 26]);
    let mut challenge_values = vec![[0; 16]; 11];
    challenge_values[1] = query_word;
    challenge_values[5] = query_word;
    let challenges = allocate_values(builder, &challenge_values);
    let (cap_0, path_0) = cap_and_path(2 * F128_BYTES);
    let (cap_1, path_1) = cap_and_path(4 * F128_BYTES);
    let cap_values = [cap_0, cap_1]
      .into_iter()
      .map(|digest| digest.as_chunks::<16>().0.to_vec())
      .collect::<Vec<_>>();
    let payload_variables = cap_values
      .iter()
      .map(|values| allocate_values(builder, values))
      .collect::<Vec<_>>();
    let payloads = payload_variables
      .iter()
      .map(|values| {
        values
          .iter()
          .map(F128TranscriptWordV1::from_f128_variables)
          .collect::<Vec<_>>()
      })
      .collect::<Vec<_>>();
    let rho = allocate_values(builder, &[[0; 16]; 3]);
    let frontend = F128MergedPcsFrontendCircuitOutputV1 {
      topology_digest: [7; 32],
      commitment_cap: payloads[0].clone(),
      ring_switches: vec![],
      packed_direct_claims: vec![],
      batching_challenges: vec![],
      rho,
      running: observed[0].clone(),
      q_eval: observed[0].clone(),
    };
    let private_digests = path_0.into_iter().chain(path_1).collect::<Vec<_>>();
    constrain_f128_inner_ligerito(
      builder,
      &trace,
      F128InnerLigeritoCircuitInputsV1 {
        observed_values: &observed,
        challenges: &challenges,
        byte_payloads: &payloads,
        private_values: &[[0; 16]; 6],
        private_digests: &private_digests,
        frontend: &frontend,
      },
    )
    .expect("constrain synthetic inner Ligerito proof")
  }

  #[test]
  fn constrains_a_zero_two_level_opening() {
    let mut builder = R1csBuilder::new();
    let output = constrain_fixture(&mut builder, [0; 16]);
    assert_eq!(output.authenticated_queries, 2);
    let (r1cs, witness) = builder.finish().unwrap();
    r1cs.check(&witness).unwrap();
  }

  #[test]
  fn query_values_do_not_change_the_projection() {
    let mut first = R1csBuilder::new_projection();
    constrain_fixture(&mut first, [0; 16]);
    let first = first.finish_projection().unwrap();
    let mut query_one = [0; 16];
    query_one[0] = 1;
    let mut second = R1csBuilder::new_projection();
    constrain_fixture(&mut second, query_one);
    let second = second.finish_projection().unwrap();
    assert_eq!(first.census(), second.census());
    assert_eq!(first.digest(), second.digest());
  }
}
