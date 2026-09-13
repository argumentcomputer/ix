//! Inner Ligerito's F256 ladder, fixed query schedule, private row/path slots,
//! and exact parent transcript. All loop bounds come from approved PCS data;
//! queries are not sampled and duplicate query values cannot change topology.

use super::tape::{Tape, pow2};
use anyhow::{Result, ensure};
use flock_prover::{hash::HashKind, pcs::ligerito::VerifierConfig};
use ix_stage4_trace::{
  F128InnerLigeritoTraceV1, F128LigeritoLevelV1, F128LigeritoOodClaimV1,
  F128MergedPcsFrontendTraceV1, F256IndexPairV1, F256LigeritoMessageV1,
};
use ixby_flock::ixby::exec::CompiledExec;

pub(super) fn compile_inner(
  setup: &CompiledExec,
  frontend: &F128MergedPcsFrontendTraceV1,
  tape: &mut Tape,
) -> Result<F128InnerLigeritoTraceV1> {
  let params = setup.pcs_params();
  let config = params.ligerito_verifier_config().map_err(anyhow::Error::msg)?;
  let count = config.recursive_steps + 1;
  let log_n = params
    .m
    .checked_sub(7)
    .ok_or_else(|| anyhow::anyhow!("inner dimension"))?;
  ensure!(
    count >= 2
      && config.merkle_hash == HashKind::Blake3
      && config.log_inv_rates.len() == count
      && config.recursive_ks.len() + 1 == count
      && config.recursive_log_msg_cols.len() + 1 == count
      && config.queries.len() == count
      && config.stratified.len() == count
      && config.ood_samples.len() == count
      && config.grinding_bits.len() == count
      && config.claim_batch_grinding_bits.len() == count
      && config.consistency_batch_grinding_bits.len() == count
      && config.fold_grinding_bits.iter().all(|&bits| bits == 0)
      && config.recursive_ks.iter().all(|&k| k >= 2)
      && config.initial_k == config.initial_log_num_interleaved
      && config.initial_log_msg_cols + config.initial_k == log_n,
    "unsupported approved inner Ligerito configuration"
  );
  let mut levels = (0..count)
    .map(|level| empty_level(&config, level, params.num_ntts()))
    .collect::<Result<Vec<_>>>()?;
  tape.label(b"flock-pcs-open-batch-v0");
  tape.label(b"flock-pcs-packed-direct-v0");
  let q_eval_observation = tape.observe();
  ensure!(
    q_eval_observation == frontend.q_eval_observation,
    "inner/frontend q address"
  );
  // The sole packed-direct claim uses a one-word VECTOR squeeze, no batch
  // nonce. Replacing it with a scalar squeeze changes the hash transcript.
  let batching_challenge = tape.squeeze_slice(1, None)[0];
  tape.label(b"flock-ligerito-basis-f256-split-v0");
  let target_observation = tape.observe();
  levels[0].cap_payload = tape.bytes(levels[0].cap_nodes as usize * 32);
  levels[0].ood_claims = oods(tape, &config, 0, log_n)?;
  let first_message = tape.message();
  (levels[0].lane_challenges, levels[0].round_messages) =
    rounds(tape, config.initial_k);
  levels[1].cap_payload = tape.bytes(levels[1].cap_nodes as usize * 32);
  levels[1].ood_claims =
    oods(tape, &config, 1, config.initial_log_msg_cols + 1)?;
  let mut private = PrivateSlots::default();
  opening(tape, &config, 0, &mut levels[0], &mut private)?;
  let mut final_yr_observations = Vec::new();
  for level in 1..count {
    (levels[level].lane_challenges, levels[level].round_messages) =
      rounds(tape, config.recursive_ks[level - 1]);
    if level + 1 == count {
      final_yr_observations = (0..2
        * pow2(config.recursive_log_msg_cols[level - 1])?)
        .map(|_| tape.observe())
        .collect();
    } else {
      levels[level + 1].cap_payload =
        tape.bytes(levels[level + 1].cap_nodes as usize * 32);
      levels[level + 1].ood_claims = oods(
        tape,
        &config,
        level + 1,
        config.recursive_log_msg_cols[level - 1] + 1,
      )?;
    }
    opening(tape, &config, level, &mut levels[level], &mut private)?;
  }
  let trace = F128InnerLigeritoTraceV1 {
    frontend_topology_digest: frontend.topology_digest(),
    commitment_variables: u32::try_from(params.m)?,
    q_eval_observation,
    batching_challenge,
    target_observation,
    first_message,
    levels,
    final_yr_observations,
  };
  trace.validate(
    usize::try_from(tape.address.observed)?,
    usize::try_from(tape.address.challenges)?,
    &tape.payload_lengths,
    usize::try_from(private.values)?,
    usize::try_from(private.digests)?,
  )?;
  Ok(trace)
}

fn empty_level(
  config: &VerifierConfig,
  level: usize,
  l0_lanes: usize,
) -> Result<F128LigeritoLevelV1> {
  let schedule = &config.stratified[level];
  ensure!(schedule.queries() == config.queries[level], "inner query schedule");
  let (lanes, columns) = if level == 0 {
    (l0_lanes, config.initial_log_msg_cols)
  } else {
    (
      pow2(config.recursive_ks[level - 1])?,
      config.recursive_log_msg_cols[level - 1],
    )
  };
  ensure!(
    schedule.log_block_len == columns + config.log_inv_rates[level],
    "inner codeword dimension"
  );
  Ok(F128LigeritoLevelV1 {
    cap_payload: 0,
    cap_nodes: u32::try_from(pow2(schedule.cap_depth())?)?,
    block_variables: u32::try_from(schedule.log_block_len)?,
    lane_count: u32::try_from(lanes)?,
    log_message_columns: u32::try_from(columns)?,
    summand_depths: schedule
      .summand_depths
      .iter()
      .map(|&depth| u32::try_from(depth))
      .collect::<Result<Vec<_>, _>>()?,
    query_challenges: Vec::new(),
    opened_rows: Vec::new(),
    merkle_paths: Vec::new(),
    lane_challenges: Vec::new(),
    round_messages: Vec::new(),
    alpha_challenges: Vec::new(),
    ood_claims: Vec::new(),
    intro_message: None,
    beta_challenge: 0,
  })
}

fn oods(
  tape: &mut Tape,
  config: &VerifierConfig,
  level: usize,
  variables: usize,
) -> Result<Vec<F128LigeritoOodClaimV1>> {
  let bits = u32::try_from(config.claim_batch_grinding_bits[level])?;
  Ok(
    (0..config.ood_samples[level])
      .map(|_| F128LigeritoOodClaimV1 {
        point_challenges: tape.squeeze_slice(variables, None),
        value_observation: tape.observe(),
        intro_message: (level != 0).then(|| tape.message()),
        beta_challenge: tape.squeeze(Some(bits)),
      })
      .collect(),
  )
}

fn rounds(
  tape: &mut Tape,
  count: usize,
) -> (Vec<F256IndexPairV1>, Vec<F256LigeritoMessageV1>) {
  (0..count)
    .map(|_| {
      let pair = tape.squeeze_slice(2, None);
      (F256IndexPairV1 { c0: pair[0], c1: pair[1] }, tape.message())
    })
    .unzip()
}

#[derive(Default)]
struct PrivateSlots {
  values: u64,
  digests: u64,
}

fn opening(
  tape: &mut Tape,
  config: &VerifierConfig,
  index: usize,
  level: &mut F128LigeritoLevelV1,
  private: &mut PrivateSlots,
) -> Result<()> {
  let queries = config.queries[index];
  let alpha_count =
    if queries <= 1 { 0 } else { usize::BITS - (queries - 1).leading_zeros() };
  level.query_challenges = tape
    .squeeze_slice(queries, Some(u32::try_from(config.grinding_bits[index])?));
  level.alpha_challenges = tape.squeeze_slice(
    alpha_count as usize,
    Some(u32::try_from(config.consistency_batch_grinding_bits[index])?),
  );
  let path = config.stratified[index]
    .log_block_len
    .checked_sub(config.stratified[index].cap_depth())
    .ok_or_else(|| anyhow::anyhow!("inner Merkle CAP exceeds tree"))?;
  level.opened_rows = (0..queries)
    .map(|_| {
      (0..level.lane_count)
        .map(|_| {
          let slot = private.values;
          private.values += 1;
          slot
        })
        .collect()
    })
    .collect();
  level.merkle_paths = (0..queries)
    .map(|_| {
      (0..path)
        .map(|_| {
          let slot = private.digests;
          private.digests += 1;
          slot
        })
        .collect()
    })
    .collect();
  let has_intro = index < config.recursive_steps;
  level.intro_message = has_intro.then(|| tape.message());
  let claim_level = if has_intro { index + 1 } else { index };
  level.beta_challenge = tape.squeeze(Some(u32::try_from(
    config.claim_batch_grinding_bits[claim_level],
  )?));
  Ok(())
}
