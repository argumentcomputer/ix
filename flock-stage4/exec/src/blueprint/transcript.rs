//! The complete main operation tree, reconstructed solely from approved
//! circuit/protocol geometry. Each fork, vector squeeze, label and grinding
//! marker is explicit; equality of F128 address counts alone is insufficient.

use super::{
  boolean::BooleanBlueprint,
  pcs::PcsBlueprint,
  tape::{Tape, nonzero, pow2},
};
use crate::replay::Stage4TranscriptOpV1;
use anyhow::{Result, ensure};
use flock_prover::{
  challenger::grinding_bits_for_degree, union::UnionInstance,
};
use ix_stage4_trace::F128InnerLigeritoTraceV1;
use ixby_flock::ixby::exec::CompiledExec;

pub(crate) struct MainBlueprint {
  pub(crate) operations: Vec<Stage4TranscriptOpV1>,
  pub(crate) payload_lengths: Vec<usize>,
  pub(crate) observed_values: u64,
  pub(crate) challenges: u64,
  pub(crate) inner: F128InnerLigeritoTraceV1,
}

pub(crate) fn compile_transcript(
  setup: &CompiledExec,
  boolean: &BooleanBlueprint,
  pcs: &PcsBlueprint,
) -> Result<MainBlueprint> {
  let shape = setup.verifier_shape();
  let union = UnionInstance::new(&shape.registry, shape.counts.clone());
  ensure!(
    !union.has_element() && union.num_boolean() != 0,
    "Boolean Exec tape required"
  );
  let params = setup.pcs_params();
  let mut tape = Tape::new();
  tape.label(b"flock-mixed-v1");
  tape.bytes(32);
  tape.bytes(8 * shape.counts.len());
  tape.bytes(32 * pow2(params.l0_cap_depth())?);
  tape.label(b"flock-circuit-stmt-v2");
  tape.bytes(32);
  tape.bytes(32);
  let wiring = tape.fork(b"flock-par-wiring-v1", |child| {
    let grinding = params.product_gkr_grinding();
    let live = shape.circuit.live_mask().counts.iter().sum::<usize>();
    let bits = nonzero(grinding.fingerprint_bits)
      .map(|bits| bits.max(grinding_bits_for_degree(live.saturating_sub(1))));
    child.label(b"flock-product-gkr-batched-v0");
    child.squeeze(bits);
    child.squeeze(None);
    child.observe();
    child.observe();
    for layer in 0..shape.circuit.cells().mu() {
      child.squeeze(nonzero(grinding.lambda_bits));
      for _ in 0..layer {
        child.observe();
        child.observe();
        child.squeeze(nonzero(grinding.round_bits));
      }
      for _ in 0..4 {
        child.observe();
      }
      child.squeeze(nonzero(grinding.close_bits));
    }
    for _ in 0..3 {
      child.observe();
    }
    Ok(())
  })?;
  let m = union.m_bool();
  ensure!(m >= 13 && m >= union.n_log() + 7, "Boolean tape dimensions");
  let zc = params.zerocheck_grinding();
  tape.label(b"flock-zerocheck-v0");
  tape.squeeze_slice(6, zc.initial_bits(m));
  tape.squeeze_slice(m - 13, None);
  tape.observe_slice(64);
  tape.observe_slice(64);
  tape.squeeze(zc.skip_bits());
  for _ in 0..m - 6 {
    tape.observe();
    tape.observe();
    tape.squeeze(zc.multilinear_round_bits());
  }
  tape.observe();
  tape.observe();
  let lc = params.lincheck_grinding();
  tape.label(b"flock-lincheck-v0");
  tape.squeeze(lc.alpha_bits());
  for ty in shape.registry.boolean_types() {
    if ty.const_pin.is_some() {
      tape.squeeze(lc.beta_bits());
    }
  }
  for _ in 0..m - union.n_log() - 6 {
    tape.observe();
    tape.observe();
    tape.squeeze(lc.multilinear_round_bits());
  }
  tape.observe_slice(64);
  tape.squeeze(lc.skip_bits(6));
  ensure!(
    tape.address == boolean.end,
    "Boolean algebra/tape address agreement"
  );
  tape.merge(wiring);

  let grinding = params.opening_grinding();
  tape.label(b"flock-merged-open-v1");
  for ring in &pcs.frontend.ring_switches {
    tape.label(b"flock-ring-switch-v0");
    ensure!(
      tape.observe_slice(128) == ring.s_hat_v_observations,
      "ring-switch slice tape"
    );
    ensure!(
      tape.squeeze_slice(7, nonzero(grinding.ring_switch_bits))
        == ring.r_dprime_challenges,
      "ring-switch challenge tape"
    );
  }
  for &expected in &pcs.frontend.packed_direct_observations {
    ensure!(tape.observe() == expected, "packed-direct tape");
  }
  ensure!(
    tape.squeeze_slice(
      pcs.frontend.batching_challenges.len(),
      nonzero(grinding.claim_batch_bits)
    ) == pcs.frontend.batching_challenges,
    "PCS batching tape"
  );
  for round in &pcs.frontend.merged_rounds {
    ensure!(tape.observe() == round.one_observation, "merged round one tape");
    ensure!(
      tape.observe() == round.infinity_observation,
      "merged round infinity tape"
    );
    ensure!(
      tape.squeeze(nonzero(grinding.merged_round_bits)) == round.challenge,
      "merged round challenge tape"
    );
  }
  let assist = tape.fork(b"flock-par-assist-v1", |child| {
    let mp = &pcs.multipoint;
    let grinding = grinding.multipoint;
    child.label(b"flock-multipoint-twisted-v1");
    for &expected in mp
      .dual_value_observations
      .iter()
      .flatten()
      .chain(&mp.group_value_observations)
    {
      ensure!(child.observe() == expected, "multipoint value tape");
    }
    ensure!(
      child.squeeze(nonzero(grinding.gamma_bits_for(2, 1)))
        == mp.gamma_challenge,
      "multipoint gamma tape"
    );
    for round in &mp.multipoint_rounds {
      ensure!(child.observe() == round.one_observation, "multipoint one tape");
      ensure!(
        child.observe() == round.infinity_observation,
        "multipoint infinity tape"
      );
      ensure!(
        child.squeeze(nonzero(grinding.round_bits)) == round.challenge,
        "multipoint challenge tape"
      );
    }
    child.label(b"flock-frobenius-assist-v0");
    ensure!(
      child.observe() == mp.anchor_value_observation,
      "anchor value tape"
    );
    for round in &mp.anchor_rounds {
      ensure!(child.observe() == round.one_observation, "anchor one tape");
      ensure!(
        child.observe() == round.infinity_observation,
        "anchor infinity tape"
      );
      ensure!(
        child.squeeze(nonzero(grinding.anchor_round_bits)) == round.challenge,
        "anchor challenge tape"
      );
    }
    Ok(())
  })?;
  let inner = super::inner::compile_inner(setup, &pcs.frontend, &mut tape)?;
  tape.merge(assist);
  Ok(MainBlueprint {
    operations: tape.ops,
    payload_lengths: tape.payload_lengths,
    observed_values: tape.address.observed,
    challenges: tape.address.challenges,
    inner,
  })
}
