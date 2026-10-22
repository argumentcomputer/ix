//! Fixed-layout proving of an already executed invocation. Used after a
//! recursive wrap to normalize arbitrary child proofs for compression.
use super::*;
use multi_stark::{batch::ShardInput, system::SystemWitness};

impl AiurSystem {
  /// Prove one invocation in a fixed, all-active trace layout. Function and
  /// memory tables have their configured power-of-two heights; fixed byte
  /// tables retain their native heights. Empty tables are zero-padded. Memory
  /// closures have one pair per statically declared width, including empty intervals.
  /// Heights are in system order: function circuits, memories, then byte tables.
  /// Returns an error before trace allocation if any execution table exceeds
  /// its bound. The caller supplies the matching execution record and output.
  pub fn prove_from_execution_normalized(
    &self,
    fun_idx: FunIdx,
    input: &[G],
    io: &IOBuffer,
    record: QueryRecord,
    output: &[G],
    log_heights: &[u8],
  ) -> Result<(Vec<G>, AiurProof), String> {
    if record.pointer_base != 0 {
      return Err("normalization requires pointer base zero".into());
    }
    if log_heights.len() != self.system.circuits.len()
      || log_heights.iter().any(|log| !(1..=26).contains(log))
    {
      return Err(
        "normalization requires one log-height in 1–26 per circuit".into(),
      );
    }
    for (i, (circuit, &log)) in
      self.system.circuits.iter().zip(log_heights).enumerate()
    {
      if circuit.preprocessed_height != 0
        && circuit.preprocessed_height != 1usize << log
      {
        return Err(format!(
          "normalization circuit {i} must retain its preprocessed height"
        ));
      }
    }
    let mut plan = self.single_shard_plan(&record);
    for (i, (rows, &log)) in
      plan.shards[0].rows.iter().zip(log_heights).enumerate()
    {
      let target = 1usize << log;
      if rows.len() > target {
        return Err(format!(
          "normalization circuit {i} needs {} rows; configured bound is {target}",
          rows.len()
        ));
      }
    }
    let active = vec![true; log_heights.len()];
    if lookup_query_bound(
      self.system.circuits.iter().map(|c| c.num_lookups),
      &active,
      log_heights,
    )
    .is_none()
      || !trace_cap_coverage(
        self.commitment_parameters.log_blowup,
        self.commitment_parameters.cap_height,
        log_heights,
      )
    {
      return Err("normalized layout exceeds the Aiur proof bounds".into());
    }
    plan.memory_totals = self
      .toplevel
      .memory_sizes
      .iter()
      .map(|&width| {
        (
          width,
          0,
          record.memory_queries.get(&width).map_or(0, |rows| rows.len()),
        )
      })
      .collect();
    plan.memory_totals.sort_unstable();
    let messages = Self::boundary_messages(&plan);
    let index = self.row_index(&record, &plan);
    let mut traces = self.shard_witness(&record, io, &plan, &index, 0).traces;
    drop(record);
    for (trace, &log) in traces.iter_mut().zip(log_heights) {
      let size = trace
        .width
        .checked_mul(1usize << log)
        .ok_or("normalized trace size overflow")?;
      trace.values.resize(size, G::ZERO);
    }
    let witness = SystemWitness::from_stage_1(traces, &self.system);
    let mut claim = vec![function_channel(), G::from_usize(fun_idx)];
    claim.extend(input);
    claim.extend(output);
    let proof = self.system.prove_batch(
      &self.key,
      vec![ShardInput { claims: vec![claim.clone()], witness }],
      messages,
    );
    self
      .verify(&claim, &proof)
      .map_err(|e| format!("normalized proof: {e:?}"))?;
    Ok((claim, proof))
  }
}
