//! Fixed-layout proving of an already executed invocation. Used after a
//! recursive wrap to normalize arbitrary child proofs for compression.
use super::*;
use multi_stark::{batch::ShardInput, system::SystemWitness};

impl AiurSystem {
  /// Prove one invocation in a fixed, all-active trace layout. Function and
  /// memory tables have exactly 2^log_height rows; fixed byte tables retain
  /// their native heights. Empty tables are zero-padded. Memory closures have
  /// one pair per statically declared width, including empty intervals.
  /// Returns an error before trace allocation if any execution table exceeds
  /// its bound. The caller supplies the matching execution record and output.
  pub fn prove_from_execution_normalized(
    &self,
    fun_idx: FunIdx,
    input: &[G],
    io: &IOBuffer,
    record: QueryRecord,
    output: &[G],
    log_height: u32,
  ) -> Result<(Vec<G>, AiurProof), String> {
    if !(1..=26).contains(&log_height) || record.pointer_base != 0 {
      return Err(
        "normalization requires log-height 1–26 and pointer base zero".into(),
      );
    }
    let height = 1usize << log_height;
    let mut plan = self.single_shard_plan(&record);
    let mut logs = Vec::new();
    for (i, (circuit, rows)) in
      self.system.circuits.iter().zip(&plan.shards[0].rows).enumerate()
    {
      let target = if circuit.preprocessed_height == 0 {
        height
      } else {
        circuit.preprocessed_height
      };
      if rows.len() > target {
        return Err(format!(
          "normalization circuit {i} needs {} rows; configured bound is {target}",
          rows.len()
        ));
      }
      logs.push(u8::try_from(target.ilog2()).map_err(|e| e.to_string())?);
    }
    let active = vec![true; logs.len()];
    if lookup_query_bound(
      self.system.circuits.iter().map(|c| c.num_lookups),
      &active,
      &logs,
    )
    .is_none()
      || !trace_cap_coverage(
        self.commitment_parameters.log_blowup,
        self.commitment_parameters.cap_height,
        &logs,
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
    for (trace, &log) in traces.iter_mut().zip(&logs) {
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
