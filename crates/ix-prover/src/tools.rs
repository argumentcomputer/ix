//! Stateless prover operations on program and system handles: proof
//! verification, verifying-key identity, execution-only checks and plans,
//! single-claim proving, and recursive range advice.
use crate::{
  PrepFailure,
  protocol::{Kind, Request},
  request::{IXVM_ENTRY, RECURSIVE_ENTRIES, Uncharged},
  system::{Program, System},
};
use aiur::trace::stark::{BatchProof, planning};
use serde_json::{Value, json};
use std::{path::Path, time::Instant};

/// The prefix of a formal IxVM proof as stored in an `Ixon.Proof`.
pub const IXVM_MAGIC: &[u8] = b"IXAIUR2\0";

/// Available host memory in bytes, when known, and logical cores.
pub fn resources() -> (Option<u64>, usize) {
  (
    planning::available_memory(),
    std::thread::available_parallelism().map_or(1, usize::from),
  )
}

/// What a check or proof decided: whether its plan fits the budget, and how
/// a caller that splits claims should split this one.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Planned {
  pub fits: bool,
  /// Whether splitting the claim can help; false when the fixed tables
  /// alone exceed the budget.
  pub can_split: bool,
  pub suggested_parts: usize,
  pub generation_peak_bytes: u64,
  pub proving_peak_bytes: u64,
}

impl Planned {
  fn of(plan: &planning::BatchPlan, can_split: bool) -> Self {
    Self {
      fits: plan.fits,
      can_split,
      suggested_parts: plan.suggested_parts,
      generation_peak_bytes: plan.generation_peak_bytes,
      proving_peak_bytes: plan.proving_peak_bytes,
    }
  }
}

/// The result of one stateless job: its status (0, or 75 when no plan fits
/// the budget), what its plan decided (none for execution alone), and a
/// diagnostic report that callers render only when asked to.
pub struct Outcome {
  pub status: u32,
  pub plan: Option<Planned>,
  pub report: Value,
}

/// Verify `proof` of `entry(args)` against the system's circuits on the
/// CPU. An IxVM proof carries [`IXVM_MAGIC`]; a recursive proof is raw.
/// Returns the number of trace shards.
pub fn verify(
  system: &System,
  entry: &str,
  args: &[u64],
  proof: &[u8],
) -> Result<usize, String> {
  let bytes = if entry == IXVM_ENTRY {
    if args.len() != 8 {
      return Err("expected eight digest words".into());
    }
    proof.strip_prefix(IXVM_MAGIC).ok_or("not a formal Aiur proof")?
  } else if RECURSIVE_ENTRIES.contains(&entry) {
    if args.len() != 16 {
      return Err(
        "expected a recursive entrypoint with sixteen public digest words"
          .into(),
      );
    }
    proof
  } else {
    return Err(format!("unknown verification entrypoint `{entry}`"));
  };
  system.verify(entry, args, bytes)
}

pub use crate::system::Identity;

/// The verifying key of a system and how its claims address it: the IxVM
/// claim entry, or the recursive program's first entry.
pub fn identity(system: &System, kind: Kind) -> Result<Identity, String> {
  match kind {
    Kind::Ixvm => system.identity(IXVM_ENTRY, 8),
    Kind::Recursion => system.identity(system.program().first_entry()?, 16),
  }
}

fn decode_proof(bytes: &[u8]) -> Result<BatchProof, String> {
  let proof = BatchProof::from_bytes(bytes).map_err(|e| e.to_string())?;
  if proof.to_bytes().map_err(|e| e.to_string())? != bytes
    || proof.proofs.is_empty()
  {
    return Err("noncanonical, empty or trailing proof bytes".into());
  }
  Ok(proof)
}

/// The number of trace shards of a raw (unprefixed) proof.
pub fn proof_shards(bytes: &[u8]) -> Result<usize, String> {
  Ok(decode_proof(bytes)?.proofs.len())
}

/// One node of a range plan. Leaves cover consecutive shards and carry
/// their proofs; inner nodes join two earlier nodes.
pub struct Range {
  pub lo: usize,
  pub hi: usize,
  pub children: Vec<usize>,
  pub statement: Vec<u8>,
  pub proofs: Vec<u8>,
}

/// Range advice for a raw proof: its preamble and a balanced plan of
/// ranges of at most `size` shards, children before parents. This produces
/// advice, never a verification result; the caller verifies the proof
/// first and the Aiur range circuit checks every statement again.
pub fn ranges(
  bytes: &[u8],
  size: usize,
) -> Result<(Vec<u8>, Vec<Range>), String> {
  use stark_key::range::{
    preamble_bytes, proofs_slice_bytes, range_residual, range_statement,
  };
  if size == 0 {
    return Err("range size must be positive".into());
  }
  let proof = decode_proof(bytes)?;
  let preamble = preamble_bytes(&proof)?;
  let digest = blake3::hash(&preamble);
  let mut nodes = Vec::new();
  let mut layer = Vec::new();
  for lo in (0..proof.proofs.len()).step_by(size) {
    let hi = lo.saturating_add(size).min(proof.proofs.len());
    layer.push((nodes.len(), lo, hi));
    nodes.push(Range {
      lo,
      hi,
      children: Vec::new(),
      statement: Vec::new(),
      proofs: proofs_slice_bytes(&proof, lo, hi)?,
    });
  }
  while layer.len() > 1 {
    let mut next = Vec::new();
    for pair in layer.chunks(2) {
      let [(left, lo, _), (right, _, hi)] = pair else {
        next.push(pair[0]);
        continue;
      };
      next.push((nodes.len(), *lo, *hi));
      nodes.push(Range {
        lo: *lo,
        hi: *hi,
        children: vec![*left, *right],
        statement: Vec::new(),
        proofs: Vec::new(),
      });
    }
    layer = next;
  }
  for node in &mut nodes {
    if proof.proofs[node.lo..node.hi]
      .iter()
      .any(|p| p.intermediate_accumulators.is_empty())
    {
      return Err("range contains a shard without accumulators".into());
    }
    node.statement = range_statement(
      digest.as_bytes(),
      node.lo,
      node.hi,
      range_residual(&proof, node.lo, node.hi),
    );
  }
  Ok((preamble, nodes))
}

fn bind_error(failure: PrepFailure) -> String {
  match failure {
    PrepFailure::Other(error) => error,
    PrepFailure::Resource(error) => error.to_string(),
  }
}

/// Execute an IxVM claim on the system's program without proving it.
/// Returns the job status (0) and a report with the record's circuit
/// statistics; a rejected claim is an error.
pub fn execute(system: &System, request: &Request) -> Result<Outcome, String> {
  let program = system.program();
  let start = Instant::now();
  let bound =
    crate::request::bind(program.checked(), Kind::Ixvm, request, &Uncharged)
      .map_err(bind_error)?;
  let (result, ran) = run(program, &bound)?;
  if !result.output.is_empty() {
    return Err("claim verifier returned a value".into());
  }
  let seconds = start.elapsed().as_secs_f64();
  println!(
    "verified claim in {seconds:.3}s ({} queries, {} instructions)",
    result.queries.len(),
    result.instructions
  );
  let mut report = json!({"execution_seconds":seconds, "queries":result.queries.len(),
    "instructions":result.instructions, "executor":ran,
    "execution_statistics":system.verifier().execution_statistics(&result)});
  for (key, value) in bound.report {
    report[key] = value;
  }
  Ok(Outcome { status: 0, plan: None, report })
}

/// Execute an IxVM claim and plan its proof within the RAM budget, without
/// proving. Returns the job status (0, or 75 when the fixed tables alone
/// exceed the budget) and a report; a rejected claim is an error.
pub fn plan(
  system: &System,
  request: &Request,
  options: &planning::Options,
) -> Result<Outcome, String> {
  options.validate()?;
  let program = system.program();
  ixvm::register_compiled_trace();
  let backend = system.prover(options.device)?;
  // The resident program, system and proving setup all count against the
  // budget's static floor.
  let static_resident = planning::resident_memory();
  let fixed = backend.plan_fixed(options, static_resident)?;
  if !fixed.fits {
    let report = json!({"plan":fixed, "can_split":false, "verified":false,
      "error":"budget is below the estimated artifact and fixed-table floor"});
    println!("{report}");
    return Ok(Outcome {
      status: 0,
      plan: Some(Planned::of(&fixed, false)),
      report,
    });
  }
  let bound =
    crate::request::bind(program.checked(), Kind::Ixvm, request, &Uncharged)
      .map_err(bind_error)?;
  let start = Instant::now();
  let (record, ran) = run(program, &bound)?;
  let execute = start.elapsed().as_secs_f64();
  if !record.output.is_empty() {
    return Err("claim verifier returned a value".into());
  }
  let batch = backend.plan_batch(&record, options)?;
  let mut report = json!({"plan":batch, "execution_seconds":execute,
    "storage":record.storage_usage(),
    "execution_statistics":backend.execution_statistics(&record),
    "execution_statistics":backend.execution_statistics(&record),
    "queries":record.queries.len(), "instructions":record.instructions,
    "executor":ran, "verified":false});
  for (key, value) in bound.report {
    report[key] = value;
  }
  println!("{report}");
  Ok(Outcome { status: 0, plan: Some(Planned::of(&batch, true)), report })
}

/// Prove one IxVM claim with no controller: execute it, plan its proof
/// within `options` (device and RAM budget), prove it on `threads` threads
/// (0: the current pool) and write the proof next to `output`. Returns the
/// status (0, or 75 when no trace-shard plan fits) and a report; a rejected
/// claim is an error.
pub fn prove(
  system: &System,
  request: &Request,
  options: &planning::Options,
  output: &Path,
  threads: usize,
) -> Result<Outcome, String> {
  options.validate()?;
  let program = system.program();
  ixvm::register_compiled_trace();
  let backend = system.prover(options.device)?;
  let bound =
    crate::request::bind(program.checked(), Kind::Ixvm, request, &Uncharged)
      .map_err(bind_error)?;
  let start = Instant::now();
  let (record, ran) = run(program, &bound)?;
  if !record.output.is_empty() {
    return Err("claim verifier returned a value".into());
  }
  let mut report = json!({"execution_seconds":start.elapsed().as_secs_f64(),
    "executor":ran, "instructions":record.instructions,
    "execution_statistics":backend.execution_statistics(&record),
    "parameters":backend.parameters(),
    "conjectured_security_bits":backend.parameters().conjectured_bits(),
    "execution_statistics":backend.execution_statistics(&record),
    "parameters":backend.parameters(),
    "conjectured_security_bits":backend.parameters().conjectured_bits(),
    "queries":record.queries.len(), "verified":false});
  for (key, value) in &bound.report {
    report[key] = value.clone();
  }
  let batch = backend.plan_batch(&record, options)?;
  report["plan"] = serde_json::to_value(&batch).map_err(|e| e.to_string())?;
  let planned = Planned::of(&batch, true);
  if !batch.fits {
    report["can_split"] = true.into();
    crate::output::report(output, Kind::Ixvm, &report)?;
    return Ok(Outcome { status: 75, plan: Some(planned), report });
  }
  let layout = batch
    .layout
    .as_ref()
    .ok_or("the proving plan has no incremental layout")?;
  let prove = || {
    backend.prove_incremental_timed(
      &record,
      &bound.entry,
      &bound.args,
      &[],
      layout,
      batch.retention(),
      batch.pipelined,
    )
  };
  let run = if threads == 0 {
    prove()?
  } else {
    rayon::ThreadPoolBuilder::new()
      .num_threads(threads)
      .build()
      .map_err(|e| e.to_string())?
      .install(prove)?
  };
  report["trace_seconds"] = run.trace_seconds.into();
  report["proving_seconds"] = run.proving_seconds.into();
  let report = crate::output::proof(
    output,
    false,
    Kind::Ixvm,
    system.verifier(),
    &bound.entry,
    &bound.args,
    &run.proof,
    report,
  )?;
  Ok(Outcome { status: 0, plan: Some(planned), report })
}

/// Execute on the executor selected for this program: its
/// native kernel when one is linked for exactly this program and binds,
/// otherwise the interpreter. A stateless check has no record budget.
fn run(
  program: &Program,
  bound: &crate::request::Bound<'_>,
) -> Result<(aiur::Execution<crate::Field>, &'static str), String> {
  let executor = program.executor();
  let pool = record_pool::RecordPool::new(usize::MAX / 2, 16 << 20);
  let reservation = pool
    .try_admit()
    .map_err(|e| e.to_string())?
    .ok_or("record pool refused admission")?;
  let (record, ran) = executor.execute(
    &bound.hints,
    &bound.entry,
    bound.args.clone(),
    &reservation,
  );
  Ok((record.map_err(|e| e.to_string())?, ran))
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn malformed_inputs_are_errors() {
    assert!(proof_shards(&[]).is_err());
    assert!(ranges(&[1, 2, 3], 1).is_err());
    assert!(ranges(&[], 0).is_err());
  }
}
