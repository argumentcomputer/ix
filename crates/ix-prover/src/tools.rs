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

/// The default host budget in bytes ([`planning::default_budget`]), when
/// known, logical cores, and GPUs ([`planning::gpu_count`]).
pub fn resources() -> (Option<u64>, usize, usize) {
  (
    planning::default_budget(),
    std::thread::available_parallelism().map_or(1, usize::from),
    planning::gpu_count(),
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
  // The span also closes when binding or execution fails, so a rejected
  // claim still records its time; a check that fails before reaching this
  // call records no `aiur/execute` span at all.
  let (bound, (result, ran)) = tracing_texray::examine(tracing::info_span!(
    "aiur/execute"
  ))
  .in_scope(|| -> Result<_, String> {
    let bound =
      crate::request::bind(program.checked(), Kind::Ixvm, request, &Uncharged)
        .map_err(bind_error)?;
    let ran = run(program, &bound)?;
    Ok((bound, ran))
  })?;
  if !result.output.is_empty() {
    return Err("claim verifier returned a value".into());
  }
  let seconds = start.elapsed().as_secs_f64();
  println!(
    "verified claim in {seconds:.3}s ({} queries, {} instructions)",
    result.queries.len(),
    result.instructions
  );
  if let Some(path) = std::env::var_os("IX_KERNEL_HINTS_TRACE") {
    kernel_hints_trace(program, &result, Path::new(&path))?;
  }
  if let Some(path) = std::env::var_os("IX_KERNEL_ROWS_PROFILE") {
    kernel_rows_profile(program, &result, Path::new(&path))?;
  }
  let mut report = json!({"execution_seconds":seconds, "queries":result.queries.len(),
    "instructions":result.instructions, "executor":ran,
    "execution_statistics":system.verifier().execution_statistics(&result)});
  for (key, value) in bound.report {
    report[key] = value;
  }
  Ok(Outcome { status: 0, plan: None, report })
}

/// Append one JSON line describing an accepted IxVM execution to `path`:
/// the rows (distinct queries) and uses (summed multiplicities) of every
/// function that ran, every `lazy_delta_step_const_const` row as its two
/// head addresses with its fuel, success flag and uses, and the addresses
/// whose reducibility hint the claim loaded. A row is one memoized call, so
/// a function's rows are its share of the trace before padding.
///
/// `lazy_delta_step_const_const(rc, a_addr, b_addr, a, b, fuel, types)` and
/// `load_constant_hint(addr)` take only pointers and fields, so their
/// arguments are positional; an address argument points at a 32-byte cell.
fn kernel_hints_trace(
  program: &Program,
  record: &aiur::Execution<crate::Field>,
  path: &Path,
) -> Result<(), String> {
  use multi_stark::p3_field::PrimeField64;
  use std::io::Write;
  let checked = program.checked();
  let address = |ptr: &crate::Val| -> String {
    let ptr = ptr.as_canonical_u64() as usize;
    match record.memory.get_by_width(32, ptr) {
      Some(entry) => entry
        .cell
        .value
        .iter()
        .map(|b| format!("{:02x}", b.as_canonical_u64()))
        .collect(),
      None => format!("?{ptr}"),
    }
  };
  let mut functions: std::collections::BTreeMap<String, (u64, u64)> =
    std::collections::BTreeMap::new();
  let mut steps = Vec::new();
  let mut hint_loads = Vec::new();
  for (key, output) in record.queries.iter() {
    let name = checked.callable_name(key.function).unwrap_or("?");
    let entry = functions.entry(name.to_string()).or_default();
    entry.0 += 1;
    entry.1 += output.multiplicity;
    let args = &key.args;
    if name.ends_with("lazy_delta_step_const_const") && args.len() == 7 {
      steps.push(json!([
        address(&args[1]),
        address(&args[2]),
        args[5].as_canonical_u64(),
        output.output.first().map(PrimeField64::as_canonical_u64),
        output.multiplicity
      ]));
    } else if name.ends_with("load_constant_hint") && args.len() == 1 {
      hint_loads.push(address(&args[0]));
    }
  }
  let line = json!({"queries": record.queries.len(),
    "instructions": record.instructions, "functions": functions,
    "steps": steps, "hint_loads": hint_loads});
  let mut file = std::fs::OpenOptions::new()
    .create(true)
    .append(true)
    .open(path)
    .map_err(|e| format!("cannot open {}: {e}", path.display()))?;
  writeln!(file, "{line}").map_err(|e| e.to_string())
}

/// Append one JSON line profiling the arguments of the functions whose names
/// contain one of the comma-separated patterns in `IX_KERNEL_ROWS_PROFILE_FNS`
/// (default: the `KernelSubst` module). For each such function and each
/// flattened argument position: the number of distinct values, the rows that
/// would remain if that position were ignored, and the most frequent values.
/// The outputs' most frequent first elements are reported the same way.
/// Arguments are positional field elements; a pointer is one element.
fn kernel_rows_profile(
  program: &Program,
  record: &aiur::Execution<crate::Field>,
  path: &Path,
) -> Result<(), String> {
  use multi_stark::p3_field::PrimeField64;
  use std::collections::{BTreeMap, HashMap, HashSet};
  use std::io::Write;
  let patterns: Vec<String> = std::env::var("IX_KERNEL_ROWS_PROFILE_FNS")
    .unwrap_or_else(|_| "KernelSubst::".into())
    .split(',')
    .map(str::to_string)
    .collect();
  let checked = program.checked();
  type Rows = Vec<(Vec<u64>, Option<u64>, u64)>;
  let mut by_fn: BTreeMap<String, Rows> = BTreeMap::new();
  for (key, output) in record.queries.iter() {
    let name = checked.callable_name(key.function).unwrap_or("?");
    if !patterns.iter().any(|p| name.contains(p.as_str())) {
      continue;
    }
    let args = key.args.iter().map(PrimeField64::as_canonical_u64).collect();
    let out = output.output.first().map(PrimeField64::as_canonical_u64);
    by_fn
      .entry(name.to_string())
      .or_default()
      .push((args, out, output.multiplicity));
  }
  let top = |counts: HashMap<u64, u64>| -> Value {
    let mut v: Vec<(u64, u64)> = counts.into_iter().collect();
    v.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
    v.truncate(24);
    json!(v)
  };
  let mut fns = serde_json::Map::new();
  for (name, rows) in by_fn {
    let arity = rows.first().map_or(0, |r| r.0.len());
    let mut positions = Vec::new();
    for i in 0..arity {
      let mut counts: HashMap<u64, u64> = HashMap::new();
      let mut without: HashSet<Vec<u64>> = HashSet::new();
      for (args, _, _) in &rows {
        *counts.entry(args[i]).or_default() += 1;
        let mut rest = args.clone();
        rest.remove(i);
        without.insert(rest);
      }
      let distinct = counts.len();
      positions.push(json!({"distinct": distinct, "rows_without": without.len(),
        "top": if distinct <= 100_000 { top(counts) } else { Value::Null }}));
    }
    let mut outs: HashMap<u64, u64> = HashMap::new();
    let mut uses = 0;
    for (_, out, m) in &rows {
      *outs.entry(out.unwrap_or(u64::MAX)).or_default() += 1;
      uses += m;
    }
    let distinct_out = outs.len();
    fns.insert(name, json!({"rows": rows.len(), "uses": uses, "args": positions,
      "out_distinct": distinct_out,
      "out_top": if distinct_out <= 100_000 { top(outs) } else { Value::Null }}));
  }
  let line = json!({"queries": record.queries.len(), "functions": fns});
  let mut file = std::fs::OpenOptions::new()
    .create(true)
    .append(true)
    .open(path)
    .map_err(|e| format!("cannot open {}: {e}", path.display()))?;
  writeln!(file, "{line}").map_err(|e| e.to_string())
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
  #[cfg(feature = "cuda")]
  if std::env::var_os("AIUR_SHARD_IMAGE_REPORT").is_some() {
    let layout = batch.layout.as_ref().ok_or("plan has no shard layout")?;
    eprintln!(
      "[aiur] shard images {}",
      backend.shard_image_report(&record, layout)?
    );
  }
  let mut report = json!({"plan":batch, "execution_seconds":execute,
    "storage":record.storage_usage(),
    "execution_statistics":backend.execution_statistics(&record),
    "execution_statistics":backend.execution_statistics(&record),
    "queries":record.queries.len(), "instructions":record.instructions,
    "executor":ran, "verified":false});
  for (key, value) in bound.report {
    report[key] = value;
  }
  if let Some(path) = std::env::var_os("AIUR_INDEX_SIZES_OUT") {
    std::fs::write(path, record.index_sizes())
      .map_err(|e| format!("cannot write index sizes: {e}"))?;
  }
  if std::env::var_os("AIUR_RECORD_DIGEST").is_some() {
    report["record_digest"] =
      aiur::native::record_digest(&record).to_string().into();
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
