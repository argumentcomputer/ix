//! Stateless prover operations: proof verification, verifying-key identity,
//! execution-only checks and plans, and recursive range advice. Each call
//! loads and checks its artifact.
use crate::{
  PrepFailure, load_package,
  protocol::{Kind, Request},
  request::{IXVM_ENTRY, RECURSIVE_ENTRIES, Uncharged},
};
use aiur::{
  field::FieldBackend,
  trace::{
    TracePlan,
    stark::{Backend, BatchProof, Parameters, planning},
  },
};
use multi_stark::{
  p3_field::{PrimeCharacteristicRing, PrimeField64},
  types::Val,
};
use serde_json::{Value, json};
use std::{path::Path, time::Instant};

/// The prefix of a formal IxVM proof as stored in an `Ixon.Proof`.
pub const IXVM_MAGIC: &[u8] = b"IXAIUR2\0";

/// Available host memory and logical cores.
pub fn resources() -> Value {
  json!({"available_bytes":planning::available_memory(),
    "cores":std::thread::available_parallelism().map_or(1, usize::from)})
}

/// Verify `proof` of `entry(args)` against the artifact's circuits on the
/// CPU. An IxVM proof carries [`IXVM_MAGIC`]; a recursive proof is raw.
/// Returns the number of trace shards.
pub fn verify(
  artifact: &Path,
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
  let package = load_package(artifact)?;
  let program = package.program.check_field::<Val>()?;
  let plan = TracePlan::new(&program, package.trace)?;
  let backend = Backend::for_batch_verification(&plan, Parameters::default())?;
  let args = program.field().decode(args)?;
  let proof = BatchProof::from_bytes(bytes).map_err(|e| e.to_string())?;
  if proof.to_bytes().map_err(|e| e.to_string())? != bytes {
    return Err("noncanonical or trailing proof bytes".into());
  }
  backend.verify_batch(entry, &args, &[], &proof)?;
  Ok(proof.proofs.len())
}

/// The verifying key of an artifact and how its claims address it.
pub struct Identity {
  pub key: Vec<u8>,
  pub function_index: u64,
  pub call_channel: u64,
}

pub fn identity(artifact: &Path, kind: Kind) -> Result<Identity, String> {
  let package = load_package(artifact)?;
  let program = package.program.check_field::<Val>()?;
  let plan = TracePlan::new(&program, package.trace)?;
  let backend = Backend::for_batch_verification(&plan, Parameters::default())?;
  let claim = match kind {
    Kind::Ixvm => backend.claim(IXVM_ENTRY, &[Val::ZERO; 8], &[])?,
    Kind::Recursion => {
      let entry = &program
        .program()
        .entries
        .first()
        .ok_or("artifact has no entrypoint")?
        .name;
      backend.claim(entry, &[Val::ZERO; 16], &[])?
    },
  };
  let [call_channel, function_index, ..] = claim[..] else {
    return Err("claim lacks its call namespace".into());
  };
  Ok(Identity {
    key: backend.verifying_key_bytes()?,
    function_index: function_index.as_canonical_u64(),
    call_channel: call_channel.as_canonical_u64(),
  })
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

/// The fixed shape a one-shard recursive root normalizes to: one log2
/// height per circuit in system order, `(memory width, circuit index)` for
/// each memory circuit the root's preamble closes, and the claim length.
pub struct FixedShape {
  pub log_heights: Vec<u8>,
  pub memory_traces: Vec<(usize, usize)>,
  pub claim_len: usize,
}

/// The fixed shape of one more wrap of `proof`, a raw one-shard proof of
/// the recursive artifact. A wrap of a one-shard root verifies the same
/// kind of proof the root itself verified, so the root's heights, raised by
/// `headroom` doublings, size it. Fixed tables keep their heights; circuits
/// the root leaves inactive get two rows. The normalizing prover rejects a
/// wrap that does not fit.
pub fn fixed_root_shape(
  artifact: &Path,
  proof: &[u8],
  headroom: u8,
) -> Result<FixedShape, String> {
  let proof = decode_proof(proof)?;
  let [header] = proof.preamble.headers.as_slice() else {
    return Err(
      "normalize a root of exactly one trace shard; `ix aggregate --wrap-root` \
       wraps a root until it has one"
        .into(),
    );
  };
  let [claim] = header.claims.as_slice() else {
    return Err("the root shard carries no single claim".into());
  };
  let package = load_package(artifact)?;
  let program = package.program.check_field::<Val>()?;
  let plan = TracePlan::new(&program, package.trace)?;
  let backend = Backend::for_batch_verification(&plan, Parameters::default())?;
  let key = aiur::trace::stark::VerifyingKey::from_bytes(
    &backend.verifying_key_bytes()?,
  )?;
  let circuits = &key.system().circuits;
  if header.active.len() != circuits.len() {
    return Err("the root belongs to another artifact".into());
  }
  let mut degrees = header.log_degrees.iter();
  let mut log_heights = Vec::with_capacity(circuits.len());
  for (ci, (circuit, &active)) in
    circuits.iter().zip(&header.active).enumerate()
  {
    let root = if active {
      Some(*degrees.next().ok_or("missing trace height")?)
    } else {
      None
    };
    let log = if backend.is_fixed_table(ci) {
      u8::try_from(circuit.preprocessed_height.ilog2())
        .map_err(|e| e.to_string())?
    } else {
      root.map_or(1, |log| log.saturating_add(headroom).max(1))
    };
    log_heights.push(log);
  }
  let closed: std::collections::BTreeSet<u64> = proof
    .preamble
    .messages
    .iter()
    .step_by(2)
    .filter_map(|m| m.args.get(1).map(PrimeField64::as_canonical_u64))
    .collect();
  let memory_traces = backend
    .memory_circuits()
    .into_iter()
    .filter(|&(width, _)| closed.contains(&(width as u64)))
    .collect::<Vec<_>>();
  if memory_traces.len() != closed.len() {
    return Err("the root closes memory no circuit holds".into());
  }
  Ok(FixedShape { log_heights, memory_traces, claim_len: claim.len() })
}

/// What [`check`] does after executing the claim.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Check {
  /// Execute only.
  Execute,
  /// Also plan the proof within the RAM budget.
  Plan,
}

/// Execute an IxVM claim without proving it. Returns the job status (0, or
/// 75 when [`Check::Plan`] finds that the fixed tables alone exceed the
/// budget) and a report; a rejected claim is an error.
pub fn check(
  mode: Check,
  artifact: &Path,
  request: &Request,
  options: &planning::Options,
) -> Result<(u32, Value), String> {
  let artifact_resident = planning::resident_memory();
  let package = load_package(artifact)?;
  let program = package.program.check_field::<Val>()?;
  let bind = |program| {
    crate::request::bind(program, Kind::Ixvm, request, &Uncharged).map_err(
      |failure| match failure {
        PrepFailure::Other(error) => error,
        PrepFailure::Resource(error) => error.to_string(),
      },
    )
  };
  if mode == Check::Execute {
    let start = Instant::now();
    let bound = bind(&program)?;
    let (result, ran) = run(&program, &bound)?;
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
      "instructions":result.instructions, "executor":ran});
    for (key, value) in bound.report {
      report[key] = value;
    }
    return Ok((0, report));
  }
  options.validate()?;
  let before_setup = planning::resident_memory();
  ixvm::register_compiled_trace();
  let plan = TracePlan::new(&program, package.trace)?;
  let backend =
    Backend::for_batch_on_device(&plan, Parameters::default(), options.device)?;
  let static_resident = artifact_resident
    .saturating_add(planning::resident_memory().saturating_sub(before_setup));
  let fixed = backend.plan_fixed(options, static_resident)?;
  if !fixed.fits {
    let report = json!({"plan":fixed, "can_split":false, "verified":false,
      "error":"budget is below the estimated artifact and fixed-table floor"});
    println!("{report}");
    return Ok((0, report));
  }
  let bound = bind(&program)?;
  let start = Instant::now();
  let (record, ran) = run(&program, &bound)?;
  let execute = start.elapsed().as_secs_f64();
  if !record.output.is_empty() {
    return Err("claim verifier returned a value".into());
  }
  let batch = backend.plan_batch(&record, options)?;
  let mut report = json!({"plan":batch, "execution_seconds":execute,
    "storage":record.storage_usage(),
    "queries":record.queries.len(), "instructions":record.instructions,
    "executor":ran, "verified":false});
  for (key, value) in bound.report {
    report[key] = value;
  }
  println!("{report}");
  Ok((0, report))
}

/// Prove one IxVM claim with no controller: execute it, plan its proof
/// within `options` (device and RAM budget), prove it on `threads` threads
/// (0: the current pool) and write the proof next to `output`. Returns the
/// status (0, or 75 when no trace-shard plan fits) and a report; a rejected
/// claim is an error.
pub fn prove(
  artifact: &Path,
  request: &Request,
  options: &planning::Options,
  output: &Path,
  threads: usize,
) -> Result<(u32, Value), String> {
  options.validate()?;
  let package = load_package(artifact)?;
  let program = package.program.check_field::<Val>()?;
  ixvm::register_compiled_trace();
  let plan = TracePlan::new(&program, package.trace)?;
  let backend =
    Backend::for_batch_on_device(&plan, Parameters::default(), options.device)?;
  let bound = crate::request::bind(&program, Kind::Ixvm, request, &Uncharged)
    .map_err(|failure| match failure {
    PrepFailure::Other(error) => error,
    PrepFailure::Resource(error) => error.to_string(),
  })?;
  let start = Instant::now();
  let (record, ran) = run(&program, &bound)?;
  if !record.output.is_empty() {
    return Err("claim verifier returned a value".into());
  }
  let mut report = json!({"execution_seconds":start.elapsed().as_secs_f64(),
    "executor":ran, "instructions":record.instructions,
    "queries":record.queries.len(), "verified":false});
  for (key, value) in &bound.report {
    report[key] = value.clone();
  }
  let batch = backend.plan_batch(&record, options)?;
  report["plan"] = serde_json::to_value(&batch).map_err(|e| e.to_string())?;
  if !batch.fits {
    report["can_split"] = true.into();
    crate::output::report(output, Kind::Ixvm, &report)?;
    return Ok((75, report));
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
    &backend,
    &bound.entry,
    &bound.args,
    &run.proof,
    report,
  )?;
  Ok((0, report))
}

/// Execute on the executor selected for this program: its
/// native kernel when one is linked for exactly this program and binds,
/// otherwise the interpreter. A stateless check has no record budget.
fn run(
  program: &crate::Program,
  bound: &crate::request::Bound<'_>,
) -> Result<(aiur::Execution<crate::Field>, &'static str), String> {
  let executor = crate::executor::Executor::select(program)?;
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
    let missing = Path::new("/nonexistent/artifact.json");
    assert!(
      verify(missing, "IxVM::verify_claim", &[0; 8], b"IXAIUR2\0").is_err()
    );
    assert!(
      verify(missing, "IxVM::verify_claim", &[0; 8], b"other").unwrap_err()
        == "not a formal Aiur proof"
    );
    assert!(verify(missing, "Other::entry", &[0; 8], &[]).is_err());
    assert!(
      verify(missing, "MultiStark::ix_aggr", &[0; 8], &[])
        .unwrap_err()
        .contains("sixteen")
    );
  }
}
