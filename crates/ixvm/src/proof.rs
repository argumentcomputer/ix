//! Production claim driver. The trusted artifact is separate from witness and
//! proof inputs. No legacy executor or generated kernels are linked here.
use aiur::{
  artifact::{Package, load_cases},
  field::FieldBackend,
  library::io::Invocation,
  trace::{
    TracePlan,
    stark::{Backend, BatchProof, Parameters, VerifyingKey, planning::Options},
  },
};
use multi_stark::{p3_field::PrimeField64, types::Val};
use std::{error::Error, time::Instant};

const MAGIC: &[u8] = b"IXAIUR2\0";

fn main() -> Result<(), Box<dyn Error>> {
  let cli: Vec<_> = std::env::args().collect();
  if cli.get(1).is_some_and(|s| s == "resources") {
    println!(
      "{}",
      serde_json::json!({"available_bytes":aiur::trace::stark::planning::available_memory(),
      "cores":std::thread::available_parallelism().map_or(1, usize::from)})
    );
    return Ok(());
  }
  if cli.len() < 4 {
    return Err("usage: ixvm-proof execute|plan|prove|verify ARTIFACT INPUT.ixi [PROOF] [SHARD_ROWS] [RETENTION] [OPTIONS.json]".into());
  }
  let mode = cli[1].as_str();
  if !["execute", "plan", "prove", "verify", "test", "key"].contains(&mode) {
    return Err("unknown mode".into());
  }
  let (package, artifact) = Package::load(cli[2].as_ref())?;
  eprintln!("artifact {}: blake3 {artifact}", cli[2]);
  let mut program = package.program.check_field::<Val>()?;
  if let Some(trace) = &package.trace {
    program.track_depth(trace)?;
  }
  let artifact_resident = aiur::trace::stark::planning::resident_memory();
  if mode == "key" {
    let plan = TracePlan::new(
      &program,
      package.trace.ok_or("artifact has no circuits")?,
    )?;
    let backend =
      Backend::for_batch_verification(&plan, Parameters::default())?;
    let key = backend.verifying_key_bytes()?;
    let claim = backend.claim(
      "IxVM::verify_claim",
      &program.field().decode(&[0; 8])?,
      &[],
    )?;
    let dir = std::path::Path::new(&cli[3]);
    std::fs::create_dir_all(dir)?;
    std::fs::write(dir.join("key.bin"), &key)?;
    serde_json::to_writer(
      std::fs::File::create(dir.join("identity.json"))?,
      &serde_json::json!({"function_index":claim[1].as_canonical_u64(),
        "call_channel":claim[0].as_canonical_u64(), "key_digest":blake3::hash(&key).to_hex().to_string(),
        "artifact_digest":artifact.to_string()}),
    )?;
    return Ok(());
  }
  if mode == "test" {
    // Every case runs, so that one report names every unexpected verdict.
    let cases = load_cases(cli[3].as_ref())?;
    let stats_path =
      match &cli[4..] {
        [] => None,
        [flag, path] if flag == "--stats-out" => Some(path),
        _ => return Err(
          "usage: ixvm-proof test ARTIFACT CASES.ixt [--stats-out STATS.json]"
            .into(),
        ),
      };
    let plan = if stats_path.is_some() {
      Some(TracePlan::new(
        &program,
        package.trace.ok_or("statistics require an artifact with circuits")?,
      )?)
    } else {
      None
    };
    let backend = plan
      .as_ref()
      .map(|plan| Backend::for_batch_verification(plan, Parameters::default()))
      .transpose()?;
    let mut statistics = serde_json::Map::new();
    let mut failed = Vec::new();
    for case in cases {
      let args = program.field().decode(&case.invocation.args)?;
      let start = Instant::now();
      let result = ixvm::prepare_streams(&program, &case.invocation.streams)?
        .execute(&case.invocation.entry, args);
      let seconds = start.elapsed().as_secs_f64();
      if let (Some(backend), Ok(record)) = (&backend, &result)
        && statistics
          .insert(
            case.label.clone(),
            serde_json::to_value(backend.execution_statistics(record))?,
          )
          .is_some()
      {
        return Err(format!("duplicate case label: {}", case.label).into());
      }
      let error = result.as_ref().err().map(ToString::to_string);
      let reached = match (&result, &case.exercises) {
        (Ok(record), Some(name)) => record.queries.keys().any(|query| {
          program.callable_name(query.function) == Some(name.as_str())
        }),
        _ => true,
      };
      // A witness that lacks data the program asks for stops execution before
      // the logic under test: that is not a verdict unless the case names it.
      let expected = match (&error, case.accept, &case.rejects_with) {
        (None, accept, _) => accept && reached,
        (Some(_), true, _) => false,
        (Some(e), false, Some(reason)) => e.contains(reason.as_str()),
        (Some(e), false, None) => !e.contains("missing hint"),
      };
      let verdict = match &error {
        None => "accepted".to_owned(),
        Some(e) => format!("rejected: {e}"),
      };
      if expected {
        println!("{}: {verdict} ({seconds:.3}s)", case.label);
      } else {
        let wanted = match (case.accept, &case.rejects_with) {
          (true, _) if !reached => format!(
            "an acceptance calling {}",
            case.exercises.as_deref().unwrap_or_default()
          ),
          (true, _) => "acceptance".to_owned(),
          (false, Some(reason)) => format!("a rejection containing {reason:?}"),
          (false, None) => "a rejection by the program".to_owned(),
        };
        println!("FAILED {}: {verdict}; expected {wanted}", case.label);
        failed.push(case.label);
      }
    }
    if let Some(path) = stats_path {
      serde_json::to_writer(std::fs::File::create(path)?, &statistics)?;
    }
    if !failed.is_empty() {
      return Err(
        format!("{} unexpected verdicts: {}", failed.len(), failed.join("; "))
          .into(),
      );
    }
    return Ok(());
  }
  let input = Invocation::load(cli[3].as_ref())?;
  let args = program.field().decode(&input.args)?;
  // A production claim has precisely eight public digest words and no result.
  if input.entry != "IxVM::verify_claim" || args.len() != 8 {
    return Err("expected IxVM::verify_claim and eight digest words".into());
  }
  if mode == "execute" {
    let start = Instant::now();
    let result = ixvm::prepare_streams(&program, &input.streams)?
      .execute(&input.entry, args)?;
    if !result.output.is_empty() {
      return Err("claim verifier returned a value".into());
    }
    let seconds = start.elapsed().as_secs_f64();
    if let Some(path) = cli.get(4) {
      let plan = TracePlan::new(
        &program,
        package.trace.ok_or("statistics require an artifact with circuits")?,
      )?;
      let backend =
        Backend::for_batch_verification(&plan, Parameters::default())?;
      let report = serde_json::json!({"execution_statistics": backend.execution_statistics(&result), "execution_seconds": seconds});
      serde_json::to_writer(
        std::fs::File::create(format!("{path}.report.json"))?,
        &report,
      )?;
    }
    println!(
      "verified claim in {:.3}s ({} queries, {} instructions)",
      seconds,
      result.queries.len(),
      result.instructions
    );
    return Ok(());
  }
  let path = cli.get(4).ok_or("missing proof path")?;
  let options = Options::read(cli.get(7), cli.get(5), cli.get(6))?;
  let before_setup = aiur::trace::stark::planning::resident_memory();
  let plan =
    TracePlan::new(&program, package.trace.ok_or("artifact has no circuits")?)?;
  let backend = if mode == "verify" {
    Backend::for_batch_verification(&plan, Parameters::default())?
  } else {
    Backend::for_batch_on_device(&plan, Parameters::default(), options.device)?
  };
  if mode == "verify" {
    let bytes = std::fs::read(path)?;
    let bytes = bytes.strip_prefix(MAGIC).ok_or("not a formal Aiur proof")?;
    let proof = BatchProof::from_bytes(bytes)?;
    if proof.to_bytes()? != bytes {
      return Err("noncanonical or trailing proof bytes".into());
    }
    backend.verify_batch(&input.entry, &args, &[], &proof)?;
    println!(
      "verified formal Aiur proof ({} trace shards, artifact {artifact})",
      proof.proofs.len()
    );
    return Ok(());
  }
  let static_resident = artifact_resident.saturating_add(
    aiur::trace::stark::planning::resident_memory()
      .saturating_sub(before_setup),
  );
  let fixed = backend.plan_fixed(&options, static_resident)?;
  if !fixed.fits {
    let report = serde_json::json!({"plan":fixed, "can_split":false, "verified":false,
      "error":"budget is below the estimated artifact and fixed-table floor"});
    std::fs::write(
      format!("{path}.report.json"),
      serde_json::to_vec_pretty(&report)?,
    )?;
    println!("{report}");
    if mode == "plan" {
      return Ok(());
    }
    std::process::exit(75);
  }
  let hints = ixvm::prepare_streams(&program, &input.streams)?;
  drop(input.streams);
  let start = Instant::now();
  let record = hints.execute(&input.entry, args.clone())?;
  let execute = start.elapsed().as_secs_f64();
  if !record.output.is_empty() {
    return Err("claim verifier returned a value".into());
  }
  let batch = backend.plan_batch(&record, &options)?;
  let mut report = serde_json::json!({"plan":batch, "artifact_digest":artifact.to_string(), "execution_seconds":execute,
    "queries":record.queries.len(), "instructions":record.instructions,
    "execution_statistics":backend.execution_statistics(&record), "parameters":backend.parameters(),
    "conjectured_security_bits":backend.parameters().conjectured_bits(),
    "verified":false});
  let report_path = format!("{path}.report.json");
  std::fs::write(&report_path, serde_json::to_vec_pretty(&report)?)?;
  if mode == "plan" {
    report.as_object_mut().unwrap().remove("execution_statistics");
    println!("{}", report);
    return Ok(());
  }
  if !batch.fits {
    eprintln!("proving estimate exceeds budget; see {report_path}");
    std::process::exit(75);
  }
  let start = Instant::now();
  let witness = backend.prepare_stage_1(&record, &input.entry, &args)?;
  if witness.cells() != batch.stage1_cells {
    return Err("generated trace differs from the resource plan".into());
  }
  let trace = start.elapsed().as_secs_f64();
  drop(record);
  drop(hints);
  let start = Instant::now();
  let proof = backend.prove_stage_one(
    &input.entry,
    &args,
    &[],
    witness,
    batch.max_rows,
    batch.retention(),
  )?;
  let proving = start.elapsed().as_secs_f64();
  let raw = proof.to_bytes()?;
  let mut bytes = MAGIC.to_vec();
  bytes.extend(&raw);
  let key = backend.verifying_key_bytes()?;
  let claim = backend.claim(&input.entry, &args, &[])?;
  VerifyingKey::from_bytes(&key)?
    .verify(std::slice::from_ref(&claim), &proof)?;
  std::fs::write(path, bytes)?;
  // Sidecars make the proof immediately consumable by the recursive verifier.
  std::fs::write(format!("{path}.vk"), &key)?;
  let mut claims = 1u64.to_le_bytes().to_vec();
  claims.extend_from_slice(&(claim.len() as u64).to_le_bytes());
  for v in claim {
    claims.extend_from_slice(&v.as_canonical_u64().to_le_bytes());
  }
  std::fs::write(format!("{path}.claims"), claims)?;
  report["verified"] = true.into();
  report["trace_seconds"] = trace.into();
  report["proving_seconds"] = proving.into();
  report["shards"] = proof.proofs.len().into();
  report["proof_bytes"] = raw.len().into();
  report["key_digest"] = blake3::hash(&key).to_hex().to_string().into();
  std::fs::write(report_path, serde_json::to_vec_pretty(&report)?)?;
  report.as_object_mut().unwrap().remove("execution_statistics");
  println!("{}", report);
  Ok(())
}
