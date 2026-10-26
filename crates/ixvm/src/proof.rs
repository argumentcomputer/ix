//! Production claim driver. The trusted artifact is separate from witness and
//! proof inputs. No legacy executor or generated kernels are linked here.
use aiur::{
  field::FieldBackend,
  library::io::Invocation,
  trace::{
    TraceArtifact, TracePlan,
    stark::{Backend, BatchProof, Parameters, VerifyingKey, planning::Options},
  },
};
use multi_stark::{p3_field::PrimeField64, types::Val};
use std::{error::Error, time::Instant};

const MAGIC: &[u8] = b"IXAIUR2\0";
#[derive(serde::Deserialize)]
struct Package {
  program: aiur::Program,
  trace: Option<TraceArtifact>,
}

#[derive(serde::Deserialize)]
struct Case {
  label: String,
  accept: bool,
  invocation: Invocation,
}

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
    return Err("usage: ixvm-proof execute|plan|prove|verify ARTIFACT INPUT [PROOF] [SHARD_ROWS] [RETENTION] [OPTIONS.json]".into());
  }
  let mode = cli[1].as_str();
  if !["execute", "plan", "prove", "verify", "test", "key"].contains(&mode) {
    return Err("unknown mode".into());
  }
  let package: Package = aiur::decode_artifact(&std::fs::read(&cli[2])?)?;
  let program = package.program.check_field::<Val>()?;
  let artifact_resident = aiur::trace::stark::planning::resident_memory();
  if mode == "key" {
    let plan = TracePlan::new(
      &program,
      package.trace.ok_or("artifact has no circuits")?,
    )?;
    let backend = Backend::for_batch(&plan, Parameters::default())?;
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
        "call_channel":claim[0].as_canonical_u64(), "key_digest":blake3::hash(&key).to_hex().to_string()}),
    )?;
    return Ok(());
  }
  if mode == "test" {
    let cases: Vec<Case> = serde_json::from_slice(&std::fs::read(&cli[3])?)?;
    for case in cases {
      let args = program.field().decode(&case.invocation.args)?;
      let result = ixvm::prepare_streams(&program, &case.invocation.streams)?
        .execute(&case.invocation.entry, args);
      if result.is_ok() != case.accept {
        return Err(
          format!("{}: unexpected result: {:?}", case.label, result.err())
            .into(),
        );
      }
      println!(
        "{}: {}",
        case.label,
        if case.accept { "accepted" } else { "rejected" }
      );
    }
    return Ok(());
  }
  let input: Invocation = serde_json::from_slice(&std::fs::read(&cli[3])?)?;
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
    println!(
      "verified claim in {:.3}s ({} queries, {} instructions)",
      start.elapsed().as_secs_f64(),
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
  let backend =
    Backend::for_batch_on_device(&plan, Parameters::default(), options.device)?;
  if mode == "verify" {
    let bytes = std::fs::read(path)?;
    let bytes = bytes.strip_prefix(MAGIC).ok_or("not a formal Aiur proof")?;
    let proof = BatchProof::from_bytes(bytes)?;
    if proof.to_bytes()? != bytes {
      return Err("noncanonical or trailing proof bytes".into());
    }
    backend.verify_batch(&input.entry, &args, &[], &proof)?;
    println!(
      "verified formal Aiur proof ({} trace shards)",
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
  let mut report = serde_json::json!({"plan":batch, "execution_seconds":execute,
    "queries":record.queries.len(), "instructions":record.instructions,
    "circuits":backend.statistics(), "verified":false});
  let report_path = format!("{path}.report.json");
  std::fs::write(&report_path, serde_json::to_vec_pretty(&report)?)?;
  if mode == "plan" {
    report.as_object_mut().unwrap().remove("circuits");
    println!("{}", report);
    return Ok(());
  }
  if !batch.fits {
    eprintln!("proving estimate exceeds budget; see {report_path}");
    std::process::exit(75);
  }
  let start = Instant::now();
  let witness = backend.generate_stage_1(&record, &input.entry, &args)?;
  if witness.iter().map(|m| m.values.len() as u64).sum::<u64>()
    != batch.stage1_cells
  {
    return Err("generated trace differs from the resource plan".into());
  }
  let trace = start.elapsed().as_secs_f64();
  drop(record);
  drop(hints);
  let start = Instant::now();
  let proof = backend.prove_batch_stage_1(
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
  report.as_object_mut().unwrap().remove("circuits");
  println!("{}", report);
  Ok(())
}
