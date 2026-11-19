//! Prove an execution package as a single-shard batch root, the input format
//! of the compression wrapper and the L3 ladder.
//!
//! `batch_root PACKAGE.ixa OUT_DIR` writes `root-vk.bin`, `root-claims.bin`,
//! `root-proof.bin` and `report.json` (key digest, circuit heights, timings).
use aiur::field::FieldBackend;
use aiur::{
  artifact::ExecutionPackage,
  trace::{
    TracePlan,
    stark::{Backend, Parameters},
  },
};
use multi_stark::p3_field::PrimeField64;
use serde_json::json;
use std::{error::Error, fs, path::Path, time::Instant};

fn main() -> Result<(), Box<dyn Error>> {
  let args: Vec<_> = std::env::args().collect();
  let (Some(path), Some(out)) = (args.get(1), args.get(2)) else {
    return Err("usage: batch_root PACKAGE.ixa OUT_DIR".into());
  };
  let out = Path::new(out);
  fs::create_dir_all(out)?;
  let start = Instant::now();
  let (package, digest) = ExecutionPackage::load(path.as_ref())?;
  eprintln!("artifact {path}: blake3 {digest}");
  let (program, trace) = package.package.traced()?;
  let mut program = program.check_field::<multi_stark::types::Val>()?;
  program.track_depth(&trace)?;
  let address = program.field().decode(&package.args)?;
  let hints = program.prepare_hints(&package.hints)?;
  let plan = TracePlan::new(&program, trace)?;
  let entry = program
    .program()
    .entries
    .first()
    .ok_or("no selected entrypoint")?
    .name
    .clone();
  let prepare_seconds = start.elapsed().as_secs_f64();

  let start = Instant::now();
  let mut parameters = Parameters::default();
  for (name, field) in [
    ("AIUR_STARK_LOG_BLOWUP", &mut parameters.log_blowup),
    ("AIUR_STARK_QUERIES", &mut parameters.num_queries),
    ("AIUR_STARK_QUERY_POW", &mut parameters.query_proof_of_work_bits),
  ] {
    if let Ok(n) = std::env::var(name) {
      *field = n.parse()?;
    }
  }
  let backend = Backend::for_batch(&plan, parameters)?;
  let key = backend.verifying_key_bytes()?;
  let setup_seconds = start.elapsed().as_secs_f64();

  let start = Instant::now();
  let record = hints.execute(&entry, address.clone())?;
  let execution_seconds = start.elapsed().as_secs_f64();
  let rows = backend.execution_rows(&record);
  let log_heights = backend.normalized_log_heights(&rows, 0)?;
  let output = record.output.clone();
  let statistics = backend.statistics();

  let start = Instant::now();
  let (claim, proof) = backend.prove_normalized(
    &entry,
    &address,
    &output,
    record,
    &log_heights,
  )?;
  let prove_seconds = start.elapsed().as_secs_f64();
  let proof_bytes = proof.to_bytes().map_err(|e| e.to_string())?;

  let start = Instant::now();
  backend.verify_batch(&entry, &address, &output, &proof)?;
  let verify_seconds = start.elapsed().as_secs_f64();

  let claims = stark_verifier::claims_bytes(std::slice::from_ref(&claim));
  fs::write(out.join("root-vk.bin"), &key)?;
  fs::write(out.join("root-claims.bin"), &claims)?;
  fs::write(out.join("root-proof.bin"), &proof_bytes)?;
  let circuits: Vec<_> = statistics
    .iter()
    .zip(&rows)
    .zip(&log_heights)
    .map(|((s, rows), log)| {
      let mut value = serde_json::to_value(s).unwrap();
      value["rows"] = json!(rows);
      value["log_height"] = json!(log);
      value
    })
    .collect();
  let report = json!({
    "package_blake3": digest.to_string(),
    "entry": entry,
    "args_len": address.len(),
    "output": output.iter().map(|v| v.as_canonical_u64()).collect::<Vec<_>>(),
    "claim_len": claim.len(),
    "root_key_blake3": blake3::hash(&key).to_hex().to_string(),
    "root_key_bytes": key.len(),
    "root_claims_blake3": blake3::hash(&claims).to_hex().to_string(),
    "root_proof_blake3": blake3::hash(&proof_bytes).to_hex().to_string(),
    "proof_bytes": proof_bytes.len(),
    "prepare_seconds": prepare_seconds,
    "setup_seconds": setup_seconds,
    "execution_seconds": execution_seconds,
    "prove_seconds": prove_seconds,
    "verify_seconds": verify_seconds,
    "peak_rss_bytes": aiur::trace::stark::planning::peak_resident_memory(),
    "verified": true,
    "circuits": circuits,
  });
  fs::write(out.join("report.json"), serde_json::to_vec_pretty(&report)?)?;
  let mut summary = report;
  summary.as_object_mut().unwrap().remove("circuits");
  println!("{}", serde_json::to_string_pretty(&summary)?);
  Ok(())
}
