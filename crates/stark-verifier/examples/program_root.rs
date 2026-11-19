//! Prove an execution package on the device as a batch of planned trace
//! shards, streamed, the way `aiur_exec_tree` proves a node and `ix prove`
//! proves an execution (`aiur-gpu-proving.md` §3): one resident
//! `Backend::for_batch_on_device` prover, the record planned into shards
//! within the lane workspace for `AIUR_TRACE_SHARD_MAX_CELLS`-cell shards,
//! the next shard's witness built on a `ShardFeed` while the current one
//! proves, then the batch verified.
//!
//! `program_root PACKAGE.ixa OUT_DIR` writes what `batch_root` writes:
//! `root-vk.bin`, `root-claims.bin`, `root-proof.bin` and `report.json`, so
//! `aiur_exec leaf` and `aiur_exec_tree` take the directory as a program root.
use aiur::{
  artifact::ExecutionPackage,
  field::FieldBackend,
  trace::{
    TracePlan,
    stark::{Backend, Parameters, ShardFeed, planning},
  },
};
use multi_stark::p3_field::PrimeField64;
use serde_json::json;
use std::{error::Error, fs, path::Path, time::Instant};

fn main() -> Result<(), Box<dyn Error>> {
  let args: Vec<_> = std::env::args().collect();
  let (Some(path), Some(out)) = (args.get(1), args.get(2)) else {
    return Err("usage: program_root PACKAGE.ixa OUT_DIR".into());
  };
  let out = Path::new(out);
  fs::create_dir_all(out)?;
  if planning::gpu_count() == 0 {
    return Err("no visible GPU in this build or host".into());
  }
  let device = match std::env::var("MULTI_STARK_CUDA_DEVICE") {
    Ok(v) => v.parse::<i32>()?,
    Err(_) => 0,
  };
  let start = Instant::now();
  let (package, digest) = ExecutionPackage::load(path.as_ref())?;
  eprintln!("artifact {path}: blake3 {digest}");
  let (program, trace) = package.package.traced()?;
  let mut program = program.check_field::<multi_stark::types::Val>()?;
  program.track_depth(&trace)?;
  let address = program.field().decode(&package.args)?;
  // The package's hint table, plus the word libraries' channels (BLAKE3's
  // `u32.*` and `bytes_le`), which are computed rather than tabulated.
  let mut channels = aiur::hints::HintChannels::new();
  aiur::library::u32::register(&mut channels, program.field())?;
  aiur::library::u64::register(&mut channels, program.field())?;
  let hints = program.prepare_hint_channels(&package.hints, &channels)?;
  let plan = TracePlan::new(&program, trace)?;
  let entry = program.program().entries.first().ok_or("no selected entrypoint")?.name.clone();
  let prepare_seconds = start.elapsed().as_secs_f64();

  let start = Instant::now();
  let prover = Backend::for_batch_on_device(&plan, Parameters::default(), Some(device))?;
  let feed = ShardFeed::matching_current()?;
  let key = prover.verifying_key_bytes()?;
  let setup_seconds = start.elapsed().as_secs_f64();

  let cells = planning::configured_cells()? as usize;
  // The lane workspace of the aggregate controller (`lanes::cell_workspace`).
  let workspace = (cells * 16 + (256 << 20)) * 43 / 40;
  let options = planning::Options {
    device: Some(device),
    max_ram_bytes: Some(workspace as u64),
    ..Default::default()
  };

  let start = Instant::now();
  let record = hints.execute(&entry, address.clone())?;
  drop(hints);
  let execution_seconds = start.elapsed().as_secs_f64();
  let output = record.output.clone();
  let rows = prover.execution_rows(&record);

  let start = Instant::now();
  let _ = prover.plan_record(&record, &options, 0);
  let prepared = prover.prepare_host(record, &entry, &address)?;
  let host_seconds = start.elapsed().as_secs_f64();

  let start = Instant::now();
  let batch = prover.plan_record(prepared.record(), &options, 0)?;
  if !batch.fits {
    return Err(format!(
      "no trace-shard plan fits the {workspace}-byte lane workspace (generation peak {}, proving peak {})",
      batch.generation_peak_bytes, batch.proving_peak_bytes
    )
    .into());
  }
  let layout = batch.layout.as_ref().ok_or("the proving plan has no incremental layout")?;
  let run = prover.prove_prepared(
    &prepared,
    &output,
    layout,
    batch.retention(),
    batch.pipelined.then_some(&feed),
  )?;
  let prove_seconds = start.elapsed().as_secs_f64();
  drop(prepared);

  let start = Instant::now();
  prover.verify_batch(&entry, &address, &output, &run.proof)?;
  let verify_seconds = start.elapsed().as_secs_f64();
  let claim = prover.claim(&entry, &address, &output)?;
  let proof_bytes = run.proof.to_bytes().map_err(|e| e.to_string())?;
  let claims = stark_verifier::claims_bytes(std::slice::from_ref(&claim));
  fs::write(out.join("root-vk.bin"), &key)?;
  fs::write(out.join("root-claims.bin"), &claims)?;
  fs::write(out.join("root-proof.bin"), &proof_bytes)?;
  let report = json!({
    "package_blake3": digest.to_string(),
    "entry": entry,
    "prover": "program_root: resident device prover, planned trace shards, streamed",
    "device": device,
    "args_len": address.len(),
    "output": output.iter().map(|v| v.as_canonical_u64()).collect::<Vec<_>>(),
    "claim_len": claim.len(),
    "root_key_blake3": blake3::hash(&key).to_hex().to_string(),
    "root_key_bytes": key.len(),
    "root_claims_blake3": blake3::hash(&claims).to_hex().to_string(),
    "root_proof_blake3": blake3::hash(&proof_bytes).to_hex().to_string(),
    "proof_bytes": proof_bytes.len(),
    "trace_shards": run.proof.proofs.len(),
    "shard_cells": batch.shard_cells,
    "lane_workspace_bytes": workspace,
    "planned_device_peak_bytes": batch.device_peak_bytes,
    "planned_host_peak_bytes": batch.proving_peak_bytes,
    "pipelined": run.population.pipelined,
    "population_stall_seconds": run.population.stall_seconds,
    "prepare_seconds": prepare_seconds,
    "setup_seconds": setup_seconds,
    "execution_seconds": execution_seconds,
    "host_prepare_seconds": host_seconds,
    "prove_seconds": prove_seconds,
    "trace_seconds": run.trace_seconds,
    "proving_seconds": run.proving_seconds,
    "verify_seconds": verify_seconds,
    "peak_rss_bytes": planning::peak_resident_memory(),
    "verified": true,
    "rows": rows,
  });
  fs::write(out.join("report.json"), serde_json::to_vec_pretty(&report)?)?;
  let mut summary = report;
  summary.as_object_mut().unwrap().remove("rows");
  println!("{}", serde_json::to_string_pretty(&summary)?);
  Ok(())
}
