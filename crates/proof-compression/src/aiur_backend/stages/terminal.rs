//! `plonk`: the terminal relation (`CompressFinalNarrow`) on the
//! narrow proof, proved by gnark PLONK on the prepared circuit of the
//! Lean-checked constraint system (`aiur_narrow_terminal_prove --cuda
//! --reuse --scs ...`).
//!
//! Manifest fields: `artifact`, `policy`, `prepared_manifest` (the prepared
//! directory's `manifest.json`), all products; `scs` (`path` and `sha256`;
//! the file is hashed off the critical path), `cuda` (default true).
//!
//! The prepared directory (`prepared/` beside the manifest) is reused, never
//! rebuilt: its manifest must name this SCS file's and this terminal's
//! pairing configuration's digests.
use super::{Error, Handoff, Stage};
use crate::{
  aiur_backend::{
    Bn254,
    compress_bn::{PackedCapacity, PackedPolicy},
    fq, g1,
    kzg::Compiler,
    kzg_advice as wire,
    pairing::final_program::{
      Configuration, NARROW_ACCUMULATOR_ENTRY, statement_arguments,
    },
    plonk::{gnark, scs},
  },
  pipeline::SetupConfig,
};
use aiur::{
  artifact::WidePackage, field::FieldBackend, hints::HintChannels,
  maps::MapOverrides, trace::TracePlan,
};
use ark_ec::pairing::Pairing;
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::{fs, path::Path, sync::Arc, time::Instant};

fn sha256_file(path: &Path) -> Result<String, String> {
  let mut hash = Sha256::new();
  std::io::copy(
    &mut fs::File::open(path)
      .map_err(|e| format!("{}: {e}", path.display()))?,
    &mut hash,
  )
  .map_err(|e| e.to_string())?;
  Ok(format!("{:x}", hash.finalize()))
}

/// Reads the files gnark's open loads from `prepared` once, outside the GPU
/// lock, so the open finds them in the page cache. Read cold from disk the
/// 5 GB take tens of seconds; inside the lock that delay would hold back the
/// narrow stage's fixed-slot commitment and, through the memory budget,
/// CompressGL's trace phase, both on the critical path.
fn prefetch(prepared: &Path) -> Result<(), String> {
  use std::io::Read;
  let raw = prepared.join("proving-key.raw");
  let key = if raw.exists() { raw } else { prepared.join("proving-key.bin") };
  let mut buffer = vec![0u8; 8 << 20];
  for path in
    [prepared.join("circuit.bin"), prepared.join("verifying-key.bin"), key]
  {
    let mut file =
      fs::File::open(&path).map_err(|e| format!("{}: {e}", path.display()))?;
    while file
      .read(&mut buffer)
      .map_err(|e| format!("{}: {e}", path.display()))?
      != 0
    {}
  }
  Ok(())
}

struct Phases(serde_json::Map<String, Value>);

impl Phases {
  fn record(&mut self, name: &str, started: Instant) {
    self.0.insert(
      name.into(),
      json!({"seconds": started.elapsed().as_secs_f64(),
        "peak_rss_gb_after": super::peak_rss_gb()}),
    );
  }
}

pub(super) fn run(stage: &Stage<'_>) -> Result<Handoff, Error> {
  let spec = &stage.spec.spec;
  let backend = if spec["cuda"].as_bool().unwrap_or(true) {
    let gib: u64 = std::env::var("IX_PLONK_CUDA_MEMORY_GIB")
      .unwrap_or_else(|_| "64".into())
      .parse()
      .map_err(|e| format!("IX_PLONK_CUDA_MEMORY_GIB: {e}"))?;
    gnark::Backend::Cuda { device: 0, memory_bytes: gib << 30, mask_msm: false }
  } else {
    gnark::Backend::Cpu
  };
  let scs_path = stage.stages.manifest.path(&spec["scs"]["path"])?;
  let scs_pin = spec["scs"]["sha256"].as_str().ok_or("scs.sha256")?.to_owned();
  // The 0.8 GB file's digest is computed while the terminal prepares.
  let scs_hash = {
    let path = scs_path.clone();
    std::thread::spawn(move || sha256_file(&path))
  };
  let mut phases = Phases(serde_json::Map::new());

  let started = Instant::now();
  let artifact = stage.product("artifact")?;
  let pin = blake3::hash(&artifact.bytes);
  let package = WidePackage::decode(&artifact.bytes)?;
  let trace = package.trace.ok_or("missing trace")?;
  let mut program = package.program.check_with(Bn254)?;
  program.track_depth(&trace)?;
  let plan = TracePlan::new(Arc::new(program), trace)?;
  let setup = SetupConfig::from_env(false).map_err(|e| e.to_string())?;
  let capacity = PackedCapacity {
    log_cap: 1,
    quotient_degree: 1,
    lookup_quotient_budget: None,
  };
  let config = capacity.config(&setup)?;
  let parameters = multi_stark::config::ProofConfig::pcs(&config).parameters();
  let policy_file = stage.product("policy")?;
  let policy = PackedPolicy::from_chain_bytes(parameters, &policy_file.bytes)?;
  let manifest_file = stage.product("prepared_manifest")?;
  let manifest: gnark::Manifest =
    serde_json::from_slice(&manifest_file.bytes).map_err(|e| e.to_string())?;
  let prepared_root =
    manifest_file.path.parent().ok_or("prepared manifest path")?.to_path_buf();
  let prepared = prepared_root.join("prepared");
  phases.record("setup", started);
  let started = Instant::now();
  prefetch(&prepared)?;
  phases.record("prefetch", started);
  let started = Instant::now();
  let mut prover = Some(
    stage
      .gpu(|| gnark::Prover::open(&prepared, &manifest, backend))
      .map_err(|e| e.to_string())?,
  );
  phases.record("load", started);
  stage.reserve(1);

  let started = Instant::now();
  let (narrow, _) = stage.input()?;
  phases.record("wait", started);
  stage.cancelled()?;
  stage.reserve(2);
  let started = Instant::now();
  let statement_bytes =
    narrow.statement.ok_or("the narrow stage passed no statement")?;
  let configuration =
    Configuration::narrow(&policy, parameters, narrow.stage + 1)?;
  let mut hints = HintChannels::new();
  aiur::library::u32::register(&mut hints, Bn254)?;
  aiur::library::u64::register(&mut hints, Bn254)?;
  fq::register(&mut hints)?;
  g1::register(&mut hints)?;
  wire::register(&mut hints)?;
  wire::Inputs::new(
    narrow.key.clone(),
    narrow.claims.clone(),
    narrow.proof.clone(),
    policy_file.bytes.clone(),
  )?
  .register(&mut hints)?;
  let mut maps = MapOverrides::new();
  aiur::library::u8::register_maps(plan.program(), &mut maps)?;
  let arguments = statement_arguments(&statement_bytes).to_vec();
  let record = plan
    .program()
    .prepare_hint_channels(&[], &hints)?
    .with_map_overrides(&maps)?
    .execute(NARROW_ACCUMULATOR_ENTRY, arguments.clone())
    .map_err(|e| e.to_string())?;
  let pair =
    [g1::decode(&record.output[..9])?, g1::decode(&record.output[9..])?];
  let (_, anchors) = crate::aiur_backend::pairing::verifier_anchors(parameters);
  if ark_bn254::Bn254::multi_pairing(pair, [anchors[0], anchors[1]]).0
    != <ark_bn254::Bn254 as Pairing>::TargetField::from(1u8)
  {
    return Err("terminal accumulator fails the Ignition pairing check".into());
  }
  phases.record("execute", started);

  let compiler = Compiler::new(&plan)?;
  let capacities: Vec<usize> =
    compiler.row_counts(&record)?.into_iter().map(|rows| rows.max(1)).collect();
  let pairing = serde_json::to_vec(&scs::pairing(
    &plan,
    NARROW_ACCUMULATOR_ENTRY,
    &configuration,
  )?)
  .map_err(|e| e.to_string())?;

  let started = Instant::now();
  let scs_sha256 = scs_hash
    .join()
    .map_err(|_error| "SCS digest thread panicked".to_string())??;
  if scs_sha256 != scs_pin {
    return Err(format!(
      "SCS SHA-256 {scs_sha256} differs from the pinned {scs_pin}"
    ));
  }
  let pairing_sha256 = format!("{:x}", Sha256::digest(&pairing));
  if manifest.scs_sha256 != scs_sha256
    || manifest.pairing_sha256 != pairing_sha256
  {
    return Err(
      "the prepared circuit is not this SCS file's and pairing configuration's"
        .into(),
    );
  }
  phases.record("scs_digest", started);
  let started = Instant::now();
  let layout =
    fs::read(prepared.join("inputs.json")).map_err(|e| e.to_string())?;
  let pinned =
    manifest.files.get("inputs.json").ok_or("manifest without inputs.json")?;
  if format!("{:x}", Sha256::digest(&layout)) != pinned.sha256 {
    return Err("prepared inputs.json differs from its manifest".into());
  }
  let witness = scs::Witness::new(
    &plan,
    compiler,
    &capacities,
    NARROW_ACCUMULATOR_ENTRY,
    serde_json::from_slice(&layout).map_err(|e| e.to_string())?,
  )?
  .binary(&record, &arguments)?;
  phases.record("witness", started);

  let started = Instant::now();
  let mut open = prover.take().ok_or("the PLONK prover is gone")?;
  let proof = stage
    .gpu(|| open.prove(&witness, &arguments))
    .map_err(|e| e.to_string())?;
  phases.record("prove", started);
  let mut wrong = arguments.clone();
  wrong[0] += Bn254.one();
  let refused = stage.gpu(|| open.prove(&witness, &wrong)).is_err();
  open.close().map_err(|e| e.to_string())?;
  stage.stages.checks.set("plonk_wrong_statement_refused_by_prover", refused);

  let started = Instant::now();
  let key =
    fs::read(prepared.join("verifying-key.bin")).map_err(|e| e.to_string())?;
  let key_sha256 = format!("{:x}", Sha256::digest(&key));
  let key_pin: [u8; 32] = Sha256::digest(&key).into();
  let anchor_bytes = gnark::anchors(parameters);
  gnark::verify(&key, &key_pin, &proof.native, &arguments, &anchor_bytes)
    .map_err(|e| e.to_string())?;
  phases.record("verify", started);
  let rejected =
    gnark::verify(&key, &key_pin, &proof.native, &wrong, &anchor_bytes)
      .is_err();
  stage
    .stages
    .checks
    .set("plonk_wrong_statement_rejected_by_verifier", rejected);
  let prepared_key = manifest
    .files
    .get("verifying-key.bin")
    .is_some_and(|file| file.sha256 == key_sha256);
  stage.stages.checks.set("plonk_verifying_key_is_prepared", prepared_key);
  if !rejected {
    return Err("PLONK verifier accepted a changed statement".into());
  }
  if !prepared_key {
    return Err(
      "the verifying key differs from the prepared manifest's".into(),
    );
  }
  stage.write("proof.bin", &proof.native)?;
  stage.write("proof.solidity.bin", &proof.solidity)?;
  let info = &manifest.info;
  let summary = json!({
    "format": "ix-aiur-narrow-terminal-plonk-v1",
    "circuit": "ix-aiur-scs-v1", "scs": scs_path, "scs_sha256": scs_sha256, "pairing_sha256": pairing_sha256,
    "entry": NARROW_ACCUMULATOR_ENTRY,
    "artifact": artifact.path, "artifact_blake3": pin.to_hex().as_str(),
    "statement": super::hex(&statement_bytes),
    "backend": if matches!(backend, gnark::Backend::Cpu) { "cpu" } else { "cuda" },
    "constraints": info.constraints, "domain": info.domain, "public_inputs": info.public_inputs,
    "commitments": info.commitments,
    "witness_bytes": witness.len(), "witness_sha256": format!("{:x}", Sha256::digest(&witness)),
    "srs_blake3": manifest.srs_blake3,
    "verifying_key_sha256": key_sha256,
    "proof_bytes": proof.native.len(), "solidity_proof_bytes": proof.solidity.len(),
    "public_inputs_decimal": arguments.iter().map(|v| v.0.to_string()).collect::<Vec<_>>(),
    "outputs_decimal": record.output.iter().map(|v| v.0.to_string()).collect::<Vec<_>>(),
    "wrong_statement_refused_by_prover": refused,
    "wrong_statement_rejected_by_verifier": rejected,
    "phases": phases.0,
    "peak_rss_gb": super::peak_rss_gb(),
  });
  stage.write_json("summary.json", &summary)?;
  Ok(Handoff {
    key,
    claims: Vec::new(),
    proof: proof.native,
    stage: narrow.stage + 1,
    statement: Some(statement_bytes),
    solidity: proof.solidity,
  })
}
