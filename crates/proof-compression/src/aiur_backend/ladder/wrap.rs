//! `wrap`: the normalized CompressWrap proof of the root at a pinned layout
//! (`stark-verifier wrap-prove`).
//!
//! Manifest fields: `package` and `layout` (products), `device` (CUDA
//! device, default 0).
use super::{Error, Handoff, Stage, exports::WideSource};
use aiur::{artifact::Package, trace::stark::Parameters};
use serde_json::json;
use stark_verifier::compress_wrap::{LayoutConfig, Wrapper};
use std::time::Instant;

pub(super) fn run(stage: &Stage<'_>) -> Result<Handoff, Error> {
  let started = Instant::now();
  let package_file = stage.product("package")?;
  let layout_file = stage.product("layout")?;
  let config: LayoutConfig = serde_json::from_slice(&layout_file.bytes)
    .map_err(|e| format!("wrap layout: {e}"))?;
  let device = stage.spec.spec["device"]
    .as_i64()
    .map_or(Ok(0), i32::try_from)
    .map_err(|e| e.to_string())?;
  let package = Package::decode(&package_file.bytes)?;
  let artifact_digest = blake3::hash(&package_file.bytes).to_hex().to_string();
  let wrapper = Wrapper::for_layout_with(
    package,
    Parameters::default(),
    Some(device),
    &config.layout,
    &WideSource(&stage.ladder.exports),
  )?;
  config.check(&wrapper)?;
  let key_blake3 = blake3::hash(wrapper.key_bytes()).to_hex().to_string();
  let key_is_layout_key = key_blake3 == config.layout.key_blake3;
  stage.ladder.checks.set("wrap_key_is_layout_key", key_is_layout_key);
  if !key_is_layout_key {
    return Err("the wrapper key differs from the layout's".into());
  }
  let setup_seconds = started.elapsed().as_secs_f64();
  stage.reserve(1);
  stage.cancelled()?;

  stage.reserve(2);
  let input = &stage.ladder.root;
  let started = Instant::now();
  let execution = wrapper.execute(input)?;
  let execution_seconds = started.elapsed().as_secs_f64();
  let started = Instant::now();
  let admission = wrapper.admit(&execution, &config.layout)?;
  let admission_seconds = started.elapsed().as_secs_f64();
  let started = Instant::now();
  let result =
    stage.gpu(|| wrapper.prove_normalized(execution, &config.layout))?;
  wrapper.verify_normalized(
    input.statement(),
    &result.proof,
    &config.layout,
  )?;
  let proving_seconds = started.elapsed().as_secs_f64();
  stage.ladder.checks.set("wrap_verified", true);
  stage.write("out/key.bin", &result.key)?;
  stage.write("out/claims.bin", &result.claims)?;
  stage.write("out/proof.bin", &result.proof)?;
  let report = json!({
    "format": "ix-compress-wrap-profile-v1",
    "input": {
      "key_blake3": blake3::hash(input.key_bytes()).to_hex().to_string(),
      "claims_blake3": blake3::hash(input.claims_bytes()).to_hex().to_string(),
      "proof_blake3": blake3::hash(input.proof_bytes()).to_hex().to_string(),
    },
    "wrapper": {
      "artifact_blake3": artifact_digest,
      "key_blake3": key_blake3,
      "entry": stark_verifier::compress_wrap::ENTRY,
      "lowering": wrapper.lowering(),
      "setup_seconds": setup_seconds,
    },
    "execution_seconds": execution_seconds,
    "admission": admission,
    "admission_seconds": admission_seconds,
    "layout_blake3": config.layout_blake3,
    "verified": true,
    "proving_seconds": proving_seconds,
    "proof_bytes": result.proof.len(),
    "proof_blake3": blake3::hash(&result.proof).to_hex().to_string(),
    "shards": 1,
    "peak_rss_bytes": aiur::trace::stark::planning::peak_resident_memory(),
  });
  stage.write_json("stdout.json", &report)?;
  Ok(Handoff {
    key: result.key,
    claims: result.claims,
    proof: result.proof,
    ..Handoff::default()
  })
}
