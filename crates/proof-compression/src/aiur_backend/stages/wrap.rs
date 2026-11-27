//! `fri`: the normalized CompressWrap proof of the root at a pinned layout
//! (`stark-verifier wrap-prove`).
//!
//! Manifest fields: `package` and `layout` (products), optional `advice`
//! (product, pre-guess `ixcc` advice artifact), optional `entry` (default
//! `stark_verifier::compress_wrap::ENTRY`), `device` (CUDA device, default 0).
use super::{Error, Handoff, Stage, exports::WideSource};
use aiur::{artifact::Package, trace::stark::Parameters};
use serde_json::{Value, json};
use stark_verifier::compress_wrap::{LayoutConfig, Wrapper};
use std::time::Instant;

fn parse_entry<'a>(
  spec: &'a Value,
  stage_name: &str,
) -> Result<&'a str, Error> {
  match spec.get("entry") {
    None | Some(Value::Null) => Ok(stark_verifier::compress_wrap::ENTRY),
    Some(value) => value
      .as_str()
      .ok_or_else(|| format!("{stage_name} entry: expected a string")),
  }
}

fn has_advice(spec: &Value) -> bool {
  spec.get("advice").is_some_and(|value| !value.is_null())
}

pub(super) fn run(stage: &Stage<'_>) -> Result<Handoff, Error> {
  let started = Instant::now();
  let package_file = stage.product("package")?;
  let layout_file = stage.product("layout")?;
  let advice_file = if has_advice(&stage.spec.spec) {
    Some(stage.product("advice")?)
  } else {
    None
  };
  let entry = parse_entry(&stage.spec.spec, &stage.spec.name)?;
  let config: LayoutConfig = serde_json::from_slice(&layout_file.bytes)
    .map_err(|e| format!("wrap layout: {e}"))?;
  let device = stage.spec.spec["device"]
    .as_i64()
    .map_or(Ok(0), i32::try_from)
    .map_err(|e| e.to_string())?;
  let package = Package::decode(&package_file.bytes)?;
  let artifact_digest = blake3::hash(&package_file.bytes).to_hex().to_string();
  let mut wrapper = Wrapper::for_layout_with_entry(
    package,
    Parameters::default(),
    Some(device),
    &config.layout,
    &WideSource(&stage.stages.exports),
    entry,
  )?;
  let advice_digest = match &advice_file {
    Some(file) => {
      wrapper = wrapper.with_advice_bytes(&file.bytes)?;
      Some(blake3::hash(&file.bytes).to_hex().to_string())
    },
    None => None,
  };
  config.check(&wrapper)?;
  let key_blake3 = blake3::hash(wrapper.key_bytes()).to_hex().to_string();
  let key_is_layout_key = key_blake3 == config.layout.key_blake3;
  stage.stages.checks.set("wrap_key_is_layout_key", key_is_layout_key);
  if !key_is_layout_key {
    return Err("the wrapper key differs from the layout's".into());
  }
  let setup_seconds = started.elapsed().as_secs_f64();
  stage.reserve(1);
  stage.cancelled()?;

  stage.reserve(2);
  let input = &stage.stages.root;
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
  stage.stages.checks.set("wrap_verified", true);
  stage.write("out/key.bin", &result.key)?;
  stage.write("out/claims.bin", &result.claims)?;
  stage.write("out/proof.bin", &result.proof)?;
  let mut wrapper_report = json!({
    "artifact_blake3": artifact_digest,
    "key_blake3": key_blake3,
    "entry": wrapper.entry(),
    "lowering": wrapper.lowering(),
    "setup_seconds": setup_seconds,
  });
  if let Some(digest) = advice_digest
    && let Some(obj) = wrapper_report.as_object_mut()
  {
    obj.insert("advice_blake3".to_owned(), json!(digest));
  }
  let report = json!({
    "format": "ix-compress-wrap-profile-v1",
    "input": {
      "key_blake3": blake3::hash(input.key_bytes()).to_hex().to_string(),
      "claims_blake3": blake3::hash(input.claims_bytes()).to_hex().to_string(),
      "proof_blake3": blake3::hash(input.proof_bytes()).to_hex().to_string(),
    },
    "wrapper": wrapper_report,
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

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn manifest_entry_and_advice_defaults_preserve_existing_manifests() {
    let legacy = json!({
      "name": "fri",
      "kind": "fri",
      "package": { "path": "wrap.ixa", "blake3": "00" },
      "layout": { "path": "wrap.layout.json", "blake3": "11" },
      "device": 0
    });
    assert_eq!(
      parse_entry(&legacy, "fri").unwrap(),
      stark_verifier::compress_wrap::ENTRY
    );
    assert!(!has_advice(&legacy));

    let explicit_null = json!({ "entry": null, "advice": null });
    assert_eq!(
      parse_entry(&explicit_null, "fri").unwrap(),
      stark_verifier::compress_wrap::ENTRY
    );
    assert!(!has_advice(&explicit_null));

    let compiled = json!({
      "entry": "Prog::main0",
      "advice": { "path": "wrap.advice.ixa", "blake3": "22" }
    });
    assert_eq!(parse_entry(&compiled, "fri").unwrap(), "Prog::main0");
    assert!(has_advice(&compiled));

    let bad_entry = json!({ "entry": 42 });
    assert!(parse_entry(&bad_entry, "fri").is_err());
  }
}
