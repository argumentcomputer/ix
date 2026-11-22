//! Trusted configuration of the L3 chain: the chain policy of the fixed-key
//! narrow stage and the narrow terminal's configuration.
//!
//! `aiur_packed_final_config --narrow CHAIN_DIR NARROW_DIR OUT_JSON`
//!
//! `CHAIN_DIR` holds the chain's `policy.bin` (`IXAUKG01`) and `gl-key.bin`,
//! the CompressGL key the fixed-key narrow stage (`CompressNarrowFixed`)
//! verifies; `NARROW_DIR` holds the narrow stage's `key.bin` and
//! `narrow.json` (`aiur_template_v2_init --save`). The policy's anchors are
//! checked against the Ignition anchors of the release setup loader, its GL
//! key digest against `gl-key.bin` and its later-stage slot against the
//! narrow key. The configuration's stage interval is the one terminal stage
//! after the narrow stage, and it carries the narrow claim's chunk headers
//! `[tag, instance key, value count]`; the JSON is the input of
//! `compress_final_narrow_export`, which embeds the narrow key.
//!
//! `aiur_packed_final_config --fixed-key-policy GL_DIR NARROW_ARTIFACT
//! [NARROW_KEY] OUT` writes the chain policy: the CompressGL key
//! `GL_DIR/gl-key.bin` with the entry of its claim `GL_DIR/gl/claims.bin` at
//! stage one, and the narrow key with the narrow program's entry after it.
//! Without `NARROW_KEY` the second slot's digest is zero; such a bootstrap
//! policy only serves to produce the narrow key, which depends on the layout
//! and not on the policy.

use ix_proof_compression::{
  aiur_backend::{
    compress_bn::{
      PACKED_NARROW_FIXED_ENTRY, PackedCapacity, PackedPolicy, Wrapper,
    },
    pairing::final_program::Configuration,
  },
  pipeline::SetupConfig,
};
use std::{fs, path::Path};

fn main() -> Result<(), Box<dyn std::error::Error>> {
  let args: Vec<_> = std::env::args().skip(1).collect();
  if let [flag, chain, narrow, out] = args.as_slice()
    && flag == "--narrow"
  {
    return narrow_configuration(
      Path::new(chain),
      Path::new(narrow),
      Path::new(out),
    );
  }
  if args.first().map(String::as_str) == Some("--fixed-key-policy") {
    let (gl, artifact, key, out) = match &args[1..] {
      [gl, artifact, out] => (gl, artifact, None, out),
      [gl, artifact, key, out] => (gl, artifact, Some(key), out),
      _ => return Err("usage: aiur_packed_final_config --fixed-key-policy GL_DIR NARROW_ARTIFACT [NARROW_KEY] OUT".into()),
    };
    return fixed_key_policy(
      Path::new(gl),
      Path::new(artifact),
      key.map(Path::new),
      Path::new(out),
    );
  }
  Err("usage: aiur_packed_final_config --narrow CHAIN_DIR NARROW_DIR OUT_JSON | --fixed-key-policy GL_DIR NARROW_ARTIFACT [NARROW_KEY] OUT".into())
}

fn narrow_configuration(
  chain: &Path,
  narrow: &Path,
  out: &Path,
) -> Result<(), Box<dyn std::error::Error>> {
  let setup = SetupConfig::from_env(false)?;
  let capacity = PackedCapacity {
    log_cap: 1,
    quotient_degree: 1,
    lookup_quotient_budget: None,
  };
  let config = capacity.config(&setup)?;
  let parameters = multi_stark::config::ProofConfig::pcs(&config).parameters();
  let policy_bytes = fs::read(chain.join("policy.bin"))?;
  let policy = PackedPolicy::from_chain_bytes(parameters, &policy_bytes)?;
  let stage: serde_json::Value =
    serde_json::from_slice(&fs::read(narrow.join("narrow.json"))?)?;
  let key = fs::read(narrow.join("key.bin"))?;
  if stage["stage"].as_u64() != Some(1) {
    return Err("the narrow stage is the fixed-key stage one".into());
  }
  if policy.bn().0 != *blake3::hash(&key).as_bytes() {
    return Err("policy does not name the fixed-key narrow key".into());
  }
  if policy.gl().0
    != *blake3::hash(&fs::read(chain.join("gl-key.bin"))?).as_bytes()
  {
    return Err(
      "policy does not authorize the narrow stage's predecessor key".into(),
    );
  }
  if stage["key_blake3"].as_str() != Some(blake3::hash(&key).to_hex().as_str())
    || stage["policy_blake3"].as_str()
      != Some(blake3::hash(&policy_bytes).to_hex().as_str())
  {
    return Err(
      "narrow stage record does not match its key or the policy".into(),
    );
  }
  let narrow_stage =
    u32::try_from(stage["stage"].as_u64().ok_or("narrow stage")?)?;
  let configuration =
    Configuration::narrow(&policy, parameters, narrow_stage + 1)?;
  let mut json: serde_json::Value =
    serde_json::from_slice(&configuration.to_json()?)?;
  let headers = stage["claim_headers"].as_array().ok_or("claim headers")?;
  let chunk = stage["chunk_values"].as_u64().ok_or("chunk values")?;
  let total = stage["claim_values"].as_u64().ok_or("claim values")?;
  let mut rows = vec![];
  for (j, header) in headers.iter().enumerate() {
    let values = chunk.min(total - chunk * j as u64);
    rows.push(serde_json::json!([header[0], header[1], values.to_string()]));
  }
  json["claim_headers"] = serde_json::Value::Array(rows);
  json["narrow_key_blake3"] = stage["key_blake3"].clone();
  json["narrow_stage"] = narrow_stage.into();
  fs::write(out, serde_json::to_vec_pretty(&json)?)?;
  println!(
    "policy {} narrow key {} terminal stage {}",
    blake3::Hash::from_bytes(policy.digest()).to_hex(),
    blake3::hash(&key).to_hex(),
    narrow_stage + 1
  );
  Ok(())
}

fn fixed_key_policy(
  gl: &Path,
  artifact: &Path,
  narrow_key: Option<&Path>,
  out: &Path,
) -> Result<(), Box<dyn std::error::Error>> {
  let setup = SetupConfig::from_env(false)?;
  let capacity = PackedCapacity {
    log_cap: 1,
    quotient_degree: 1,
    lookup_quotient_budget: None,
  };
  let config = capacity.config(&setup)?;
  let parameters = multi_stark::config::ProofConfig::pcs(&config).parameters();
  let gl_digest = *blake3::hash(&fs::read(gl.join("gl-key.bin"))?).as_bytes();
  // `kzg_advice::claims_bytes`: magic, count, length, then 32-byte words; a
  // CompressGL claim is `[tag, entry, reserved(8), statement(8)]`.
  let claims = fs::read(gl.join("gl/claims.bin"))?;
  let word = claims.get(16 + 32..16 + 32 + 32).ok_or("CompressGL claims")?;
  if word[4..].iter().any(|&b| b != 0) {
    return Err("CompressGL entry exceeds u32".into());
  }
  let gl_entry = u32::from_le_bytes(word[..4].try_into()?);
  let bytes = fs::read(artifact)?;
  let wrapper = Wrapper::from_bytes_with_entry(
    &bytes,
    blake3::hash(&bytes).as_bytes(),
    PACKED_NARROW_FIXED_ENTRY,
  )?;
  let narrow_digest = match narrow_key {
    Some(path) => *blake3::hash(&fs::read(path)?).as_bytes(),
    None => [0; 32],
  };
  let policy = PackedPolicy::chain(
    parameters,
    (gl_digest, gl_entry),
    (narrow_digest, wrapper.entry()),
  )?;
  fs::write(out, policy.to_bytes())?;
  println!(
    "policy {} gl key {} entry {gl_entry} narrow key {} entry {}",
    blake3::Hash::from_bytes(policy.digest()).to_hex(),
    blake3::Hash::from_bytes(gl_digest).to_hex(),
    blake3::Hash::from_bytes(narrow_digest).to_hex(),
    wrapper.entry()
  );
  Ok(())
}
