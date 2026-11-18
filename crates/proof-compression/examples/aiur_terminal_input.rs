//! Authenticate a completed chain and export canonical terminal advice.
//! Core configuration and expected root digests are independent caller inputs.
use ix_proof_compression::{
  aiur_backend::chain::{Assets, Configuration, Envelope, Verifier},
  pipeline::SetupClass,
};
use stark_verifier::compress_wrap::Statement;
use std::{fs, path::Path};

type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;
const USAGE: &str = "usage: aiur_terminal_input CORE_CONFIG_JSON CONFIG_BLAKE3 GL_ARTIFACT GL_KEY BN_ARTIFACT BN_KEY ROOT_KEY_BLAKE3 ROOT_CLAIMS_BLAKE3 CHAIN_ENVELOPE NEW_DIRECTORY [--dev-srs]";

fn pin(value: &str) -> Result<[u8; 32]> {
  Ok(*blake3::Hash::from_hex(value)?.as_bytes())
}

fn main() -> Result<()> {
  let mut args: Vec<_> = std::env::args().skip(1).collect();
  let development = args.last().is_some_and(|arg| arg == "--dev-srs");
  if development {
    args.pop();
  }
  let [
    config,
    expected_config,
    gl_artifact,
    gl_key,
    bn_artifact,
    bn_key,
    root_key,
    root_claims,
    envelope,
    output,
  ] = args.as_slice()
  else {
    return Err(USAGE.into());
  };
  let config_bytes = fs::read(config)?;
  if blake3::hash(&config_bytes).as_bytes() != &pin(expected_config)? {
    return Err(
      "core chain configuration differs from the independent pin".into(),
    );
  }
  let configuration: Configuration = serde_json::from_slice(&config_bytes)?;
  let gl_artifact = fs::read(gl_artifact)?;
  let gl_key = fs::read(gl_key)?;
  let bn_artifact = fs::read(bn_artifact)?;
  let bn_key = fs::read(bn_key)?;
  let verifier = Verifier::from_bytes(
    configuration,
    Assets {
      gl_artifact: &gl_artifact,
      gl_key: &gl_key,
      bn_artifact: &bn_artifact,
      bn_key: &bn_key,
    },
  )?;
  let setup = SetupClass::of(verifier.parameters());
  if setup != SetupClass::Ignition && !development {
    return Err(
      "terminal input preparation requires Ignition or explicit --dev-srs"
        .into(),
    );
  }
  let expected =
    Statement { key_digest: pin(root_key)?, claims_digest: pin(root_claims)? };
  let envelope_bytes = fs::read(envelope)?;
  let envelope = Envelope::from_bytes(&envelope_bytes)?;
  let prepared = verifier.prepare_terminal(&expected, &envelope)?;
  let configuration = prepared.configuration.to_json()?;
  let output = Path::new(output);
  fs::create_dir(output)?;
  let mut streams = serde_json::Map::new();
  for (name, bytes) in [
    ("key", &prepared.key),
    ("claims", &prepared.claims),
    ("proof", &prepared.proof),
    ("policy", &prepared.policy),
  ] {
    let path = format!("{name}.bin");
    fs::write(output.join(&path), bytes)?;
    streams.insert(name.into(), serde_json::json!({"path":path,"blake3":blake3::hash(bytes).to_hex().as_str()}));
  }
  streams.insert("format".into(), "ix-aiur-terminal-input-v1".into());
  streams.insert(
    "statement".into(),
    blake3::Hash::from_bytes(prepared.statement).to_hex().to_string().into(),
  );
  streams.insert("stage".into(), prepared.stage.into());
  let input = serde_json::to_vec_pretty(&serde_json::Value::Object(streams))?;
  let input_pin = blake3::hash(&input).to_hex().to_string();
  let configuration_pin = blake3::hash(&configuration).to_hex().to_string();
  let receipt = serde_json::json!({
    "format":"ix-aiur-terminal-preparation-v1","native_chain_verified":true,
    "setup":setup.label(),"core_configuration_blake3":expected_config,
    "chain_envelope_blake3":blake3::hash(&envelope_bytes).to_hex().as_str(),
    "root_key_blake3":root_key,"root_claims_blake3":root_claims,
    "policy_blake3":blake3::Hash::from_bytes(verifier.policy().digest()).to_hex().as_str(),
    "predecessor_stage":envelope.stage,"terminal_stage":prepared.stage,
    "input_manifest_blake3":input_pin,"configuration_blake3":configuration_pin,
  });
  fs::write(output.join("configuration.json"), configuration)?;
  fs::write(output.join("receipt.json"), serde_json::to_vec_pretty(&receipt)?)?;
  fs::write(output.join("input.json"), input)?;
  println!("{}", serde_json::to_string_pretty(&receipt)?);
  Ok(())
}
