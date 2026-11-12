//! Execute and prove a policy-authenticated BN compression layer.
//! The JSON configuration is trusted caller input, separate from proof advice.
use ix_proof_compression::{
  aiur_backend::{
    compress_bn::{
      Input, PolicyDigest, PublicInputs, Stage, StatementDigest, TraceLimits,
      VerifyingKeys, Wrapper,
    },
    compress_gl::{self, Capacity},
    kzg::{Compiler, MAX_TOTAL_ROWS, VerifyingKey},
    kzg_advice as wire,
  },
  kzg::VerifierParams,
  pipeline::{SetupClass, SetupConfig},
};
use multi_stark::config::ProofConfig;
use serde::{Deserialize, Serialize};
use std::{
  fs,
  path::{Path, PathBuf},
};

type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct Options {
  artifact: PathBuf,
  artifact_blake3: String,
  max_log_height: u8,
  quotient_degree: usize,
  #[serde(default)]
  development: bool,
  input: Option<SourceInput>,
  gl_predecessor: Option<GlPredecessor>,
}

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct SourceInput {
  policy: PathBuf,
  policy_blake3: String,
  statement_blake3: String,
  stage: u32,
  key: PathBuf,
  claims: PathBuf,
  proof: PathBuf,
  max_record_bytes: usize,
  max_trace_bytes: usize,
}

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct GlPredecessor {
  artifact: PathBuf,
  artifact_blake3: String,
  key: PathBuf,
  key_blake3: String,
  proof: PathBuf,
  root_key_blake3: String,
  root_claims_blake3: String,
  max_record_bytes: usize,
  max_trace_bytes: usize,
}

fn pin(text: &str) -> Result<[u8; 32]> {
  Ok(*blake3::Hash::from_hex(text)?.as_bytes())
}

fn save_report(out: &Path, report: &serde_json::Value) -> Result<()> {
  fs::write(out.join("report.json"), serde_json::to_vec_pretty(report)?)?;
  println!("{}", serde_json::to_string_pretty(report)?);
  Ok(())
}

fn prepare_input(
  predecessor: GlPredecessor,
  keys: &VerifyingKeys,
  parameters: &VerifierParams,
  out: &Path,
) -> Result<SourceInput> {
  let wrapper = compress_gl::Wrapper::from_bytes(
    &fs::read(predecessor.artifact)?,
    &pin(&predecessor.artifact_blake3)?,
  )?;
  let key = VerifyingKey::from_bytes(
    &fs::read(predecessor.key)?,
    &pin(&predecessor.key_blake3)?,
  )?;
  if !key.is_key_bound() {
    return Err("GL predecessor requires a key-bound transcript".into());
  }
  let statement = stark_verifier::compress_wrap::Statement {
    key_digest: pin(&predecessor.root_key_blake3)?,
    claims_digest: pin(&predecessor.root_claims_blake3)?,
  };
  let claim = wrapper.claim(&statement)?;
  let proof = key.decode_proof(&fs::read(predecessor.proof)?)?;
  key.verify(&claim, &proof)?;
  let source_key = wire::key_bytes(&key)?;
  let entry = claim[1].canonical_limbs_le();
  if entry[1..].iter().any(|&word| word != 0) {
    return Err("GL entry exceeds u32".into());
  }
  let policy = wire::Policy::new(
    parameters,
    *blake3::hash(&source_key).as_bytes(),
    u32::try_from(entry[0])?,
    keys.source_digest(),
    keys.entry,
  )?;
  let statement_digest = StatementDigest::from_root(&statement);
  let claims = wire::claims_bytes(&[claim])?;
  let proof = wire::proof_bytes(&proof)?;
  Input::from_source(
    PublicInputs {
      policy: PolicyDigest::from_trusted(policy.digest()),
      stage: Stage::FIRST,
      statement: statement_digest,
    },
    source_key.clone(),
    claims.clone(),
    proof.clone(),
    policy.to_bytes(),
  )?;
  for (name, bytes) in [
    ("predecessor-key.bin", source_key),
    ("predecessor-claims.bin", claims),
    ("predecessor-proof.bin", proof),
    ("policy.bin", policy.to_bytes()),
    ("statement.bin", statement.preimage().to_vec()),
  ] {
    fs::write(out.join(name), bytes)?;
  }
  Ok(SourceInput {
    policy: out.join("policy.bin"),
    policy_blake3: blake3::Hash::from_bytes(policy.digest())
      .to_hex()
      .to_string(),
    statement_blake3: blake3::Hash::from_bytes(*statement_digest.as_bytes())
      .to_hex()
      .to_string(),
    stage: Stage::FIRST.get(),
    key: out.join("predecessor-key.bin"),
    claims: out.join("predecessor-claims.bin"),
    proof: out.join("predecessor-proof.bin"),
    max_record_bytes: predecessor.max_record_bytes,
    max_trace_bytes: predecessor.max_trace_bytes,
  })
}

fn main() -> Result<()> {
  tracing_subscriber::fmt()
    .with_env_filter(tracing_subscriber::EnvFilter::from_default_env())
    .with_writer(std::io::stderr)
    .init();
  let args: Vec<_> = std::env::args_os().skip(1).collect();
  let [mode, options, out] = args.as_slice() else {
    return Err(
      "usage: compress_bn key|plan|prove TRUSTED_CONFIG_JSON NEW_OUTPUT".into(),
    );
  };
  let mode = mode.to_str().ok_or("invalid mode")?;
  if !matches!(mode, "key" | "plan" | "prove") {
    return Err("mode must be key, plan or prove".into());
  }
  let mut options: Options = serde_json::from_slice(&fs::read(options)?)?;
  let wrapper = Wrapper::from_bytes(
    &fs::read(&options.artifact)?,
    &pin(&options.artifact_blake3)?,
  )?;
  let capacity = Capacity {
    max_log_height: options.max_log_height,
    quotient_degree: options.quotient_degree,
  };
  let max_height = capacity.height()?;
  let out = Path::new(out);
  fs::create_dir(out)?;

  if mode == "key" {
    if options.input.is_some() {
      return Err("key preparation takes no predecessor input".into());
    }
    let compiler = Compiler::new(wrapper.plan())?;
    let fixed_height = compiler
      .inputs()
      .iter()
      .filter_map(|input| input.preprocessed.as_ref())
      .map(|matrix| matrix.values.len() / matrix.width)
      .max()
      .unwrap_or(2)
      .max(2);
    let config = capacity
      .config(&SetupConfig::from_env(options.development)?, fixed_height)?;
    let class = SetupClass::of(config.pcs().verifier_params());
    let parameters = config.pcs().verifier_params().clone();
    let keys = wrapper.verifying_key(config)?;
    fs::write(out.join("key.bin"), &keys.portable)?;
    fs::write(out.join("source-key.bin"), &keys.source)?;
    if let Some(predecessor) = options.gl_predecessor.take() {
      options.input = Some(prepare_input(
        predecessor,
        &keys,
        &parameters,
        &fs::canonicalize(out)?,
      )?);
      fs::write(out.join("input.json"), serde_json::to_vec_pretty(&options)?)?;
    }
    return save_report(
      out,
      &serde_json::json!({
        "format":"ix-aiur-compress-bn-key-v1", "setup":class.label(),
        "artifact_blake3":options.artifact_blake3, "entry":keys.entry,
        "portable_key_blake3":blake3::hash(&keys.portable).to_hex().as_str(),
        "source_key_blake3":blake3::hash(&keys.source).to_hex().as_str(),
        "max_log_height":options.max_log_height, "quotient_degree":options.quotient_degree,
      }),
    );
  }

  if options.gl_predecessor.is_some() {
    return Err(
      "GL predecessor projection is only available in key mode".into(),
    );
  }
  let source = options.input.ok_or("plan/prove requires predecessor input")?;
  let public = PublicInputs {
    policy: PolicyDigest::from_trusted(pin(&source.policy_blake3)?),
    stage: Stage::new(source.stage)?,
    statement: StatementDigest::new(pin(&source.statement_blake3)?),
  };
  let input = Input::from_source(
    public,
    fs::read(source.key)?,
    fs::read(source.claims)?,
    fs::read(source.proof)?,
    fs::read(source.policy)?,
  )?;
  let execution = wrapper.execute(&input, source.max_record_bytes)?;
  let profile = wrapper.profile(&execution)?;
  let mut report = serde_json::json!({
    "format":"ix-aiur-compress-bn-v1", "proof_verified":false,
    "pairing_deferred":true, "profile":profile,
  });
  save_report(out, &report)?;
  if mode == "plan" {
    return Ok(());
  }
  let limits = TraceLimits {
    max_height,
    max_total_rows: MAX_TOTAL_ROWS,
    max_trace_bytes: source.max_trace_bytes,
  };
  let setup = SetupConfig::from_env(options.development)?;
  let admission = capacity.config(&setup, 2)?;
  limits.check(&profile, &admission)?;
  if profile.quotient_degree > capacity.quotient_degree {
    return Err("execution exceeds the admitted quotient degree".into());
  }
  let config = capacity.config(&setup, profile.max_height)?;
  let class = SetupClass::of(config.pcs().verifier_params());
  let parameters = config.pcs().verifier_params().clone();
  let proven = wrapper.prove(&execution, config, limits)?;
  proven.accumulator.check_pairing(&parameters)?;
  for (name, bytes) in [
    ("key.bin", proven.keys.portable.as_slice()),
    ("source-key.bin", proven.keys.source.as_slice()),
    ("proof.bin", proven.proof.as_slice()),
    ("source-proof.bin", proven.source_proof.as_slice()),
    ("source-claims.bin", proven.source_claims.as_slice()),
  ] {
    fs::write(out.join(name), bytes)?;
  }
  report["proof_verified"] = true.into();
  report["native_accumulator_verified"] = true.into();
  report["setup"] = class.label().into();
  report["proof_bytes"] = proven.proof.len().into();
  report["setup_seconds"] = proven.setup_seconds.into();
  report["trace_seconds"] = proven.trace_seconds.into();
  report["proving_seconds"] = proven.proving_seconds.into();
  report["verification_seconds"] = proven.verification_seconds.into();
  save_report(out, &report)
}
