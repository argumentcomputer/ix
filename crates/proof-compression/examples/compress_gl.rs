//! Execute or prove a separately authenticated Goldilocks root over BN254.
//!
//! Artifact and root-key pins, and expected root claims, are caller inputs.
//! The proof cannot authorize its own verifier or choose a new public capacity.
use ix_proof_compression::{
  aiur_backend::compress_gl::{Capacity, Wrapper},
  pipeline::SetupConfig,
};
use stark_verifier::compress_wrap::Input;
use std::{fs, path::Path, time::Instant};

type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;
const USAGE: &str = "usage: compress_gl plan|prove PACKAGE ARTIFACT_BLAKE3 ROOT_KEY ROOT_KEY_BLAKE3 EXPECTED_ROOT_CLAIMS ROOT_PROOF OUT [MAX_LOG_HEIGHT QUOTIENT_DEGREE] [--dev-srs]";

fn pin(hex: &str) -> Result<[u8; 32]> {
  Ok(*blake3::Hash::from_hex(hex)?.as_bytes())
}

fn main() -> Result<()> {
  tracing_subscriber::fmt()
    .with_env_filter(tracing_subscriber::EnvFilter::from_default_env())
    .with_writer(std::io::stderr)
    .init();
  let args: Vec<_> = std::env::args().skip(1).collect();
  let mut development = false;
  let mut positional = Vec::new();
  for arg in &args {
    match arg.as_str() {
      "--dev-srs" if !development => development = true,
      flag if flag.starts_with("--") => {
        return Err(format!("unknown option {flag}; {USAGE}").into());
      },
      _ => positional.push(arg.as_str()),
    }
  }
  let [
    mode,
    package,
    artifact_pin,
    root_key,
    root_pin,
    root_claims,
    root_proof,
    out,
    capacity @ ..,
  ] = positional.as_slice()
  else {
    return Err(USAGE.into());
  };
  let capacity = match (*mode, capacity) {
    ("plan", []) if !development => None,
    ("prove", [max_log, quotient]) => Some(Capacity {
      max_log_height: max_log.parse()?,
      quotient_degree: quotient.parse()?,
    }),
    _ => return Err(USAGE.into()),
  };
  let started = Instant::now();
  eprintln!("authenticating compiler artifact and root input");
  let wrapper = Wrapper::from_bytes(&fs::read(package)?, &pin(artifact_pin)?)?;
  let root_key = fs::read(root_key)?;
  let root_claims = fs::read(root_claims)?;
  let input = Input::from_bytes(
    &root_key,
    pin(root_pin)?,
    &root_claims,
    &fs::read(root_proof)?,
  )?;
  let load_seconds = started.elapsed().as_secs_f64();
  let out = Path::new(out);
  if out.exists() {
    if !out.is_dir() || fs::read_dir(out)?.next().is_some() {
      return Err("output directory must be new or empty".into());
    }
  } else {
    fs::create_dir_all(out)?;
  }
  eprintln!("executing CompressGL::verify_root");
  let execution = wrapper.execute(&input)?;
  eprintln!("counting compiled trace rows");
  let profile = wrapper.profile(&execution)?;
  let report = serde_json::json!({
    "format": "ix-aiur-compress-gl-v1", "proof_verified": false,
    "load_seconds": load_seconds, "profile": profile,
  });
  fs::write(out.join("report.json"), serde_json::to_vec_pretty(&report)?)?;
  fs::write(out.join("root-key.bin"), root_key)?;
  fs::write(out.join("root-claims.bin"), root_claims)?;
  fs::write(out.join("statement.bin"), input.statement().preimage())?;
  let Some(capacity) = capacity else {
    println!("{}", serde_json::to_string_pretty(&report)?);
    return Ok(());
  };
  eprintln!(
    "proving {} main cells across {} circuits",
    profile.main_cells,
    profile.circuits.len()
  );
  let proven = wrapper.prove(
    &execution,
    &SetupConfig::from_env(development)?,
    capacity,
  )?;
  let mut claim = Vec::with_capacity(proven.claim.len() * 32);
  for value in &proven.claim {
    for limb in value.canonical_limbs_le() {
      claim.extend_from_slice(&limb.to_le_bytes());
    }
  }
  fs::write(out.join("key.bin"), &proven.key)?;
  fs::write(out.join("proof.bin"), &proven.proof)?;
  fs::write(out.join("claim.bin"), claim)?;
  let report = serde_json::json!({
    "format": "ix-aiur-compress-gl-v1", "proof_verified": true,
    "load_seconds": load_seconds, "profile": proven.profile,
    "capacity": proven.capacity, "setup": proven.setup,
    "setup_seconds": proven.setup_seconds, "trace_seconds": proven.trace_seconds,
    "proving_seconds": proven.proving_seconds, "verification_seconds": proven.verification_seconds,
    "proof_bytes": proven.proof.len(), "candidate_key_bytes": proven.key.len(),
    "candidate_key_blake3": blake3::hash(&proven.key).to_hex().as_str(),
    "peak_resident_bytes": aiur::trace::stark::planning::peak_resident_memory(),
  });
  fs::write(out.join("report.json"), serde_json::to_vec_pretty(&report)?)?;
  println!("{}", serde_json::to_string_pretty(&report)?);
  eprintln!(
    "The candidate key requires independent authorization by consumers."
  );
  Ok(())
}
