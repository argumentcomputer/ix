//! Compress a separately authenticated Goldilocks compression wrapper.
//!
//! Usage: compress_wrap prepare|compress PACKAGE WRAPPER_DIR WRAPPER_KEY_BLAKE3
//!        ROOT_KEY_BLAKE3 EXPECTED_ROOT_CLAIMS OUT [CACHE] [--plonk] [--dev-srs]
//!
//! PACKAGE is trusted compiler output for CompressWrap::verify_root. The key
//! pins and expected original claim rows must come from the caller, independently
//! of WRAPPER_DIR. The PLONK public digest names a domain-separated statement of
//! the original key and claims, rather than the original Ix claim bytes alone.
use aiur::{artifact::Package, trace::stark::Parameters};
use ix_proof_compression::pipeline::{
  self, CompressConfig, CompressInput, FinalOptions, FinalSystem, FixedRoot,
};
use stark_verifier::compress_wrap::{
  Layout, Statement, Wrapper, decode_claims,
};
use std::{fs, path::Path};

type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

const USAGE: &str = "usage: compress_wrap prepare|compress PACKAGE WRAPPER_DIR WRAPPER_KEY_BLAKE3 ROOT_KEY_BLAKE3 EXPECTED_ROOT_CLAIMS OUT [CACHE] [--plonk] [--dev-srs]";

struct Checked {
  key: Vec<u8>,
  claims: Vec<u8>,
  proof: Vec<u8>,
  statement: Vec<u8>,
  layout: Vec<u8>,
}

fn pin(hex: &str) -> Result<[u8; 32]> {
  Ok(*blake3::Hash::from_hex(hex)?.as_bytes())
}

fn checked(
  package: &Path,
  dir: &Path,
  wrapper_pin: [u8; 32],
  root_pin: [u8; 32],
  expected_root_claims: &[u8],
) -> Result<Checked> {
  let root_claims = decode_claims(expected_root_claims)?;
  if root_claims.is_empty() {
    return Err("an independently expected root claim is required".into());
  }
  if fs::read(dir.join("root-claims.bin"))? != expected_root_claims {
    return Err(
      "exported root claims differ from the caller's statement".into(),
    );
  }
  if blake3::hash(&fs::read(dir.join("root-key.bin"))?).as_bytes() != &root_pin
  {
    return Err("exported root key differs from the caller's pin".into());
  }
  let (package, _) = Package::load(package)?;
  let wrapper = Wrapper::new(package, Parameters::DEFAULT, None)?;
  let key = fs::read(dir.join("key.bin"))?;
  if wrapper.key_digest() != &wrapper_pin
    || blake3::hash(&key).as_bytes() != &wrapper_pin
    || key != wrapper.key_bytes()
  {
    return Err(
      "wrapper artifact or exported key differs from the trusted pin".into(),
    );
  }
  let expected = Statement::new(root_pin, &root_claims);
  let statement = expected.preimage().to_vec();
  if fs::read(dir.join("statement.bin"))? != statement {
    return Err(
      "exported compression statement differs from the expected root".into(),
    );
  }
  let claims = stark_verifier::claims_bytes(&[wrapper.claim_for(&expected)?]);
  if fs::read(dir.join("claims.bin"))? != claims {
    return Err(
      "exported wrapper claims differ from its entry and root statement".into(),
    );
  }
  pipeline::check_claim(&statement, &claims)?;
  let proof = fs::read(dir.join("proof.bin"))?;
  let layout: Layout =
    serde_json::from_slice(&fs::read(dir.join("layout.json"))?)?;
  wrapper.verify_normalized(&expected, &proof, &layout)?;
  let fixed = FixedRoot::new(
    layout.log_heights,
    layout.memory_circuits,
    layout.claim_len,
  )?;
  Ok(Checked { key, claims, proof, statement, layout: fixed.to_bytes() })
}

fn main() -> Result<()> {
  let args: Vec<_> = std::env::args().skip(1).collect();
  let mut positional = Vec::new();
  let mut plonk = false;
  let mut development = false;
  for arg in &args {
    match arg.as_str() {
      "--plonk" => plonk = true,
      "--dev-srs" => development = true,
      flag if flag.starts_with("--") => {
        return Err(format!("unknown option {flag}; {USAGE}").into());
      },
      _ => positional.push(arg.as_str()),
    }
  }
  let [
    mode,
    package,
    source,
    wrapper_pin,
    root_pin,
    root_claims,
    out,
    rest @ ..,
  ] = positional.as_slice()
  else {
    return Err(USAGE.into());
  };
  if !matches!(*mode, "prepare" | "compress")
    || (*mode == "prepare" && (!rest.is_empty() || plonk || development))
    || (*mode == "compress" && rest.len() != 1)
  {
    return Err(USAGE.into());
  }
  if plonk && !cfg!(feature = "plonk") {
    return Err(
      "--plonk requires building this example with --features plonk".into(),
    );
  }
  let input = checked(
    Path::new(package),
    Path::new(source),
    pin(wrapper_pin)?,
    pin(root_pin)?,
    &fs::read(root_claims)?,
  )?;
  let out = Path::new(out);
  if *mode == "prepare" {
    pipeline::write_root_input(
      out,
      &input.key,
      &input.proof,
      &input.statement,
      &input.claims,
      Some(&input.layout),
    )?;
    fs::write(out.join("claim.bin"), &input.statement)?;
    println!("prepared authenticated wrapper input in {}", out.display());
    return Ok(());
  }
  let final_proof = FinalOptions {
    system: if plonk { FinalSystem::Plonk } else { FinalSystem::None },
    allow_development: development && plonk,
  };
  let config =
    CompressConfig::from_env(Path::new(rest[0]), development, final_proof)?;
  let compressed = pipeline::compress(
    CompressInput {
      vk: &input.key,
      proof: &input.proof,
      claim: &input.statement,
      statement: &input.claims,
      fixed_root: Some(&input.layout),
      out,
    },
    &config,
  )?;
  fs::write(out.join("claim.bin"), &input.statement)?;
  let key_path = out.join(if plonk {
    "plonk/verifying-key.bin"
  } else {
    "final-kzg/vk.bin"
  });
  let key = fs::read(&key_path)?;
  let key_digest = blake3::hash(&key);
  if !plonk {
    pipeline::verify_with_vk(
      &compressed,
      &input.statement,
      &input.claims,
      &key,
      key_digest.as_bytes(),
      development,
    )?;
  }
  println!(
    "{}",
    serde_json::json!({
      "format": "ix-compress-wrap-result-v1",
      "system": if plonk { "plonk" } else { "recursive-kzg" },
      "setup": if development { "development" } else { "ignition" },
      "proof_bytes": compressed.len(),
      "statement_blake3": blake3::hash(&input.statement).to_hex().as_str(),
      "candidate_key": key_path,
      "candidate_key_blake3": key_digest.to_hex().as_str(),
      "root_key_blake3": root_pin,
      "wrapper_key_blake3": wrapper_pin,
    })
  );
  eprintln!(
    "The candidate key is derived locally; consumers must authorize it independently."
  );
  Ok(())
}
