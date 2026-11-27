//! Derive the pins of a verifying-key release from trusted inputs alone, as
//! `ix compress setup` derives and checks them: the aggregation and IxVM
//! keys (`stark-verifier key` and `ixvm-proof key` directories), the root
//! layout (`.ixl`, from `ix compress layout`) and the Ignition SRS that
//! `IX_PARAMS_DIR` or `IX_KZG_SRS` selects. No proof is read.
//!
//! Usage: release_keys IXVM_KEY_DIR AGGR_KEY_DIR LAYOUT OUT_DIR CACHE_ROOT
//!        release_keys --finals IXVM_KEY_DIR AGGR_KEY_DIR RECURSIVE_VK OUT_DIR
//!          CACHE_ROOT
//!
//! Writes `root-layout.ixl` and `recursive-vk.bin` to `OUT_DIR`, then prints
//! every pin of `pipeline/verifying_keys.rs`. With `--features plonk` or
//! `--features groth16`, also prints `FINAL_SCHEMA_SHA256` (legacy Go/gnark
//! final key derivation has been retired in favor of
//! `aiur_backend::plonk::native` and `aiur_backend::groth16`). `--finals`
//! starts from an existing recursive key and prints only the final schema pin.
//! `CACHE_ROOT` is the cache root `ix compress` reads
//! (`~/.ix/compression/cache`): both stages' fixed preprocessing is published
//! to its `fixed-preprocessing` (or `IX_KZG_FIXED_CACHE`), where a later
//! compression finds them.
use ix_proof_compression::pipeline::{
  CompressConfig, FinalOptions, FixedRoot, backend_prefix, derive_release,
};
use std::{fs, path::Path, time::Instant};

type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

fn hex(bytes: &[u8]) -> String {
  bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// A key directory's `key.bin` and the function index its `identity.json`
/// names.
fn identity(dir: &Path) -> Result<(Vec<u8>, u64)> {
  let key = fs::read(dir.join("key.bin"))?;
  let json: serde_json::Value =
    serde_json::from_slice(&fs::read(dir.join("identity.json"))?)?;
  if json["call_channel"].as_u64() != Some(1) {
    return Err("unexpected call channel".into());
  }
  let index = json["function_index"].as_u64().ok_or("missing index")?;
  if json["key_digest"].as_str() != Some(blake3::hash(&key).to_hex().as_str()) {
    return Err("key digest differs from identity.json".into());
  }
  Ok((key, index))
}

fn main() -> Result<()> {
  let args: Vec<String> = std::env::args().collect();
  let usage = "usage: release_keys IXVM_KEY_DIR AGGR_KEY_DIR LAYOUT OUT_DIR CACHE_ROOT\n       release_keys --finals IXVM_KEY_DIR AGGR_KEY_DIR RECURSIVE_VK OUT_DIR CACHE_ROOT";
  let finals_only = args.get(1).map(String::as_str) == Some("--finals");
  let args = &args[1 + usize::from(finals_only)..];
  let [ixvm_dir, aggr_dir, input, out, cache] = args else {
    return Err(usage.into());
  };
  let out = Path::new(out);
  fs::create_dir_all(out)?;
  let (ixvm_key, ixvm_index) = identity(Path::new(ixvm_dir))?;
  let (aggr_key, aggr_index) = identity(Path::new(aggr_dir))?;
  let prefix = backend_prefix(&ixvm_key, ixvm_index, &aggr_key, aggr_index);
  // The Ignition setup and the caches `ix compress` would use.
  let config =
    CompressConfig::from_env(Path::new(cache), false, FinalOptions::default())?;
  println!("ROOT_VK_BLAKE3 = {}", blake3::hash(&aggr_key).to_hex());
  println!("STATEMENT_PREFIX = {prefix:?}");
  let recursive_vk = if finals_only {
    fs::read(input)?
  } else {
    let layout = fs::read(input)?;
    // Reject a non-canonical layout before spending hours on it.
    if FixedRoot::from_bytes(&layout)?.to_bytes() != layout {
      return Err("layout is not canonical".into());
    }
    fs::write(out.join("root-layout.ixl"), &layout)?;
    println!("LAYOUT_BLAKE3 = {}", blake3::hash(&layout).to_hex());
    let start = Instant::now();
    let release =
      derive_release(&aggr_key, &layout, &config.setup, &config.fixed_cache)?;
    eprintln!("recursive key derived in {:?}", start.elapsed());
    fs::write(out.join("recursive-vk.bin"), &release.recursive_vk)?;
    println!("RECURSIVE_VK_ID = {}", hex(&release.recursive_vk_id));
    println!("FIRST_PLAN_ID = {}", hex(&release.first_plan_id));
    println!("RECURSIVE_FRONTEND_ID = {}", hex(&release.recursive_frontend_id));
    release.recursive_vk
  };
  println!("RECURSIVE_VK_BLAKE3 = {}", blake3::hash(&recursive_vk).to_hex());
  #[cfg(any(feature = "plonk", feature = "groth16"))]
  finals(&recursive_vk, &prefix, out)?;
  #[cfg(not(any(feature = "plonk", feature = "groth16")))]
  eprintln!("built without plonk or groth16: no final schema derived");
  Ok(())
}

#[cfg(any(feature = "plonk", feature = "groth16"))]
fn finals(recursive_vk: &[u8], prefix: &[u64; 10], out: &Path) -> Result<()> {
  use sha2::{Digest, Sha256};
  let schema =
    ix_proof_compression::pipeline::final_schema(recursive_vk, prefix)?;
  let schema_path = out.join("final-schema.json");
  fs::write(&schema_path, &schema)?;
  println!("FINAL_SCHEMA_SHA256 = {}", hex(&Sha256::digest(&schema)));
  eprintln!(
    "legacy Go/gnark final key derivation has been retired; use \
     aiur_backend::plonk::native or aiur_backend::groth16 for final keys"
  );
  Ok(())
}
