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
//!
//! Release keys are derived from a clean state: the Ignition
//! SRS is checked against its pin whatever selected it, the variables that
//! redirect the SRS or a cache are refused, and the cache directories a mode
//! publishes to (`fixed-preprocessing`, or `plonk` and `groth16` with
//! `--finals`) must not hold entries yet, so no cached entry is adopted.
use ix_proof_compression::pipeline::{
  CompressConfig, FinalOptions, FixedRoot, backend_prefix, check_release_srs,
  derive_release,
};
use std::{fs, path::Path, time::Instant};

/// Variables that would let an unpinned setup or another cache directory
/// reach the derivation.
const REFUSED_VARIABLES: [&str; 5] = [
  "IX_KZG_SRS",
  "IX_KZG_SRS_CACHE",
  "IX_KZG_FIXED_CACHE",
  "IX_KZG_FILECOIN_CACHE",
  "IX_KZG_FILECOIN_MANIFEST",
];

/// Refuse a cache directory that already holds entries.
fn require_fresh(directory: &Path) -> Result<()> {
  match fs::read_dir(directory) {
    Ok(mut entries) => {
      if entries.next().is_some() {
        return Err(
          format!(
            "{} already holds entries; release keys are derived into a fresh \
             cache so that no cached entry is adopted",
            directory.display()
          )
          .into(),
        );
      }
      Ok(())
    },
    Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(()),
    Err(error) => Err(error.into()),
  }
}

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
  for variable in REFUSED_VARIABLES {
    if std::env::var_os(variable).is_some() {
      return Err(
        format!("{variable} is set; unset it to derive release keys").into(),
      );
    }
  }
  // The Ignition setup and the caches `ix compress` would use.
  let config =
    CompressConfig::from_env(Path::new(cache), false, FinalOptions::default())?;
  check_release_srs(&config.setup)?;
  if finals_only {
    require_fresh(&config.plonk_cache)?;
    require_fresh(&config.groth16_cache)?;
  } else {
    require_fresh(&config.fixed_cache)?;
  }
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
