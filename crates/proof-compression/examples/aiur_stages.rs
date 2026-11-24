//! Runs the compression stages of a manifest (`ix-aiur-stages-v1`) in this process, with the
//! Lean exporters as executables (`ix compress run-stages` links them
//! instead).
//!
//! `aiur_stages MANIFEST MANIFEST_BLAKE3 ROOT_DIR OUT_DIR --wide-export EXE
//! --tiling-export EXE [--cache DIR] [--memory-gb N] [--no-gpu-lock]`
//!
//! - `ROOT_DIR` holds `root-vk.bin`, `root-claims.bin` and `root-proof.bin`.
//! - `--cache` overrides the manifest's export cache directory.
//! - `--memory-gb` is the memory budget the stages reserve from (default:
//!   the manifest's `memory_gb`).
//!
//! `aiur_stages digest FILE...` prints each file's BLAKE3 and SHA-256, the
//! digests a manifest pins.
use ix_proof_compression::aiur_backend::stages::{
  Manifest, Options, Stages,
  exports::{Exports, Runner},
};
use std::path::{Path, PathBuf};

fn flag(args: &[String], name: &str) -> Option<String> {
  args.iter().position(|a| a == name).and_then(|i| args.get(i + 1)).cloned()
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
  tracing_subscriber::fmt()
    .with_env_filter(tracing_subscriber::EnvFilter::from_default_env())
    .with_writer(std::io::stderr)
    .init();
  let args: Vec<String> = std::env::args().skip(1).collect();
  if args.first().map(String::as_str) == Some("digest") {
    for file in &args[1..] {
      let bytes = std::fs::read(file)?;
      println!(
        "{} {} {file}",
        blake3::hash(&bytes).to_hex(),
        ix_proof_compression::aiur_backend::stages::sha256_hex(&bytes)
      );
    }
    return Ok(());
  }
  let [manifest_path, pin, root_dir, out, ..] = args.as_slice() else {
    return Err("usage: aiur_stages MANIFEST MANIFEST_BLAKE3 ROOT_DIR OUT_DIR --wide-export EXE --tiling-export EXE [--cache DIR] [--memory-gb N] [--no-gpu-lock]".into());
  };
  let manifest_path = std::path::absolute(manifest_path)?;
  let base = manifest_path.parent().unwrap_or(Path::new(".")).to_path_buf();
  let manifest = Manifest::new(&std::fs::read(&manifest_path)?, pin, &base)?;
  let cache = flag(&args, "--cache").map_or_else(
    || manifest.path(&manifest.value["cache"]),
    |c| Ok(PathBuf::from(c)),
  )?;
  let runner = Runner::Binaries {
    wide: flag(&args, "--wide-export").ok_or("--wide-export")?.into(),
    tiling2: flag(&args, "--tiling-export").ok_or("--tiling-export")?.into(),
  };
  let exports = Exports::new(&cache, runner, None)?;
  let memory_gb = match flag(&args, "--memory-gb") {
    Some(n) => n.parse()?,
    None => manifest.value["memory_gb"].as_f64().ok_or("manifest memory_gb")?,
  };
  let options = Options {
    root_dir: root_dir.into(),
    out: out.into(),
    memory_gb,
    gpu_lock: !args.iter().any(|a| a == "--no-gpu-lock"),
  };
  let stages = Stages::open(manifest, exports, &options)?;
  let (_, summary) = stages.run()?;
  println!("{}", serde_json::to_string_pretty(&summary)?);
  Ok(())
}
