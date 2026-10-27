//! Inspect, import and authenticate a local Ignition SRS prefix.

use ix_proof_compression::kzg::srs::ignition::{
  FINAL_ADDRESS, FINAL_POSITION, IGNITION_MANIFEST_URL, IgnitionAdmission,
  MAX_G1_POINTS, MAX_PREFIX_LEN, PREDECESSOR_ADDRESS, PREDECESSOR_POSITION,
  SHIFTED_TAU_BASIS, import_ignition_transcripts, inspect_ignition_source,
  load_ignition_cache,
};
use std::{
  fs::{self, OpenOptions},
  io::Write,
  path::Path,
  time::Instant,
};

type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

const USAGE: &str = "usage: kzg_ignition_import info\n\
  kzg_ignition_import inspect <source-root> <new-candidate-manifest.json>\n\
  kzg_ignition_import import <source-root> <source-manifest.json> <trusted-source-manifest-blake3> <new-cache> <log-prefix:1..26>\n\
  kzg_ignition_import admission <cache> <trusted-cache-manifest-blake3> <source-manifest.json> <trusted-source-manifest-blake3> <new-admission.json>\n\
  kzg_ignition_import verify <cache> <trusted-cache-manifest-blake3> <log-prefix:1..26>";

fn hex(bytes: &[u8]) -> String {
  bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn digest(text: &str) -> Result<[u8; 32]> {
  if text.len() != 64 || !text.is_ascii() {
    return Err(
      "manifest digest must contain 64 hexadecimal characters".into(),
    );
  }
  let mut digest = [0; 32];
  for (i, byte) in digest.iter_mut().enumerate() {
    *byte = u8::from_str_radix(&text[2 * i..2 * i + 2], 16)?;
  }
  Ok(digest)
}

fn prefix(text: &str) -> Result<usize> {
  let log: u32 = text.parse()?;
  if !(1..=MAX_PREFIX_LEN.ilog2()).contains(&log) {
    return Err("prefix log must be in 1..=26".into());
  }
  Ok(1usize << log)
}

fn print(report: &serde_json::Value) -> Result<()> {
  println!("{}", serde_json::to_string_pretty(report)?);
  Ok(())
}

fn main() -> Result<()> {
  let args: Vec<_> = std::env::args().skip(1).collect();
  let start = Instant::now();
  match args.iter().map(String::as_str).collect::<Vec<_>>().as_slice() {
    ["info"] => print(&serde_json::json!({
      "curve": "bn254",
      "ceremony_manifest_url": IGNITION_MANIFEST_URL,
      "basis": SHIFTED_TAU_BASIS,
      "available_g1_entries": MAX_G1_POINTS,
      "public_max_degree": MAX_G1_POINTS - 1,
      "max_prefix_len": MAX_PREFIX_LEN,
      "contribution": {"position": FINAL_POSITION, "address": FINAL_ADDRESS},
      "predecessor": {"position": PREDECESSOR_POSITION, "address": PREDECESSOR_ADDRESS},
      "requires_independently_trusted_source_manifest": true,
    })),
    ["inspect", source, destination] => {
      let destination = Path::new(destination);
      if destination.try_exists()? {
        return Err("candidate manifest destination already exists".into());
      }
      eprintln!(
        "Hashing complete local contributions 196 and 197; output is an untrusted candidate, not ceremony authentication."
      );
      let manifest = inspect_ignition_source(
        Path::new(source),
        FINAL_POSITION,
        FINAL_ADDRESS,
        Some((PREDECESSOR_POSITION, PREDECESSOR_ADDRESS)),
      )?;
      let mut bytes = serde_json::to_vec_pretty(&manifest)?;
      bytes.push(b'\n');
      if let Some(parent) =
        destination.parent().filter(|p| !p.as_os_str().is_empty())
      {
        fs::create_dir_all(parent)?;
      }
      let mut file =
        OpenOptions::new().write(true).create_new(true).open(destination)?;
      file.write_all(&bytes)?;
      file.sync_all()?;
      print(&serde_json::json!({
        "candidate_manifest": destination,
        "candidate_manifest_blake3": blake3::hash(&bytes).to_hex().as_str(),
        "source_provenance_authenticated": false,
        "scope": "Observed file hashes and internal framing/checksums only. Independently authenticate the ceremony source before trusting this manifest digest.",
        "elapsed_seconds": start.elapsed().as_secs_f64(),
      }))
    },
    ["import", source, manifest, trusted, destination, log] => {
      let prefix_len = prefix(log)?;
      let trusted = digest(trusted)?;
      eprintln!(
        "Authenticating complete source files and validating {prefix_len} retained powers per selected contribution; the destination must be new."
      );
      let receipt = import_ignition_transcripts(
        Path::new(source),
        Path::new(manifest),
        trusted,
        Path::new(destination),
        prefix_len,
      )?;
      print(&serde_json::json!({
        "cache": destination,
        "prefix_len": receipt.prefix_len,
        "cache_manifest_blake3": hex(&receipt.digest),
        "source_manifest_blake3": hex(&receipt.source_manifest_digest),
        "setup_id": hex(&receipt.public_setup.id),
        "public_max_degree": receipt.public_setup.max_degree,
        "basis": SHIFTED_TAU_BASIS,
        "scope": "Source bytes authenticated against the caller's pinned manifest and retained powers validated; no participant-signature or full ceremony replay.",
        "elapsed_seconds": start.elapsed().as_secs_f64(),
      }))?;
      eprintln!(
        "Retain cache_manifest_blake3 in trusted configuration separately from the cache."
      );
      Ok(())
    },
    ["verify", cache, trusted, log] => {
      let srs =
        load_ignition_cache(Path::new(cache), digest(trusted)?, prefix(log)?)?;
      print(&serde_json::json!({
        "cache_authenticated": true,
        "loaded_prefix_len": srs.max_len(),
        "public_max_degree": srs.public_setup.max_degree,
        "setup_id": hex(&srs.public_setup.id),
        "basis": SHIFTED_TAU_BASIS,
        "elapsed_seconds": start.elapsed().as_secs_f64(),
      }))
    },
    [
      "admission",
      cache,
      trusted_cache,
      source,
      trusted_source,
      destination,
    ] => {
      let destination = Path::new(destination);
      if destination.try_exists()? {
        return Err("admission destination already exists".into());
      }
      let admission = IgnitionAdmission::from_cache(
        Path::new(cache),
        digest(trusted_cache)?,
        Path::new(source),
        digest(trusted_source)?,
      )?;
      let bytes = admission.to_bytes()?;
      if let Some(parent) =
        destination.parent().filter(|p| !p.as_os_str().is_empty())
      {
        fs::create_dir_all(parent)?;
      }
      let mut file =
        OpenOptions::new().write(true).create_new(true).open(destination)?;
      file.write_all(&bytes)?;
      file.sync_all()?;
      print(&serde_json::json!({
        "admission": destination,
        "admission_blake3": hex(blake3::hash(&bytes).as_bytes()),
        "source_manifest_blake3": hex(&admission.source_manifest_digest()),
        "setup_id": hex(&admission.public_setup().id),
        "public_max_degree": admission.public_setup().max_degree,
        "basis": SHIFTED_TAU_BASIS,
        "scope": "Portable authorization from the caller's trusted source and cache pins. The admission pin must be configured separately; no participant-signature or full ceremony replay.",
        "elapsed_seconds": start.elapsed().as_secs_f64(),
      }))?;
      eprintln!(
        "Retain admission_blake3 in trusted verifier configuration separately from the admission and proof."
      );
      Ok(())
    },
    _ => Err(USAGE.into()),
  }
}
