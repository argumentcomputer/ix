//! Saved-proof compression and verification with an explicitly pinned profile.

use super::{Result, setup::SetupConfig, storage};
use crate::kzg::curve;
use std::{fs, path::Path};

const USAGE: &str = "usage: ix-compression-worker pipeline run <root-dir> <claim-file> <output-dir> [24|25] [--dev-srs]\n       ix-compression-worker pipeline run-fri <fri-dir> <claim-file> <root-claims.bin> <output-dir> [24|25] [--dev-srs]\n       ix-compression-worker pipeline verify <proof.envelope.bin> <claim-file> <root-claims.bin> <verifier.bin> <trusted-profile-blake3> [--dev-srs]";

fn arguments(args: &[String]) -> Result<(Vec<&str>, bool)> {
  let mut positional = Vec::new();
  let mut development = false;
  for arg in args {
    if arg == "--dev-srs" {
      if development {
        return Err("duplicate --dev-srs".into());
      }
      development = true;
    } else if arg.starts_with("--") {
      return Err(format!("unknown pipeline option: {arg}").into());
    } else {
      positional.push(arg.as_str());
    }
  }
  Ok((positional, development))
}

fn height(args: &[&str]) -> Result<u32> {
  let height =
    args.first().map(|value| value.parse()).transpose()?.unwrap_or(24);
  if args.len() > 1 || !matches!(height, 24 | 25) {
    return Err("pipeline log-height must be 24 or 25".into());
  }
  Ok(height)
}

fn digest(text: &str) -> Result<[u8; 32]> {
  if text.len() != 64 || !text.is_ascii() {
    return Err(
      "trusted profile BLAKE3 must contain exactly 64 hexadecimal characters"
        .into(),
    );
  }
  let mut digest = [0; 32];
  for (i, byte) in digest.iter_mut().enumerate() {
    *byte = u8::from_str_radix(&text[2 * i..2 * i + 2], 16)?;
  }
  Ok(digest)
}

fn publish(
  out: &Path,
  envelope: &[u8],
  expected: &[u8],
  source: &str,
  development: bool,
) -> Result<()> {
  let profile_path = out.join("final-kzg/verifier.bin");
  let profile = fs::read(&profile_path)?;
  storage::write_atomic(&out.join("proof.envelope.bin"), envelope)?;
  storage::write_atomic(&out.join("expected-root-claims.bin"), expected)?;
  let report = serde_json::json!({
    "format": "ix-saved-compression-run/v1",
    "curve": curve::NAME,
    "input_stage": source,
    "known_trapdoor": development,
    "cuda": cfg!(feature = "cuda"),
    "parallel": cfg!(feature = "parallel"),
    "native_verification_passed": true,
    "proof_bytes": envelope.len(),
    "proof_blake3": blake3::hash(envelope).to_hex().as_str(),
    "profile": "final-kzg/verifier.bin",
    "profile_blake3": blake3::hash(&profile).to_hex().as_str(),
    "expected_root_claims": "expected-root-claims.bin",
  });
  storage::write_atomic(
    &out.join("pipeline-report.json"),
    &serde_json::to_vec_pretty(&report)?,
  )?;
  println!("{}", serde_json::to_string_pretty(&report)?);
  Ok(())
}

pub(super) fn run(args: &[String]) -> Result<()> {
  let (positional, development) = arguments(args)?;
  let Some((command, args)) = positional.split_first() else {
    return Err(USAGE.into());
  };
  match (*command, args) {
    ("run", [root, claim, out, log @ ..]) if log.len() <= 1 => {
      let log_height = height(log)?;
      SetupConfig::from_env(development)?;
      let root = Path::new(root);
      let out = Path::new(out);
      let claim = fs::read(claim)?;
      let expected = fs::read(root.join("root-claims.bin"))?;
      let envelope = super::compress(
        &fs::read(root.join("root-vk.bin"))?,
        &fs::read(root.join("root-proof.bin"))?,
        &claim,
        &expected,
        out,
        &out.join("cache"),
        development,
        log_height,
        false,
      )?;
      publish(out, &envelope, &expected, "root", development)
    },
    ("run-fri", [fri, claim, expected, out, log @ ..]) if log.len() <= 1 => {
      let log_height = height(log)?;
      SetupConfig::from_env(development)?;
      let out = Path::new(out);
      let expected = fs::read(expected)?;
      let envelope = super::compress_fri(
        Path::new(fri),
        &fs::read(claim)?,
        &expected,
        out,
        &out.join("cache"),
        development,
        log_height,
      )?;
      publish(out, &envelope, &expected, "fri", development)
    },
    ("verify", [proof, claim, expected, profile, trusted]) => {
      let trusted = digest(trusted)?;
      let class = super::verify_with_profile(
        &fs::read(proof)?,
        &fs::read(claim)?,
        &fs::read(expected)?,
        &fs::read(profile)?,
        &trusted,
        development,
      )?;
      println!(
        "{}",
        serde_json::json!({
          "curve": curve::NAME,
          "verified": true,
          "setup": class.label(),
          "profile_blake3": blake3::Hash::from_bytes(trusted).to_hex().as_str(),
        })
      );
      Ok(())
    },
    _ => Err(USAGE.into()),
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn options_and_profile_digest_are_explicit() {
    let args = ["run", "root", "claim", "out", "--dev-srs"].map(str::to_owned);
    let (positional, development) = arguments(&args).unwrap();
    assert_eq!(positional, ["run", "root", "claim", "out"]);
    assert!(development);
    assert!(arguments(&["--dev-srs".into(), "--dev-srs".into()]).is_err());
    assert!(arguments(&["--unknown".into()]).is_err());
    assert_eq!(height(&[]).unwrap(), 24);
    assert_eq!(height(&["25"]).unwrap(), 25);
    assert!(height(&["28"]).is_err());
    assert!(height(&["24", "25"]).is_err());
    assert_eq!(digest(&"a5".repeat(32)).unwrap(), [0xa5; 32]);
    for text in ["ab".repeat(31), "gg".repeat(32), "é".repeat(32)] {
      assert!(digest(&text).is_err());
    }
  }
}
