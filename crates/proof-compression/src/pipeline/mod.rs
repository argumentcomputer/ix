//! Checkpointed Init compression and verification.
mod first;
mod init_claim;
mod init_fri;
pub mod registry;
mod root;
mod setup;
mod storage;
mod wrap;

use std::{
  fs,
  path::Path,
  process::{Command, Stdio},
};

pub const PROOF_TAG: &[u8; 8] = b"IXCMP\0\0\x04";
pub type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

pub fn command(stage: &str, args: &[String]) -> Result<()> {
  match stage {
    "fri" => root::run(args),
    "kzg" => first::run(args),
    "wrap" => wrap::run(args),
    _ => Err("unknown compression stage".into()),
  }
}

/// The subprocess entry point used by the statically linked ix executable.
pub fn worker(json: &str) -> Result<()> {
  let (stage, args): (String, Vec<String>) = serde_json::from_str(json)?;
  command(&stage, &args)
}

fn child(stage: &str, args: &[&str]) -> Result<()> {
  let json = serde_json::to_string(&(stage, args))?;
  let status = Command::new(std::env::current_exe()?)
    .arg("--compression-worker")
    .arg(json)
    .stdout(Stdio::from(std::io::stderr()))
    .stderr(Stdio::inherit())
    .status()?;
  if !status.success() {
    return Err(
      format!("compression {stage} failed ({status}); checkpoints retained")
        .into(),
    );
  }
  Ok(())
}

pub fn check_claim(claim: &[u8]) -> Result<()> {
  let digest = blake3::hash(claim);
  for (bytes, expected) in digest
    .as_bytes()
    .as_chunks::<4>()
    .0
    .iter()
    .zip(&init_claim::INIT_PUBLIC_WORDS[10..])
  {
    if u64::from(u32::from_le_bytes(*bytes)) != *expected {
      return Err(
        "compression currently supports only the measured Init root claim"
          .into(),
      );
    }
  }
  Ok(())
}

pub fn verify(dir: &Path, proof: &[u8], claim: &[u8]) -> Result<()> {
  check_claim(claim)?;
  let packet = proof
    .strip_prefix(PROOF_TAG)
    .ok_or("unsupported compressed proof version")?;
  wrap::verify(dir, packet)
}

fn identity(
  vk: &[u8],
  proof: &[u8],
  claim: &[u8],
  log_height: u32,
) -> blake3::Hash {
  let mut h = blake3::Hasher::new();
  h.update(b"ix-compress-run/v4");
  for bytes in [vk, proof, claim] {
    h.update(&(bytes.len() as u64).to_le_bytes());
    h.update(bytes);
  }
  h.update(&log_height.to_le_bytes());
  h.finalize()
}

/// Runs the three measured profiles. Every heavy phase exits before the next starts.
pub fn compress(
  vk: &[u8],
  proof: &[u8],
  claim: &[u8],
  out: &Path,
  resume: bool,
  resident: bool,
  log_height: u32,
) -> Result<Vec<u8>> {
  check_claim(claim)?;
  if !matches!(log_height, 24 | 25) {
    return Err(
      "--log-height must be 24 or 25 for the supported recursive profiles"
        .into(),
    );
  }
  if std::env::var_os("IX_ROOT_GENERIC_HASHES").is_some() {
    return Err(
      "unset IX_ROOT_GENERIC_HASHES for the supported compression profile"
        .into(),
    );
  }
  fs::create_dir_all(out)?;
  let lock = out.join("run.lock");
  let guard = fs::OpenOptions::new()
    .write(true)
    .create_new(true)
    .open(&lock)
    .map_err(|e| {
    format!(
      "cannot lock {}: {e}; remove a stale lock only after its process exits",
      lock.display()
    )
  })?;
  struct Lock<'a>(&'a Path, fs::File);
  impl Drop for Lock<'_> {
    fn drop(&mut self) {
      let _ = self.1.sync_all();
      let _ = fs::remove_file(self.0);
    }
  }
  let _guard = Lock(&lock, guard);
  let id = identity(vk, proof, claim, log_height);
  let marker = out.join("input-id.bin");
  if marker.exists() {
    if !resume {
      return Err(
        "output already initialized; use --resume or a new --out directory"
          .into(),
      );
    }
    if fs::read(&marker)? != id.as_bytes() {
      return Err("resume input or compression profile differs".into());
    }
  } else {
    if fs::read_dir(out)?.count() != 1 {
      return Err("output must be empty for a new run".into());
    }
    fs::write(&marker, id.as_bytes())?;
  }
  let root = out.join("root");
  fs::create_dir_all(&root)?;
  fs::write(root.join("root-vk.bin"), vk)?;
  fs::write(root.join("root-proof.bin"), proof)?;
  let mut claims = Vec::new();
  for word in [1, 18].into_iter().chain(init_claim::INIT_PUBLIC_WORDS) {
    claims.extend(word.to_le_bytes());
  }
  fs::write(root.join("root-claims.bin"), claims)?;
  let fri = out.join("fri");
  let first = out.join("first-kzg");
  let final_dir = out.join("final-kzg");
  let path = |p: &Path| -> Result<String> {
    Ok(p.to_str().ok_or("non-UTF8 output path")?.to_owned())
  };
  let (root_s, fri_s, first_s, final_s) =
    (path(&root)?, path(&fri)?, path(&first)?, path(&final_dir)?);
  // Recheck the source even when resuming an existing run.
  child("fri", &[&root_s, &fri_s, "--native-only"])?;
  if !["outer-proof.bin", "outer-vk.bin", "outer-claims.bin"]
    .iter()
    .all(|p| fri.join(p).exists())
  {
    child("fri", &[&root_s, &fri_s, "--prove-outer"])?;
  }
  if !first.join("manifest.bin").exists() {
    child("kzg", &["stage", &fri_s, &first_s, &log_height.to_string()])?;
  }
  let prove = |stage, dir: &str| {
    let mut args = vec!["prove", dir];
    if resident {
      args.push("--resident");
    }
    child(stage, &args)
  };
  if !first.join("kzg/packet.bin").exists() {
    prove("kzg", &first_s)?;
  } else {
    child("kzg", &["verify", &first_s])?;
  }
  if !final_dir.join("manifest.bin").exists() {
    child("wrap", &["stage", &first_s, &final_s])?;
  }
  if !final_dir.join("kzg/packet.bin").exists() {
    prove("wrap", &final_s)?;
  } else {
    child("wrap", &["verify", &final_s])?;
  }
  let mut result = PROOF_TAG.to_vec();
  result.extend(fs::read(final_dir.join("kzg/packet.bin"))?);
  Ok(result)
}

#[cfg(test)]
mod tests {
  use super::*;
  #[test]
  fn resume_identity_binds_all_inputs() {
    let id = identity(b"vk", b"proof", b"claim", 24);
    for (vk, proof, claim, height) in [
      (&b"VK"[..], &b"proof"[..], &b"claim"[..], 24),
      (b"vk", b"PROOF", b"claim", 24),
      (b"vk", b"proof", b"CLAIM", 24),
      (b"vk", b"proof", b"claim", 25),
    ] {
      assert_ne!(id, identity(vk, proof, claim, height));
    }
    assert_ne!(
      identity(b"a", b"bc", b"d", 24),
      identity(b"ab", b"c", b"d", 24)
    );
  }
  #[test]
  fn unsupported_claim_is_rejected_before_io() {
    assert!(
      compress(
        b"",
        b"",
        b"wrong",
        Path::new("/does-not-exist"),
        false,
        false,
        24
      )
      .is_err()
    );
    assert!(verify(Path::new("/does-not-exist"), PROOF_TAG, b"wrong").is_err());
  }
}
