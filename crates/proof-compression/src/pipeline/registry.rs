//! Accepted development profiles, separate from untrusted proof/checkpoint storage.
use super::{PROOF_TAG, Result, wrap::VerifierProfile};
use std::{
  fs,
  io::{Read, Write},
  path::Path,
  sync::atomic::{AtomicU64, Ordering},
};
const LIMIT: u64 = 1 << 20;

fn hex(id: [u8; 32]) -> String {
  blake3::Hash::from(id).to_hex().to_string()
}
fn parse_hex(s: &str) -> Result<[u8; 32]> {
  if s.len() != 64 || !s.is_ascii() {
    return Err("expected a 64-character verifier digest".into());
  }
  let mut id = [0; 32];
  for (i, byte) in id.iter_mut().enumerate() {
    *byte = u8::from_str_radix(&s[2 * i..2 * i + 2], 16)?;
  }
  Ok(id)
}
fn read(path: &Path) -> Result<Vec<u8>> {
  let mut bytes = vec![];
  fs::File::open(path)?.take(LIMIT + 1).read_to_end(&mut bytes)?;
  if bytes.len() as u64 > LIMIT {
    return Err("verifier file too large".into());
  }
  Ok(bytes)
}
fn publish(path: &Path, bytes: &[u8]) -> Result<()> {
  static NEXT: AtomicU64 = AtomicU64::new(0);
  fs::create_dir_all(path.parent().ok_or("missing registry parent")?)?;
  let temp = path.with_extension(format!(
    "tmp-{}-{}",
    std::process::id(),
    NEXT.fetch_add(1, Ordering::Relaxed)
  ));
  let mut file =
    fs::OpenOptions::new().write(true).create_new(true).open(&temp)?;
  let result = (|| -> Result<()> {
    file.write_all(bytes)?;
    file.sync_all()?;
    match fs::hard_link(&temp, path) {
      Ok(()) => Ok(()),
      Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => {
        if read(path)? == bytes {
          Ok(())
        } else {
          Err(
            "conflicting registered verifier; existing entry preserved".into(),
          )
        }
      },
      Err(e) => Err(e.into()),
    }
  })();
  drop(file);
  let _ = fs::remove_file(temp);
  result
}

/// Called only after local compression, or with an independently authenticated digest on import.
pub fn register(
  file: &Path,
  registry: &Path,
  expected_digest: Option<&str>,
) -> Result<String> {
  let bytes = read(file)?;
  let digest = *blake3::hash(&bytes).as_bytes();
  if let Some(expected) = expected_digest
    && parse_hex(expected)? != digest
  {
    return Err("verifier digest mismatch; nothing registered".into());
  }
  let profile = VerifierProfile::from_bytes(&bytes)?;
  let id = hex(profile.id());
  let registry = registry.join("development");
  publish(&registry.join("keys").join(format!("{}.bin", hex(digest))), &bytes)?;
  publish(&registry.join("profiles").join(&id), &digest)?;
  Ok(id)
}

pub fn verify(registry: &Path, proof: &[u8], claim: &[u8]) -> Result<()> {
  super::check_claim(claim)?;
  let packet = proof
    .strip_prefix(PROOF_TAG)
    .ok_or("unsupported compressed proof version")?;
  let id: [u8; 32] =
    packet.get(..32).ok_or("truncated compressed proof")?.try_into()?;
  let registry = registry.join("development");
  let mapping = registry.join("profiles").join(hex(id));
  if !mapping.exists() {
    return Err(format!("unknown compression verifier {}; import an independently trusted verifier with ix verifier import FILE --digest HASH --dev-srs", hex(id)).into());
  }
  let digest: [u8; 32] = read(&mapping)?
    .try_into()
    .map_err(|_error| "invalid verifier registry entry")?;
  let bytes =
    read(&registry.join("keys").join(format!("{}.bin", hex(digest))))?;
  if blake3::hash(&bytes).as_bytes() != &digest {
    return Err("registered verifier digest mismatch".into());
  }
  let profile = VerifierProfile::from_bytes(&bytes)?;
  if profile.id() != id {
    return Err("registered verifier profile mismatch".into());
  }
  profile.verify(packet)
}

#[cfg(test)]
mod tests {
  use super::*;
  #[test]
  fn registration_never_overwrites_different_content() {
    let dir = std::env::temp_dir()
      .join(format!("ix-verifier-publish-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let path = dir.join("entry");
    publish(&path, b"trusted").unwrap();
    publish(&path, b"trusted").unwrap();
    assert!(publish(&path, b"different").is_err());
    assert_eq!(read(&path).unwrap(), b"trusted");
    fs::remove_dir_all(dir).unwrap();
  }
  #[test]
  fn digest_must_be_canonical_length_and_hex() {
    assert!(parse_hex("../untrusted").is_err());
    assert!(parse_hex(&"g".repeat(64)).is_err());
    assert_eq!(parse_hex(&"00".repeat(32)).unwrap(), [0; 32]);
  }
}
