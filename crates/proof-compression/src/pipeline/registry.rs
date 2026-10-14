//! Accepted verifier profiles, separate from untrusted proof/checkpoint
//! storage and filed by the trust class of their public setup.
use super::{PROOF_TAG, Result, setup::SetupClass, wrap::VerifierProfile};
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

/// Called only after local compression, or with an independently
/// authenticated digest on import. A development-setup verifier is filed
/// only with explicit permission.
pub fn register(
  file: &Path,
  registry: &Path,
  expected_digest: Option<&str>,
  allow_development: bool,
) -> Result<(SetupClass, String)> {
  let bytes = read(file)?;
  let digest = *blake3::hash(&bytes).as_bytes();
  if let Some(expected) = expected_digest
    && parse_hex(expected)? != digest
  {
    return Err("verifier digest mismatch; nothing registered".into());
  }
  let profile = VerifierProfile::from_bytes(&bytes)?;
  let class = SetupClass::of(&profile.verifier_params()?);
  if class == SetupClass::Development && !allow_development {
    return Err(
      "verifier uses the known-trapdoor development setup; pass --dev-srs to \
       register it (not production-secure)"
        .into(),
    );
  }
  let id = hex(profile.id());
  let registry = registry.join(class.label());
  publish(&registry.join("keys").join(format!("{}.bin", hex(digest))), &bytes)?;
  publish(&registry.join("profiles").join(&id), &digest)?;
  Ok((class, id))
}

/// Verify a compressed proof against its registered verifier and report the
/// setup class it was proved under. A development-setup proof is accepted
/// only with explicit permission.
pub fn verify(
  registry: &Path,
  proof: &[u8],
  claim: &[u8],
  allow_development: bool,
) -> Result<SetupClass> {
  super::check_claim(claim)?;
  let packet = proof
    .strip_prefix(PROOF_TAG)
    .ok_or("unsupported compressed proof version")?;
  let id: [u8; 32] =
    packet.get(..32).ok_or("truncated compressed proof")?.try_into()?;
  let Some(class) =
    [SetupClass::Filecoin, SetupClass::Development].into_iter().find(|class| {
      registry.join(class.label()).join("profiles").join(hex(id)).exists()
    })
  else {
    return Err(format!("unknown compression verifier {}; import an independently trusted verifier with ix verifier import FILE --digest HASH", hex(id)).into());
  };
  if class == SetupClass::Development && !allow_development {
    return Err(
      "compressed proof was produced under the known-trapdoor development \
       setup; pass --dev-srs to accept it (not production-secure)"
        .into(),
    );
  }
  let registry = registry.join(class.label());
  let digest: [u8; 32] = read(&registry.join("profiles").join(hex(id)))?
    .try_into()
    .map_err(|_error| "invalid verifier registry entry")?;
  let bytes =
    read(&registry.join("keys").join(format!("{}.bin", hex(digest))))?;
  if blake3::hash(&bytes).as_bytes() != &digest {
    return Err("registered verifier digest mismatch".into());
  }
  let profile = VerifierProfile::from_bytes(&bytes)?;
  if profile.id() != id || SetupClass::of(&profile.verifier_params()?) != class
  {
    return Err("registered verifier profile mismatch".into());
  }
  profile.verify(packet)?;
  Ok(class)
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
  #[test]
  fn unknown_profiles_are_rejected_before_any_setup_policy() {
    let dir = std::env::temp_dir()
      .join(format!("ix-verifier-unknown-{}", std::process::id()));
    let mut proof = PROOF_TAG.to_vec();
    proof.extend([7; 32]);
    for allow in [false, true] {
      let error = verify(&dir, &proof, b"wrong", allow).unwrap_err();
      assert!(error.to_string().contains("Init root claim"));
    }
  }
}
