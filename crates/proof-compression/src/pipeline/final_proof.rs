//! Shared transport and artifact checks for final proof backends.
use super::Result;
#[cfg(any(feature = "plonk", feature = "groth16"))]
use super::statement;
#[cfg(all(test, any(feature = "plonk", feature = "groth16")))]
use super::storage;
use serde::{Deserialize, Serialize};
#[cfg(any(feature = "plonk", feature = "groth16"))]
use sha2::{Digest, Sha256};
use std::{fs, io::Read, path::Path};

#[cfg(all(test, any(feature = "plonk", feature = "groth16")))]
use std::path::PathBuf;

// TODO: Decide between SHA-256 and BLAKE3 for artifact/cache metadata.
// Coordinate Rust/Go encodings and any catalog or envelope key-ID changes;
// proof-protocol hashes have separate compatibility requirements.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "PascalCase", deny_unknown_fields)]
pub struct Artifact {
  #[serde(rename = "SHA256")]
  pub sha256: String,
  pub bytes: u64,
}

#[derive(
  Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize,
)]
#[serde(rename_all = "lowercase")]
#[repr(u8)]
pub enum FinalSystem {
  #[default]
  None = 0,
  Plonk = 1,
  Groth16 = 2,
}

impl TryFrom<u8> for FinalSystem {
  type Error = &'static str;
  fn try_from(value: u8) -> std::result::Result<Self, Self::Error> {
    match value {
      0 => Ok(Self::None),
      1 => Ok(Self::Plonk),
      2 => Ok(Self::Groth16),
      _ => Err("unknown final proof system"),
    }
  }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct FinalOptions {
  pub system: FinalSystem,
  pub allow_development: bool,
}

impl From<FinalSystem> for FinalOptions {
  fn from(system: FinalSystem) -> Self {
    Self { system, allow_development: false }
  }
}

impl FinalOptions {
  /// A development inner verifier needs separately prepared final keys; the
  /// production final keys remain bound to the admitted inner verifier.
  pub(super) fn validate_setup(
    self,
    development_kzg: bool,
  ) -> std::result::Result<(), &'static str> {
    if development_kzg
      && self.system != FinalSystem::None
      && !self.allow_development
    {
      return Err(
        "development inner KZG requires --dev-final-srs with a final proof",
      );
    }
    if self.allow_development {
      match self.system {
        FinalSystem::None => {
          return Err("--dev-final-srs requires a final proof system");
        },
        FinalSystem::Plonk | FinalSystem::Groth16 => {},
      }
    }
    Ok(())
  }
}

/// Reconstruct the final circuit from the authenticated inner key and expected
/// program prefix, independently of any saved final proof or witness.
#[cfg(any(feature = "plonk", feature = "groth16"))]
pub(super) fn description(
  verifier: &Path,
  expected: &statement::Statement,
  setup: &super::SetupConfig,
) -> Result<Vec<u8>> {
  let vk = super::wrap::VerifyingKey::from_bytes(&fs::read(verifier)?)?;
  match setup.ignition_admission() {
    Some(admission) => vk.check_ignition_admission(admission)?,
    None => vk.check_setup_class(setup.class())?,
  }
  super::wrap::final_description(&vk, &expected[..10])
}

#[cfg(all(test, any(feature = "plonk", feature = "groth16")))]
pub(super) struct Scratch(pub(super) PathBuf);
#[cfg(all(test, any(feature = "plonk", feature = "groth16")))]
impl Scratch {
  pub(super) fn new() -> Result<Self> {
    let path = storage::temporary_path(&std::env::temp_dir().join("ix-final"));
    fs::create_dir(&path)?;
    Ok(Self(path))
  }
}
#[cfg(all(test, any(feature = "plonk", feature = "groth16")))]
impl Drop for Scratch {
  fn drop(&mut self) {
    let _ = fs::remove_dir_all(&self.0);
  }
}

#[cfg(any(feature = "plonk", feature = "groth16"))]
pub(super) fn hex(bytes: &[u8]) -> String {
  use std::fmt::Write as _;
  let mut output = String::with_capacity(bytes.len() * 2);
  for byte in bytes {
    write!(output, "{byte:02x}").unwrap();
  }
  output
}

pub(super) fn decode_hex(text: &str) -> Result<Vec<u8>> {
  let text = text.strip_prefix("0x").unwrap_or(text);
  if !text.is_ascii() || !text.len().is_multiple_of(2) {
    return Err("invalid hexadecimal bytes".into());
  }
  (0..text.len())
    .step_by(2)
    .map(|i| Ok(u8::from_str_radix(&text[i..i + 2], 16)?))
    .collect()
}

pub(super) fn digest(text: &str) -> Result<[u8; 32]> {
  decode_hex(text)?
    .try_into()
    .map_err(|_bytes| "expected a 32-byte hexadecimal digest".into())
}

#[cfg(any(feature = "plonk", feature = "groth16"))]
pub(super) fn sha256(path: &Path) -> Result<[u8; 32]> {
  let mut file = fs::File::open(path)?;
  let mut hash = Sha256::new();
  let mut buffer = vec![0; 65536];
  loop {
    let count = file.read(&mut buffer)?;
    if count == 0 {
      break;
    }
    hash.update(&buffer[..count]);
  }
  Ok(hash.finalize().into())
}

pub(super) fn read_bounded(path: &Path, limit: usize) -> Result<Vec<u8>> {
  let mut bytes = Vec::new();
  fs::File::open(path)?.take((limit + 1) as u64).read_to_end(&mut bytes)?;
  if bytes.len() > limit {
    return Err("final input exceeds its size limit".into());
  }
  Ok(bytes)
}

pub(super) fn load_json<T: serde::de::DeserializeOwned>(
  path: &Path,
) -> Result<T> {
  Ok(serde_json::from_slice(&read_bounded(path, 1 << 20)?)?)
}

#[cfg(any(feature = "plonk", feature = "groth16"))]
pub(super) fn claim_digest(
  expected: &statement::Statement,
) -> Result<[u8; 32]> {
  let mut result = [0; 32];
  for (chunk, value) in
    result.as_chunks_mut::<4>().0.iter_mut().zip(&expected[10..])
  {
    *chunk = u32::try_from(*value)?.to_le_bytes();
  }
  Ok(result)
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn final_selection_keeps_development_explicit() {
    for (tag, system) in [
      (0, FinalSystem::None),
      (1, FinalSystem::Plonk),
      (2, FinalSystem::Groth16),
    ] {
      assert_eq!(FinalSystem::try_from(tag).unwrap(), system);
      assert!(!FinalOptions::from(system).allow_development);
    }
    assert!(FinalSystem::try_from(3).is_err());
    assert!(FinalSystem::try_from(4).is_err());
    for system in [FinalSystem::None, FinalSystem::Plonk, FinalSystem::Groth16]
    {
      for development_kzg in [false, true] {
        for allow_development in [false, true] {
          let options = FinalOptions { system, allow_development };
          let allowed = match system {
            FinalSystem::None => !allow_development,
            FinalSystem::Plonk | FinalSystem::Groth16 => {
              !development_kzg || allow_development
            },
          };
          assert_eq!(options.validate_setup(development_kzg).is_ok(), allowed);
        }
      }
    }
  }
}
