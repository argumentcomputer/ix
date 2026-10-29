//! Shared transport and artifact checks for terminal proof backends.
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

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
#[repr(u8)]
pub enum TerminalSystem {
  #[default]
  None = 0,
  Plonk = 1,
  Groth16 = 2,
}

impl TryFrom<u8> for TerminalSystem {
  type Error = &'static str;
  fn try_from(value: u8) -> std::result::Result<Self, Self::Error> {
    match value {
      0 => Ok(Self::None),
      1 => Ok(Self::Plonk),
      2 => Ok(Self::Groth16),
      _ => Err("unknown terminal proof system"),
    }
  }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct TerminalOptions {
  pub system: TerminalSystem,
  pub allow_development: bool,
}

impl From<TerminalSystem> for TerminalOptions {
  fn from(system: TerminalSystem) -> Self {
    Self { system, allow_development: false }
  }
}

impl TryFrom<u8> for TerminalOptions {
  type Error = &'static str;
  fn try_from(value: u8) -> std::result::Result<Self, Self::Error> {
    if value == 3 {
      Ok(Self { system: TerminalSystem::Groth16, allow_development: true })
    } else {
      Ok(TerminalSystem::try_from(value)?.into())
    }
  }
}

#[cfg(all(test, any(feature = "plonk", feature = "groth16")))]
pub(super) struct Scratch(pub(super) PathBuf);
#[cfg(all(test, any(feature = "plonk", feature = "groth16")))]
impl Scratch {
  pub(super) fn new() -> Result<Self> {
    let path =
      storage::temporary_path(&std::env::temp_dir().join("ix-terminal"));
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
    return Err("terminal input exceeds its size limit".into());
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
  fn terminal_selection_keeps_development_explicit() {
    assert_eq!(
      TerminalOptions::try_from(0).unwrap().system,
      TerminalSystem::None
    );
    assert_eq!(
      TerminalOptions::try_from(1).unwrap().system,
      TerminalSystem::Plonk
    );
    let production = TerminalOptions::try_from(2).unwrap();
    let development = TerminalOptions::try_from(3).unwrap();
    assert_eq!(production.system, TerminalSystem::Groth16);
    assert!(!production.allow_development);
    assert!(development.allow_development);
    assert_eq!(development.system, TerminalSystem::Groth16);
    assert!(TerminalOptions::try_from(4).is_err());
  }
}
