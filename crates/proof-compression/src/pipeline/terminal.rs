//! Shared transport and artifact checks for terminal proof backends.
#![cfg_attr(
  not(any(feature = "plonk", feature = "groth16")),
  allow(dead_code, unused_imports)
)]
use super::{Result, statement, storage};
use sha2::{Digest, Sha256};
use std::{
  fs,
  io::Read,
  path::{Path, PathBuf},
  process::{Command, Stdio},
};

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

pub(super) struct Scratch(pub(super) PathBuf);
impl Scratch {
  pub(super) fn new() -> Result<Self> {
    let path =
      storage::temporary_path(&std::env::temp_dir().join("ix-terminal"));
    fs::create_dir(&path)?;
    Ok(Self(path))
  }
}
impl Drop for Scratch {
  fn drop(&mut self) {
    let _ = fs::remove_dir_all(&self.0);
  }
}

pub(super) fn hex(bytes: &[u8]) -> String {
  use std::fmt::Write as _;
  let mut output = String::with_capacity(bytes.len() * 2);
  for byte in bytes {
    write!(output, "{byte:02x}").unwrap();
  }
  output
}

pub(super) fn digest(text: &str) -> Result<[u8; 32]> {
  let text = text.strip_prefix("0x").unwrap_or(text);
  if text.len() != 64 || !text.is_ascii() {
    return Err("expected a 32-byte hexadecimal digest".into());
  }
  let mut bytes = [0; 32];
  for (index, byte) in bytes.iter_mut().enumerate() {
    *byte = u8::from_str_radix(&text[2 * index..2 * index + 2], 16)?;
  }
  Ok(bytes)
}

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

pub(super) fn load_json<T: serde::de::DeserializeOwned>(
  path: &Path,
) -> Result<T> {
  let mut bytes = Vec::new();
  fs::File::open(path)?.take((1 << 20) + 1).read_to_end(&mut bytes)?;
  if bytes.len() > 1 << 20 {
    return Err("terminal metadata exceeds its size limit".into());
  }
  Ok(serde_json::from_slice(&bytes)?)
}

pub(super) fn helper_executable(variable: &str) -> Result<PathBuf> {
  let path = if let Some(path) = std::env::var_os(variable) {
    PathBuf::from(path)
  } else if let Some(path) = std::env::var_os("IX_PLONK_HELPER") {
    PathBuf::from(path)
  } else {
    std::env::current_exe()?.with_file_name("ix-bn254-plonk-wrapper")
  };
  if !path.is_file() {
    return Err(
      format!("gnark terminal helper is missing; set {variable}").into(),
    );
  }
  Ok(path)
}

pub(super) fn checked(command: &mut Command) -> Result<()> {
  let status = command
    .stdout(Stdio::from(std::io::stderr()))
    .stderr(Stdio::inherit())
    .status()?;
  if !status.success() {
    return Err(format!("terminal helper failed ({status})").into());
  }
  Ok(())
}

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
