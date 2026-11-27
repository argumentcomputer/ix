//! Shared transport and artifact checks for final proof backends.
use super::Result;
use serde::{Deserialize, Serialize};
#[cfg(all(test, feature = "plonk"))]
use std::{fs, io::Read, path::Path};

// TODO: Decide between SHA-256 and BLAKE3 for artifact/cache metadata.
// Coordinate any catalog or envelope key-ID changes; proof-protocol hashes
// have separate compatibility requirements.
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

#[cfg(all(test, feature = "plonk"))]
fn read_bounded(path: &Path, limit: usize) -> Result<Vec<u8>> {
  let mut bytes = Vec::new();
  fs::File::open(path)?.take((limit + 1) as u64).read_to_end(&mut bytes)?;
  if bytes.len() > limit {
    return Err("final input exceeds its size limit".into());
  }
  Ok(bytes)
}

#[cfg(all(test, feature = "plonk"))]
pub(super) fn load_json<T: serde::de::DeserializeOwned>(
  path: &Path,
) -> Result<T> {
  Ok(serde_json::from_slice(&read_bounded(path, 1 << 20)?)?)
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
