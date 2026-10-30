//! Compression uses the release's Ignition parameters or an explicitly selected
//! known-trapdoor development setup. The released verifying keys authorize the
//! production parameters; ceremony verification belongs to release preparation.
use super::{storage, verifying_keys};
use crate::kzg::srs::gnark;
use crate::kzg::{KzgConfig, PublicSetup, Srs, TranscriptKind, VerifierParams};
use multi_stark::traits::TwoAdicField;
use std::ffi::OsString;
use std::{
  fs,
  path::{Path, PathBuf},
  sync::Arc,
};

/// The first KZG stage's development seed. It is the recursive stage's seed,
/// so under development setups the first, recursive and merge stages share
/// one trapdoor and a merge can fold the pairings they defer. Ignition
/// setups ignore stage seeds.
pub(crate) const FIRST_SEED: &[u8] = b"init-kzg-recursive-bn254-v1";
pub(crate) const BINDING_FILE: &str = "kzg-setup-id.bin";
pub(crate) const IGNITION_SRS_VAR: &str = "IX_KZG_SRS";
pub(crate) const PARAMETERS_DIR_VAR: &str = "IX_PARAMS_DIR";
const IGNITION_DIRECTORY: &str = "bn254-ignition-main-197";
const IGNITION_FILE: &str = "srs.bin";

/// `IX_PARAMS_DIR`, else `$HOME/.ix/compression/params`.
fn parameters_directory_from(
  mut lookup: impl FnMut(&str) -> Option<OsString>,
) -> Option<PathBuf> {
  lookup(PARAMETERS_DIR_VAR).map(PathBuf::from).or_else(|| {
    lookup("HOME")
      .map(|home| PathBuf::from(home).join(".ix/compression/params"))
  })
}

/// The trust class of verifier parameters.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SetupClass {
  /// Ignition parameters matching the released verifying key.
  Ignition,
  /// A trapdoor derived from a seed; anyone can forge proofs.
  Development,
  /// A circuit-specific Groth16 key admitted independently of the proof.
  Groth16,
}

impl SetupClass {
  /// Match the complete setup identity and anchors authorized by the release.
  pub fn of(params: &VerifierParams) -> Self {
    let matches = verifying_keys::ignition_parameters().is_ok_and(|release| {
      params.public_setup == release.public_setup
        && params.g1 == release.g1
        && params.g2 == release.g2
        && params.tau_g2 == release.tau_g2
    });
    if matches { Self::Ignition } else { Self::Development }
  }

  pub fn label(self) -> &'static str {
    match self {
      Self::Ignition => "ignition",
      Self::Groth16 => "groth16",
      Self::Development => "development",
    }
  }

  pub fn description(self) -> &'static str {
    match self {
      Self::Ignition => "the released Aztec Ignition BN254 powers of tau",
      Self::Groth16 => "an admitted BN254 Groth16 circuit-specific ceremony",
      Self::Development => {
        "a known-trapdoor development SRS (not production-secure)"
      },
    }
  }
}

fn development_refused<T>() -> storage::Result<T> {
  Err(
    format!(
      "no BN254 Ignition SRS is installed; run `ix compress fetch-params`, \
     set {IGNITION_SRS_VAR} to the released gnark SRS, or pass --dev-kzg-srs \
     to use the known-trapdoor development setup (not production-secure)"
    )
    .into(),
  )
}

#[derive(Clone)]
pub enum SetupConfig {
  #[non_exhaustive]
  Ignition { srs: PathBuf },
  #[non_exhaustive]
  Development { cache_directory: Option<PathBuf> },
}

impl SetupConfig {
  /// Select the release SRS or the explicitly requested development setup.
  pub fn from_env(development: bool) -> storage::Result<Self> {
    Self::from_ignition_env(development, |name| std::env::var_os(name))
  }

  fn from_ignition_env(
    development: bool,
    mut lookup: impl FnMut(&str) -> Option<OsString>,
  ) -> storage::Result<Self> {
    if development {
      return Ok(Self::Development {
        cache_directory: lookup("IX_KZG_SRS_CACHE").map(PathBuf::from),
      });
    }
    let path = lookup(IGNITION_SRS_VAR).map(PathBuf::from).or_else(|| {
      parameters_directory_from(&mut lookup)
        .map(|directory| directory.join(IGNITION_DIRECTORY).join(IGNITION_FILE))
    });
    let Some(srs) = path.filter(|path| path.is_file()) else {
      return development_refused();
    };
    let config = Self::Ignition { srs };
    config.for_stage(FIRST_SEED, 2)?.srs(2, false)?;
    Ok(config)
  }

  pub(crate) fn class(&self) -> SetupClass {
    match self {
      Self::Ignition { .. } => SetupClass::Ignition,
      Self::Development { .. } => SetupClass::Development,
    }
  }

  pub(crate) fn for_stage(
    &self,
    seed: &[u8],
    height: usize,
  ) -> storage::Result<SetupSource> {
    if height < 2
      || !height.is_power_of_two()
      || height.ilog2() as usize > crate::kzg::Scalar::TWO_ADICITY
    {
      return Err("invalid trace height".into());
    }
    match self {
      Self::Ignition { srs } => {
        let source = SetupSource::ignition(srs.clone())?;
        source.check_height(height)?;
        Ok(source)
      },
      Self::Development { cache_directory } => {
        let mut source = SetupSource::development(seed, height - 1)?;
        if let Some(directory) = cache_directory {
          source = source.with_cache_directory(directory.clone());
        }
        Ok(source)
      },
    }
  }
}

#[derive(Clone)]
enum Policy {
  Development { seed: Vec<u8>, cache_directory: Option<PathBuf> },
  Ignition { srs: PathBuf },
}

#[derive(Clone)]
pub(crate) struct SetupSource {
  policy: Policy,
  public_setup: PublicSetup,
  transcript_kind: TranscriptKind,
}

impl SetupSource {
  pub(crate) fn development(
    seed: &[u8],
    public_max_degree: usize,
  ) -> storage::Result<Self> {
    if public_max_degree < 1 || public_max_degree.checked_add(1).is_none() {
      return Err("invalid public degree allowance".into());
    }
    Ok(Self {
      policy: Policy::Development {
        seed: seed.to_vec(),
        cache_directory: None,
      },
      public_setup: PublicSetup::known_trapdoor(public_max_degree, seed),
      transcript_kind: TranscriptKind::Blake3,
    })
  }

  pub(crate) fn ignition(srs: PathBuf) -> storage::Result<Self> {
    Ok(Self {
      public_setup: verifying_keys::ignition_parameters()?.public_setup,
      policy: Policy::Ignition { srs },
      transcript_kind: TranscriptKind::Blake3,
    })
  }

  /// Bind checkpoint identity to the selected Fiat-Shamir protocol.
  pub(crate) fn with_transcript(mut self, kind: TranscriptKind) -> Self {
    self.transcript_kind = kind;
    self
  }

  /// Serve development parameters from a shared directory of cached
  /// files, keyed by prefix length and seed, instead of regenerating them.
  pub(crate) fn with_cache_directory(mut self, directory: PathBuf) -> Self {
    match &mut self.policy {
      Policy::Development { cache_directory, .. } => {
        *cache_directory = Some(directory);
      },
      Policy::Ignition { .. } => {},
    }
    self
  }

  pub(crate) fn class(&self) -> SetupClass {
    match self.policy {
      Policy::Development { .. } => SetupClass::Development,
      Policy::Ignition { .. } => SetupClass::Ignition,
    }
  }

  pub(crate) fn security_description(&self) -> &'static str {
    match self.policy {
      Policy::Ignition { .. } => {
        "Aztec Ignition BN254 powers of tau selected during release preparation. Verification uses the fixed release keys.\n"
      },
      Policy::Development { .. } => {
        "Known-trapdoor development public-degree KZG. Not ceremony parameters. For development and testing only.\n"
      },
    }
  }

  fn check_height(&self, height: usize) -> storage::Result<()> {
    if height < 2
      || !height.is_power_of_two()
      || height.ilog2() as usize > crate::kzg::Scalar::TWO_ADICITY
      || height - 1 > self.public_setup.max_degree
    {
      return Err("trace height exceeds public setup allowance".into());
    }
    Ok(())
  }

  #[tracing::instrument(level = "info", skip_all, name = "compression/setup")]
  pub(crate) fn srs(
    &self,
    height: usize,
    verify_only: bool,
  ) -> storage::Result<Srs> {
    self.check_height(height)?;
    let length = if verify_only { 2 } else { height };
    match &self.policy {
      Policy::Ignition { .. } if verify_only => {
        verifying_keys::ignition_anchors()
      },
      Policy::Ignition { srs } => {
        let srs = gnark::load(srs, length, self.public_setup)?;
        if SetupClass::of(&VerifierParams::from_srs(&srs))
          != SetupClass::Ignition
        {
          return Err(
            "SRS anchors differ from the released Ignition parameters".into(),
          );
        }
        Ok(srs)
      },
      Policy::Development { seed, cache_directory } => {
        if !verify_only && let Some(directory) = cache_directory {
          return Ok(Srs::unsafe_dev_setup_prefix_in_cache_directory(
            length,
            self.public_setup.max_degree,
            seed,
            directory,
          )?);
        }
        Ok(Srs::unsafe_dev_setup_prefix(
          length,
          self.public_setup.max_degree,
          seed,
        ))
      },
    }
  }

  pub(crate) fn verifier_params(
    &self,
    height: usize,
  ) -> storage::Result<VerifierParams> {
    Ok(VerifierParams::with_max_trace_len(&self.srs(height, true)?, height))
  }

  pub(crate) fn config(
    &self,
    height: usize,
    quotient: usize,
    verify_only: bool,
  ) -> storage::Result<KzgConfig> {
    self.check_height(height)?;
    if !quotient.is_power_of_two() {
      return Err("invalid quotient budget".into());
    }
    if height.ilog2() as usize + quotient.ilog2() as usize
      > crate::kzg::Scalar::TWO_ADICITY
    {
      return Err("quotient domain exceeds scalar field two-adicity".into());
    }
    Ok(
      (if verify_only {
        KzgConfig::verifier_only(self.verifier_params(height)?, quotient)
      } else {
        KzgConfig::with_max_trace_len(
          Arc::new(self.srs(height, false)?),
          height,
          quotient,
        )
      })
      .with_transcript(self.transcript_kind),
    )
  }

  /// The setup identity bound into checkpoints and fixed-cache verifying keys.
  pub(crate) fn identity(
    &self,
    height: usize,
    quotient: usize,
  ) -> storage::Result<[u8; 32]> {
    let config = self.config(height, quotient, true)?;
    let mut hash = blake3::Hasher::new();
    hash.update(b"ix/compression/setup/v4");
    hash.update(config.transcript_seed());
    Ok(*hash.finalize().as_bytes())
  }

  pub(crate) fn bind_stage(
    &self,
    dir: &Path,
    height: usize,
    quotient: usize,
  ) -> storage::Result<()> {
    storage::write_atomic(
      &dir.join(BINDING_FILE),
      &self.identity(height, quotient)?,
    )?;
    Ok(())
  }

  pub(crate) fn check_binding(
    &self,
    dir: &Path,
    height: usize,
    quotient: usize,
  ) -> storage::Result<()> {
    if fs::read(dir.join(BINDING_FILE))? != self.identity(height, quotient)? {
      return Err(
        "checkpoint setup, transcript, public degree or trace cap mismatch"
          .into(),
      );
    }
    Ok(())
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn setup_binding_preserves_public_identity_and_rejects_mismatch()
  -> storage::Result<()> {
    let dir = std::env::temp_dir()
      .join(format!("ix-setup-binding-{}", std::process::id()));
    fs::create_dir(&dir)?;
    let setup = SetupSource::development(b"setup-binding", 63)?;
    let prover = setup.srs(64, false)?;
    let verifier = setup.srs(64, true)?;
    assert_eq!(prover.public_setup, verifier.public_setup);
    assert_eq!(verifier.max_len(), 2);
    assert_eq!(
      setup.config(64, 2, false)?.transcript_seed(),
      setup.config(64, 2, true)?.transcript_seed()
    );
    setup.bind_stage(&dir, 64, 2)?;
    setup.check_binding(&dir, 64, 2)?;
    let keccak = setup.clone().with_transcript(TranscriptKind::Keccak256);
    assert_eq!(
      setup.verifier_params(64)?.to_bytes()?,
      keccak.verifier_params(64)?.to_bytes()?
    );
    assert_ne!(setup.identity(64, 2)?, keccak.identity(64, 2)?);
    assert_eq!(
      keccak.config(64, 2, false)?.transcript_seed(),
      keccak.config(64, 2, true)?.transcript_seed()
    );
    assert!(keccak.check_binding(&dir, 64, 2).is_err());
    assert!(setup.check_binding(&dir, 32, 2).is_err());
    assert!(setup.check_binding(&dir, 64, 4).is_err());
    assert!(
      SetupSource::development(b"other", 63)?
        .check_binding(&dir, 64, 2)
        .is_err()
    );
    assert!(
      SetupSource::development(b"setup-binding", 127)?
        .check_binding(&dir, 64, 2)
        .is_err()
    );
    assert!(setup.config(128, 2, true).is_err());
    fs::remove_dir_all(dir)?;
    Ok(())
  }

  #[test]
  fn cache_directory_yields_the_generated_parameters() -> storage::Result<()> {
    let dir = std::env::temp_dir()
      .join(format!("ix-setup-cache-dir-{}", std::process::id()));
    fs::create_dir(&dir)?;
    let generated = SetupSource::development(b"setup-cache", 63)?;
    let directory = SetupSource::development(b"setup-cache", 63)?
      .with_cache_directory(dir.join("shared"));
    let a = generated.srs(64, false)?;
    let b = directory.srs(64, false)?;
    let c = directory.srs(64, false)?;
    assert_eq!(a.g1, b.g1);
    assert_eq!(b.g1, c.g1);
    assert_eq!(a.public_setup, c.public_setup);
    assert_eq!(fs::read_dir(dir.join("shared"))?.count(), 1);
    assert_eq!(
      generated.config(64, 2, false)?.transcript_seed(),
      directory.config(64, 2, false)?.transcript_seed()
    );
    fs::remove_dir_all(dir)?;
    Ok(())
  }

  #[test]
  fn development_flag_selects_development_parameters() -> storage::Result<()> {
    let config = SetupConfig::from_env(true)?;
    assert_eq!(config.class(), SetupClass::Development);
    assert_eq!(
      config.for_stage(FIRST_SEED, 64)?.identity(64, 2)?,
      SetupSource::development(FIRST_SEED, 63)?.identity(64, 2)?
    );
    Ok(())
  }

  #[test]
  fn setup_rejects_unsupported_trace_and_quotient_domains()
  -> storage::Result<()> {
    let max_height = 1usize << crate::kzg::Scalar::TWO_ADICITY;
    let source = SetupSource::development(FIRST_SEED, max_height * 2 - 1)?;
    assert!(source.config(max_height / 2, 2, true).is_ok());
    assert!(source.config(max_height, 1, true).is_ok());
    assert!(source.config(max_height, 2, true).is_err());
    assert!(source.verifier_params(max_height * 2).is_err());
    assert!(source.config(8, 0, true).is_err());
    assert!(source.config(8, 3, true).is_err());
    assert!(
      SetupConfig::from_env(true)?
        .for_stage(FIRST_SEED, max_height * 2)
        .is_err()
    );
    Ok(())
  }
}

#[cfg(test)]
mod ignition_tests;
