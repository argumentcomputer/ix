//! Setup selection and binding for compression checkpoints.
//!
//! Every setup declares a public identity and full public degree. The
//! Filecoin policy loads an authenticated prefix of the phase-one powers of
//! tau from the cache named by `IX_KZG_FILECOIN_CACHE`, pinned by the manifest
//! receipt in `IX_KZG_FILECOIN_MANIFEST` or, when that is unset, the built-in
//! receipt of the complete `2^27` cache. The development policy derives a
//! known trapdoor from the stage seed, with parameters from a per-stage cache
//! file or from the shared directory named by `IX_KZG_SRS_CACHE`.
use super::kzg_storage as storage;
use crate::kzg::{
  KzgConfig, PublicSetup, Srs, VerifierParams,
  srs::filecoin::{
    FILECOIN_PREFIX_2P27_MANIFEST_BLAKE3, FILECOIN_PUBLIC_MAX_DEGREE,
    filecoin_setup_id, load_filecoin_cache,
  },
};
use std::{
  fs,
  path::{Path, PathBuf},
  sync::Arc,
};

pub(crate) const FIRST_SEED: &[u8] = b"init-fri-kzg-ordinary-v1";
pub(crate) const BINDING_FILE: &str = "kzg-setup-id.bin";
pub(crate) const FILECOIN_CACHE_VAR: &str = "IX_KZG_FILECOIN_CACHE";
pub(crate) const FILECOIN_MANIFEST_VAR: &str = "IX_KZG_FILECOIN_MANIFEST";

/// The trust class a public setup identity declares.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SetupClass {
  /// Filecoin's phase-one powers of tau. The trapdoor is unknown unless
  /// every ceremony participant colluded.
  Filecoin,
  /// A trapdoor derived from a seed; anyone can forge proofs.
  Development,
}

impl SetupClass {
  pub fn of(setup: PublicSetup) -> Self {
    if setup.id == filecoin_setup_id()
      && setup.max_degree == FILECOIN_PUBLIC_MAX_DEGREE
    {
      Self::Filecoin
    } else {
      Self::Development
    }
  }

  /// Registry subdirectory and report label.
  pub fn label(self) -> &'static str {
    match self {
      Self::Filecoin => "filecoin",
      Self::Development => "development",
    }
  }

  pub fn description(self) -> &'static str {
    match self {
      Self::Filecoin => "the Filecoin phase-one powers of tau",
      Self::Development => {
        "a known-trapdoor development SRS (not production-secure)"
      },
    }
  }

  /// The class a new run proves under. A configured Filecoin cache is always
  /// used; the development setup needs explicit permission.
  pub fn configured(allow_development: bool) -> storage::Result<Self> {
    if SetupSource::filecoin_from_env()?.is_some() {
      return Ok(Self::Filecoin);
    }
    if allow_development {
      return Ok(Self::Development);
    }
    Err(
      format!(
        "no Filecoin SRS cache is configured; set {FILECOIN_CACHE_VAR} to an \
         authenticated prefix cache, or pass --dev-srs to use the \
         known-trapdoor development setup (not production-secure)"
      )
      .into(),
    )
  }
}

#[derive(Clone)]
enum Policy {
  Development {
    seed: Vec<u8>,
    cache: Option<PathBuf>,
    cache_directory: Option<PathBuf>,
  },
  Filecoin {
    cache: PathBuf,
    manifest: [u8; 32],
  },
}

#[derive(Clone)]
pub(crate) struct SetupSource {
  policy: Policy,
  public_setup: PublicSetup,
}

fn parse_digest(text: &str) -> storage::Result<[u8; 32]> {
  if text.len() != 64 || !text.is_ascii() {
    return Err(
      format!("{FILECOIN_MANIFEST_VAR} must be a 64-character BLAKE3 digest")
        .into(),
    );
  }
  let mut digest = [0; 32];
  for (i, byte) in digest.iter_mut().enumerate() {
    *byte = u8::from_str_radix(&text[2 * i..2 * i + 2], 16)?;
  }
  Ok(digest)
}

impl SetupSource {
  pub(crate) fn development(
    seed: &[u8],
    public_max_degree: usize,
    cache: Option<PathBuf>,
  ) -> storage::Result<Self> {
    if public_max_degree < 1 || public_max_degree.checked_add(1).is_none() {
      return Err("invalid public degree allowance".into());
    }
    Ok(Self {
      policy: Policy::Development {
        seed: seed.to_vec(),
        cache,
        cache_directory: None,
      },
      public_setup: PublicSetup::known_trapdoor(public_max_degree, seed),
    })
  }

  /// Filecoin parameters from an authenticated prefix cache, pinned by the
  /// manifest receipt of its import.
  pub(crate) fn filecoin(cache: PathBuf, manifest: [u8; 32]) -> Self {
    Self {
      policy: Policy::Filecoin { cache, manifest },
      public_setup: PublicSetup {
        max_degree: FILECOIN_PUBLIC_MAX_DEGREE,
        id: filecoin_setup_id(),
      },
    }
  }

  /// The Filecoin cache named by `IX_KZG_FILECOIN_CACHE`, if any. The
  /// receipt comes from `IX_KZG_FILECOIN_MANIFEST`, or is the built-in
  /// receipt of the complete `2^27` cache.
  pub(crate) fn filecoin_from_env() -> storage::Result<Option<Self>> {
    let Some(cache) = std::env::var_os(FILECOIN_CACHE_VAR) else {
      return Ok(None);
    };
    let cache = PathBuf::from(cache);
    if !cache.is_file() {
      return Err(
        format!(
          "{FILECOIN_CACHE_VAR} does not name a file: {}",
          cache.display()
        )
        .into(),
      );
    }
    let manifest = match std::env::var(FILECOIN_MANIFEST_VAR) {
      Ok(text) => parse_digest(text.trim())?,
      Err(std::env::VarError::NotPresent) => {
        FILECOIN_PREFIX_2P27_MANIFEST_BLAKE3
      },
      Err(error) => return Err(error.into()),
    };
    Ok(Some(Self::filecoin(cache, manifest)))
  }

  /// The setup a stage of trace height `height` uses: the configured
  /// Filecoin cache, or else the development setup of `seed` with its
  /// per-stage cache file or the shared `IX_KZG_SRS_CACHE` directory.
  pub(crate) fn for_stage(
    seed: &[u8],
    height: usize,
    development_cache: Option<PathBuf>,
  ) -> storage::Result<Self> {
    if let Some(filecoin) = Self::filecoin_from_env()? {
      return Ok(filecoin);
    }
    let mut setup = Self::development(seed, height - 1, development_cache)?;
    if let Some(directory) = Self::cache_directory_from_env() {
      setup = setup.with_cache_directory(directory);
    }
    Ok(setup)
  }

  /// Prefer a shared directory of cached development parameters, keyed by
  /// prefix length and seed, over the per-stage cache file.
  pub(crate) fn with_cache_directory(mut self, directory: PathBuf) -> Self {
    if let Policy::Development { cache_directory, .. } = &mut self.policy {
      *cache_directory = Some(directory);
    }
    self
  }

  /// The shared cache directory named by `IX_KZG_SRS_CACHE`, if any.
  pub(crate) fn cache_directory_from_env() -> Option<PathBuf> {
    std::env::var_os("IX_KZG_SRS_CACHE").map(PathBuf::from)
  }

  pub(crate) fn class(&self) -> SetupClass {
    match self.policy {
      Policy::Development { .. } => SetupClass::Development,
      Policy::Filecoin { .. } => SetupClass::Filecoin,
    }
  }

  pub(crate) fn security_description(&self) -> &'static str {
    match self.class() {
      SetupClass::Filecoin => {
        "Filecoin phase-one powers of tau (challenge_19), authenticated against the published BLAKE2b-512 digest and loaded from a receipt-pinned prefix cache. Public ceremony parameters; the trapdoor is unknown unless every participant colluded.\n"
      },
      SetupClass::Development => {
        "Known-trapdoor development public-degree KZG. Not ceremony parameters. Correctness and cost experiment only.\n"
      },
    }
  }

  fn check_height(&self, height: usize) -> storage::Result<()> {
    if height < 2
      || !height.is_power_of_two()
      || height.ilog2() > 32
      || height - 1 > self.public_setup.max_degree
    {
      return Err("trace height exceeds public setup allowance".into());
    }
    Ok(())
  }

  pub(crate) fn srs(
    &self,
    height: usize,
    verify_only: bool,
  ) -> storage::Result<Srs> {
    self.check_height(height)?;
    let length = if verify_only { 2 } else { height };
    match &self.policy {
      Policy::Filecoin { cache, manifest } => {
        Ok(load_filecoin_cache(cache, *manifest, length)?)
      },
      Policy::Development { seed, cache, cache_directory } => {
        if !verify_only && let Some(directory) = cache_directory {
          return Ok(Srs::unsafe_dev_setup_prefix_in_cache_directory(
            length,
            self.public_setup.max_degree,
            seed,
            directory,
          )?);
        }
        if !verify_only && let Some(path) = cache {
          return Ok(Srs::unsafe_dev_setup_prefix_cached(
            length,
            self.public_setup.max_degree,
            seed,
            path,
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
    if !quotient.is_power_of_two() {
      return Err("invalid quotient budget".into());
    }
    Ok(if verify_only {
      KzgConfig::verifier_only(self.verifier_params(height)?, quotient)
    } else {
      KzgConfig::with_max_trace_len(
        Arc::new(self.srs(height, false)?),
        height,
        quotient,
      )
    })
  }

  /// The setup identity bound into checkpoints and fixed-cache profiles.
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
    let marker = dir.join(BINDING_FILE);
    if marker.exists() {
      return self.check_binding(dir, height, quotient);
    }
    if dir.join("manifest.bin").exists()
      || (dir.join("kzg").exists()
        && fs::read_dir(dir.join("kzg"))?.next().transpose()?.is_some())
    {
      return Err(
        "existing checkpoints have no authenticated setup binding".into(),
      );
    }
    fs::write(marker, self.identity(height, quotient)?)?;
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
        "checkpoint setup, public degree or trace cap mismatch".into(),
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
    let setup = SetupSource::development(b"setup-binding", 63, None)?;
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
    assert!(setup.check_binding(&dir, 32, 2).is_err());
    assert!(setup.check_binding(&dir, 64, 4).is_err());
    assert!(
      SetupSource::development(b"other", 63, None)?
        .check_binding(&dir, 64, 2)
        .is_err()
    );
    assert!(
      SetupSource::development(b"setup-binding", 127, None)?
        .check_binding(&dir, 64, 2)
        .is_err()
    );
    assert!(setup.config(128, 2, true).is_err());
    fs::remove_file(dir.join(BINDING_FILE))?;
    fs::write(dir.join("manifest.bin"), [])?;
    assert!(setup.bind_stage(&dir, 64, 2).is_err());
    fs::remove_dir_all(dir)?;
    Ok(())
  }

  #[test]
  fn cache_directory_and_cache_file_yield_the_same_parameters()
  -> storage::Result<()> {
    let dir = std::env::temp_dir()
      .join(format!("ix-setup-cache-dir-{}", std::process::id()));
    fs::create_dir(&dir)?;
    let file = SetupSource::development(
      b"setup-cache",
      63,
      Some(dir.join("dev-srs.bin")),
    )?;
    let directory = SetupSource::development(b"setup-cache", 63, None)?
      .with_cache_directory(dir.join("shared"));
    let a = file.srs(64, false)?;
    let b = directory.srs(64, false)?;
    let c = directory.srs(64, false)?;
    assert_eq!(a.g1, b.g1);
    assert_eq!(b.g1, c.g1);
    assert_eq!(a.public_setup, c.public_setup);
    assert_eq!(fs::read_dir(dir.join("shared"))?.count(), 1);
    assert_eq!(
      file.config(64, 2, false)?.transcript_seed(),
      directory.config(64, 2, false)?.transcript_seed()
    );
    fs::remove_dir_all(dir)?;
    Ok(())
  }

  #[test]
  fn setup_class_follows_the_public_identity() {
    assert_eq!(
      SetupClass::of(PublicSetup::known_trapdoor(63, FIRST_SEED)),
      SetupClass::Development
    );
    assert_eq!(
      SetupClass::of(PublicSetup {
        max_degree: FILECOIN_PUBLIC_MAX_DEGREE,
        id: filecoin_setup_id(),
      }),
      SetupClass::Filecoin
    );
    assert_eq!(
      SetupClass::of(PublicSetup {
        max_degree: FILECOIN_PUBLIC_MAX_DEGREE - 1,
        id: filecoin_setup_id(),
      }),
      SetupClass::Development
    );
    let filecoin = SetupSource::filecoin(PathBuf::from("/missing"), [0; 32]);
    assert_eq!(filecoin.class(), SetupClass::Filecoin);
    assert_eq!(filecoin.public_setup.max_degree, FILECOIN_PUBLIC_MAX_DEGREE);
    assert!(filecoin.srs(1 << 28, true).is_err());
    assert!(filecoin.srs(1 << 27, true).is_err());
    assert!(parse_digest(&"0".repeat(63)).is_err());
    assert!(parse_digest(&"g".repeat(64)).is_err());
    assert_eq!(parse_digest(&"00".repeat(32)).unwrap(), [0; 32]);
  }

  #[test]
  fn development_setup_needs_permission_without_a_filecoin_cache()
  -> storage::Result<()> {
    if std::env::var_os(FILECOIN_CACHE_VAR).is_some() {
      return Ok(());
    }
    assert_eq!(SetupClass::configured(true)?, SetupClass::Development);
    assert!(
      SetupClass::configured(false)
        .unwrap_err()
        .to_string()
        .contains("--dev-srs")
    );
    assert_eq!(
      SetupSource::for_stage(FIRST_SEED, 64, None)?.identity(64, 2)?,
      SetupSource::development(FIRST_SEED, 63, None)?.identity(64, 2)?
    );
    Ok(())
  }

  /// Opt-in: `IX_KZG_FILECOIN_CACHE` names a cache holding at least 256
  /// powers whose receipt is pinned or given in `IX_KZG_FILECOIN_MANIFEST`.
  #[test]
  fn configured_filecoin_cache_proves_and_binds_under_its_identity()
  -> storage::Result<()> {
    let Some(setup) = SetupSource::filecoin_from_env()? else {
      return Ok(());
    };
    assert_eq!(SetupClass::configured(false)?, SetupClass::Filecoin);
    assert_eq!(
      SetupSource::for_stage(FIRST_SEED, 256, None)?.identity(256, 2)?,
      setup.identity(256, 2)?
    );
    let verifier = setup.srs(256, true)?;
    assert_eq!(verifier.max_len(), 2);
    assert_eq!(SetupClass::of(verifier.public_setup), SetupClass::Filecoin);
    let prover = setup.srs(256, false)?;
    assert_eq!(prover.max_len(), 256);
    assert_eq!(prover.public_setup, verifier.public_setup);
    assert_eq!(
      setup.config(256, 2, false)?.transcript_seed(),
      setup.config(256, 2, true)?.transcript_seed()
    );
    assert_ne!(
      setup.identity(256, 2)?,
      SetupSource::development(FIRST_SEED, 255, None)?.identity(256, 2)?
    );
    Ok(())
  }
}
