//! Development setup selection and binding for compression checkpoints.
//!
//! Every setup declares a public identity and full public degree; the
//! development policy derives both from the stage seed. Parameters come
//! from a per-stage cache file, or from a shared cache directory holding
//! one file per prefix length when `IX_KZG_SRS_CACHE` names it.
use super::kzg_storage as storage;
use crate::kzg::{KzgConfig, PublicSetup, Srs, VerifierParams};
use std::{
  fs,
  path::{Path, PathBuf},
  sync::Arc,
};

pub(crate) const FIRST_SEED: &[u8] = b"init-fri-kzg-ordinary-v1";
pub(crate) const BINDING_FILE: &str = "kzg-setup-id.bin";

#[derive(Clone)]
pub(crate) struct SetupSource {
  seed: Vec<u8>,
  public_setup: PublicSetup,
  cache: Option<PathBuf>,
  cache_directory: Option<PathBuf>,
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
      seed: seed.to_vec(),
      public_setup: PublicSetup::known_trapdoor(public_max_degree, seed),
      cache,
      cache_directory: None,
    })
  }

  /// Prefer a shared directory of cached development parameters, keyed by
  /// prefix length and seed, over the per-stage cache file.
  pub(crate) fn with_cache_directory(mut self, directory: PathBuf) -> Self {
    self.cache_directory = Some(directory);
    self
  }

  /// The shared cache directory named by `IX_KZG_SRS_CACHE`, if any.
  pub(crate) fn cache_directory_from_env() -> Option<PathBuf> {
    std::env::var_os("IX_KZG_SRS_CACHE").map(PathBuf::from)
  }

  pub(crate) fn security_description(&self) -> &'static str {
    "Known-trapdoor development public-degree KZG. Not ceremony parameters. Correctness and cost experiment only.\n"
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
    if !verify_only && let Some(directory) = &self.cache_directory {
      return Ok(Srs::unsafe_dev_setup_prefix_in_cache_directory(
        length,
        self.public_setup.max_degree,
        &self.seed,
        directory,
      )?);
    }
    if !verify_only && let Some(path) = &self.cache {
      return Ok(Srs::unsafe_dev_setup_prefix_cached(
        length,
        self.public_setup.max_degree,
        &self.seed,
        path,
      )?);
    }
    Ok(Srs::unsafe_dev_setup_prefix(
      length,
      self.public_setup.max_degree,
      &self.seed,
    ))
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
}
