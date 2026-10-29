//! Setup selection and binding for compression checkpoints.
//!
//! Every setup declares a public identity and full public degree. The
//! Ignition policy requires independently pinned admission
//! metadata and an authenticated prefix cache. The development policy derives a
//! known trapdoor from the stage seed, with parameters from a per-stage cache
//! file or from the shared directory named by `IX_KZG_SRS_CACHE`.
//!
//! Without explicit Ignition settings, the pinned Ignition release is used
//! when its files are present in the parameters directory (`IX_PARAMS_DIR`,
//! else `~/.ix/compression/params`), as `ix compress fetch-params` leaves
//! them.
use super::storage;
use crate::kzg::srs::ignition::{
  IgnitionAdmission, load_ignition_cache_with_identity,
};
use crate::kzg::{KzgConfig, PublicSetup, Srs, TranscriptKind, VerifierParams};
use multi_stark::traits::TwoAdicField;
use std::ffi::{OsStr, OsString};
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
pub(crate) const IGNITION_CACHE_VAR: &str = "IX_KZG_IGNITION_CACHE";
pub(crate) const IGNITION_CACHE_MANIFEST_VAR: &str =
  "IX_KZG_IGNITION_CACHE_BLAKE3";
pub(crate) const IGNITION_ADMISSION_VAR: &str = "IX_KZG_IGNITION_ADMISSION";
pub(crate) const IGNITION_ADMISSION_DIGEST_VAR: &str =
  "IX_KZG_IGNITION_ADMISSION_BLAKE3";
const IGNITION_ENV_VARS: [&str; 4] = [
  IGNITION_CACHE_VAR,
  IGNITION_CACHE_MANIFEST_VAR,
  IGNITION_ADMISSION_VAR,
  IGNITION_ADMISSION_DIGEST_VAR,
];
pub(crate) const PARAMETERS_DIR_VAR: &str = "IX_PARAMS_DIR";

/// Published BN254 Ignition proving parameters and their pins. The objects are
/// publicly readable from the URL `ix compress fetch-params` downloads; the
/// pins, not the location, authenticate them.
struct IgnitionRelease {
  name: &'static str,
  cache_file: &'static str,
  cache_manifest_blake3: &'static str,
  admission_file: &'static str,
  admission_blake3: &'static str,
}

const IGNITION_RELEASE: IgnitionRelease = IgnitionRelease {
  name: "bn254-ignition-main-197",
  cache_file: "ix-prefix-26.bin",
  cache_manifest_blake3: "6b4a939d863d026ab045d3da2c8175abb9224889a58ccbf26bacb92f74248e6b",
  admission_file: "admission.json",
  admission_blake3: "4e16f069766667b6f5b9710b23bbf4fce067053967666db78f34ff058b48ff46",
};

impl IgnitionRelease {
  fn directory(&self, parameters: &Path) -> PathBuf {
    parameters.join(self.name)
  }

  fn config(&self, directory: &Path) -> storage::Result<SetupConfig> {
    SetupConfig::ignition(
      directory.join(self.cache_file),
      parse_ignition_digest(
        IGNITION_CACHE_MANIFEST_VAR,
        OsStr::new(self.cache_manifest_blake3),
      )?,
      &directory.join(self.admission_file),
      parse_ignition_digest(
        IGNITION_ADMISSION_DIGEST_VAR,
        OsStr::new(self.admission_blake3),
      )?,
    )
  }

  fn present(&self, directory: &Path) -> bool {
    directory.join(self.cache_file).is_file()
      && directory.join(self.admission_file).is_file()
  }
}

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
  /// Ignition parameters whose identity, degree and anchors match an
  /// independently pinned admission of the ceremony source.
  Ignition,
  /// A trapdoor derived from a seed; anyone can forge proofs.
  Development,
  /// A circuit-specific Groth16 key admitted independently of the proof.
  Groth16,
}

impl SetupClass {
  /// Production classification requires independently admitted Ignition
  /// metadata; verifier parameters alone do not establish provenance.
  pub fn of(_params: &VerifierParams) -> Self {
    Self::Development
  }

  pub fn of_with_ignition(
    params: &VerifierParams,
    admission: &IgnitionAdmission,
  ) -> storage::Result<Self> {
    admission.check_verifier(params)?;
    Ok(Self::Ignition)
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
      Self::Ignition => "the admitted Aztec Ignition BN254 powers of tau",
      Self::Groth16 => "an admitted BN254 Groth16 circuit-specific ceremony",
      Self::Development => {
        "a known-trapdoor development SRS (not production-secure)"
      },
    }
  }
}

fn development_refused<T>() -> storage::Result<T> {
  let message = format!(
    "no admitted BN254 Ignition setup is configured; set \
     {IGNITION_CACHE_VAR}, {IGNITION_CACHE_MANIFEST_VAR}, \
     {IGNITION_ADMISSION_VAR} and {IGNITION_ADMISSION_DIGEST_VAR}, run \
     `ix compress fetch-params` to install the pinned release, or pass \
     --dev-kzg-srs to use the known-trapdoor development setup \
     (not production-secure)"
  );
  Err(message.into())
}

/// The KZG parameters a compression proves under: admitted Ignition
/// parameters, or with `development` the known-trapdoor development setup.
#[derive(Clone)]
pub enum SetupConfig {
  #[non_exhaustive]
  Ignition {
    cache: PathBuf,
    manifest: [u8; 32],
    admission: Arc<IgnitionAdmission>,
  },
  #[non_exhaustive]
  Development { cache_directory: Option<PathBuf> },
}

impl SetupConfig {
  /// Select the setup from the `IX_KZG_IGNITION_*` variables or the
  /// parameters directory, admitting Ignition parameters before returning.
  /// With `development`, the development setup caches its SRS files in
  /// `IX_KZG_SRS_CACHE` when set.
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
    let values = IGNITION_ENV_VARS.map(&mut lookup);
    if values.iter().all(Option::is_none) {
      let release = parameters_directory_from(&mut lookup)
        .map(|parameters| IGNITION_RELEASE.directory(&parameters))
        .filter(|directory| IGNITION_RELEASE.present(directory));
      return match release {
        Some(directory) => IGNITION_RELEASE.config(&directory),
        None => development_refused(),
      };
    }
    let [cache, manifest, admission, admission_digest] = values;
    let required = |name, value: Option<OsString>| {
      value.ok_or_else(|| {
        format!("incomplete BN254 Ignition configuration: missing {name}")
      })
    };
    let cache = PathBuf::from(required(IGNITION_CACHE_VAR, cache)?);
    let manifest = parse_ignition_digest(
      IGNITION_CACHE_MANIFEST_VAR,
      &required(IGNITION_CACHE_MANIFEST_VAR, manifest)?,
    )?;
    let admission_path =
      PathBuf::from(required(IGNITION_ADMISSION_VAR, admission)?);
    let admission_digest = parse_ignition_digest(
      IGNITION_ADMISSION_DIGEST_VAR,
      &required(IGNITION_ADMISSION_DIGEST_VAR, admission_digest)?,
    )?;
    Self::ignition(cache, manifest, &admission_path, admission_digest)
  }

  fn ignition(
    cache: PathBuf,
    manifest: [u8; 32],
    admission_path: &Path,
    admission_digest: [u8; 32],
  ) -> storage::Result<Self> {
    let admission =
      Arc::new(IgnitionAdmission::read(admission_path, admission_digest)?);
    let (anchors, identity) =
      load_ignition_cache_with_identity(&cache, manifest, 2)?;
    admission.check_cache(&anchors, &identity)?;
    Ok(Self::Ignition { cache, manifest, admission })
  }

  pub(crate) fn ignition_admission(&self) -> Option<&IgnitionAdmission> {
    match self {
      Self::Ignition { admission, .. } => Some(admission),
      Self::Development { .. } => None,
    }
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
      Self::Ignition { cache, manifest, admission } => {
        let source =
          SetupSource::ignition(cache.clone(), *manifest, admission.clone());
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
  Development {
    seed: Vec<u8>,
    cache_directory: Option<PathBuf>,
  },
  Ignition {
    cache: PathBuf,
    manifest: [u8; 32],
    admission: Arc<IgnitionAdmission>,
  },
}

#[derive(Clone)]
pub(crate) struct SetupSource {
  policy: Policy,
  public_setup: PublicSetup,
  transcript_kind: TranscriptKind,
}

fn parse_ignition_digest(
  variable: &str,
  value: &OsStr,
) -> storage::Result<[u8; 32]> {
  let text = value
    .to_str()
    .ok_or_else(|| format!("{variable} must contain an ASCII BLAKE3 digest"))?
    .trim();
  if text.len() != 64 || !text.bytes().all(|byte| byte.is_ascii_hexdigit()) {
    return Err(
      format!("{variable} must be a 64-character BLAKE3 digest").into(),
    );
  }
  let mut digest = [0; 32];
  for (byte, pair) in digest.iter_mut().zip(text.as_bytes().as_chunks::<2>().0)
  {
    let pair = std::str::from_utf8(pair).expect("validated ASCII hex");
    *byte = u8::from_str_radix(pair, 16)?;
  }
  Ok(digest)
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

  /// Verification uses admitted anchors directly. Proving additionally
  /// authenticates the requested cache prefix and matches its provenance.
  pub(crate) fn ignition(
    cache: PathBuf,
    manifest: [u8; 32],
    admission: Arc<IgnitionAdmission>,
  ) -> Self {
    Self {
      public_setup: admission.public_setup(),
      policy: Policy::Ignition { cache, manifest, admission },
      transcript_kind: TranscriptKind::Blake3,
    }
  }

  pub(crate) fn ignition_admission(&self) -> Option<&IgnitionAdmission> {
    match &self.policy {
      Policy::Ignition { admission, .. } => Some(admission),
      Policy::Development { .. } => None,
    }
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
        "Aztec Ignition BN254 powers of tau, with setup identity, full public degree and shifted-basis anchors authorized by an independently pinned admission. Proving prefixes are authenticated against a separate cache receipt. Ceremony provenance depends on the admission's trusted source pins.\n"
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
      Policy::Ignition { admission, .. } if verify_only => {
        Ok(admission.anchors())
      },
      Policy::Ignition { cache, manifest, admission } => {
        let (srs, identity) =
          load_ignition_cache_with_identity(cache, *manifest, length)?;
        admission.check_cache(&srs, &identity)?;
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
  fn bn254_requires_an_admission_or_explicit_development_setup()
  -> storage::Result<()> {
    if IGNITION_ENV_VARS.iter().all(|name| std::env::var_os(name).is_none()) {
      let error = SetupConfig::from_env(false).err().unwrap().to_string();
      assert!(error.contains("BN254"));
      assert!(error.contains("--dev-kzg-srs"));
    }
    let source = SetupConfig::from_env(true)?.for_stage(FIRST_SEED, 8)?;
    assert_eq!(source.class(), SetupClass::Development);
    assert_eq!(
      SetupClass::of(&source.verifier_params(8)?),
      SetupClass::Development
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
