//! Setup selection and binding for compression checkpoints.
//!
//! Every setup declares a public identity and full public degree. The
//! Filecoin policy loads an authenticated prefix of the phase-one powers of
//! tau from the cache named by `IX_KZG_FILECOIN_CACHE`, pinned by the manifest
//! receipt in `IX_KZG_FILECOIN_MANIFEST` or, when that is unset, the built-in
//! receipt of the complete `2^27` cache. Filecoin is available only with
//! BLS12-381. BN254's Ignition policy requires independently pinned admission
//! metadata and an authenticated prefix cache. The development policy derives a
//! known trapdoor from the stage seed, with parameters from a per-stage cache
//! file or from the shared directory named by `IX_KZG_SRS_CACHE`.
use super::storage;
#[cfg(not(feature = "bn254"))]
use crate::kzg::srs::filecoin::{
  FILECOIN_PREFIX_2P27_MANIFEST_BLAKE3, filecoin_anchors, load_filecoin_cache,
};
#[cfg(feature = "bn254")]
use crate::kzg::srs::ignition::{
  IgnitionAdmission, load_ignition_cache_with_identity,
};
use crate::kzg::{KzgConfig, PublicSetup, Srs, TranscriptKind, VerifierParams};
use multi_stark::traits::TwoAdicField;
#[cfg(feature = "bn254")]
use std::ffi::{OsStr, OsString};
use std::{
  fs,
  path::{Path, PathBuf},
  sync::Arc,
};

pub(crate) const FIRST_SEED: &[u8] = b"init-fri-kzg-ordinary-v1";
pub(crate) const BINDING_FILE: &str = "kzg-setup-id.bin";
#[cfg(not(feature = "bn254"))]
pub(crate) const FILECOIN_CACHE_VAR: &str = "IX_KZG_FILECOIN_CACHE";
#[cfg(not(feature = "bn254"))]
pub(crate) const FILECOIN_MANIFEST_VAR: &str = "IX_KZG_FILECOIN_MANIFEST";
#[cfg(feature = "bn254")]
pub(crate) const IGNITION_CACHE_VAR: &str = "IX_KZG_IGNITION_CACHE";
#[cfg(feature = "bn254")]
pub(crate) const IGNITION_CACHE_MANIFEST_VAR: &str =
  "IX_KZG_IGNITION_CACHE_BLAKE3";
#[cfg(feature = "bn254")]
pub(crate) const IGNITION_ADMISSION_VAR: &str = "IX_KZG_IGNITION_ADMISSION";
#[cfg(feature = "bn254")]
pub(crate) const IGNITION_ADMISSION_DIGEST_VAR: &str =
  "IX_KZG_IGNITION_ADMISSION_BLAKE3";
#[cfg(feature = "bn254")]
const IGNITION_ENV_VARS: [&str; 4] = [
  IGNITION_CACHE_VAR,
  IGNITION_CACHE_MANIFEST_VAR,
  IGNITION_ADMISSION_VAR,
  IGNITION_ADMISSION_DIGEST_VAR,
];

/// The trust class of verifier parameters.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SetupClass {
  /// Filecoin's phase-one powers of tau. The trapdoor is unknown unless
  /// every ceremony participant colluded. No BN254 parameters have this class.
  Filecoin,
  /// Ignition parameters whose identity, degree and anchors match an
  /// independently pinned admission of the ceremony source.
  #[cfg(feature = "bn254")]
  Ignition,
  /// A trapdoor derived from a seed; anyone can forge proofs.
  Development,
}

impl SetupClass {
  /// Filecoin only when the identity, public degree and all four anchor
  /// points equal the pinned ceremony values; an identity alone is just
  /// bytes any verifying key could carry.
  #[cfg(not(feature = "bn254"))]
  pub fn of(params: &VerifierParams) -> Self {
    let pinned = filecoin_anchors();
    if params.public_setup == pinned.public_setup
      && params.g1 == [pinned.g1[0], pinned.g1[1]]
      && params.g2 == pinned.g2
      && params.tau_g2 == pinned.tau_g2
    {
      Self::Filecoin
    } else {
      Self::Development
    }
  }

  /// Production classification requires independently admitted Ignition
  /// metadata; verifier parameters alone do not establish provenance.
  #[cfg(feature = "bn254")]
  pub fn of(_params: &VerifierParams) -> Self {
    Self::Development
  }

  #[cfg(feature = "bn254")]
  pub fn of_with_ignition(
    params: &VerifierParams,
    admission: &IgnitionAdmission,
  ) -> storage::Result<Self> {
    admission.check_verifier(params)?;
    Ok(Self::Ignition)
  }

  pub fn label(self) -> &'static str {
    match self {
      Self::Filecoin => "filecoin",
      #[cfg(feature = "bn254")]
      Self::Ignition => "ignition",
      Self::Development => "development",
    }
  }

  pub fn description(self) -> &'static str {
    match self {
      Self::Filecoin => "the Filecoin phase-one powers of tau",
      #[cfg(feature = "bn254")]
      Self::Ignition => "the admitted Aztec Ignition BN254 powers of tau",
      Self::Development => {
        "a known-trapdoor development SRS (not production-secure)"
      },
    }
  }
}

fn development_refused<T>() -> storage::Result<T> {
  #[cfg(feature = "bn254")]
  let message = format!(
    "no admitted BN254 Ignition setup is configured; set \
     {IGNITION_CACHE_VAR}, {IGNITION_CACHE_MANIFEST_VAR}, \
     {IGNITION_ADMISSION_VAR} and {IGNITION_ADMISSION_DIGEST_VAR}, or pass \
     --dev-srs to use the known-trapdoor development setup \
     (not production-secure)"
  );
  #[cfg(not(feature = "bn254"))]
  let message = format!(
    "no Filecoin SRS cache is configured; set {FILECOIN_CACHE_VAR} to an \
     authenticated prefix cache, or pass --dev-srs to use the \
     known-trapdoor development setup (not production-secure)"
  );
  Err(message.into())
}

/// Setup policy captured for one worker invocation.
#[derive(Clone)]
pub(crate) enum SetupConfig {
  #[cfg(not(feature = "bn254"))]
  Filecoin {
    cache: PathBuf,
    manifest: [u8; 32],
  },
  #[cfg(feature = "bn254")]
  Ignition {
    cache: PathBuf,
    manifest: [u8; 32],
    admission: Arc<IgnitionAdmission>,
  },
  Development {
    cache_directory: Option<PathBuf>,
  },
}

impl SetupConfig {
  pub(crate) fn from_env(development: bool) -> storage::Result<Self> {
    #[cfg(feature = "bn254")]
    {
      Self::from_ignition_env(development, |name| std::env::var_os(name))
    }
    #[cfg(not(feature = "bn254"))]
    {
      if development {
        return Ok(Self::Development {
          cache_directory: std::env::var_os("IX_KZG_SRS_CACHE")
            .map(PathBuf::from),
        });
      }
      if let Some(cache) = std::env::var_os(FILECOIN_CACHE_VAR) {
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
        return Ok(Self::Filecoin { cache, manifest });
      }
      development_refused()
    }
  }

  #[cfg(feature = "bn254")]
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
      return development_refused();
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
    let admission =
      Arc::new(IgnitionAdmission::read(&admission_path, admission_digest)?);
    let (anchors, identity) =
      load_ignition_cache_with_identity(&cache, manifest, 2)?;
    admission.check_cache(&anchors, &identity)?;
    Ok(Self::Ignition { cache, manifest, admission })
  }

  #[cfg(feature = "bn254")]
  pub(crate) fn ignition_admission(&self) -> Option<&IgnitionAdmission> {
    match self {
      Self::Ignition { admission, .. } => Some(admission),
      Self::Development { .. } => None,
    }
  }

  pub(crate) fn class(&self) -> SetupClass {
    match self {
      #[cfg(not(feature = "bn254"))]
      Self::Filecoin { .. } => SetupClass::Filecoin,
      #[cfg(feature = "bn254")]
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
      #[cfg(not(feature = "bn254"))]
      Self::Filecoin { cache, manifest } => {
        Ok(SetupSource::filecoin(cache.clone(), *manifest))
      },
      #[cfg(feature = "bn254")]
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
  #[cfg(not(feature = "bn254"))]
  Filecoin {
    cache: PathBuf,
    manifest: [u8; 32],
  },
  #[cfg(feature = "bn254")]
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

#[cfg(not(feature = "bn254"))]
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

#[cfg(feature = "bn254")]
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

  /// Filecoin parameters: pinned anchors for verification, and proving
  /// prefixes from an authenticated cache pinned by its import receipt.
  #[cfg(not(feature = "bn254"))]
  pub(crate) fn filecoin(cache: PathBuf, manifest: [u8; 32]) -> Self {
    Self {
      policy: Policy::Filecoin { cache, manifest },
      public_setup: filecoin_anchors().public_setup,
      transcript_kind: TranscriptKind::Blake3,
    }
  }

  /// Verification uses admitted anchors directly. Proving additionally
  /// authenticates the requested cache prefix and matches its provenance.
  #[cfg(feature = "bn254")]
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

  #[cfg(feature = "bn254")]
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
      #[cfg(not(feature = "bn254"))]
      Policy::Filecoin { .. } => {},
      #[cfg(feature = "bn254")]
      Policy::Ignition { .. } => {},
    }
    self
  }

  pub(crate) fn class(&self) -> SetupClass {
    match self.policy {
      Policy::Development { .. } => SetupClass::Development,
      #[cfg(not(feature = "bn254"))]
      Policy::Filecoin { .. } => SetupClass::Filecoin,
      #[cfg(feature = "bn254")]
      Policy::Ignition { .. } => SetupClass::Ignition,
    }
  }

  pub(crate) fn security_description(&self) -> &'static str {
    match self.class() {
      SetupClass::Filecoin => {
        "Filecoin phase-one powers of tau (challenge_19), authenticated against the published BLAKE2b-512 digest and loaded from a receipt-pinned prefix cache. Public ceremony parameters; the trapdoor is unknown unless every participant colluded.\n"
      },
      #[cfg(feature = "bn254")]
      SetupClass::Ignition => {
        "Aztec Ignition BN254 powers of tau, with setup identity, full public degree and shifted-basis anchors authorized by an independently pinned admission. Proving prefixes are authenticated against a separate cache receipt. Ceremony provenance depends on the admission's trusted source pins.\n"
      },
      SetupClass::Development => {
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
      #[cfg(not(feature = "bn254"))]
      Policy::Filecoin { .. } if verify_only => Ok(filecoin_anchors()),
      #[cfg(not(feature = "bn254"))]
      Policy::Filecoin { cache, manifest } => {
        Ok(load_filecoin_cache(cache, *manifest, length)?)
      },
      #[cfg(feature = "bn254")]
      Policy::Ignition { admission, .. } if verify_only => {
        Ok(admission.anchors())
      },
      #[cfg(feature = "bn254")]
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
  #[cfg(not(feature = "bn254"))]
  use crate::kzg::srs::filecoin::{
    FILECOIN_PREFIX_2P8_FIXTURE, FILECOIN_PREFIX_2P8_MANIFEST_BLAKE3,
  };

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

  #[cfg(not(feature = "bn254"))]
  #[test]
  fn setup_class_requires_the_pinned_anchors_and_identity() {
    let pinned = filecoin_anchors();
    assert_eq!(
      SetupClass::of(&VerifierParams::from_srs(&pinned)),
      SetupClass::Filecoin
    );
    let development = Srs::unsafe_dev_setup(8, FIRST_SEED);
    assert_eq!(
      SetupClass::of(&VerifierParams::from_srs(&development)),
      SetupClass::Development
    );
    // The Filecoin identity over development anchors is not Filecoin.
    let forged = Srs {
      g1: development.g1[..2].to_vec(),
      g2: development.g2,
      tau_g2: development.tau_g2,
      public_setup: pinned.public_setup,
    };
    assert_eq!(
      SetupClass::of(&VerifierParams::from_srs(&forged)),
      SetupClass::Development
    );
    // The pinned anchors under another identity are not Filecoin either.
    let relabeled = Srs {
      g1: pinned.g1.clone(),
      g2: pinned.g2,
      tau_g2: pinned.tau_g2,
      public_setup: PublicSetup {
        max_degree: pinned.public_setup.max_degree - 1,
        id: pinned.public_setup.id,
      },
    };
    assert_eq!(
      SetupClass::of(&VerifierParams::from_srs(&relabeled)),
      SetupClass::Development
    );
    let filecoin = SetupSource::filecoin(PathBuf::from("/missing"), [0; 32]);
    assert_eq!(filecoin.class(), SetupClass::Filecoin);
    assert_eq!(filecoin.public_setup, pinned.public_setup);
    // Verification needs no cache file; proving does.
    assert_eq!(filecoin.srs(1 << 27, true).unwrap().g1, pinned.g1);
    assert!(filecoin.srs(1 << 28, true).is_err());
    assert!(filecoin.srs(1 << 27, false).is_err());
    assert_eq!(
      filecoin.identity(1 << 27, 2).unwrap(),
      SetupSource::filecoin(PathBuf::from("/other"), [1; 32])
        .identity(1 << 27, 2)
        .unwrap()
    );
    assert!(parse_digest(&"0".repeat(63)).is_err());
    assert!(parse_digest(&"g".repeat(64)).is_err());
    assert_eq!(parse_digest(&"00".repeat(32)).unwrap(), [0; 32]);
  }

  #[test]
  fn development_flag_selects_development_parameters() -> storage::Result<()> {
    let config = SetupConfig::from_env(true)?;
    assert_eq!(config.class(), SetupClass::Development);
    assert_eq!(
      config.for_stage(FIRST_SEED, 64)?.identity(64, 2)?,
      SetupSource::development(FIRST_SEED, 63)?.identity(64, 2)?
    );
    #[cfg(not(feature = "bn254"))]
    if std::env::var_os(FILECOIN_CACHE_VAR).is_none() {
      assert!(
        SetupConfig::from_env(false)
          .err()
          .unwrap()
          .to_string()
          .contains("--dev-srs")
      );
    }
    Ok(())
  }

  #[cfg(not(feature = "bn254"))]
  #[test]
  fn checked_in_filecoin_cache_proves_and_binds_under_its_identity()
  -> storage::Result<()> {
    let setup = SetupSource::filecoin(
      PathBuf::from(FILECOIN_PREFIX_2P8_FIXTURE),
      FILECOIN_PREFIX_2P8_MANIFEST_BLAKE3,
    );
    assert!(setup.srs(512, false).is_err());
    let verifier = setup.srs(256, true)?;
    assert_eq!(verifier.max_len(), 2);
    assert_eq!(
      SetupClass::of(&VerifierParams::from_srs(&verifier)),
      SetupClass::Filecoin
    );
    let prover = setup.srs(256, false)?;
    assert_eq!(prover.max_len(), 256);
    assert_eq!(prover.public_setup, verifier.public_setup);
    assert_eq!(prover.g1[..2], verifier.g1[..]);
    assert_eq!(prover.tau_g2, verifier.tau_g2);
    assert_eq!(
      SetupClass::of(&VerifierParams::with_max_trace_len(&prover, 256)),
      SetupClass::Filecoin
    );
    assert_eq!(
      setup.config(256, 2, false)?.transcript_seed(),
      setup.config(256, 2, true)?.transcript_seed()
    );
    assert_ne!(
      setup.identity(256, 2)?,
      SetupSource::development(FIRST_SEED, 255)?.identity(256, 2)?
    );
    Ok(())
  }

  #[cfg(feature = "bn254")]
  #[test]
  fn bn254_requires_an_admission_or_explicit_development_setup()
  -> storage::Result<()> {
    if IGNITION_ENV_VARS.iter().all(|name| std::env::var_os(name).is_none()) {
      let error = SetupConfig::from_env(false).err().unwrap().to_string();
      assert!(error.contains("BN254"));
      assert!(error.contains("--dev-srs"));
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

#[cfg(all(test, feature = "bn254"))]
mod ignition_tests;
