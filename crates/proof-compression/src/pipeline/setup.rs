//! Compression setup selection and binding for BN254 (Ignition) and BLS12-381
//! (Filecoin `challenge_19`), plus explicitly requested known-trapdoor
//! development setups for either curve.
//!
//! For BN254, the released verifying keys authorize the Ignition parameters.
//! For BLS12-381, the Filecoin policy loads an authenticated prefix of the
//! `challenge_19` ($2^{27}$) phase-one powers of tau from the cache named by
//! `IX_KZG_FILECOIN_CACHE` (or `$IX_PARAMS_DIR/bls12-381-filecoin-challenge19/filecoin-prefix-2p27.bin`),
//! pinned by `IX_KZG_FILECOIN_MANIFEST` or the built-in `2^27` receipt.
use super::{storage, verifying_keys};
use crate::kzg::{
  KzgConfig, PublicSetup, Srs, TranscriptKind, VerifierParams,
  curve::{Bls12381, Bn254, Curve, KzgCurve},
  field::CurveScalar,
  srs::{
    filecoin::{
      FILECOIN_PREFIX_2P27_MANIFEST_BLAKE3, filecoin_anchors,
      load_filecoin_cache,
    },
    gnark,
  },
};
use multi_stark::traits::TwoAdicField;
use std::ffi::OsString;
use std::marker::PhantomData;
use std::{
  fs,
  path::{Path, PathBuf},
  sync::Arc,
};

pub(crate) const FIRST_SEED: &[u8] = b"init-fri-kzg-ordinary-v1";
pub(crate) const BINDING_FILE: &str = "kzg-setup-id.bin";
pub(crate) const IGNITION_SRS_VAR: &str = "IX_KZG_SRS";
pub(crate) const FILECOIN_CACHE_VAR: &str = "IX_KZG_FILECOIN_CACHE";
pub(crate) const FILECOIN_MANIFEST_VAR: &str = "IX_KZG_FILECOIN_MANIFEST";
pub(crate) const PARAMETERS_DIR_VAR: &str = "IX_PARAMS_DIR";
const IGNITION_DIRECTORY: &str = "bn254-ignition-main-197";
const IGNITION_FILE: &str = "srs.bin";
const FILECOIN_DIRECTORY: &str = "bls12-381-filecoin-challenge19";
const FILECOIN_FILE: &str = "filecoin-prefix-2p27.bin";

/// `IX_PARAMS_DIR`, else `$HOME/.ix/compression/params`.
fn parameters_directory_from(
  mut lookup: impl FnMut(&str) -> Option<OsString>,
) -> Option<PathBuf> {
  lookup(PARAMETERS_DIR_VAR).map(PathBuf::from).or_else(|| {
    lookup("HOME")
      .map(|home| PathBuf::from(home).join(".ix/compression/params"))
  })
}

fn parse_manifest_digest(name: &str, text: &str) -> storage::Result<[u8; 32]> {
  let text = text.trim();
  let text = text.strip_prefix("0x").unwrap_or(text);
  if text.len() != 64 || !text.is_ascii() {
    return Err(
      format!("{name} must be a 64-character hex BLAKE3 digest").into(),
    );
  }
  let mut out = [0u8; 32];
  for (i, slot) in out.iter_mut().enumerate() {
    *slot = u8::from_str_radix(&text[2 * i..2 * i + 2], 16)
      .map_err(|err| format!("{name} contains non-hex characters: {err}"))?;
  }
  Ok(out)
}

/// The trust class of verifier parameters.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SetupClass {
  /// Ignition parameters matching the released BN254 verifying key.
  Ignition,
  /// Filecoin `challenge_19` ($2^{27}$) phase-one powers of tau for BLS12-381.
  Filecoin,
  /// A trapdoor derived from a seed; anyone can forge proofs.
  Development,
  /// A circuit-specific Groth16 key admitted independently of the proof.
  Groth16,
}

impl SetupClass {
  /// Match the complete setup identity and anchors authorized by the curve's
  /// production ceremony.
  pub fn of<C: KzgCurve>(params: &VerifierParams<C>) -> Self {
    match C::CURVE {
      Curve::Bn254 => {
        let matches =
          verifying_keys::ignition_parameters().is_ok_and(|release| {
            let Ok(actual) = params.to_bytes() else {
              return false;
            };
            let Ok(actual) = VerifierParams::<Bn254>::from_bytes(&actual)
            else {
              return false;
            };
            actual.public_setup == release.public_setup
              && actual.g1 == release.g1
              && actual.g2 == release.g2
              && actual.tau_g2 == release.tau_g2
          });
        if matches { Self::Ignition } else { Self::Development }
      },
      Curve::Bls12381 => {
        let Ok(actual) = params.to_bytes() else {
          return Self::Development;
        };
        let Ok(actual) = VerifierParams::<Bls12381>::from_bytes(&actual) else {
          return Self::Development;
        };
        let pinned = filecoin_anchors();
        if actual.public_setup == pinned.public_setup
          && actual.g1 == [pinned.g1[0], pinned.g1[1]]
          && actual.g2 == pinned.g2
          && actual.tau_g2 == pinned.tau_g2
        {
          Self::Filecoin
        } else {
          Self::Development
        }
      },
    }
  }

  pub fn label(self) -> &'static str {
    match self {
      Self::Ignition => "ignition",
      Self::Filecoin => "filecoin",
      Self::Groth16 => "groth16",
      Self::Development => "development",
    }
  }

  pub fn description(self) -> &'static str {
    match self {
      Self::Ignition => "the released Aztec Ignition BN254 powers of tau",
      Self::Filecoin => {
        "the Filecoin challenge_19 (2^27) BLS12-381 phase-one powers of tau"
      },
      Self::Groth16 => "an admitted Groth16 circuit-specific ceremony",
      Self::Development => {
        "a known-trapdoor development SRS (not production-secure)"
      },
    }
  }
}

fn bn254_development_refused<T>() -> storage::Result<T> {
  Err(
    format!(
      "no BN254 Ignition SRS is installed; run `ix compress setup`, \
     set {IGNITION_SRS_VAR} to the released gnark SRS, or pass --dev-kzg-srs \
     to use the known-trapdoor development setup (not production-secure)"
    )
    .into(),
  )
}

fn bls12_381_development_refused<T>() -> storage::Result<T> {
  Err(
    format!(
      "no BLS12-381 Filecoin challenge_19 SRS cache is installed; set \
     {FILECOIN_CACHE_VAR} to an authenticated prefix cache (optionally \
     {FILECOIN_MANIFEST_VAR} for a non-2^27 prefix), or pass --dev-kzg-srs \
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
  Filecoin { cache: PathBuf, manifest: [u8; 32] },
  #[non_exhaustive]
  Development { cache_directory: Option<PathBuf> },
}

impl SetupConfig {
  /// Select the release BN254 SRS or the explicitly requested development setup.
  pub fn from_env(development: bool) -> storage::Result<Self> {
    Self::from_env_for_curve(Curve::Bn254, development)
  }

  /// Select the curve's ceremony SRS or the explicitly requested development setup.
  pub fn from_env_for_curve(
    curve: Curve,
    development: bool,
  ) -> storage::Result<Self> {
    match curve {
      Curve::Bn254 => {
        Self::from_ignition_env(development, |name| std::env::var_os(name))
      },
      Curve::Bls12381 => {
        Self::from_filecoin_env(development, |name| std::env::var_os(name))
      },
    }
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
      return bn254_development_refused();
    };
    let config = Self::Ignition { srs };
    config.for_stage::<Bn254>(FIRST_SEED, 2)?.srs(2, false)?;
    Ok(config)
  }

  fn from_filecoin_env(
    development: bool,
    mut lookup: impl FnMut(&str) -> Option<OsString>,
  ) -> storage::Result<Self> {
    if development {
      return Ok(Self::Development {
        cache_directory: lookup("IX_KZG_SRS_CACHE").map(PathBuf::from),
      });
    }
    let path = lookup(FILECOIN_CACHE_VAR).map(PathBuf::from).or_else(|| {
      parameters_directory_from(&mut lookup)
        .map(|directory| directory.join(FILECOIN_DIRECTORY).join(FILECOIN_FILE))
    });
    let Some(cache) = path.filter(|path| path.is_file()) else {
      return bls12_381_development_refused();
    };
    let manifest = match lookup(FILECOIN_MANIFEST_VAR) {
      Some(value) => {
        let text = value
          .to_str()
          .ok_or(format!("{FILECOIN_MANIFEST_VAR} must be valid UTF-8"))?;
        parse_manifest_digest(FILECOIN_MANIFEST_VAR, text)?
      },
      None => FILECOIN_PREFIX_2P27_MANIFEST_BLAKE3,
    };
    let config = Self::Filecoin { cache, manifest };
    config.for_stage::<Bls12381>(FIRST_SEED, 2)?.srs(2, false)?;
    Ok(config)
  }

  pub(crate) fn class(&self) -> SetupClass {
    match self {
      Self::Ignition { .. } => SetupClass::Ignition,
      Self::Filecoin { .. } => SetupClass::Filecoin,
      Self::Development { .. } => SetupClass::Development,
    }
  }

  pub(crate) fn for_stage<C: KzgCurve>(
    &self,
    seed: &[u8],
    height: usize,
  ) -> storage::Result<SetupSource<C>> {
    if height < 2
      || !height.is_power_of_two()
      || height.ilog2() as usize > CurveScalar::<C>::TWO_ADICITY
    {
      return Err("invalid trace height".into());
    }
    match self {
      Self::Ignition { srs } => {
        if C::CURVE != Curve::Bn254 {
          return Err(
            "BN254 Ignition SRS cannot be used with BLS12-381".into(),
          );
        }
        let source = SetupSource::<C>::ignition(srs.clone())?;
        source.check_height(height)?;
        Ok(source)
      },
      Self::Filecoin { cache, manifest } => {
        if C::CURVE != Curve::Bls12381 {
          return Err(
            "BLS12-381 Filecoin SRS cannot be used with BN254".into(),
          );
        }
        let source = SetupSource::<C>::filecoin(cache.clone(), *manifest)?;
        source.check_height(height)?;
        Ok(source)
      },
      Self::Development { cache_directory } => {
        let mut source = SetupSource::<C>::development(seed, height - 1)?;
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
  Filecoin { cache: PathBuf, manifest: [u8; 32] },
}

pub(crate) struct SetupSource<C: KzgCurve = Bn254> {
  policy: Policy,
  public_setup: PublicSetup,
  transcript_kind: TranscriptKind,
  _curve: PhantomData<C>,
}

impl<C: KzgCurve> Clone for SetupSource<C> {
  fn clone(&self) -> Self {
    Self {
      policy: self.policy.clone(),
      public_setup: self.public_setup,
      transcript_kind: self.transcript_kind,
      _curve: PhantomData,
    }
  }
}

impl<C: KzgCurve> SetupSource<C> {
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
      public_setup: PublicSetup::known_trapdoor_for::<C>(
        public_max_degree,
        seed,
      ),
      transcript_kind: TranscriptKind::Blake3,
      _curve: PhantomData,
    })
  }

  pub(crate) fn ignition(srs: PathBuf) -> storage::Result<Self> {
    if C::CURVE != Curve::Bn254 {
      return Err("Ignition setup is only valid for BN254".into());
    }
    Ok(Self {
      public_setup: verifying_keys::ignition_parameters()?.public_setup,
      policy: Policy::Ignition { srs },
      transcript_kind: TranscriptKind::Blake3,
      _curve: PhantomData,
    })
  }

  pub(crate) fn filecoin(
    cache: PathBuf,
    manifest: [u8; 32],
  ) -> storage::Result<Self> {
    if C::CURVE != Curve::Bls12381 {
      return Err("Filecoin setup is only valid for BLS12-381".into());
    }
    Ok(Self {
      public_setup: filecoin_anchors().public_setup,
      policy: Policy::Filecoin { cache, manifest },
      transcript_kind: TranscriptKind::Blake3,
      _curve: PhantomData,
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
      Policy::Ignition { .. } | Policy::Filecoin { .. } => {},
    }
    self
  }

  pub(crate) fn class(&self) -> SetupClass {
    match self.policy {
      Policy::Development { .. } => SetupClass::Development,
      Policy::Ignition { .. } => SetupClass::Ignition,
      Policy::Filecoin { .. } => SetupClass::Filecoin,
    }
  }

  pub(crate) fn security_description(&self) -> &'static str {
    match self.policy {
      Policy::Ignition { .. } => {
        "Aztec Ignition BN254 powers of tau (~100b classical / 0b PQ, pre-Pectra EVM, AGM/q-SDH + Ignition SRS; gnark ZK vs non-ZK final-kzg). Verification uses the fixed release keys.\n"
      },
      Policy::Filecoin { .. } => {
        "Filecoin challenge_19 (2^27) BLS12-381 phase-one powers of tau (~126–128b classical / 0b PQ, EIP-2537, AGM/q-SDH + Filecoin challenge_19 SRS; gnark ZK vs non-ZK final-kzg).\n"
      },
      Policy::Development { .. } => {
        "Known-trapdoor development public-degree KZG. Not ceremony parameters. For development and testing only.\n"
      },
    }
  }

  fn check_height(&self, height: usize) -> storage::Result<()> {
    if height < 2
      || !height.is_power_of_two()
      || height.ilog2() as usize > CurveScalar::<C>::TWO_ADICITY
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
  ) -> storage::Result<Srs<C>> {
    self.check_height(height)?;
    let length = if verify_only { 2 } else { height };
    match &self.policy {
      Policy::Ignition { .. } if verify_only => {
        let anchors = verifying_keys::ignition_anchors()?;
        convert_srs::<Bn254, C>(anchors)
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
        convert_srs::<Bn254, C>(srs)
      },
      Policy::Filecoin { .. } if verify_only => {
        convert_srs::<Bls12381, C>(filecoin_anchors())
      },
      Policy::Filecoin { cache, manifest } => {
        let srs = load_filecoin_cache(cache, *manifest, length)?;
        if SetupClass::of(&VerifierParams::from_srs(&srs))
          != SetupClass::Filecoin
        {
          return Err(
            "SRS anchors differ from the pinned Filecoin challenge_19 parameters"
              .into(),
          );
        }
        convert_srs::<Bls12381, C>(srs)
      },
      Policy::Development { seed, cache_directory } => {
        if !verify_only && let Some(directory) = cache_directory {
          return Ok(Srs::<C>::unsafe_dev_setup_prefix_in_cache_directory(
            length,
            self.public_setup.max_degree,
            seed,
            directory,
          )?);
        }
        Ok(Srs::<C>::unsafe_dev_setup_prefix(
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
  ) -> storage::Result<VerifierParams<C>> {
    Ok(VerifierParams::with_max_trace_len(&self.srs(height, true)?, height))
  }

  pub(crate) fn config(
    &self,
    height: usize,
    quotient: usize,
    verify_only: bool,
  ) -> storage::Result<KzgConfig<C>> {
    self.check_height(height)?;
    if !quotient.is_power_of_two() {
      return Err("invalid quotient budget".into());
    }
    if height.ilog2() as usize + quotient.ilog2() as usize
      > CurveScalar::<C>::TWO_ADICITY
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

/// Safe type-level cast between identical `Srs<From>` and `Srs<To>` verified
/// at runtime via `From::CURVE == To::CURVE` and `Any::downcast`.
fn convert_srs<From: KzgCurve, To: KzgCurve>(
  srs: Srs<From>,
) -> storage::Result<Srs<To>> {
  let boxed: Box<dyn std::any::Any> = Box::new(srs);
  boxed
    .downcast::<Srs<To>>()
    .map(|b| *b)
    .map_err(|_unmatched| "curve mismatch while loading ceremony SRS".into())
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::test_support::TempDir;

  fn check_setup_binding<C: KzgCurve>() -> storage::Result<()> {
    let dir = TempDir::new(&format!("setup-binding-{}", C::NAME));
    let setup = SetupSource::<C>::development(b"setup-binding", 63)?;
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
      SetupSource::<C>::development(b"other", 63)?
        .check_binding(&dir, 64, 2)
        .is_err()
    );
    assert!(
      SetupSource::<C>::development(b"setup-binding", 127)?
        .check_binding(&dir, 64, 2)
        .is_err()
    );
    assert!(setup.config(128, 2, true).is_err());
    Ok(())
  }

  #[test]
  fn setup_binding_preserves_public_identity_and_rejects_mismatch()
  -> storage::Result<()> {
    check_setup_binding::<Bn254>()?;
    check_setup_binding::<Bls12381>()?;
    Ok(())
  }

  #[test]
  fn cache_directory_yields_the_generated_parameters() -> storage::Result<()> {
    let dir = TempDir::new("setup-cache-dir");
    let generated = SetupSource::<Bn254>::development(b"setup-cache", 63)?;
    let directory = SetupSource::<Bn254>::development(b"setup-cache", 63)?
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
    Ok(())
  }

  #[test]
  fn setup_rejects_unsupported_trace_and_quotient_domains()
  -> storage::Result<()> {
    let max_height = 1usize << crate::kzg::Scalar::TWO_ADICITY;
    let source =
      SetupSource::<Bn254>::development(FIRST_SEED, max_height * 2 - 1)?;
    assert!(source.config(max_height / 2, 2, true).is_ok());
    assert!(source.config(max_height, 1, true).is_ok());
    assert!(source.config(max_height, 2, true).is_err());
    assert!(source.verifier_params(max_height * 2).is_err());
    assert!(source.config(8, 0, true).is_err());
    assert!(source.config(8, 3, true).is_err());
    assert!(
      SetupConfig::from_env(true)?
        .for_stage::<Bn254>(FIRST_SEED, max_height * 2)
        .is_err()
    );
    Ok(())
  }

  #[test]
  fn filecoin_fixture_loads_classifies_and_rejects_cross_curve()
  -> storage::Result<()> {
    use crate::kzg::srs::filecoin::{
      FILECOIN_PREFIX_2P8_FIXTURE, FILECOIN_PREFIX_2P8_MANIFEST_BLAKE3,
    };
    let fixture = PathBuf::from(FILECOIN_PREFIX_2P8_FIXTURE);
    let manifest = FILECOIN_PREFIX_2P8_MANIFEST_BLAKE3;
    let config = SetupConfig::Filecoin { cache: fixture.clone(), manifest };
    assert_eq!(config.class(), SetupClass::Filecoin);
    // Cross-curve rejected immediately.
    assert!(config.for_stage::<Bn254>(FIRST_SEED, 256).is_err());
    let source = config.for_stage::<Bls12381>(FIRST_SEED, 256)?;
    assert_eq!(source.class(), SetupClass::Filecoin);
    let srs = source.srs(256, false)?;
    srs.validate()?;
    let params = VerifierParams::from_srs(&srs);
    assert_eq!(SetupClass::of(&params), SetupClass::Filecoin);
    assert_eq!(
      source.config(256, 2, false)?.transcript_seed(),
      source.config(256, 2, true)?.transcript_seed()
    );
    assert_ne!(
      source.identity(256, 2)?,
      SetupSource::<Bls12381>::development(FIRST_SEED, 255)?
        .identity(256, 2)?
    );
    // Missing Filecoin cache requires explicit --dev-kzg-srs.
    let err = SetupConfig::from_filecoin_env(false, |_| None).err().unwrap();
    assert!(err.to_string().contains(FILECOIN_CACHE_VAR));
    // Env lookup loads the pinned fixture cleanly.
    let loaded = SetupConfig::from_filecoin_env(false, |name| match name {
      FILECOIN_CACHE_VAR => Some(fixture.as_os_str().to_os_string()),
      FILECOIN_MANIFEST_VAR => {
        Some(blake3::Hash::from_bytes(manifest).to_hex().as_str().into())
      },
      _ => None,
    })?;
    assert_eq!(loaded.class(), SetupClass::Filecoin);
    Ok(())
  }
}

#[cfg(test)]
mod ignition_tests;
