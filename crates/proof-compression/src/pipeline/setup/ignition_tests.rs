use super::*;
use crate::kzg::srs::ignition::{
  IgnitionCacheIdentity, test_admission, test_admission_cache,
};
use std::{
  collections::BTreeMap,
  sync::atomic::{AtomicU64, Ordering},
};

static NEXT_DIRECTORY: AtomicU64 = AtomicU64::new(0);

struct Fixture {
  directory: PathBuf,
  cache: PathBuf,
  admission_path: PathBuf,
  admission: Arc<IgnitionAdmission>,
  admission_digest: [u8; 32],
  receipt: IgnitionCacheIdentity,
  srs: Srs,
}

impl Fixture {
  fn new(tau: u64, marker: u8) -> Self {
    let directory = std::env::temp_dir().join(format!(
      "ix-ignition-setup-{}-{}",
      std::process::id(),
      NEXT_DIRECTORY.fetch_add(1, Ordering::Relaxed),
    ));
    fs::create_dir(&directory).unwrap();
    let (admission, srs) = test_admission(tau, 16, marker);
    let cache = directory.join("prefix.bin");
    let receipt = test_admission_cache(&cache, &admission, &srs);
    let admission_path = directory.join("admission.json");
    let bytes = admission.to_bytes().unwrap();
    fs::write(&admission_path, &bytes).unwrap();
    let admission_digest = *blake3::hash(&bytes).as_bytes();
    Self {
      directory,
      cache,
      admission_path,
      admission: Arc::new(admission),
      admission_digest,
      receipt,
      srs,
    }
  }

  fn configuration(&self) -> SetupConfig {
    SetupConfig::Ignition {
      cache: self.cache.clone(),
      manifest: self.receipt.digest,
      admission: self.admission.clone(),
    }
  }

  fn environment(&self) -> BTreeMap<&'static str, OsString> {
    BTreeMap::from([
      (IGNITION_CACHE_VAR, self.cache.as_os_str().to_owned()),
      (IGNITION_CACHE_MANIFEST_VAR, digest_text(self.receipt.digest).into()),
      (IGNITION_ADMISSION_VAR, self.admission_path.as_os_str().to_owned()),
      (
        IGNITION_ADMISSION_DIGEST_VAR,
        digest_text(self.admission_digest).into(),
      ),
    ])
  }
}

impl Drop for Fixture {
  fn drop(&mut self) {
    let _ = fs::remove_dir_all(&self.directory);
  }
}

fn digest_text(digest: [u8; 32]) -> String {
  blake3::Hash::from(digest).to_hex().to_string()
}

fn parse_environment(
  values: &BTreeMap<&'static str, OsString>,
) -> storage::Result<SetupConfig> {
  SetupConfig::from_ignition_env(false, |name| values.get(name).cloned())
}

#[test]
fn ignition_class_requires_admitted_identity_degree_and_every_anchor() {
  let (admission, srs) = test_admission(7, 16, 1);
  let params = VerifierParams::from_srs(&srs);
  assert_eq!(SetupClass::of(&params), SetupClass::Development);
  assert_eq!(
    SetupClass::of_with_ignition(&params, &admission).unwrap(),
    SetupClass::Ignition,
  );
  let mut changed = Vec::new();
  let mut params_changed = params.clone();
  params_changed.public_setup.id[0] ^= 1;
  changed.push(params_changed);
  let mut params_changed = params.clone();
  params_changed.public_setup.max_degree += 1;
  changed.push(params_changed);
  for i in 0..2 {
    let mut params_changed = params.clone();
    params_changed.g1[i] = -params_changed.g1[i];
    changed.push(params_changed);
  }
  let mut params_changed = params.clone();
  params_changed.g2 = -params_changed.g2;
  changed.push(params_changed);
  let mut params_changed = params.clone();
  params_changed.tau_g2 = -params_changed.tau_g2;
  changed.push(params_changed);
  for params in changed {
    assert!(SetupClass::of_with_ignition(&params, &admission).is_err());
    assert_eq!(SetupClass::of(&params), SetupClass::Development);
  }
  let development = Srs::unsafe_dev_setup(16, b"admission-substitution");
  assert!(
    SetupClass::of_with_ignition(
      &VerifierParams::from_srs(&development),
      &admission,
    )
    .is_err()
  );
}

#[test]
fn ignition_prefixes_preserve_identity_and_verification_needs_no_cache()
-> storage::Result<()> {
  let fixture = Fixture::new(7, 2);
  let config = fixture.configuration();
  assert_eq!(config.class(), SetupClass::Ignition);
  assert_eq!(
    config.ignition_admission().unwrap().public_setup(),
    fixture.srs.public_setup,
  );
  let source = config.for_stage(FIRST_SEED, 8)?;
  assert_eq!(source.class(), SetupClass::Ignition);
  assert_eq!(
    source.ignition_admission().unwrap().public_setup(),
    fixture.srs.public_setup,
  );
  let prefix = source.srs(8, false)?;
  assert_eq!(prefix.g1, fixture.srs.g1[..8]);
  assert_eq!(prefix.public_setup, fixture.srs.public_setup);
  assert_eq!(prefix.public_setup.max_degree, 15);
  assert_eq!(
    source.config(8, 2, false)?.transcript_seed(),
    source.config(8, 2, true)?.transcript_seed(),
  );
  assert!(config.for_stage(FIRST_SEED, 32).is_err());
  assert!(source.srs(32, true).is_err());
  assert!(source.srs(3, true).is_err());
  fs::remove_file(&fixture.cache)?;
  let verifier = source.srs(16, true)?;
  assert_eq!(verifier.g1, fixture.srs.g1[..2]);
  assert_eq!(verifier.public_setup, fixture.srs.public_setup);
  assert!(source.srs(16, false).is_err());
  Ok(())
}

#[test]
fn ignition_stage_seeds_and_cache_locations_do_not_change_public_identity()
-> storage::Result<()> {
  let fixture = Fixture::new(7, 3);
  let config = fixture.configuration();
  let first = config.for_stage(FIRST_SEED, 8)?;
  let recursive = config.for_stage(b"recursive-stage", 8)?;
  assert_eq!(first.identity(8, 2)?, recursive.identity(8, 2)?);
  let missing = SetupSource::ignition(
    fixture.directory.join("missing"),
    [0; 32],
    fixture.admission.clone(),
  )
  .with_cache_directory(fixture.directory.join("development-cache"));
  assert_eq!(first.identity(8, 2)?, missing.identity(8, 2)?);
  assert!(missing.srs(8, false).is_err());
  assert!(!fixture.directory.join("development-cache").exists());
  assert_ne!(first.identity(8, 2)?, first.identity(4, 2)?);
  assert_ne!(first.identity(8, 2)?, first.identity(8, 4)?);
  assert_ne!(
    first.identity(8, 2)?,
    first.clone().with_transcript(TranscriptKind::Keccak256).identity(8, 2)?,
  );
  let (other_admission, _) = test_admission(7, 16, 4);
  let other = SetupSource::ignition(
    fixture.cache.clone(),
    fixture.receipt.digest,
    Arc::new(other_admission),
  );
  assert_ne!(first.identity(8, 2)?, other.identity(8, 2)?);
  assert!(other.srs(8, false).is_err());
  Ok(())
}

#[test]
fn ignition_cache_receipt_must_match_admitted_provenance() {
  let fixture = Fixture::new(7, 5);
  fixture.admission.check_cache(&fixture.srs, &fixture.receipt).unwrap();
  let mut changed = fixture.receipt;
  changed.source_manifest_digest[0] ^= 1;
  assert!(fixture.admission.check_cache(&fixture.srs, &changed).is_err());
  let mut changed = fixture.receipt;
  changed.public_setup.id[0] ^= 1;
  assert!(fixture.admission.check_cache(&fixture.srs, &changed).is_err());
  let mut changed = fixture.receipt;
  changed.public_setup.max_degree += 1;
  assert!(fixture.admission.check_cache(&fixture.srs, &changed).is_err());
  let other = Fixture::new(11, 6);
  let wrong_cache = SetupSource::ignition(
    other.cache.clone(),
    other.receipt.digest,
    fixture.admission.clone(),
  );
  assert!(wrong_cache.srs(8, false).is_err());
}

#[test]
fn ignition_environment_requires_every_value_and_authenticates_before_stages()
-> storage::Result<()> {
  let fixture = Fixture::new(7, 7);
  let environment = fixture.environment();
  let config = parse_environment(&environment)?;
  assert_eq!(config.class(), SetupClass::Ignition);
  for mask in 0usize..15 {
    let partial: BTreeMap<_, _> = IGNITION_ENV_VARS
      .iter()
      .enumerate()
      .filter(|(i, _)| mask & (1 << *i) != 0)
      .map(|(_, name)| (*name, environment[*name].clone()))
      .collect();
    assert!(parse_environment(&partial).is_err());
  }
  for variable in [IGNITION_CACHE_MANIFEST_VAR, IGNITION_ADMISSION_DIGEST_VAR] {
    for bad in ["".to_owned(), "g".repeat(64), "0".repeat(63)] {
      let mut changed = environment.clone();
      changed.insert(variable, bad.into());
      assert!(parse_environment(&changed).is_err());
    }
    let mut changed = environment.clone();
    changed.insert(variable, digest_text([0; 32]).into());
    assert!(parse_environment(&changed).is_err());
  }
  let other = Fixture::new(11, 8);
  let mut changed = environment.clone();
  changed.insert(
    IGNITION_ADMISSION_VAR,
    other.admission_path.as_os_str().to_owned(),
  );
  changed.insert(
    IGNITION_ADMISSION_DIGEST_VAR,
    digest_text(other.admission_digest).into(),
  );
  assert!(parse_environment(&changed).is_err());
  fs::remove_file(&fixture.cache)?;
  assert!(parse_environment(&environment).is_err());
  assert!(config.for_stage(FIRST_SEED, 8)?.srs(8, true).is_ok());
  assert!(config.for_stage(FIRST_SEED, 8)?.srs(8, false).is_err());
  Ok(())
}

#[test]
fn explicit_development_ignores_production_configuration() -> storage::Result<()>
{
  let config = SetupConfig::from_ignition_env(true, |name| {
    assert_eq!(name, "IX_KZG_SRS_CACHE");
    Some("development-cache".into())
  })?;
  assert_eq!(config.class(), SetupClass::Development);
  assert!(config.ignition_admission().is_none());
  assert!(config.for_stage(FIRST_SEED, 8)?.ignition_admission().is_none());
  assert_eq!(
    config.for_stage(FIRST_SEED, 8)?.identity(8, 2)?,
    SetupSource::development(FIRST_SEED, 7)?.identity(8, 2)?,
  );
  Ok(())
}

#[cfg(unix)]
#[test]
fn ignition_digest_parser_rejects_non_unicode_values() {
  use std::os::unix::ffi::OsStringExt;
  let value = OsString::from_vec(vec![0xff; 64]);
  assert!(parse_ignition_digest(IGNITION_CACHE_MANIFEST_VAR, &value).is_err());
  assert_eq!(
    parse_ignition_digest(
      IGNITION_CACHE_MANIFEST_VAR,
      OsStr::new(&"ab".repeat(32))
    )
    .unwrap(),
    [0xab; 32],
  );
}
