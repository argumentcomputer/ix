use super::*;

#[test]
fn release_parameters_fix_identity_degree_and_anchors() -> storage::Result<()> {
  let release = verifying_keys::ignition_parameters()?;
  assert_eq!(SetupClass::of(&release), SetupClass::Ignition);
  for index in 0..6 {
    let mut changed = release.clone();
    match index {
      0 => changed.public_setup.id[0] ^= 1,
      1 => changed.public_setup.max_degree += 1,
      2 => changed.g1[0] = -changed.g1[0],
      3 => changed.g1[1] = -changed.g1[1],
      4 => changed.g2 = -changed.g2,
      _ => changed.tau_g2 = -changed.tau_g2,
    }
    assert_eq!(SetupClass::of(&changed), SetupClass::Development);
  }
  let source = SetupSource::ignition(PathBuf::from("absent-srs.bin"))?;
  assert_eq!(source.class(), SetupClass::Ignition);
  assert_eq!(source.srs(8, true)?.g1, release.g1);
  assert!(source.srs(8, false).is_err());
  Ok(())
}

#[test]
fn release_identity_does_not_depend_on_path_or_stage() -> storage::Result<()> {
  let a = SetupConfig::Ignition { srs: PathBuf::from("a.bin") }
    .for_stage(FIRST_SEED, 8)?;
  let b = SetupConfig::Ignition { srs: PathBuf::from("b.bin") }
    .for_stage(b"other-stage", 8)?;
  assert_eq!(a.identity(8, 2)?, b.identity(8, 2)?);
  assert_ne!(a.identity(8, 2)?, a.identity(4, 2)?);
  assert_ne!(a.identity(8, 2)?, a.identity(8, 4)?);
  assert_ne!(
    a.identity(8, 2)?,
    a.clone().with_transcript(TranscriptKind::Keccak256).identity(8, 2)?
  );
  Ok(())
}

#[test]
fn missing_release_requires_explicit_development() -> storage::Result<()> {
  let error = SetupConfig::from_ignition_env(false, |_| None).err().unwrap();
  assert!(error.to_string().contains("fetch-params"));
  let config = SetupConfig::from_ignition_env(true, |name| {
    assert_eq!(name, "IX_KZG_SRS_CACHE");
    Some("development-cache".into())
  })?;
  assert_eq!(config.class(), SetupClass::Development);
  assert_eq!(
    config.for_stage(FIRST_SEED, 8)?.identity(8, 2)?,
    SetupSource::development(FIRST_SEED, 7)?.identity(8, 2)?
  );
  Ok(())
}

#[test]
#[ignore = "requires the released native gnark SRS under IX_KZG_SRS or IX_PARAMS_DIR"]
fn installed_gnark_srs_matches_release() -> storage::Result<()> {
  let config = SetupConfig::from_env(false)?;
  let source = config.for_stage(FIRST_SEED, 1024)?;
  let srs = source.srs(1024, false)?;
  srs.validate()?;
  assert_eq!(
    SetupClass::of(&VerifierParams::from_srs(&srs)),
    SetupClass::Ignition
  );
  assert_eq!(
    source.config(1024, 2, true)?.transcript_seed(),
    source.config(1024, 2, false)?.transcript_seed()
  );
  Ok(())
}
