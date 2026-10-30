//! Compression and verification of aggregate root proofs.
mod stages;
pub use stages::{
  FixedRoot, FriVerifier, KzgVerifier, Prepared, RecursiveProof,
  RecursiveStage, RecursiveVerifier, prepare_kzg, prepare_recursive,
  prepare_root,
};

mod compress;
mod derive;
mod development;
pub(crate) use compress::StageConfig;
pub use compress::{CompressConfig, CompressInput, compress};
pub use derive::derive_recursive_vk;
pub use development::verify_with_development_verifier;
mod final_proof;
mod first;
mod fixed_cache;
#[cfg(any(feature = "plonk", feature = "groth16"))]
pub mod gnark;
pub mod groth16;
#[cfg(test)]
mod init_claim;
mod init_fri;
pub mod plonk;
mod prepare;
pub use final_proof::{Artifact, FinalOptions, FinalSystem};
pub use prepare::{prepare, prepare_plonk};
mod prover;
mod root;
mod verifying_keys;
pub use verifying_keys::release_root_layout;
mod setup;
pub use setup::{SetupClass, SetupConfig};
mod statement;
mod storage;
mod verifier;
mod wrap;

use std::{fs, path::Path};

pub const PROOF_TAG: &[u8; 8] = b"IXBN\0\0\0\x01";
pub type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

/// The statement a compressed proof of `claim` exposes, as the caller
/// derived it from its aggregation backend, checked to end in the packed
/// digest of the claim itself.
pub fn check_claim(
  claim: &[u8],
  statement: &[u8],
) -> Result<statement::Statement> {
  let words = statement::from_claims_bytes(statement)?;
  statement::bind_claim(claim, &words)?;
  Ok(words)
}

/// Describe the inner KZG setup selected for a compression run.
pub fn setup_description(
  development_kzg: bool,
  final_proof: FinalOptions,
) -> Result<&'static str> {
  final_proof.validate_setup(development_kzg)?;
  Ok(SetupConfig::from_env(development_kzg)?.class().description())
}

/// Verify a compressed proof of `claim` under the release key its tag selects.
/// Proving parameters are not required.
pub fn verify(
  proof: &[u8],
  claim: &[u8],
  allow_development: bool,
) -> Result<SetupClass> {
  if let Some(packet) = proof.strip_prefix(groth16::PROOF_TAG) {
    return groth16::verify(packet, claim, allow_development);
  }
  if let Some(packet) = proof.strip_prefix(plonk::PROOF_TAG) {
    return plonk::verify(packet, claim);
  }
  if let Some(packet) = proof.strip_prefix(PROOF_TAG) {
    return verifying_keys::verify_recursive(packet, claim);
  }
  Err("unsupported compressed proof version".into())
}

/// Verify with a caller-authorized verifying key digest and independently expected
/// root statement. No proving parameters or bundled catalog entry are needed.
pub fn verify_with_vk(
  proof: &[u8],
  claim: &[u8],
  expected_claims: &[u8],
  vk: &[u8],
  trusted_vk_digest: &[u8; 32],
  allow_development: bool,
) -> Result<SetupClass> {
  let words = check_claim(claim, expected_claims)?;
  let packet = proof
    .strip_prefix(PROOF_TAG)
    .ok_or("unsupported compressed proof curve or version")?;
  verifier::verify_with_vk(
    packet,
    claim,
    &words,
    vk,
    trusted_vk_digest,
    allow_development,
  )
}

fn prepare_output(out: &Path) -> Result<()> {
  fs::create_dir_all(out)?;
  if fs::read_dir(out)?.next().is_some() {
    return Err(
      "output directory must be empty; use a new --out directory".into(),
    );
  }
  Ok(())
}

/// Write the root input directory for `claim` without compressing it.
pub fn write_root_input(
  dir: &Path,
  vk: &[u8],
  proof: &[u8],
  claim: &[u8],
  statement: &[u8],
  fixed_root: Option<&str>,
) -> Result<()> {
  let words = check_claim(claim, statement)?;
  prepare_output(dir)?;
  write_root(dir, vk, proof, &words, fixed_root)
}

/// Verify the root input in `root`, build its FRI verifier circuit and check
/// the circuit's constraints, writing its identity and cost to `out` without
/// proving it.
pub fn check_root(root: &Path, out: &Path) -> Result<()> {
  root::run(root, out, false)
}

/// Write a root input directory: the backend key, root proof, expected
/// statement and, for a normalized root, its fixed layout.
fn write_root(
  dir: &Path,
  vk: &[u8],
  proof: &[u8],
  words: &statement::Statement,
  fixed_root: Option<&str>,
) -> Result<()> {
  fs::create_dir_all(dir)?;
  for (name, bytes) in compress::root_files(vk, proof, words, fixed_root)? {
    storage::write_atomic(&dir.join(name), &bytes)?;
  }
  Ok(())
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn explicit_vk_verification_rejects_other_curve_envelopes() {
    let expected =
      statement::to_claims_bytes(&statement::with_claim(&[0; 10], b"claim"));
    let other = b"IXCMP\0\0\x04";
    let error = verify_with_vk(other, b"claim", &expected, b"", &[0; 32], true)
      .unwrap_err();
    assert!(error.to_string().contains("curve or version"));
  }

  #[test]
  fn recursive_kzg_proofs_must_use_the_release_key() {
    let mut proof = PROOF_TAG.to_vec();
    proof.extend([0; 32]);
    for allow_development in [false, true] {
      let error = verify(&proof, b"claim", allow_development).unwrap_err();
      assert!(error.to_string().contains("other than the"));
    }
  }

  #[test]
  fn invalid_requests_are_rejected_before_io() {
    let statement =
      statement::to_claims_bytes(&statement::with_claim(&[0; 10], b"claim"));
    let config = |final_proof: FinalSystem| CompressConfig {
      setup: SetupConfig::Development { cache_directory: None },
      fixed_cache: "/does-not-exist".into(),
      plonk_cache: "/does-not-exist".into(),
      groth16_cache: "/does-not-exist".into(),
      final_proof: final_proof.into(),
      fresh: false,
      prefetch_bytes: 0,
      #[cfg(feature = "cuda")]
      cuda: crate::kzg::cuda::Settings::default(),
    };
    let input = |claim| CompressInput {
      vk: b"",
      proof: b"",
      claim,
      statement: &statement,
      fixed_root: None,
      out: Path::new("/does-not-exist"),
    };
    let error = |claim, final_proof| {
      compress(input(claim), &config(final_proof)).unwrap_err().to_string()
    };
    assert!(error(b"other", FinalSystem::None).contains("claim"));
    assert!(error(b"claim", FinalSystem::Plonk).contains("--dev-final-srs"));
    assert!(!Path::new("/does-not-exist").exists());
    assert!(verify(PROOF_TAG, b"wrong", true).is_err());
  }

  #[test]
  fn final_proofs_without_their_feature_name_the_build_switch() {
    let mut plonk = plonk::PROOF_TAG.to_vec();
    plonk.extend([0; 64]);
    let mut groth16 = groth16::PROOF_TAG.to_vec();
    groth16.extend([0; 196 + 32]);
    if !cfg!(feature = "plonk") {
      let error = verify(&plonk, b"claim", false).unwrap_err().to_string();
      assert!(error.contains("IX_PLONK=1"), "{error}");
    }
    if !cfg!(feature = "groth16") {
      let error = verify(&groth16, b"claim", false).unwrap_err().to_string();
      assert!(error.contains("IX_GROTH16=1"), "{error}");
    }
  }
}
