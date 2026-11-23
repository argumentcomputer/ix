//! Compression and verification of aggregate root proofs.
mod claims;
mod lowering;
mod stage;
pub use root::{FixedRoot, count_root, prepare_root};
pub use stage::{
  FriVerifier, KzgVerifier, Prepared, prepare_kzg, prepare_kzg_for,
};
pub use wrap::{
  RecursiveProof, RecursiveStage, RecursiveVerifier, prepare_recursive,
};

mod compress;
mod derive;
mod development;
pub(crate) use compress::StageConfig;
pub use compress::{CompressConfig, CompressInput, compress};
pub use derive::{
  ReleaseKeys, derive_recursive_vk, derive_recursive_vk_for, derive_release,
  derive_release_for,
};
#[cfg(any(feature = "plonk", feature = "groth16"))]
pub use derive::{final_schema, final_schema_for};
pub use development::verify_with_development_verifier;
mod final_proof;
mod first;
mod fixed_cache;
#[cfg(any(feature = "plonk", feature = "groth16"))]
pub mod gnark;
pub mod groth16;
mod init_fri;
pub mod plonk;
pub mod plonk_limits;
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
pub use statement::backend_prefix;
pub(crate) mod storage;
mod wrap;

use crate::kzg::curve::{Bls12381, Bn254, Curve, KzgCurve};
use std::{fs, path::Path};

pub const PROOF_TAG: &[u8; 8] = Bn254::RECURSIVE_PROOF_TAG;
pub const BLS12_381_PROOF_TAG: &[u8; 8] = Bls12381::RECURSIVE_PROOF_TAG;
pub type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

/// The released Ignition identity and pairing anchors, without proving powers.
/// These are independent of the local SRS cache or a supplied proof.
pub fn ignition_parameters() -> Result<crate::kzg::VerifierParams> {
  verifying_keys::ignition_parameters()
}

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

/// Check that `statement` belongs to `claim` and to the aggregation backend
/// the bundled keys were derived for, as the default verifier requires.
pub fn check_release_statement(claim: &[u8], statement: &[u8]) -> Result<()> {
  let words = check_claim(claim, statement)?;
  verifying_keys::check_release_prefix(&words)
}

/// Describe the inner KZG setup selected for a BN254 compression run.
pub fn setup_description(
  development_kzg: bool,
  final_proof: FinalOptions,
) -> Result<&'static str> {
  final_proof.validate_setup(development_kzg)?;
  Ok(SetupConfig::from_env(development_kzg)?.class().description())
}

/// Describe the curve security profile and inner KZG setup selected for a
/// compression run on `curve` (`Curve::Bn254` or `Curve::Bls12381`).
pub fn setup_description_for_curve(
  curve: Curve,
  development_kzg: bool,
  final_proof: FinalOptions,
) -> Result<String> {
  final_proof.validate_setup(development_kzg)?;
  let setup = SetupConfig::from_env_for_curve(curve, development_kzg)?;
  let zk_note = match final_proof.system {
    FinalSystem::None => "final-kzg (non-ZK)",
    FinalSystem::Plonk => "gnark PLONK (ZK)",
    FinalSystem::Groth16 => "gnark Groth16 (ZK)",
  };
  Ok(format!(
    "{} [{}]; {}: {}",
    curve.as_str(),
    zk_note,
    curve.security_label(),
    setup.class().description(),
  ))
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
  if let Some(packet) = proof.strip_prefix(groth16::BLS12_381_PROOF_TAG) {
    return groth16::verify_bls12_381(packet, claim, allow_development);
  }
  if let Some(packet) = proof.strip_prefix(plonk::PROOF_TAG) {
    return plonk::verify(packet, claim);
  }
  if let Some(packet) = proof.strip_prefix(plonk::BLS12_381_PROOF_TAG) {
    return plonk::verify_bls12_381(packet, claim);
  }
  if let Some(packet) = proof.strip_prefix(PROOF_TAG) {
    return verifying_keys::verify_recursive(packet, claim);
  }
  if let Some(packet) = proof.strip_prefix(BLS12_381_PROOF_TAG) {
    return verifying_keys::verify_recursive_bls12_381(packet, claim);
  }
  Err("unsupported compressed proof version".into())
}

/// Verify with a caller-authorized verifying key digest and independently expected
/// root statement. Supports both BN254 (`IXBN\0\0\0\x01`) and BLS12-381
/// (`IXCMP\0\0\x04`) recursive KZG proofs without proving parameters or bundled
/// catalog entries.
pub fn verify_with_vk(
  proof: &[u8],
  claim: &[u8],
  expected_claims: &[u8],
  vk: &[u8],
  trusted_vk_digest: &[u8; 32],
  allow_development: bool,
) -> Result<SetupClass> {
  let words = check_claim(claim, expected_claims)?;
  if let Some(packet) = proof.strip_prefix(PROOF_TAG) {
    return verifying_keys::verify_with_vk_for::<Bn254>(
      packet,
      claim,
      &words,
      vk,
      trusted_vk_digest,
      allow_development,
    );
  }
  if let Some(packet) = proof.strip_prefix(BLS12_381_PROOF_TAG) {
    return verifying_keys::verify_with_vk_for::<Bls12381>(
      packet,
      claim,
      &words,
      vk,
      trusted_vk_digest,
      allow_development,
    );
  }
  Err("unsupported compressed proof curve or version".into())
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
  fixed_root: Option<&[u8]>,
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

/// Prove only the Goldilocks FRI compression stage and save its checked output.
/// The caller authorizes the root key, claims and optional fixed layout in
/// `root`. Place `out` at a pipeline's `fri/` directory to resume the KZG stages
/// later, including with a separately built CUDA executable. This allocates
/// the full FRI proving working set; inspect `count_root` and `check_root` first.
pub fn prove_root(root: &Path, out: &Path) -> Result<()> {
  root::run(root, out, true)
}

/// Write a root input directory: the backend key, root proof, expected
/// statement and, for a normalized root, its fixed layout.
fn write_root(
  dir: &Path,
  vk: &[u8],
  proof: &[u8],
  words: &statement::Statement,
  fixed_root: Option<&[u8]>,
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
  fn explicit_vk_verification_rejects_other_proof_tags() {
    let expected =
      statement::to_claims_bytes(&statement::with_claim(&[0; 10], b"claim"));
    let mut other = *PROOF_TAG;
    other[7] ^= 0x80;
    let error =
      verify_with_vk(&other, b"claim", &expected, b"", &[0; 32], true)
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
      curve: Curve::Bn254,
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
    let mut bls_recursive = BLS12_381_PROOF_TAG.to_vec();
    bls_recursive.extend([0; 32]);
    assert!(
      verify(&bls_recursive, b"claim", true)
        .unwrap_err()
        .to_string()
        .contains("BLS12-381")
    );
    let mut bls_plonk = plonk::BLS12_381_PROOF_TAG.to_vec();
    bls_plonk.extend([0; 64]);
    assert!(verify(&bls_plonk, b"claim", false).is_err());
    let mut bls_groth16 = groth16::BLS12_381_PROOF_TAG.to_vec();
    bls_groth16.extend([0; 292 + 32]);
    assert!(verify(&bls_groth16, b"claim", false).is_err());
  }

  #[test]
  fn setup_description_for_both_curves_carries_honest_security_labels() {
    let bn = setup_description_for_curve(
      Curve::Bn254,
      true,
      FinalOptions::from(FinalSystem::None),
    )
    .unwrap();
    assert!(bn.contains("bn254"));
    assert!(bn.contains("~100b classical / 0b PQ"));
    assert!(bn.contains("final-kzg (non-ZK)"));

    let bls = setup_description_for_curve(
      Curve::Bls12381,
      true,
      FinalOptions { system: FinalSystem::Plonk, allow_development: true },
    )
    .unwrap();
    assert!(bls.contains("bls12-381"));
    assert!(bls.contains("~126–128b classical / 0b PQ"));
    assert!(bls.contains("EIP-2537"));
    assert!(bls.contains("Filecoin challenge_19"));
    assert!(bls.contains("gnark PLONK (ZK)"));
  }
}
