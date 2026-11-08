//! Verifying keys derived from trusted inputs alone. No proof, witness or
//! stage directory is read: each stage's verifier is built by the
//! construction its proving path uses, so a derived key is the key every
//! compression under the same inputs proves to.
use super::{
  FixedRoot, Result, SetupConfig, first, root, verifying_keys, wrap,
};

/// Derive the recursive verifying key, as `compress` writes it to
/// `final-kzg/vk.bin`, for roots of the aggregation backend whose serialized
/// key is `root_vk`, normalized to the fixed layout `layout` (`.ixl` bytes),
/// and compressed under `setup`.
pub fn derive_recursive_vk(
  root_vk: &[u8],
  layout: &[u8],
  setup: &SetupConfig,
) -> Result<Vec<u8>> {
  let fri = {
    let key = aiur::trace::stark::VerifyingKey::from_bytes(root_vk)?;
    root::verifier(&key, &FixedRoot::from_bytes(layout)?)?
  };
  let (manifest, parts, _) =
    first::setup(&fri, verifying_keys::FIRST_LOG_HEIGHT, setup, None)?;
  drop(fri);
  let vk = wrap::verifying_key(&manifest, parts, setup)?;
  vk.check_setup_class(setup.class())?;
  vk.to_bytes()
}

/// The pins of a release that follow from its aggregation backend key, root
/// layout and setup, derived without a proof as `prepare` derives them.
pub struct ReleaseKeys {
  /// The first stage's FRI verifier plan (`FIRST_PLAN_ID`).
  pub first_plan_id: [u8; 32],
  /// The recursive stage's frontend (`RECURSIVE_FRONTEND_ID`).
  pub recursive_frontend_id: Vec<u8>,
  /// The recursive verifying key (`recursive-vk.bin`).
  pub recursive_vk: Vec<u8>,
  /// The identifier a recursive packet begins with (`RECURSIVE_VK_ID`).
  pub recursive_vk_id: [u8; 32],
}

/// Derive a release's pins for roots of `root_vk` normalized to `layout`
/// (`.ixl` bytes) under `setup`. Both stages' fixed preprocessing is
/// published to the fixed cache under `cache_root`, as `prepare` publishes
/// it, so a later compression reuses it.
pub fn derive_release(
  root_vk: &[u8],
  layout: &[u8],
  setup: &SetupConfig,
  cache_root: &std::path::Path,
) -> Result<ReleaseKeys> {
  let fri = {
    let key = aiur::trace::stark::VerifyingKey::from_bytes(root_vk)?;
    root::verifier(&key, &FixedRoot::from_bytes(layout)?)?
  };
  let (manifest, parts, prepared) = first::setup(
    &fri,
    verifying_keys::FIRST_LOG_HEIGHT,
    setup,
    Some(cache_root),
  )?;
  drop(fri);
  let (first_plan_id, _) = prepared.ok_or("first stage was not cached")?;
  let frontend = wrap::frontend(&manifest, parts, setup)?;
  let recursive_frontend_id = frontend.identity().to_vec();
  let (vk, _) = frontend.prepared_key(setup, cache_root)?;
  vk.check_setup_class(setup.class())?;
  Ok(ReleaseKeys {
    first_plan_id,
    recursive_frontend_id,
    recursive_vk: vk.to_bytes()?,
    recursive_vk_id: vk.id(),
  })
}

/// The recursive verifier description both final circuits prove, for the
/// recursive key `recursive_vk` and statement prefix `prefix`. Its SHA-256 is
/// `FINAL_SCHEMA_SHA256`.
#[cfg(any(feature = "plonk", feature = "groth16"))]
pub fn final_schema(
  recursive_vk: &[u8],
  prefix: &[u64; 10],
) -> Result<Vec<u8>> {
  wrap::final_description(
    &wrap::VerifyingKey::from_bytes(recursive_vk)?,
    prefix,
  )
}

#[cfg(test)]
mod tests {
  use super::super::verifying_keys;
  use super::*;

  const RECURSIVE_VK: &[u8] =
    include_bytes!("../../verifying-keys/0.2/recursive-vk.bin");

  fn ignition() -> SetupConfig {
    let setup = SetupConfig::from_env(false).unwrap();
    assert_eq!(setup.class(), super::super::SetupClass::Ignition);
    setup
  }

  #[test]
  #[ignore = "needs IX_ROOT_VK naming the release aggregation backend key, \
              the pinned Ignition release under IX_PARAMS_DIR and about \
              90 GB of memory; a CUDA build commits on the GPU"]
  fn release_recursive_key_derives_without_a_proof() {
    let root_vk =
      std::fs::read(std::env::var_os("IX_ROOT_VK").unwrap()).unwrap();
    let layout = verifying_keys::release_root_layout(&root_vk).unwrap();
    let derived = derive_recursive_vk(&root_vk, layout, &ignition()).unwrap();
    eprintln!("derived recursive key BLAKE3 {}", blake3::hash(&derived));
    assert!(derived == RECURSIVE_VK, "derived recursive key differs");
  }

  #[cfg(feature = "plonk")]
  #[test]
  fn release_plonk_description_matches_its_pin() {
    use sha2::{Digest, Sha256};
    let vk = wrap::VerifyingKey::from_bytes(RECURSIVE_VK).unwrap();
    let description =
      wrap::final_description(&vk, &verifying_keys::STATEMENT_PREFIX).unwrap();
    assert_eq!(
      Sha256::digest(&description).as_slice(),
      verifying_keys::decode(verifying_keys::FINAL_SCHEMA_SHA256).unwrap()
    );
  }

  #[cfg(feature = "plonk")]
  #[test]
  #[ignore = "needs the pinned Ignition release under IX_PARAMS_DIR and \
              compiles and sets up the PLONK circuit into a new directory \
              under the temporary directory (minutes on a GPU-backed gnark, \
              longer on CPU)"]
  fn release_plonk_key_derives_without_a_proof() {
    use sha2::{Digest, Sha256};
    let scratch = crate::test_support::TempDir::new("plonk-derive");
    let cache = scratch.join("cache");
    let derived = super::super::plonk::derive_verifying_key(
      RECURSIVE_VK,
      &verifying_keys::STATEMENT_PREFIX,
      &ignition(),
      &cache,
    )
    .unwrap();
    eprintln!("derived PLONK key SHA-256 {:x}", Sha256::digest(&derived));
    assert!(derived == verifying_keys::PLONK_VK, "derived PLONK key differs");
  }
}
