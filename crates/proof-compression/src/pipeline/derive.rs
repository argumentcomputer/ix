//! Verifying keys derived from trusted inputs alone. No proof, witness or
//! stage directory is read: each stage's verifier is built by the
//! construction its proving path uses, so a derived key is the key every
//! compression under the same inputs proves to.
use super::{FixedRoot, Result, SetupConfig, first, root, wrap};

/// Derive the recursive verifying key, as `compress` writes it to
/// `final-kzg/vk.bin`, for roots of the aggregation backend whose serialized
/// key is `root_vk`, normalized to the fixed layout `layout` (JSON), and
/// compressed under `setup` with a first KZG stage of `2^log_height` rows.
pub fn derive_recursive_vk(
  root_vk: &[u8],
  layout: &str,
  setup: &SetupConfig,
  log_height: u32,
) -> Result<Vec<u8>> {
  if !matches!(log_height, 24 | 25) {
    return Err("the first KZG stage's log-height must be 24 or 25".into());
  }
  let fri = {
    let key = aiur::vk_codec::AiurVerifyingKey::from_bytes(root_vk)?;
    root::verifier(&key, &FixedRoot::from_json(layout)?)?
  };
  let (manifest, parts) =
    first::setup(&fri, usize::try_from(log_height)?, setup)?;
  drop(fri);
  let vk = wrap::verifying_key(&manifest, parts, setup)?;
  match setup.ignition_admission() {
    Some(admission) => vk.check_ignition_admission(admission)?,
    None => vk.check_setup_class(setup.class())?,
  }
  vk.to_bytes()
}

#[cfg(test)]
mod tests {
  use super::super::verifying_keys;
  use super::*;

  const RECURSIVE_VK: &[u8] =
    include_bytes!("../../verifying-keys/0.1/recursive-vk.bin");

  fn ignition() -> SetupConfig {
    let setup = SetupConfig::from_env(false).unwrap();
    assert!(setup.ignition_admission().is_some());
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
    let derived =
      derive_recursive_vk(&root_vk, layout, &ignition(), 24).unwrap();
    eprintln!("derived recursive key BLAKE3 {}", blake3::hash(&derived));
    assert!(derived == RECURSIVE_VK, "derived recursive key differs");
  }

  #[cfg(feature = "plonk")]
  #[test]
  fn release_plonk_description_matches_its_pin() {
    use sha2::{Digest, Sha256};
    let vk = wrap::VerifyingKey::from_bytes(RECURSIVE_VK).unwrap();
    let description =
      wrap::plonk_description(&vk, &verifying_keys::STATEMENT_PREFIX).unwrap();
    assert_eq!(
      Sha256::digest(&description).as_slice(),
      verifying_keys::decode(verifying_keys::TERMINAL_SCHEMA_SHA256)
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
    let cache = super::super::storage::temporary_path(
      &std::env::temp_dir().join("ix-plonk-derive"),
    );
    let derived = super::super::plonk::derive_verifying_key(
      RECURSIVE_VK,
      &verifying_keys::STATEMENT_PREFIX,
      &ignition(),
      &cache,
    )
    .unwrap();
    eprintln!("derived PLONK key SHA-256 {:x}", Sha256::digest(&derived));
    assert!(derived == verifying_keys::PLONK_VK, "derived PLONK key differs");
    std::fs::remove_dir_all(cache).unwrap();
  }
}
