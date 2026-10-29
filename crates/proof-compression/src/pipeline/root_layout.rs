//! Fixed normalization bounds for the released aggregation backend.
use super::{FixedRoot, Result};

const RELEASE: &str = "ixvm-2026-10-29";
const LAYOUT: &str = include_str!("../../root-layouts/ixvm-2026-10-29.json");
const ROOT_VERIFIER_BLAKE3: &str =
  "f0c635f096bb2b9ff8fbeaf947c406978c11ce3bc447df94e43d6e9fe3cc6fbc";

/// The release layout for an authenticated aggregation backend's serialized key.
/// Circuit order and fixed-table heights are meaningful only under that key.
pub fn release_root_layout(root_vk: &[u8]) -> Result<&'static str> {
  if blake3::hash(root_vk).to_hex().as_str() != ROOT_VERIFIER_BLAKE3 {
    return Err(format!(
      "aggregation backend differs from the {RELEASE} root layout; a matching release layout is required"
    )
    .into());
  }
  FixedRoot::from_json(LAYOUT)?;
  Ok(LAYOUT)
}
