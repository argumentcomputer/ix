mod outer;
mod saved;
#[cfg(any(feature = "plonk", feature = "groth16"))]
pub(super) use outer::final_description;
#[cfg(any(feature = "plonk", feature = "groth16"))]
pub(super) use outer::final_export;

/// Recursively verify the first KZG stage in `first` and prove the recursive
/// stage into `out`, with its circuit report beside it.
pub(super) fn run(
  first: &std::path::Path,
  out: &std::path::Path,
  config: &super::StageConfig,
) -> Result<(), Box<dyn std::error::Error>> {
  std::fs::create_dir_all(out)?;
  saved::prove(first, out, config)
}

/// Load the first KZG stage in `first`, check its setup binding and verify
/// its proof natively; it must prove `expected`.
pub(super) fn check_first(
  first: &std::path::Path,
  expected: &super::statement::Statement,
  config: &super::StageConfig,
) -> Result<(), Box<dyn std::error::Error>> {
  let input = saved::Input::load(first, config)?;
  if super::statement::from_rows(&input.claims)? != *expected {
    return Err("first KZG proof proves another statement".into());
  }
  Ok(())
}

pub(super) use outer::{PreparedVerifyingKey, VerifyingKey};
pub(super) use saved::verifying_key;
