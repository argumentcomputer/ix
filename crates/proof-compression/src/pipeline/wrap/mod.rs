mod outer;
mod saved;
#[cfg(any(feature = "plonk", feature = "groth16"))]
pub(super) use outer::plonk_export;
#[cfg(feature = "plonk")]
pub(super) use outer::plonk_description;

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

pub(super) use outer::VerifyingKey;
pub(super) use saved::verifying_key;
