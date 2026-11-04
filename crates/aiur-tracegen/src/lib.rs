//! Generated CUDA row writers for formal Aiur population plans.
//!
//! The input is a binary compiler artifact (see [`aiur::artifact`]). The
//! plan is checked and described by `aiur` itself
//! ([`aiur::trace::TracePlan::describe`]); this crate emits, for each
//! selected function circuit, a straight-line predicated CUDA kernel that
//! writes exactly the rows `aiur`'s host population writes, reading the same
//! device record (`AiurCircuit`) as the interpreter in
//! `crates/aiur/cuda/population.cu`. [`bundle::build`] compiles the result
//! from a bundle crate's build script and emits the Rust binding.
//!
//! A circuit is compiled only when every member reads nothing but its own
//! query row, recorded callee outputs, maps with a verified closed form and
//! hints covered by [`aiur::trace::describe::WORD_HINT_CONTRACT`]. Others
//! are reported with a reason and stay on their runtime fallback.
use aiur::trace::{
  TracePlan,
  describe::{PopulationDescription, compiled_fingerprint},
};

pub mod bundle;
mod closed;
pub mod cuda;
mod hints;

pub use closed::ClosedForm;

/// A checked program with its population description.
pub struct Artifact {
  pub program: aiur::Program,
  pub description: PopulationDescription,
  /// [`compiled_fingerprint`] of the description.
  pub fingerprint: String,
}

/// Checks an encoded binary compiler artifact and describes its population
/// plans.
pub fn describe(bytes: &[u8]) -> Result<Artifact, String> {
  describe_package(
    aiur::artifact::decode(bytes)
      .map_err(|e| format!("not a compiler artifact: {e}"))?,
  )
}

/// Reads a binary compiler artifact and describes its population plans.
pub fn describe_file(path: &std::path::Path) -> Result<Artifact, String> {
  describe_package(aiur::artifact::read(path)?)
}

/// Checks a compiler artifact and describes its population plans.
pub fn describe_package(
  package: aiur::artifact::Package,
) -> Result<Artifact, String> {
  let checked = package.program.clone().check()?;
  let plan = TracePlan::new(&checked, package.trace)?;
  let description = plan.describe()?;
  let fingerprint = compiled_fingerprint(&description);
  Ok(Artifact { program: package.program, description, fingerprint })
}
