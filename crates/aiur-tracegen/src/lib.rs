//! Generated CUDA row writers for formal Aiur population plans.
//!
//! The input is an exported execution package with its trace artifact. The
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
  TraceArtifact, TracePlan,
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

#[derive(serde::Deserialize)]
struct Package {
  program: aiur::Program,
  trace: Option<TraceArtifact>,
}

/// Checks an execution package and describes its population plans.
pub fn describe(bytes: &[u8]) -> Result<Artifact, String> {
  let package: Package = aiur::decode_artifact(bytes)
    .map_err(|e| format!("not an execution package: {e}"))?;
  let trace = package.trace.ok_or("the package has no trace artifact")?;
  let checked = package.program.clone().check()?;
  let plan = TracePlan::new(&checked, trace)?;
  let description = plan.describe()?;
  let fingerprint = compiled_fingerprint(&description);
  Ok(Artifact { program: package.program, description, fingerprint })
}
