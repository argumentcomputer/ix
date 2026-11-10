//! Generated CUDA row writers for formal Aiur population plans.
//!
//! The input is a checked program with its trace artifact. The plan is
//! described by `aiur` itself ([`aiur::trace::TracePlan::describe`]); this
//! crate emits, for each selected function circuit, a straight-line
//! predicated CUDA kernel that writes exactly the rows `aiur`'s host
//! population writes, reading the same device record (`AiurCircuit`) as the
//! interpreter in `crates/aiur/cuda/population.cu`. [`bundle::sources`]
//! renders a bundle as source files in one directory, and [`bundle::build`]
//! compiles those files from a bundle crate's build script.
//!
//! A circuit is compiled only when every member reads nothing but its own
//! query row, recorded callee outputs, maps with a verified closed form and
//! hints covered by [`aiur::trace::describe::WORD_HINT_CONTRACT`]. Others
//! are reported with a reason and stay on their runtime fallback.
use aiur::{
  bytecode::CheckedProgram,
  field::FieldBackend,
  trace::{
    TraceArtifact, TracePlan,
    describe::{PopulationDescription, compiled_fingerprint},
  },
};

pub mod bundle;
mod closed;
pub mod cuda;
mod hints;

pub use closed::ClosedForm;

/// A checked program with its population description.
pub struct Described {
  pub program: aiur::Program,
  pub description: PopulationDescription,
  /// [`compiled_fingerprint`] of the description.
  pub fingerprint: String,
}

/// Describes the population plans of `program` under `trace`. A trace with
/// depth circuits needs a program that records call heights
/// ([`CheckedProgram::track_depth`]).
pub fn describe<B: FieldBackend>(
  program: &CheckedProgram<B>,
  trace: TraceArtifact,
) -> Result<Described, String> {
  let plan = TracePlan::new(program, trace)?;
  let description = plan.describe()?;
  let fingerprint = compiled_fingerprint(&description);
  Ok(Described { program: program.program().clone(), description, fingerprint })
}
