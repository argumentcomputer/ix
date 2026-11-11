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
//! hints covered by [`aiur::trace::describe::WORD_HINT_CONTRACT`], and has no
//! depth column or depth slots (the depth pass's columns are filled by the
//! interpreter). Others are reported with a reason and stay on their runtime
//! fallback.
use aiur::{
  bytecode::CheckedProgram,
  field::FieldBackend,
  trace::{
    DepthSlot, TraceArtifact, TracePlan,
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
  /// Per circuit of the description: whether a member has a depth column or
  /// depth slots, which compiled writers do not fill.
  pub depth: Vec<bool>,
}

/// Describes the population plans of `program` under `trace`. A trace with
/// depth circuits needs a program that records call heights
/// ([`CheckedProgram::track_depth`]).
pub fn describe<B: FieldBackend>(
  program: &CheckedProgram<B>,
  trace: TraceArtifact,
) -> Result<Described, String> {
  let chip_depth: Vec<bool> = trace
    .functions
    .iter()
    .map(|f| {
      trace.chips.iter().find(|c| c.name == f.chip).is_some_and(|c| {
        c.depth.column.is_some()
          || c.depth.slots.iter().any(|s| *s != DepthSlot::Plain)
      })
    })
    .collect();
  let plan = TracePlan::new(program, trace)?;
  let description = plan.describe()?;
  let fingerprint = compiled_fingerprint(&description);
  let depth = description
    .circuits
    .iter()
    .map(|c| c.members.iter().any(|m| chip_depth[m.function]))
    .collect();
  Ok(Described {
    program: program.program().clone(),
    description,
    fingerprint,
    depth,
  })
}
