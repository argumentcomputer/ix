//! Bounded original-wire parser batches with shared authenticated source pages.
//!
//! A batch authenticates two adjacent chunks and the exact final chunk once,
//! then reuses their wires for all decoder steps. Its complete initial/final
//! dispatcher states must be bound by the caller. Whole-file verification
//! requires a genuine initial state, checked equality at every boundary, one
//! expected source root/length/context, and genuine terminal completion.
//! This is grammar/scalar admission, not registry admission or execution.

mod gate;
#[cfg(test)]
mod proof_tests;
mod relation;
mod slots;
#[cfg(test)]
mod tests;
pub mod witness;

pub use gate::{StreamGate, StreamOp, StreamRow};
pub use slots::{CachedSource, StreamSlots, StreamStepWires};

use super::synthesis::{Bits, Builder};

fn word(index: usize) -> Bits {
  (index * 128..(index + 1) * 128).collect()
}
