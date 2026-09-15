//! Complete instruction/reference checks over actual Program dispatch events.
//!
//! The wrapper owns every event and checks it against the finished source-bound
//! header registry, including forward references and unreachable blocks. This
//! remains a bounded component: it does not materialize executable bodies or
//! typed value arenas, authenticate the caller's bytes, or admit an Exec image.

mod evaluate;
#[cfg(test)]
mod fixtures;
mod gate;
#[cfg(test)]
mod proof_tests;
mod relation;
mod slots;
#[cfg(test)]
mod tests;

pub use gate::{ReferenceGate, ReferenceOp, ReferenceRow};
pub use slots::{
  CheckedProgramReferences, ProgramReferenceSlots, ProgramReferenceState,
};

use super::registry::RegistryCapacity;

// Request inputs: old grammar[28], committed, tag, event fields[13],
// carried instruction, saved tail callee, and a constructor-alternative bitmap.
pub(super) const COMMITTED: usize = 28;
pub(super) const TAG: usize = 29;
pub(super) const FIELDS: usize = 30;
pub(super) const STATE: usize = 43;
pub(super) const STATE_WORDS: usize = 3;
pub(super) const REQUEST_INPUTS: usize = STATE + STATE_WORDS;

// Request outputs: next carried state[3], then these 14 check/request facts,
// then residual. Check inputs begin with these same 14 actual output wires.
pub(super) const CTOR_ENABLE: usize = 0;
pub(super) const CTOR_INDEX: usize = 1;
pub(super) const FUNCTION_ENABLE: usize = 2;
pub(super) const FUNCTION_INDEX: usize = 3;
pub(super) const BLOCK_ENABLE: usize = 4;
pub(super) const BLOCK_OWNER: usize = 5;
pub(super) const BLOCK_INDEX: usize = 6;
pub(super) const PARTIAL: usize = 7;
pub(super) const ARGUMENTS: usize = 8;
pub(super) const CONSTRUCT: usize = 9;
pub(super) const LOCALS: usize = 10;
pub(super) const ADD_ONE: usize = 11;
pub(super) const ADD_CTOR: usize = 12;
pub(super) const LOCAL_LIMIT: usize = 13;
pub(super) const FACTS: usize = 14;
pub(super) const CTOR: usize = FACTS;
pub(super) const FUNCTION: usize = CTOR + 5;
pub(super) const BLOCK: usize = FUNCTION + 5;
pub(super) const CHECK_INPUTS: usize = BLOCK + 5;
