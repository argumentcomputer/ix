//! Heterogeneous paged execution batches. Instruction consumers, fuel, state
//! continuity and memory time all use the same actual circuit wires.
//! The initial code/input memory root still requires source admission.
mod batch;
mod gate;
mod object_slots;
#[cfg(test)]
mod object_tests;
mod objects;
#[cfg(test)]
mod proof_tests;
mod slots;
mod synthesis;
#[cfg(test)]
mod tests;
mod witness;

pub use batch::{BatchAdvice, BatchClass, BatchEmission, emit_batch};
use flock_prover::field::F128;
pub use gate::{MicroGate, MicroKind, MicroRow};
pub use objects::ObjectKind;
pub use slots::{ExecutionSlots, StepWires};
pub use witness::{NativeMachine, RowAdvice};

pub const STATE_WORDS: usize = 24;
pub const FUEL: usize = 5;
pub const HEAP_COUNT: usize = 6;
pub const BYTE_COUNT: usize = 7;
pub const CONTROL: usize = 8;
pub const HEADER: usize = 9;
pub const READY: u64 = 0;
pub const RESOLVE: u64 = 1;
pub const EXECUTE: u64 = 2;
pub const STORE: u64 = 3;
pub const PENDING: usize = 10;
pub const SOURCE_A: usize = 15;
pub const SOURCE_B: usize = 16;
pub const DESTINATION: usize = 17;
pub const OLD_HEAP: usize = 18;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(usize)]
pub enum Chip {
  Fetch = 0,
  Resolve = 1,
  Numeric = 2,
  Control = 3,
  Call = 4,
  Resume = 5,
  Construct = 6,
  Closure = 7,
  ApplyInstruction = 8,
  Project = 9,
  Case = 10,
  Apply = 11,
  StoreCopy = 12,
  StoreFinish = 13,
}
impl Chip {
  pub const ALL: [Self; 14] = [
    Self::Fetch,
    Self::Resolve,
    Self::Numeric,
    Self::Control,
    Self::Call,
    Self::Resume,
    Self::Construct,
    Self::Closure,
    Self::ApplyInstruction,
    Self::Project,
    Self::Case,
    Self::Apply,
    Self::StoreCopy,
    Self::StoreFinish,
  ];
  pub fn advice_words(self) -> usize {
    match self {
      Self::Resolve | Self::Project => 4,
      Self::Numeric => 6,
      Self::Case => 5,
      Self::StoreFinish => 0,
      _ => 2,
    }
  }
  pub fn accesses(self) -> usize {
    match self {
      Self::Fetch => 1,
      Self::Resolve => 3,
      Self::Numeric => 6,
      Self::Control | Self::Call => 4,
      Self::Resume => 3,
      Self::Construct
      | Self::Closure
      | Self::ApplyInstruction
      | Self::Apply => 1,
      Self::Project | Self::Case => 5,
      Self::StoreCopy => 2,
      Self::StoreFinish => 3,
    }
  }
}
pub fn initial_state(frame: [F128; 5], budget: u64) -> [F128; STATE_WORDS] {
  let mut state = [F128::ZERO; STATE_WORDS];
  state[..5].copy_from_slice(&frame);
  state[FUEL] = F128::new(budget, 0);
  state
}
