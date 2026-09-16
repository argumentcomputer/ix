//! Heterogeneous paged execution batches. Instruction consumers, fuel, state
//! continuity and memory time all use the same actual circuit wires.
//! The initial code/input memory root still requires source admission.
mod batch;
mod gate;
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(usize)]
pub enum Chip {
  Fetch = 0,
  Resolve = 1,
  Numeric = 2,
  Control = 3,
  Call = 4,
  Resume = 5,
}
impl Chip {
  pub const ALL: [Self; 6] = [
    Self::Fetch,
    Self::Resolve,
    Self::Numeric,
    Self::Control,
    Self::Call,
    Self::Resume,
  ];
  pub fn advice_words(self) -> usize {
    match self {
      Self::Resolve => 4,
      Self::Numeric => 6,
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
    }
  }
}
pub fn initial_state(frame: [F128; 5], budget: u64) -> [F128; STATE_WORDS] {
  let mut state = [F128::ZERO; STATE_WORDS];
  state[..5].copy_from_slice(&frame);
  state[FUEL] = F128::new(budget, 0);
  state
}
