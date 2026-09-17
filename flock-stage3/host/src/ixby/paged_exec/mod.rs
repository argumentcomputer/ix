//! Heterogeneous paged execution batches. Instruction consumers, fuel, state
//! continuity and memory time all use the same actual circuit wires.
//! The initial code/input memory root still requires source admission.
mod batch;
#[cfg(test)]
mod benchmark_tests;
mod byte_slots;
#[cfg(test)]
mod byte_tests;
mod bytes;
mod collection_native;
mod collection_slots;
#[cfg(test)]
mod collection_tests;
mod collection_witness;
mod collections;
mod fast_advice;
mod gate;
mod image;
#[cfg(test)]
mod image_tests;
mod object_slots;
#[cfg(test)]
mod object_tests;
mod objects;
mod proof;
mod proof_drivers;
#[cfg(test)]
mod proof_tests;
#[cfg(test)]
mod quota_tests;
mod slots;
mod synthesis;
#[cfg(test)]
mod tests;
mod tuning;
mod witness;

pub use batch::{BatchAdvice, BatchClass, BatchEmission, emit_batch};
pub use bytes::ByteKind;
pub use collections::CollectionKind;
use flock_prover::field::F128;
pub use gate::{MicroGate, MicroKind, MicroRow};
pub use image::NativeImage;
pub use objects::ObjectKind;
pub use proof::{CompiledPagedExecution, VerifiedPagedExecution};
pub use slots::{ExecutionSlots, StepWires};
pub use witness::{NativeMachine, RowAdvice};

pub const STATE_WORDS: usize = 24;
pub const PUBLIC_WORDS: usize = 57;
pub const FUEL: usize = 5;
pub const HEAP_COUNT: usize = 6;
pub const BYTE_COUNT: usize = 7;
pub const CONTROL: usize = 8;
pub const HEADER: usize = 9;
pub const READY: u64 = 0;
pub const RESOLVE: u64 = 1;
pub const EXECUTE: u64 = 2;
pub const STORE: u64 = 3;
pub const BYTE_FINISH: u64 = 4;
pub const BYTE_READ: u64 = 5;
pub const BYTE_APPEND: u64 = 6;
pub const BYTE_EQ: u64 = 7;
pub const HASH_BLOCK: u64 = 8;
pub const HASH_MERGE: u64 = 9;
pub const BYTE_EMIT: u64 = 10;
pub const PENDING: usize = 10;
pub const SOURCE_A: usize = 15;
pub const SOURCE_B: usize = 16;
pub const DESTINATION: usize = 17;
pub const OLD_HEAP: usize = 18;

/// Three shared parameters followed by two complete [clock, state24, root2]
/// endpoints. Successful verification proves only this segment; source,
/// initialization and termination belong to the enclosing complete relation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExecutionStatement([F128; PUBLIC_WORDS]);
impl ExecutionStatement {
  pub fn from_words(words: &[F128]) -> anyhow::Result<Self> {
    anyhow::ensure!(words.len() == PUBLIC_WORDS, "execution public width");
    anyhow::ensure!(
      words[3].hi == 0
        && words[30].hi == 0
        && words[3].lo < words[30].lo
        && words[30].lo < 1 << 59,
      "execution clock endpoints"
    );
    Ok(Self(words.try_into().unwrap()))
  }
  pub fn words(&self) -> &[F128; PUBLIC_WORDS] {
    &self.0
  }
  pub fn parameters(&self) -> &[F128; 3] {
    self.0[..3].try_into().unwrap()
  }
  pub fn initial(&self) -> &[F128; 27] {
    self.0[3..30].try_into().unwrap()
  }
  pub fn final_state(&self) -> &[F128; 27] {
    self.0[30..].try_into().unwrap()
  }
}

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
  ByteStart = 14,
  ByteRead = 15,
  ByteAppend = 16,
  ByteEq = 17,
  ByteFinish = 18,
  ByteEmit = 19,
  HashBlock = 20,
  HashCombine = 21,
  HashPush = 22,
  HashSkip = 23,
  CollectionStart = 24,
  ArrayStep = 25,
  ArrayAscend = 26,
  CollectionFinish = 27,
  BuilderNode = 28,
  BuilderCopy = 29,
  BuilderEmit = 30,
}
impl Chip {
  pub const ALL: [Self; 31] = [
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
    Self::ByteStart,
    Self::ByteRead,
    Self::ByteAppend,
    Self::ByteEq,
    Self::ByteFinish,
    Self::ByteEmit,
    Self::HashBlock,
    Self::HashCombine,
    Self::HashPush,
    Self::HashSkip,
    Self::CollectionStart,
    Self::ArrayStep,
    Self::ArrayAscend,
    Self::CollectionFinish,
    Self::BuilderNode,
    Self::BuilderCopy,
    Self::BuilderEmit,
  ];
  pub fn advice_words(self) -> usize {
    match self {
      Self::Resolve | Self::Project => 4,
      Self::CollectionStart | Self::BuilderCopy => 6,
      Self::ArrayStep | Self::ArrayAscend => 2,
      Self::BuilderNode => 4,
      Self::Numeric | Self::ByteStart | Self::ByteRead | Self::HashBlock => 6,
      Self::ByteAppend | Self::ByteEq => 12,
      Self::Case => 5,
      Self::StoreFinish
      | Self::ByteFinish
      | Self::ByteEmit
      | Self::HashPush
      | Self::HashSkip => 0,
      Self::CollectionFinish | Self::BuilderEmit => 0,
      _ => 2,
    }
  }
  pub fn accesses(self) -> usize {
    match self {
      Self::Fetch => 1,
      Self::CollectionStart => 5,
      Self::ArrayStep | Self::CollectionFinish | Self::BuilderCopy => 3,
      Self::ArrayAscend | Self::BuilderNode => 2,
      Self::BuilderEmit => 1,
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
      Self::ByteStart | Self::ByteRead | Self::ByteFinish | Self::HashBlock => {
        3
      },
      Self::ByteAppend => 7,
      Self::ByteEq => 6,
      Self::ByteEmit | Self::HashCombine | Self::HashPush => 1,
      Self::HashSkip => 0,
    }
  }
}
pub fn initial_state(frame: [F128; 5], budget: u64) -> [F128; STATE_WORDS] {
  let mut state = [F128::ZERO; STATE_WORDS];
  state[..5].copy_from_slice(&frame);
  state[FUEL] = F128::new(budget, 0);
  state
}
