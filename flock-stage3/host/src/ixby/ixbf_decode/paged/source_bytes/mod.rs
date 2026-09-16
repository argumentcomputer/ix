//! Bind original unkeyed BLAKE3 source bytes to the immutable execution banks.
//! A batch copies two source chunks, with zero padding at EOF, into initially
//! zero cells. A complete chain starts at chunk zero and ends after the final
//! chunk. Program admission starts at empty memory; Input starts at the
//! Program's final root. This relation does not establish IXBF semantics.
mod gate;
mod proof;
mod slots;
#[cfg(test)]
mod tests;
mod witness;

pub use gate::{SourceBytesGate, SourceBytesOp, SourceBytesRow};
pub use proof::{CompiledSourceBytes, VerifiedSourceBytes};
pub use witness::{SourceBytesAdvice, SourceBytesWitness};

use crate::ixby::{
  auth_memory::multi::MultiCapacity,
  paged_value::{INPUT_BYTES, PROGRAM_BYTES},
};
use anyhow::{Result, ensure};
use flock_prover::field::F128;

pub const SOURCE_DEPTH: usize = 14;
pub const MEMORY_DEPTH: usize = 40;
pub const CELLS: usize = 64;
pub const PARENTS: usize = 127;
pub const PUBLIC_WORDS: usize = 9;
pub const NU: usize = 10;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SourceBank {
  Program,
  Input,
}
impl SourceBank {
  pub fn address(self) -> u64 {
    match self {
      Self::Program => PROGRAM_BYTES,
      Self::Input => INPUT_BYTES,
    }
  }
  pub fn domain(self) -> &'static [u8] {
    match self {
      Self::Program => {
        b"IxBy/Flock/paged-source:program:d14:cells64:parents127:v0"
      },
      Self::Input => b"IxBy/Flock/paged-source:input:d14:cells64:parents127:v0",
    }
  }
}
fn capacity() -> MultiCapacity {
  MultiCapacity::new(CELLS, PARENTS).unwrap()
}

/// Shared source [length, digest2], then two [chunk cursor, memory root2]
/// endpoints. Only verification establishes the relation between endpoints.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceBytesStatement([F128; PUBLIC_WORDS]);
impl SourceBytesStatement {
  pub fn from_words(words: &[F128]) -> Result<Self> {
    ensure!(words.len() == PUBLIC_WORDS, "source bytes public width");
    ensure!(
      words[0].hi == 0 && words[0].lo <= 1 << (SOURCE_DEPTH + 10),
      "source bytes length"
    );
    let end = (words[0].lo.saturating_sub(1) >> 10) + 1;
    ensure!(
      words[3].hi == 0
        && words[6].hi == 0
        && words[3].lo < words[6].lo
        && words[6].lo <= end,
      "source bytes endpoints"
    );
    Ok(Self(words.try_into().unwrap()))
  }
  pub fn words(&self) -> &[F128; PUBLIC_WORDS] {
    &self.0
  }
  pub fn source_identity(&self) -> &[F128; 3] {
    self.0[..3].try_into().unwrap()
  }
  pub fn initial(&self) -> &[F128; 3] {
    self.0[3..6].try_into().unwrap()
  }
  pub fn final_state(&self) -> &[F128; 3] {
    self.0[6..].try_into().unwrap()
  }
  /// Public endpoint policy, to apply after verifying a chain. The caller
  /// supplies the expected starting memory root from the preceding stage.
  pub fn check_complete(&self, initial_root: [F128; 2]) -> Result<()> {
    ensure!(
      self.0[3] == F128::ZERO && self.0[4..6] == initial_root,
      "source byte chain initialization"
    );
    ensure!(
      self.0[6].lo == (self.0[0].lo.saturating_sub(1) >> 10) + 1,
      "unfinished source byte chain"
    );
    Ok(())
  }
}
