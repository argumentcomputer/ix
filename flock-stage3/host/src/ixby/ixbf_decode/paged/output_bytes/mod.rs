//! Canonical original IXFO Bytes results from authenticated execution memory.
//! A complete chain checks the entire payload. The enclosing execution relation
//! must bind this read-only root and value to its actual halted state.
mod emission;
mod gate;
mod proof;
mod relation;
#[cfg(test)]
mod tests;
mod witness;
use super::synthesis::*;
use crate::ixby::auth_memory::multi::MultiCapacity;
use anyhow::{Result, ensure};
use flock_prover::field::F128;
pub use gate::{OutputBytesGate, OutputBytesOp, OutputBytesRow};
pub use proof::{CompiledOutputBytes, VerifiedOutputBytes};
pub use witness::{OutputBytesAdvice, OutputBytesWitness};
pub const STEPS: usize = 32;
pub const CELLS: usize = 40;
pub const PARENTS: usize = 255;
pub const NU: usize = 10;
pub const SOURCE_DEPTH: usize = 14;
pub const PUBLIC_WORDS: usize = 9;
pub const DOMAIN: &[u8] =
  b"IxBy/Flock/paged-output:bytes:d14:steps32:cells40:parents255:v0";
fn capacity() -> MultiCapacity {
  MultiCapacity::new(CELLS, PARENTS).unwrap()
}
/// Shared [source length, digest2, memory root2, result2], then initial/final
/// payload-window indices. Empty bytes have one checked zero-length window.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OutputBytesStatement([F128; PUBLIC_WORDS]);
impl OutputBytesStatement {
  pub fn from_words(words: &[F128]) -> Result<Self> {
    ensure!(words.len() == PUBLIC_WORDS, "output bytes public width");
    ensure!(
      words[0].hi == 0 && (15..=1 << 24).contains(&words[0].lo),
      "output source length"
    );
    ensure!(words[5] == F128::new(6, 0), "output Bytes result tag");
    ensure!(words[6].hi <= 1 << 24, "output Bytes length");
    let end = words[6].hi.div_ceil(32).max(1);
    ensure!(
      words[7].hi == 0
        && words[8].hi == 0
        && words[7].lo < words[8].lo
        && words[8].lo <= end,
      "output window endpoints"
    );
    Ok(Self(words.try_into().unwrap()))
  }
  pub fn words(&self) -> &[F128; PUBLIC_WORDS] {
    &self.0
  }
  pub fn shared(&self) -> &[F128; 7] {
    self.0[..7].try_into().unwrap()
  }
  pub fn initial(&self) -> F128 {
    self.0[7]
  }
  pub fn final_state(&self) -> F128 {
    self.0[8]
  }
  /// Endpoint policy only; verification and all intermediate links are required.
  pub fn check_complete(&self) -> Result<()> {
    ensure!(
      self.initial() == F128::ZERO
        && self.final_state() == F128::new(self.0[6].hi.div_ceil(32).max(1), 0),
      "incomplete output bytes chain"
    );
    Ok(())
  }
}
