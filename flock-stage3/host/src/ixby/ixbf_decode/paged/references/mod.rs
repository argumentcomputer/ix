//! Complete, deterministic semantic-reference walk over source-captured code.
//! The expected context and read-only memory root must be bound to a complete
//! CodeCapture chain. This component does not admit an arbitrary memory image.
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
pub use gate::{ReferenceGate, ReferenceRow};
pub use proof::{CompiledReferences, VerifiedReferences};
pub use witness::{ReferenceAdvice, ReferenceWitness};
pub const STEPS: usize = 32;
pub const CELLS: usize = 32;
pub const PARENTS: usize = 255;
pub const NU: usize = 10;
pub const PUBLIC_WORDS: usize = 11;
pub const DOMAIN: &[u8] =
  b"IxBy/Flock/paged-references:steps32:cells32:parents255:v0";
const INPUTS: usize = 15;
const OUTPUTS: usize = 20;
fn capacity() -> MultiCapacity {
  MultiCapacity::new(CELLS, PARENTS).unwrap()
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReferenceStatement([F128; PUBLIC_WORDS]);
impl ReferenceStatement {
  pub fn from_words(words: &[F128]) -> Result<Self> {
    ensure!(words.len() == PUBLIC_WORDS, "reference public width");
    ensure!(
      words[0].hi == 0 && (1..=1024).contains(&words[0].lo),
      "reference function count"
    );
    ensure!(
      words[1].hi == 0 && words[1].lo <= 256,
      "reference constructor count"
    );
    ensure!(
      words[2].hi == 0 && words[2].lo < words[0].lo,
      "reference program entry"
    );
    Ok(Self(words.try_into().unwrap()))
  }
  pub fn words(&self) -> &[F128; PUBLIC_WORDS] {
    &self.0
  }
  pub fn shared(&self) -> &[F128; 5] {
    self.0[..5].try_into().unwrap()
  }
  pub fn initial(&self) -> &[F128; 3] {
    self.0[5..8].try_into().unwrap()
  }
  pub fn final_state(&self) -> &[F128; 3] {
    self.0[8..].try_into().unwrap()
  }
  /// Endpoint policy only. Verification and all intermediate links are required.
  pub fn check_complete(&self) -> Result<()> {
    ensure!(*self.initial() == [F128::ZERO; 3], "reference initial state");
    ensure!(
      *self.final_state()
        == [F128::new(3 | self.0[0].lo << 8, 0), F128::ZERO, F128::ZERO],
      "unfinished reference walk"
    );
    Ok(())
  }
}
