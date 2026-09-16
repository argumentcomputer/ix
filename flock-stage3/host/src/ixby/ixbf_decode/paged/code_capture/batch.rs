//! Fixed source-authenticated parser/capture/memory batches. Complete public
//! boundaries carry every parser field, capture word and memory root. Whole
//! code admission also requires the separate complete reference validation.
mod emission;
mod proof;
#[cfg(test)]
mod tests;
mod witness;
use crate::ixby::{
  auth_memory::multi::MultiCapacity,
  ixbf_decode::{GrammarKind, NaturalCapacity, dispatch::DispatchConfig},
};
use anyhow::{Result, ensure};
use flock_prover::field::F128;
pub use proof::{CompiledCodeCapture, VerifiedCodeCapture};
pub use witness::{CodeCaptureAdvice, CodeCaptureWitness};
pub const STEPS: usize = 32;
pub const CELLS: usize = 32;
pub const PARENTS: usize = 255;
pub const DEPTH: usize = 14;
pub const NU: usize = 10;
pub const PUBLIC_WORDS: usize = 81;
pub const DOMAIN: &[u8] =
  b"IxBy/Flock/paged-code-capture:d14:steps32:nat128:cells32:parents255:v0";
fn config() -> DispatchConfig {
  DispatchConfig {
    kind: GrammarKind::Program,
    natural: NaturalCapacity::new(128).unwrap(),
  }
}
fn capacity() -> MultiCapacity {
  MultiCapacity::new(CELLS, PARENTS).unwrap()
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CodeCaptureStatement([F128; PUBLIC_WORDS]);
impl CodeCaptureStatement {
  pub fn from_words(words: &[F128]) -> Result<Self> {
    ensure!(words.len() == PUBLIC_WORDS, "code capture public width");
    ensure!(
      words[0].hi == 0 && words[0].lo <= 1 << (DEPTH + 10),
      "code capture source length"
    );
    Ok(Self(words.try_into().unwrap()))
  }
  pub fn words(&self) -> &[F128; PUBLIC_WORDS] {
    &self.0
  }
  pub fn source_identity(&self) -> &[F128; 3] {
    self.0[..3].try_into().unwrap()
  }
  pub fn initial(&self) -> &[F128; 39] {
    self.0[3..42].try_into().unwrap()
  }
  pub fn final_state(&self) -> &[F128; 39] {
    self.0[42..].try_into().unwrap()
  }
  /// Endpoint policy for a verified complete chain; this is not verification.
  pub fn check_complete(&self, initial_root: [F128; 2]) -> Result<()> {
    let grammar =
      self.0[..33].iter().chain(&self.0[42..72]).copied().collect::<Vec<_>>();
    crate::ixby::ixbf_decode::stream::batch::GrammarBatchStatement::from_words(
      &grammar,
    )?
    .check_complete(GrammarKind::Program, &[F128::ZERO; 15])?;
    ensure!(
      self.0[33..40] == [F128::ZERO; 7] && self.0[72..79] == [F128::ZERO; 7],
      "unfinished code capture state"
    );
    ensure!(self.0[40..42] == initial_root, "code capture initial memory");
    Ok(())
  }
}
