//! Fixed source/parser/value/memory batch. Program context comes from a
//! source-admitted program and must be linked by the complete composition.
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
pub use proof::{CompiledInputCapture, VerifiedInputCapture};
pub use witness::{InputCaptureAdvice, InputCaptureWitness};
pub const STEPS: usize = 32;
pub const CELLS: usize = 32;
pub const PARENTS: usize = 255;
pub const DEPTH: usize = 14;
pub const NU: usize = 10;
pub const PUBLIC_WORDS: usize = 77;
pub const DOMAIN: &[u8] =
  b"IxBy/Flock/paged-input-capture:d14:steps32:nat128:cells32:parents255:v1";
fn config() -> DispatchConfig {
  DispatchConfig {
    kind: GrammarKind::Input,
    natural: NaturalCapacity::new(128).unwrap(),
  }
}
fn capacity() -> MultiCapacity {
  MultiCapacity::new(CELLS, PARENTS).unwrap()
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InputCaptureStatement([F128; PUBLIC_WORDS]);
impl InputCaptureStatement {
  pub fn from_words(words: &[F128]) -> Result<Self> {
    ensure!(words.len() == PUBLIC_WORDS, "input capture public width");
    ensure!(
      words[0].hi == 0 && words[0].lo <= 1 << (DEPTH + 10),
      "input capture source length"
    );
    Ok(Self(words.try_into().unwrap()))
  }
  pub fn words(&self) -> &[F128; PUBLIC_WORDS] {
    &self.0
  }
  pub fn source_identity(&self) -> &[F128; 3] {
    self.0[..3].try_into().unwrap()
  }
  pub fn initial(&self) -> &[F128; 37] {
    self.0[3..40].try_into().unwrap()
  }
  pub fn final_state(&self) -> &[F128; 37] {
    self.0[40..].try_into().unwrap()
  }
  /// Endpoint policy, not verification. The program context and initial root
  /// must come from the recursively verified preceding admission stages.
  pub fn check_complete(
    &self,
    context: &[F128; 15],
    initial_root: [F128; 2],
  ) -> Result<()> {
    let grammar =
      self.0[..33].iter().chain(&self.0[40..70]).copied().collect::<Vec<_>>();
    crate::ixby::ixbf_decode::stream::batch::GrammarBatchStatement::from_words(
      &grammar,
    )?
    .check_complete(GrammarKind::Input, context)?;
    ensure!(self.0[33..38] == [F128::ZERO; 5], "input capture initial state");
    ensure!(self.0[38..40] == initial_root, "input capture initial memory");
    for at in [70, 72, 73] {
      ensure!(self.0[at] == F128::ZERO, "unfinished input frontier");
    }
    Ok(())
  }
}
