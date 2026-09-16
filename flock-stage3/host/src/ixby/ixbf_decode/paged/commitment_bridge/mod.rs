//! Bind an entire raw source to the exact domain-separated artifact commitment.
//! Every transformed chunk is assembled from authenticated original chunks.
//! Complete verification requires a contiguous chain from zero through EOF;
//! its parent digest must come from the profile/program commitment in the root.
mod emission;
mod gate;
mod proof;
mod relation;
#[cfg(test)]
mod tests;
mod witness;
use super::synthesis::*;
use anyhow::{Result, ensure};
use flock_prover::field::F128;
pub use gate::{CommitmentBridgeGate, CommitmentBridgeOp, CommitmentBridgeRow};
pub use proof::{CompiledCommitmentBridge, VerifiedCommitmentBridge};
pub use witness::{CommitmentBridgeAdvice, CommitmentBridgeWitness};
pub const RAW_DEPTH: usize = 14;
pub const PREFIXED_DEPTH: usize = 15;
pub const NU: usize = 10;
pub const PUBLIC_WORDS: usize = 9;
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum ArtifactDomain {
  Program = 1,
  Input = 2,
  Output = 3,
}
impl ArtifactDomain {
  pub fn transcript_domain(self) -> &'static [u8] {
    match self {
      Self::Program => {
        b"IxBy/Flock/paged-commitment:program:raw14:prefixed15:v0"
      },
      Self::Input => b"IxBy/Flock/paged-commitment:input:raw14:prefixed15:v0",
      Self::Output => b"IxBy/Flock/paged-commitment:output:raw14:prefixed15:v0",
    }
  }
  pub fn prefix(self) -> [u8; 16] {
    let mut p = *b"IxBy/commit/v0\0\0";
    p[15] = self as u8;
    p
  }
}
/// [raw length, raw digest2, parent digest2, artifact digest2, begin, end].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CommitmentBridgeStatement([F128; PUBLIC_WORDS]);
impl CommitmentBridgeStatement {
  pub fn from_words(words: &[F128]) -> Result<Self> {
    ensure!(words.len() == PUBLIC_WORDS, "commitment bridge public width");
    ensure!(
      words[0].hi == 0 && words[0].lo <= 1 << 24,
      "commitment bridge length"
    );
    ensure!(
      words[7].hi == 0
        && words[8].hi == 0
        && words[7].lo < words[8].lo
        && words[8].lo <= (words[0].lo + 48).div_ceil(1024),
      "commitment bridge endpoints"
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
  pub fn check_complete(&self) -> Result<()> {
    ensure!(
      self.initial() == F128::ZERO
        && self.final_state()
          == F128::new((self.0[0].lo + 48).div_ceil(1024), 0),
      "incomplete commitment bridge"
    );
    Ok(())
  }
}
