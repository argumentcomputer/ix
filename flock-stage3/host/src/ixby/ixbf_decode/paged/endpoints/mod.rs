//! Conditional whole-execution endpoint relation. Its 283 facts must ALL be
//! identified with the statements of recursively verified component proofs.
//! This proof alone does not prove source admission or execution. The closing
//! recursive relation publishes only the final two statement digest words.
mod emission;
mod gate;
mod profile;
mod proof;
#[cfg(test)]
mod tests;

use anyhow::{Result, ensure};
use flock_prover::field::F128;
pub use gate::{EndpointGate, EndpointOp, EndpointRow};
pub use profile::FunctionalProfile;
pub use proof::{CompiledEndpoints, VerifiedEndpoints};

pub const FACT_WORDS: usize = 283;
pub const PUBLIC_WORDS: usize = FACT_WORDS + 2;
pub const NU: usize = 5;
pub const DOMAIN: &[u8] =
  b"IxBy/Flock/paged-endpoints:IXFP0:original1:semantics1:nat128:bytes:v1";

/// The order is protocol-owned, including three distinct commitment domains.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u8)]
pub enum Component {
  ProgramBytes,
  CodeCapture,
  References,
  ConstructorIds,
  InputBytes,
  InputCapture,
  Execution,
  OutputBytes,
  ProgramCommitment,
  InputCommitment,
  OutputCommitment,
}
impl Component {
  pub const ALL: [Self; 11] = [
    Self::ProgramBytes,
    Self::CodeCapture,
    Self::References,
    Self::ConstructorIds,
    Self::InputBytes,
    Self::InputCapture,
    Self::Execution,
    Self::OutputBytes,
    Self::ProgramCommitment,
    Self::InputCommitment,
    Self::OutputCommitment,
  ];
  pub fn range(self) -> std::ops::Range<usize> {
    const OFFSETS: [usize; 12] =
      [0, 9, 90, 101, 104, 113, 190, 247, 256, 265, 274, 283];
    OFFSETS[self as usize]..OFFSETS[self as usize + 1]
  }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EndpointFacts([F128; FACT_WORDS]);
impl EndpointFacts {
  pub fn from_words(words: &[F128]) -> Result<Self> {
    ensure!(words.len() == FACT_WORDS, "endpoint facts width");
    Ok(Self(words.try_into().unwrap()))
  }
  pub fn assemble(components: [&[F128]; 11]) -> Result<Self> {
    for (kind, words) in Component::ALL.into_iter().zip(components) {
      ensure!(words.len() == kind.range().len(), "endpoint component width");
    }
    Self::from_words(&components.concat())
  }
  pub fn words(&self) -> &[F128; FACT_WORDS] {
    &self.0
  }
  pub fn component(&self, kind: Component) -> &[F128] {
    &self.0[kind.range()]
  }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EndpointStatement([F128; PUBLIC_WORDS]);
impl EndpointStatement {
  pub fn from_words(words: &[F128]) -> Result<Self> {
    ensure!(words.len() == PUBLIC_WORDS, "endpoint statement width");
    Ok(Self(words.try_into().unwrap()))
  }
  pub fn words(&self) -> &[F128; PUBLIC_WORDS] {
    &self.0
  }
  pub fn facts(&self) -> &[F128] {
    &self.0[..FACT_WORDS]
  }
  pub fn digest(&self) -> [F128; 2] {
    self.0[FACT_WORDS..].try_into().unwrap()
  }
}

#[derive(Clone, Debug)]
pub struct EndpointAdvice {
  pub facts: EndpointFacts,
  pub statement: EndpointStatement,
}
impl EndpointAdvice {
  /// Untrusted native digest advice. All links and both hashes are constrained.
  pub fn new(
    profile: &FunctionalProfile,
    facts: EndpointFacts,
  ) -> Result<Self> {
    let mut message = b"IxBy/commit/v0\0\x04".to_vec();
    for digest in [
      profile.digest(),
      facts.component(Component::ProgramCommitment)[5..7].try_into().unwrap(),
      facts.component(Component::InputCommitment)[5..7].try_into().unwrap(),
      facts.component(Component::OutputCommitment)[5..7].try_into().unwrap(),
    ] {
      for word in digest {
        message.extend(word.lo.to_le_bytes());
        message.extend(word.hi.to_le_bytes());
      }
    }
    let mut words = facts.words().to_vec();
    words.extend(profile::digest(&message));
    Ok(Self { facts, statement: EndpointStatement::from_words(&words)? })
  }
}
