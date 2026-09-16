//! Public proof-free transcript builder for native recursive protocols.
use super::{
  hash::{HashBlueprint, compile_hash},
  tape::Tape,
};
use crate::replay::Stage4FlockTranscriptWitnessV1;
use anyhow::{Result, ensure};
use flock_prover::{
  challenger::Challenger, transcript_record::RecordingChallenger,
};
use ix_stage4_trace::{ChainedBlake3TranscriptV1, F128AlgebraTraceV1};

pub struct TranscriptPlan(Tape);
impl Default for TranscriptPlan {
  fn default() -> Self {
    Self(Tape::new())
  }
}
impl TranscriptPlan {
  pub fn label(&mut self, label: &[u8]) {
    self.0.label(label);
  }
  pub fn bytes(&mut self, length: usize) -> u64 {
    self.0.bytes(length)
  }
  pub fn observe(&mut self) -> u64 {
    self.0.observe()
  }
  pub fn observe_slice(&mut self, count: usize) -> Vec<u64> {
    self.0.observe_slice(count)
  }
  pub fn squeeze(&mut self, bits: Option<u32>) -> u64 {
    self.0.squeeze(bits)
  }
  pub fn squeeze_slice(&mut self, count: usize, bits: Option<u32>) -> Vec<u64> {
    self.0.squeeze_slice(count, bits)
  }
  pub fn compile(self, domain: &[u8]) -> Result<CompiledTranscriptPlan> {
    let hash = compile_hash(
      &self.0.ops,
      domain,
      self.0.address.observed,
      self.0.address.challenges,
      &self.0.payload_lengths,
    )?;
    Ok(CompiledTranscriptPlan { tape: self.0, hash, domain: domain.to_vec() })
  }
}

pub struct CompiledTranscriptPlan {
  tape: Tape,
  hash: HashBlueprint,
  domain: Vec<u8>,
}
impl CompiledTranscriptPlan {
  pub fn topology(&self) -> &ChainedBlake3TranscriptV1 {
    self.hash.setup_topology()
  }
  pub fn observed_values(&self) -> usize {
    usize::try_from(self.tape.address.observed)
      .expect("compiled transcript count")
  }
  pub fn challenges(&self) -> usize {
    usize::try_from(self.tape.address.challenges)
      .expect("compiled transcript count")
  }
  pub fn payload_lengths(&self) -> &[usize] {
    &self.tape.payload_lengths
  }
  /// Recorded values are advice; exact shape comparison is mandatory before
  /// emitting the compiled transcript constraints.
  pub fn witness<Ch: Challenger>(
    &self,
    recording: &RecordingChallenger<Ch>,
  ) -> Result<Stage4FlockTranscriptWitnessV1> {
    let witness = Stage4FlockTranscriptWitnessV1::from_recording_with_algebra(
      recording,
      &self.domain,
      F128AlgebraTraceV1::default(),
      &[],
    )?;
    ensure!(
      witness.operations() == self.tape.ops
        && witness.observed_values().len() == self.observed_values()
        && witness.challenges().len() == self.challenges()
        && witness.byte_payloads().iter().map(Vec::len).collect::<Vec<_>>()
          == self.tape.payload_lengths
        && self.hash.matches(witness.chained_blake3()),
      "recursive fold transcript topology"
    );
    Ok(witness)
  }
}
