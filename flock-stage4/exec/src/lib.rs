//! Generic Flock verifier replay and transcript topology for recursive proofs.
mod batch_replay;
mod blueprint;
pub mod replay;

pub use batch_replay::{
  CompiledFlockReplay, CompiledGrammarBatchReplay, GrammarBatchReplayWitness,
  compile_flock_replay, compile_grammar_batch_replay,
};
pub use blueprint::VerifierSetup as FlockVerifierSetup;
pub use blueprint::{CompiledTranscriptPlan, TranscriptPlan};
