//! Algebraic and transcript gadgets for multi-stark FRI verification.
//!
//! These helpers do not verify a complete proof. Openings must also be
//! authenticated by PCS checks before accepting a statement.

mod algebra;
mod quadratic;
mod transcript;

pub use algebra::{
  AlgebraicChallenges, AlgebraicInputs, AlgebraicOutputs, CircuitEvaluation,
  CircuitOpenings, Selectors, constrain_algebraic_checks,
};
pub use multi_stark::plonkish::gadgets::ByteGadgets;
pub use multi_stark::plonkish::gadgets::ByteValue;
pub use multi_stark::plonkish::gadgets::blake3;
pub use quadratic::QuadraticValue;
pub use transcript::{
  Blake3Challenger, DEFAULT_FIELD_RETRIES, TranscriptCommitments,
  constrain_transcript,
};
