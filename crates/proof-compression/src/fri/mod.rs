//! Fixed-profile Protocol v6 (`F_p^3`) multi-stark verification with
//! domain-separated BLAKE3 transcript, algebra, tensor-batched PCS and FRI checks.
//! [`VerifierPlan`] validates a trusted key and profile; callers bind the statement.
//! Proof assignment never overwrites statement wires.
//!
//! Standalone algebraic and transcript helpers do not verify a complete proof.

mod algebra;
mod batch;
pub use batch::{
  build_single_batch_verifier, constrain_batch_verifier,
  constrain_single_batch_verifier, expand_batch_witness,
  expand_single_batch_witness,
};
mod cubic;
mod pcs;
mod pcs_witness;
mod transcript;

pub use algebra::{
  AlgebraicChallenges, AlgebraicInputs, AlgebraicOutputs, CircuitEvaluation,
  CircuitOpenings, Selectors, constrain_algebraic_checks,
};
pub use cubic::CubicValue;
pub use multi_stark::plonkish::gadgets::Blake3Domain;
pub use multi_stark::plonkish::gadgets::ByteGadgets;
pub use multi_stark::plonkish::gadgets::ByteValue;
pub use multi_stark::plonkish::gadgets::blake3;
pub use multi_stark::plonkish::gadgets::blake3_domain;
pub use pcs::{
  FixedPcsShape, FixedVerifierInputs, PcsInputs, PcsQuery,
  build_fixed_verifier, build_profile_verifier, constrain_fixed_verifier,
};
pub use pcs_witness::{ExpandedPcsWitness, expand_pcs_witness};
pub use transcript::{
  Blake3Challenger, DEFAULT_FIELD_RETRIES, TranscriptCommitments,
  constrain_transcript,
};

mod key_codec;
mod plan;
pub(crate) use plan::validate_parameters;
pub use plan::{
  Envelope, ImplementationOptions, Message, PreparedProof, ProofEnvelope,
  ProofProfile, ResourceEstimate, Statement, StatementBinding, StatementSlot,
  VerifierError, VerifierInputs, VerifierKey, VerifierLimits, VerifierPlan,
};
