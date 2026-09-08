//! KZG-FFLONK backend and proof transport for Ix Stage 4.
//!
//! The backend consumes the canonical R1CS owned by `ix-terminal-circuit`.
//! It provides constant-memory gate projection, materialized development
//! preprocessing/proving, native verification, and the fixed EIP-2537 proof
//! wire boundary.

mod arithmetization;
mod capacity;
mod eip2537;
mod kzg;
mod preprocessing;
mod proof;
mod prover;
mod transcript;
mod verifier;
mod verifier_key;

pub use arithmetization::{
  FFLONK_BLINDING_ROWS, PLONK_GATE_RECORD_BYTES, PlonkArithmetizationError,
  PlonkArithmetizationV1, PlonkCellV1, PlonkGateCensusV1,
  PlonkGateProjectionV1, PlonkGateRecordError, PlonkGateV1, PlonkWireV1,
  PlonkWitnessV1, arithmetize_r1cs, lower_plonk_witness,
};
pub use capacity::{
  BLS12_381_G1_COMPRESSED_BYTES, BLS12_381_G1_EIP2537_BYTES,
  FFLONK_FIELD_STORAGE_BYTES, FFLONK_POLYNOMIAL_FFT_DOMAIN_MULTIPLIER,
  FflonkCapacityError, FflonkCapacityPlanV1, plan_fflonk_capacity,
};
pub use eip2537::{
  EIP2537_G1_MSM_ADDRESS, EIP2537_G1_MSM_TERM_BYTES, EIP2537_PAIRING_ADDRESS,
  EIP2537_PAIRING_PAIR_BYTES, FFLONK_EIP2537_G1_MSM_INPUT_BYTES,
  FFLONK_EIP2537_G1_MSM_TERMS, FFLONK_EIP2537_GAS,
  FFLONK_EIP2537_PAIRING_INPUT_BYTES, FFLONK_EIP2537_PAIRING_PAIRS,
  FflonkEip2537GasV1, FflonkEip2537PlanV1, build_eip2537_verification_plan,
};
pub use kzg::{
  KzgCommitmentV1, KzgError, KzgOpeningV1, KzgUniversalSrsV1, KzgVerifierKeyV1,
  commit_polynomial, evaluate_polynomial, open_polynomial, verify_opening,
};
pub use preprocessing::{
  FFLONK_SRS_DEGREE_OVERHEAD, FFLONK_SRS_DOMAIN_MULTIPLIER,
  FflonkPreprocessedCircuitV1, FflonkPreprocessedPolynomialV1,
  FflonkPreprocessedPolynomialsV1, FflonkPreprocessingError, preprocess_fflonk,
  required_fflonk_srs_degree,
};

pub use proof::{
  BLS12_381_SCALAR_BYTES, Coordinate, EIP2537_G1_BYTES, FFLONK_COMMITMENTS,
  FFLONK_EVALUATIONS, FFLONK_PROOF_BYTES, FflonkCommitmentsV1,
  FflonkEvaluationsV1, FflonkProofDecodeError, FflonkProofV1,
};
pub use prover::{
  FflonkBlindingV1, FflonkProverError, FflonkProverOutputV1, prove_fflonk,
};
pub use transcript::{
  FflonkChallengesV1, FflonkEvaluationRootsV1, FflonkTranscriptError,
  derive_fflonk_challenges,
};
pub use verifier::{FflonkVerificationError, verify_fflonk};
pub use verifier_key::{FflonkVerificationKeyError, FflonkVerificationKeyV1};
