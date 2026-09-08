//! KZG-FFLONK backend and proof transport for Ix Stage 4.
//!
//! The backend consumes the canonical R1CS owned by `ix-terminal-circuit`.
//! It provides constant-memory gate projection, preprocessing/proving with
//! in-memory or authenticated file SRS, fixed polynomials, and temporary prover
//! workspaces, native verification, and the fixed EIP-2537 proof wire boundary.
//! Owned inputs release the canonical relation during gate lowering and the
//! checked assignment before polynomial work. The file workspace retains one
//! FFT array with bounded roots/I/O buffers; gates and wire lowering remain
//! materialized.

mod arithmetization;
mod capacity;
mod eip2537;
mod kzg;
mod kzg_srs_file;
mod polynomial_storage;
mod preprocessing;
mod preprocessing_file;
mod proof;
mod prover;
mod prover_workspace;
mod transcript;
mod verifier;
mod verifier_key;

pub use arithmetization::{
  FFLONK_BLINDING_ROWS, FflonkCheckedWitnessV1, PLONK_GATE_RECORD_BYTES,
  PlonkArithmetizationError, PlonkArithmetizationV1, PlonkCellV1,
  PlonkGateCensusV1, PlonkGateProjectionV1, PlonkGateRecordError, PlonkGateV1,
  PlonkWireV1, PlonkWitnessV1, arithmetize_r1cs, arithmetize_r1cs_owned,
  lower_plonk_witness,
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
  KzgCommitmentSourceV1, KzgCommitmentV1, KzgError, KzgOpeningV1,
  KzgUniversalSrsV1, KzgVerifierKeyV1, commit_polynomial,
  commit_polynomial_source, evaluate_polynomial, open_polynomial,
  verify_opening,
};
pub use kzg_srs_file::{
  KZG_SRS_FILE_CHUNK_POINTS, KZG_SRS_FILE_HEADER_BYTES, KzgFileSrsV1,
  KzgSrsFileEncodingV1, write_kzg_srs_file,
};
pub use polynomial_storage::{
  FFLONK_POLYNOMIAL_CHUNK_FIELDS, FflonkPolynomialSourceV1, FflonkStorageError,
};
pub use preprocessing::{
  FFLONK_SRS_DEGREE_OVERHEAD, FFLONK_SRS_DOMAIN_MULTIPLIER,
  FflonkFixedPolynomialV1, FflonkPreprocessedCircuitV1,
  FflonkPreprocessedPolynomialV1, FflonkPreprocessedPolynomialsV1,
  FflonkPreprocessingError, FflonkProvingKeyV1, preprocess_fflonk,
  required_fflonk_srs_degree,
};
pub use preprocessing_file::{
  FflonkFilePreprocessedCircuitV1, preprocess_fflonk_to_file,
};

pub use proof::{
  BLS12_381_SCALAR_BYTES, Coordinate, EIP2537_G1_BYTES, FFLONK_COMMITMENTS,
  FFLONK_EVALUATIONS, FFLONK_PROOF_BYTES, FflonkCommitmentsV1,
  FflonkEvaluationsV1, FflonkProofDecodeError, FflonkProofV1,
};
pub use prover::{
  FflonkBlindingV1, FflonkProverError, FflonkProverOutputV1, prove_fflonk,
  prove_fflonk_checked, prove_fflonk_checked_with_file_workspace,
  prove_fflonk_with_file_workspace,
};
pub use transcript::{
  FflonkChallengesV1, FflonkEvaluationRootsV1, FflonkTranscriptError,
  derive_fflonk_challenges,
};
pub use verifier::{FflonkVerificationError, verify_fflonk};
pub use verifier_key::{FflonkVerificationKeyError, FflonkVerificationKeyV1};
