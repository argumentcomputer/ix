//! Backend-independent Stage 4 relation over the BLS12-381 scalar field.
//!
//! This crate owns the canonical R1CS consumed by terminal proof backends.
//! KZG-FFLONK preprocessing and the later Groth16 backend must therefore agree
//! on this crate's circuit digest rather than compiling separate relations.

mod algebra;
mod binary_linear_table;
mod blake3;
mod exec_binding;
mod exec_relation;
mod f128;
mod fixed_table;
mod fixed_table_basis;
mod fixed_table_batch;
mod jagged_direct;
mod jagged_fold;
mod ligerito;
mod matrix_fold;
mod merged_pcs;
mod multipoint;
mod original_claims;
mod public_inputs;
mod r1cs;
mod relation;
mod root_closure;
mod statement;
mod structure_fold;
mod structured_matrices;
mod transcript;
mod wiring;

pub use algebra::{
  F128AlgebraCircuitError, F128AlgebraCircuitInputsV1,
  F128AlgebraCircuitOutputV1, F128DeferredMatrixClaimVariablesV1,
  F128StructuredWeightVariablesV1, build_f128_algebra_trace_r1cs,
  constrain_f128_algebra_trace, constrain_f128_algebra_trace_deferred,
  project_f128_algebra_trace_r1cs,
};
pub use binary_linear_table::constrain_f128_binary_linear_table;
pub use blake3::{
  BLAKE3_IV, Blake3CompressionInputV1, Blake3CompressionOutputV1,
  build_blake3_compression_r1cs,
};
pub use exec_binding::{
  ExecBindingCircuitError, ExecBindingCircuitInputsV0,
  ExecBindingCircuitOutputV0, constrain_exec_binding,
};
pub use exec_relation::{
  ExecOriginalClaimsClosedOutputV0, ExecOriginalClaimsWitnessV0,
  ExecReplayCircuitWitnessV0, ExecRootClosedCircuitOutputV0,
  ExecRootConditionalError, ExecRootConditionalPublicV0,
  ExecRootConditionalWitnessV0, constrain_exec_original_claims_closed,
  constrain_exec_root_closed, constrain_exec_root_conditional,
};
pub use f128::{
  F128_BITS, F128VariablesV1, alloc_f128_constant, alloc_f128_private,
  build_f128_multiplication_r1cs, constrain_f128_add, constrain_f128_frobenius,
  constrain_f128_inverse, constrain_f128_multiply,
  constrain_f128_multiply_constant, enforce_f128_equal,
};
pub use fixed_table::constrain_f128_fixed_table;
pub use fixed_table_basis::constrain_f128_fixed_table_basis;
pub use fixed_table_batch::{
  constrain_f128_fixed_table_basis_batch,
  constrain_f128_structure_original_claims,
};
pub use jagged_direct::constrain_f128_jagged_direct;
pub use jagged_fold::{
  F128JaggedAccumulatorCircuitError, F128JaggedAccumulatorCircuitInputsV1,
  F128JaggedAccumulatorCircuitOutputV1, F128JaggedRootClaimPublicInputV1,
  F128JaggedRootClaimPublicVariablesV1, F128JaggedRootClaimVariablesV1,
  alloc_f128_jagged_root_public_input, constrain_f128_jagged_accumulator,
  constrain_f128_jagged_root_public_input,
};
pub use ligerito::{
  F128InnerLigeritoCircuitError, F128InnerLigeritoCircuitInputsV1,
  F128InnerLigeritoCircuitOutputV1, constrain_f128_inner_ligerito,
};
pub use matrix_fold::{
  F128MatrixAccumulatorCircuitError, F128MatrixAccumulatorCircuitInputsV1,
  F128MatrixAccumulatorCircuitOutputV1, F128RootMatrixClaimPublicInputV1,
  F128RootMatrixClaimPublicVariablesV1, F128RootMatrixClaimVariablesV1,
  alloc_f128_matrix_root_public_inputs, constrain_f128_matrix_accumulator,
  constrain_f128_matrix_root_public_inputs,
};
pub use merged_pcs::{
  F128MergedPcsFrontendCircuitError, F128MergedPcsFrontendCircuitInputsV1,
  F128MergedPcsFrontendCircuitOutputV1, F128RingSwitchCircuitOutputV1,
  constrain_f128_merged_pcs_frontend,
};
pub use multipoint::{
  F128JaggedAssertionVariablesV1, F128JaggedClaimVariablesV1,
  F128JaggedComboTermVariablesV1, F128JaggedRowWeightVariablesV1,
  F128MultipointCircuitError, F128MultipointTwistedAssistCircuitInputsV1,
  F128MultipointTwistedAssistCircuitOutputV1,
  constrain_f128_multipoint_twisted_assist,
};
pub use original_claims::validate_exec_original_claim_tables;
pub use public_inputs::{
  STAGE4_PUBLIC_INPUT_LIMBS, Stage4PublicInputVariablesV1,
  Stage4PublicInputsV1, alloc_stage4_public_inputs,
  build_stage4_public_input_binding,
};
pub use r1cs::{
  CanonicalR1csV1, Constraint, ConstraintPhase, LinearCombination, R1csBuilder,
  R1csCensusV1, R1csError, R1csProjectionV1, R1csShapeLimitsV0, Variable,
  Witness,
};
pub use relation::{
  Stage4RelationCircuitOutputV1, Stage4RelationError,
  Stage4RelationPublicInputsV1, Stage4RelationWitnessV1, Stage4TraceWitnessV1,
  Stage4TranscriptWitnessV1, constrain_stage4_relation,
};
pub use root_closure::{
  ExecRootClosureError, constrain_f128_jagged_root_table,
  constrain_f128_matrix_root_tables, constrain_f128_structure_root_table,
  validate_exec_root_tables,
};
pub use statement::{
  F128StatementCircuitError, F128StatementCircuitInputsV1,
  F128StatementCircuitOutputV1, STAGE4_STAGE3_STATEMENT_BYTES,
  constrain_f128_statement_binding,
};
pub use structure_fold::{
  F128CircuitStructureAccumulatorCircuitError,
  F128CircuitStructureAccumulatorCircuitInputsV1,
  F128CircuitStructureAccumulatorCircuitOutputV1,
  F128CircuitStructureRootClaimPublicInputV1,
  F128CircuitStructureRootClaimPublicVariablesV1,
  F128CircuitStructureRootClaimVariablesV1,
  alloc_f128_circuit_structure_root_public_input,
  constrain_f128_circuit_structure_accumulator,
  constrain_f128_circuit_structure_root_public_input,
};
pub use structured_matrices::{
  constrain_f128_structured_matrices, constrain_f128_structured_matrix_claims,
};
pub use transcript::{
  ChainedBlake3CircuitOutputV1, F128TranscriptVariablesV1,
  F128TranscriptWordV1, TranscriptCircuitError,
  build_chained_blake3_transcript_r1cs, constrain_chained_blake3_transcript,
  project_chained_blake3_transcript_r1cs,
};
pub use wiring::{
  F128CircuitStructureClaimVariablesV1, F128PackedDirectClaimVariablesV1,
  F128WiringCircuitError, F128WiringCircuitInputsV1, F128WiringCircuitOutputV1,
  build_f128_wiring_r1cs, constrain_f128_wiring,
};
