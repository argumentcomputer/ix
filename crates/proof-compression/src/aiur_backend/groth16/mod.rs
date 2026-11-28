//! Pure-Rust (+ optional Ix-CUDA `sppark`) BN254 Groth16 prover, verifier,
//! Solidity verifier generator, and 256-byte Fermat's Last Theorem Margin Note
//! demonstration circuit.
//!
//! Compiles and runs under default features with zero Go, CGo, or `bindgen`
//! dependencies.
//!
//! # Security Notice
//! [`setup_dev`] uses a deterministic BLAKE3 XOF trapdoor derivation and is
//! explicitly **DEV / UNSAFE** (no trusted setup ceremony).

pub mod fermat_demo;
pub mod prover;
pub mod r1cs;
pub mod setup;
pub mod solidity;
pub mod verifier;

#[cfg(test)]
mod tests;

pub use fermat_demo::{
  FERMAT_DEMO_DEV_SEED, FERMAT_MARGIN_NOTE, FERMAT_VECTOR_FORMAT,
  FermatDemoVector, G1Decimal, G2Decimal, ProofDecimal, VerifyingKeyDecimal,
  claim_digest_to_public_inputs, default_fermat_claim_digest,
  export_fermat_vector, fermat_demo_assignment, fermat_demo_r1cs,
  public_inputs_to_claim_digest,
};
pub use prover::{
  Groth16Accelerator, Proof, prove, prove_with_accel, prove_with_blinding,
  prove_with_blinding_accel,
};
pub use r1cs::{Constraint, LinearCombination, R1cs};
pub use setup::{ProvingKey, VerifyingKey, setup_dev};
pub use solidity::{export_solidity, solidity_filename};
pub use verifier::{
  decode_fq_be_canonical, decode_fr_be_canonical, decode_g1_evm, decode_g2_evm,
  verify, verify_compressed_bytes, verify_evm_bytes,
  verify_evm_bytes_raw_publics,
};
