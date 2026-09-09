//! SP1 recursion over Aiur Hypercube proofs.
//!
//! An Aiur program proven by the Hypercube backend (`aiur-hypercube`) is a
//! `MachineProof` of one or more KoalaBear shards. This crate takes it the
//! rest of the way to a small BN254 PLONK proof by driving SP1's own
//! recursion pipeline with one substitution: the leaf program.
//!
//! - **normalize** ([`normalize`]): SP1's core-level recursion program
//!   asserts RISC-V execution state, so it is replaced by
//!   [`AiurRecursiveVerifier`], which verifies one Aiur shard proof with
//!   SP1's generic in-circuit shard verifier and maps Aiur's public values
//!   (claim, claim flag, septic chain digest) onto `RecursionPublicValues`.
//! - **compose, shrink, wrap** ([`pipeline`]): SP1's programs, as is, with
//!   vk verification off.
//! - **PLONK** ([`plonk`]): SP1's gnark circuit build and prover over the
//!   wrap proof, in-process (the `native-gnark` feature, on by default).
//!
//! The PLONK proof's public inputs are the Poseidon2 digest of the Aiur
//! machine's verifying key and a 32-byte Poseidon2 digest of the claim
//! ([`claim_digest_bytes`]).

pub mod normalize;
pub mod pipeline;
pub mod plonk;

pub use normalize::{
  AiurNormalizeWitnessValues, AiurRecursiveVerifier, claim_digest_bytes,
};
pub use pipeline::{AiurRecursionProver, RecursionProof, WrapProof};
pub use plonk::PlonkPublicInputs;
