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
//!   vk verification on against this pipeline's own allowlist ([`vks`]).
//! - **PLONK** ([`plonk`]): SP1's gnark circuit build and prover over the
//!   wrap proof, in-process (the `native-gnark` feature, on by default).
//! - **GPU** ([`cuda`], feature `cuda`, `IX_HC_GPU=1`): every recursion
//!   machine — leaf, compress, shrink and the BN254 wrap — proven by
//!   sp1-gpu's `CudaShardProver`, from one long-lived CUDA worker.
//!
//! Every program is compiled from a dummy input of a fixed shape and pinned
//! to a fixed recursion shape ([`shapes`]), so the pipeline is one finite
//! set of programs per machine, and above the leaves one set for every
//! machine: the wrap verifying key and the PLONK circuit do not depend on
//! the toplevel. The PLONK proof's public inputs are the Poseidon2 digest of
//! the Aiur machine's verifying key, a 32-byte Poseidon2 digest of the claim
//! ([`claim_digest_bytes`]), and the allowlist root.

#[cfg(feature = "cuda")]
pub mod cuda;
pub mod normalize;
pub mod pipeline;
pub mod plonk;
pub mod shapes;
pub mod vks;

pub use normalize::{
  AiurNormalizeWitnessValues, AiurRecursiveVerifier, claim_digest_bytes,
};
pub use pipeline::{
  AiurRecursionProver, ProgramKind, RecursionProof, WrapProof,
};
pub use plonk::PlonkPublicInputs;
pub use shapes::PinnedShapes;
pub use vks::{AiurVks, VK_TREE_HEIGHT};
