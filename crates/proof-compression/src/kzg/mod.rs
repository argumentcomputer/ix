//! BLS12-381 KZG polynomial commitments with a BLAKE3 transcript.
//! Commitments contain one G1 point per column; openings are batched by point.

mod coefficients;
pub mod domain;
mod fft_batch;
pub mod field;
pub mod pcs;
pub mod srs;
pub mod transcript;
pub mod verifier_params;

pub use domain::Radix2Coset;
pub use field::Scalar;
pub use pcs::{KzgCommitment, KzgPcs, KzgProof};
pub use srs::Srs;
pub use transcript::Blake3Transcript;
pub use verifier_params::VerifierParams;
