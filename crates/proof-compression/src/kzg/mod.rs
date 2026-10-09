//! BLS12-381 KZG backend for multi-stark, with a BLAKE3 transcript.
//! Commitments contain one G1 point per column; openings are batched by point.

mod coefficients;
pub mod compact;
pub mod config;
pub mod domain;
mod fft_batch;
pub mod field;
pub mod pcs;
mod quotient;
mod quotient_plan;
pub mod srs;
mod srs_cache;
pub mod transcript;

pub use config::KzgConfig;
pub use domain::Radix2Coset;
pub use field::Scalar;
pub use pcs::{KzgCommitment, KzgPcs, KzgProof};
pub use srs::Srs;
pub use transcript::Blake3Transcript;
