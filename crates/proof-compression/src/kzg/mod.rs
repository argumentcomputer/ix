//! BLS12-381 KZG backend with BLAKE3 and Keccak-256 transcripts.
//! Commitments contain one G1 point per column; openings are batched by point.

mod buffer;
mod coefficients;
pub mod compact;
pub mod config;
#[cfg(feature = "cuda")]
pub mod cuda;
pub mod domain;
pub mod encoding;
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
pub use srs::{PublicSetup, Srs};
pub use transcript::{Blake3Transcript, KzgTranscript, TranscriptKind};

pub mod verifier_params;
pub use verifier_params::VerifierParams;
