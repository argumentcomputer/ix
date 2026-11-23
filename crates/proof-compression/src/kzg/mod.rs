//! Multi-curve KZG backend (BN254 and BLS12-381) with BLAKE3 and Keccak-256
//! transcripts.
//! Commitments contain one G1 point per column; openings are batched by point.

mod coefficients;
pub mod compact;
pub mod config;
#[cfg(feature = "cuda")]
pub mod cuda;
pub mod curve;
mod dev_srs_cache;
pub mod domain;
pub mod encoding;
mod fft_batch;
pub mod field;
mod msm_cpu;
pub mod packed_shplonk;
pub mod pcs;
mod quotient;
mod quotient_plan;
pub mod shplonk;
pub mod srs;
pub mod transcript;

pub use config::KzgConfig;
pub use curve::{Bls12381, Bn254, Curve, KzgCurve};
pub use domain::Radix2Coset;
pub use field::{Bls12381Scalar, CurveScalar, Scalar};
pub use pcs::{KzgCommitment, KzgPcs, KzgProof};
pub use srs::{PublicSetup, Srs};
pub use transcript::{Blake3Transcript, KzgTranscript, TranscriptKind};

pub mod verifier_params;
pub use verifier_params::VerifierParams;
