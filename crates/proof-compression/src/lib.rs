//! FRI and KZG proof compression for Ix.
#[cfg(all(feature = "bn254", feature = "bls12-381"))]
compile_error!(
  "BN254 KZG requires --no-default-features --features bn254; the BLS12-381 feature cannot be combined with it"
);

mod circuit_metadata;
pub mod foreign;
pub mod fri;
pub mod kzg;
pub mod pipeline;
pub mod recursive;
