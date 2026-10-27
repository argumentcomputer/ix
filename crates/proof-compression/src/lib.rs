//! FRI and KZG proof compression for Ix.
#[cfg(all(feature = "bn254", feature = "bls12-381"))]
compile_error!(
  "select one KZG curve: BN254 is the default; BLS12-381 needs --no-default-features --features bls12-381"
);

mod circuit_metadata;
pub mod foreign;
pub mod fri;
pub mod kzg;
pub mod pipeline;
pub mod recursive;
