//! Compiled CUDA trace writers for the IxVM claim verifier exported as
//! `AIUR_IXVM_ARTIFACT`. Register [`BUNDLE`] before building a proving
//! backend and select it with `AIUR_GPU_TRACE=compiled`.

#[cfg(feature = "kernel")]
include!(concat!(env!("OUT_DIR"), "/bundle.rs"));
