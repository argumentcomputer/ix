//! Integration tests of the FRI verifier circuits, the KZG backend and the
//! compression pipeline, as one test binary.
mod support;

mod kzg;
mod kzg_sharding;
mod kzg_streaming;
mod parity_fixture;
mod pipeline_root;
mod plonkish_batch;
mod plonkish_hash;
mod plonkish_pcs;
mod plonkish_plan;
mod plonkish_verifier_algebra;
mod plonkish_verifier_security;
mod root_profile;
