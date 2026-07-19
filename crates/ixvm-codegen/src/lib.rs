//! IxVM-specific Rust glue: codegen'd kernel + codegen'd MultiStark
//! recursive verifier, their native runners, witness builders.
//! Bridges the `aiur` proving framework with `ixon` / `ix-common`
//! content-addressed env types.

pub mod aiur_ixvm;
pub mod aiur_ixvm_runner;
pub mod aiur_ixvm_witness;
pub mod aiur_multi_stark;
pub mod aiur_multi_stark_runner;
pub mod env_handle;
