//! IxVM-specific Rust glue: codegen'd kernel, native runner, witness
//! builder. Bridges the `aiur` proving framework with `ixon` /
//! `ix-common` content-addressed env types.

pub mod aiur_ixvm;
pub mod aiur_ixvm_runner;
pub mod aiur_ixvm_witness;
pub mod env_handle;
