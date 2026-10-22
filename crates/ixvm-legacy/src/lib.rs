//! Legacy IxVM, aggregation, and verifier host integration.
//! Execution uses bytecode by default; the `native` feature links the isolated
//! generated kernels. The new implementation lives in the `ixvm` crate.

/// Whether the optional generated execution kernels were compiled in.
pub const NATIVE_ENABLED: bool = cfg!(feature = "native");

pub mod aiur_ix_aggr_runner;
pub mod aiur_ixvm_runner;
pub mod aiur_ixvm_witness;
pub mod aiur_multi_stark_runner;
pub mod env_handle;
