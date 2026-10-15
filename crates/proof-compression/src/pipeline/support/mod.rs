//! Stage support shared by the first and recursive KZG stages: proof
//! metadata storage, setup selection, the fixed-preprocessing cache and the
//! worker request protocol.
pub(crate) mod kzg_fixed_cache;
pub(crate) mod kzg_setup;
pub(crate) mod kzg_storage;
pub(crate) mod kzg_worker_protocol;
