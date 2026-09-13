//! Experimental generic IxBy/Flock backend building blocks.
//!
//! Imported primitive tables and witnesses are conformance-tested native
//! components, not a certified interpreter or a Stage 2 verification oracle.
//! Public gate internals remain experimental, with no stable API guarantee.

pub mod blake3_backend;
pub mod boolean;
pub mod conformance;
pub mod equality;
pub mod extension;
pub mod goldilocks;
pub mod hash;
pub mod ixby;
pub mod multiplication;
pub mod packed_blake3;
pub mod sizing;
pub mod window;

/// Baseline protocol pin; the experimental m37 patch is not enabled here.
pub const FLOCK_UPSTREAM_REVISION: &str =
  "b310f35f35f68095537150a1c8c0a43caca9a29e";
