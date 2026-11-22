//! Tests only: see `tests/compiled.rs`. With feature `cuda`, the compiled
//! trace bundles of `aiur`'s depth, grouping and memory fixtures.

#[cfg(feature = "cuda")]
#[allow(warnings, clippy::all, clippy::pedantic)]
pub mod depth {
  include!(concat!(env!("OUT_DIR"), "/depth/bundle.rs"));
}

#[cfg(feature = "cuda")]
#[allow(warnings, clippy::all, clippy::pedantic)]
pub mod memory {
  include!(concat!(env!("OUT_DIR"), "/memory/bundle.rs"));
}

#[cfg(feature = "cuda")]
#[allow(warnings, clippy::all, clippy::pedantic)]
pub mod grouping {
  include!(concat!(env!("OUT_DIR"), "/grouping/bundle.rs"));
}
