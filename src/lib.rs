#[allow(unused_extern_crates)]
#[cfg(test)]
extern crate quickcheck;
#[allow(unused_extern_crates)]
#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;
#[allow(unused_extern_crates)]
#[cfg(test)]
extern crate rand;

use indexmap::{IndexMap, IndexSet};
use rustc_hash::FxBuildHasher;

pub mod aiur;
pub mod ffi;
// Iroh functionality is enabled by the `net` feature. However, Iroh doesn't work on `aarch64-darwin`, so it is always disabled for that target.
#[cfg(all(
  feature = "net",
  not(all(target_os = "macos", target_arch = "aarch64"))
))]
pub mod iroh;
pub mod ix;
pub mod lean;
mod sha256;

pub type FxIndexMap<K, V> = IndexMap<K, V, FxBuildHasher>;
pub type FxIndexSet<K> = IndexSet<K, FxBuildHasher>;
