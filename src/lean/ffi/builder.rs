//! LeanBuildCache struct for constructing Lean Ix types with caching.

use std::ffi::c_void;

use blake3::Hash;
use rustc_hash::FxHashMap;

/// Cache for constructing Lean Ix types with deduplication.
///
/// This struct maintains caches for names, levels, and expressions to avoid
/// rebuilding the same Lean objects multiple times during environment construction.
pub struct LeanBuildCache {
  pub(crate) names: FxHashMap<Hash, *mut c_void>,
  pub(crate) levels: FxHashMap<Hash, *mut c_void>,
  pub(crate) exprs: FxHashMap<Hash, *mut c_void>,
}

impl LeanBuildCache {
  pub fn new() -> Self {
    Self {
      names: FxHashMap::default(),
      levels: FxHashMap::default(),
      exprs: FxHashMap::default(),
    }
  }

  pub fn with_capacity(cap: usize) -> Self {
    Self {
      names: FxHashMap::with_capacity_and_hasher(cap, Default::default()),
      levels: FxHashMap::with_capacity_and_hasher(cap, Default::default()),
      exprs: FxHashMap::with_capacity_and_hasher(cap * 10, Default::default()),
    }
  }
}

impl Default for LeanBuildCache {
  fn default() -> Self {
    Self::new()
  }
}
