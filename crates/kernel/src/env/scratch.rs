//! Reuse allocation, never logical memo entries, between independent calls.

use rustc_hash::FxHashMap;

// Entry-capacity floor, not a bound on a live traversal's memory. These are
// storage heuristics only: a call may grow its memo without limit as before.
const SMALL_CAPACITY: usize = 4_096;
const SPARSE_RATIO: usize = 16;
const SPARSE_USES_BEFORE_RELEASE: u8 = 2;

/// A per-call memo whose backing allocation follows recent occupancy.
///
/// A bulk traversal can grow a table that subsequent tiny calls spend most
/// of their time clearing: HashMap::clear scans control bytes across its
/// capacity, even when few entries remain. Release an oversized allocation
/// after two consecutive uses below 1/16 occupancy. Keeping one sparse use
/// tolerates alternating large/small calls without repeatedly regrowing the
/// large table. Small and well-used tables retain their allocation.
///
/// Entries from the previous call are retained solely to observe occupancy
/// and are ALWAYS removed before handing the map to the next call. Neither
/// keys nor values nor within-call memoization semantics depend on sizing.
pub(crate) struct ScratchMap<K, V> {
  map: FxHashMap<K, V>,
  sparse_uses: u8,
}

impl<K, V> Default for ScratchMap<K, V> {
  fn default() -> Self {
    Self { map: FxHashMap::default(), sparse_uses: 0 }
  }
}

impl<K, V> ScratchMap<K, V> {
  /// Borrow an EMPTY memo for one traversal. The owner keeps only sizing
  /// history and an empty placeholder until `restore_after_call`.
  pub(crate) fn take_for_call(&mut self) -> FxHashMap<K, V> {
    let capacity = self.map.capacity();
    if capacity > SMALL_CAPACITY && self.map.len() < capacity / SPARSE_RATIO {
      self.sparse_uses += 1;
      if self.sparse_uses == SPARSE_USES_BEFORE_RELEASE {
        // Drop directly: clearing first would scan the oversized allocation
        // once more just to discard it. A fresh map allocates only on insert.
        self.map = FxHashMap::default();
        self.sparse_uses = 0;
      }
    } else {
      self.sparse_uses = 0;
    }
    let mut map = std::mem::take(&mut self.map);
    map.clear();
    map
  }

  pub(crate) fn restore_after_call(&mut self, map: FxHashMap<K, V>) {
    debug_assert_eq!(self.map.capacity(), 0, "scratch is already restored");
    self.map = map;
  }

  /// Ordinary environment reset preserves capacity but not sizing history.
  pub(crate) fn clear(&mut self) {
    self.map.clear();
    self.sparse_uses = 0;
  }

  pub(crate) fn capacity(&self) -> usize {
    self.map.capacity()
  }

  #[cfg(test)]
  pub(crate) fn is_empty(&self) -> bool {
    self.map.is_empty()
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use std::sync::Arc;

  fn large_scratch() -> ScratchMap<usize, usize> {
    let mut scratch = ScratchMap::default();
    scratch.map.reserve(SMALL_CAPACITY * 4);
    scratch
  }

  fn fill(scratch: &mut ScratchMap<usize, usize>, len: usize) {
    assert!(scratch.map.is_empty());
    scratch.map.extend((0..len).map(|i| (i, i)));
  }

  #[test]
  fn scratch_discards_only_after_two_sparse_uses() {
    let mut scratch = large_scratch();
    let large = scratch.capacity();
    fill(&mut scratch, 1);
    let mut map = scratch.take_for_call();
    assert!(map.is_empty());
    assert_eq!(map.capacity(), large, "one sparse use retains capacity");
    map.insert(2, 3);
    scratch.restore_after_call(map);
    let map = scratch.take_for_call();
    assert!(map.is_empty());
    assert_eq!(map.capacity(), 0, "sustained sparse use releases capacity");
    assert_eq!(scratch.sparse_uses, 0);
  }

  #[test]
  fn scratch_retains_small_tables() {
    let mut scratch = ScratchMap::<usize, usize>::default();
    scratch.map.reserve(128);
    let capacity = scratch.capacity();
    assert!(capacity <= SMALL_CAPACITY);
    for _ in 0..8 {
      fill(&mut scratch, 1);
      let map = scratch.take_for_call();
      assert!(map.is_empty());
      assert_eq!(map.capacity(), capacity);
      scratch.restore_after_call(map);
    }
  }

  #[test]
  fn scratch_retains_well_used_large_tables_at_ratio_boundary() {
    let mut scratch = large_scratch();
    let capacity = scratch.capacity();
    for _ in 0..8 {
      fill(&mut scratch, capacity / SPARSE_RATIO);
      let map = scratch.take_for_call();
      assert!(map.is_empty());
      assert_eq!(map.capacity(), capacity);
      assert_eq!(scratch.sparse_uses, 0);
      scratch.restore_after_call(map);
    }
  }

  #[test]
  fn scratch_alternating_large_small_uses_do_not_churn() {
    let mut scratch = large_scratch();
    let capacity = scratch.capacity();
    for _ in 0..8 {
      for len in [1, capacity / 2] {
        fill(&mut scratch, len);
        let map = scratch.take_for_call();
        assert!(map.is_empty());
        assert_eq!(map.capacity(), capacity);
        scratch.restore_after_call(map);
      }
    }
  }

  #[test]
  fn scratch_empty_large_table_also_releases() {
    let mut scratch = large_scratch();
    let map = scratch.take_for_call();
    scratch.restore_after_call(map);
    assert_eq!(scratch.take_for_call().capacity(), 0);
  }

  #[test]
  fn scratch_clear_resets_history_and_releases_values() {
    let mut scratch = large_scratch();
    let capacity = scratch.capacity();
    fill(&mut scratch, 1);
    let mut map = scratch.take_for_call();
    map.insert(1, 2);
    scratch.restore_after_call(map);
    assert_eq!(scratch.sparse_uses, 1);
    scratch.clear();
    assert!(scratch.is_empty());
    assert_eq!(scratch.sparse_uses, 0);
    assert_eq!(scratch.capacity(), capacity);
    assert_eq!(scratch.take_for_call().capacity(), capacity);
  }

  #[test]
  fn scratch_never_returns_old_entries_or_retains_their_values() {
    let mut scratch = ScratchMap::<usize, Arc<usize>>::default();
    scratch.map.reserve(SMALL_CAPACITY * 4);
    for key in 0..4 {
      let value = Arc::new(key);
      let weak = Arc::downgrade(&value);
      scratch.map.insert(key, value);
      let map = scratch.take_for_call();
      assert!(map.is_empty());
      assert!(weak.upgrade().is_none(), "old memo value survived reset");
      scratch.restore_after_call(map);
    }
  }
}
