//! Bounded, diagnostic-only heavy hitters. No expression graphs are retained.
//!
//! Space-Saving counters replace the least frequent tracked key when full.
//! A replacement inherits that counter as its error bound. For each retained
//! key, the actual event count lies in [count - error, count]; it is exact
//! before any eviction. Unlike keeping just the first N keys, late hotspots
//! can enter the report. An indexed min-heap bounds storage AND update work
//! (O(log N)); a lazy heap would accumulate stale entries without bound.

use std::fmt::{self, Write};

use rustc_hash::FxHashMap;

use crate::env::{Addr, CtxAddr};

const MAX_ENTRIES: usize = 4096;
const MAX_LABEL_BYTES: usize = 512;

/// Exact diagnostic identity, independent of the truncated display label.
/// `context` is present only for IX_HOT_MISS_CTX. FVars remain distinguished
/// by their expression UID, just as in the previous string-keyed report.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct MissKey {
  pub(crate) phase: &'static str,
  pub(crate) a: Addr,
  pub(crate) b: Option<Addr>,
  pub(crate) context: Option<(CtxAddr, u64)>,
}

struct Entry {
  key: MissKey,
  label: String,
  count: u64,
  error: u64,
}

#[derive(Default)]
pub(crate) struct HotMisses {
  positions: FxHashMap<MissKey, usize>,
  heap: Vec<Entry>,
  events: u64,
  replacements: u64,
}

impl HotMisses {
  pub(crate) fn record(
    &mut self,
    key: MissKey,
    label: impl FnOnce(&mut Label) -> fmt::Result,
  ) {
    self.record_with_capacity(key, label, MAX_ENTRIES);
  }

  fn record_with_capacity(
    &mut self,
    key: MissKey,
    label: impl FnOnce(&mut Label) -> fmt::Result,
    capacity: usize,
  ) {
    self.events = self.events.saturating_add(1);
    if let Some(&i) = self.positions.get(&key) {
      self.heap[i].count = self.heap[i].count.saturating_add(1);
      self.sift_down(i);
      return;
    }
    // Format ONLY on admission, not on every hit. Label storage is bounded
    // even for enormous metadata names. Keys hold only UIDs/context hashes.
    let mut text = Label(String::with_capacity(MAX_LABEL_BYTES));
    let _ = label(&mut text);
    if self.heap.len() < capacity {
      let i = self.heap.len();
      self.heap.push(Entry { key, label: text.0, count: 1, error: 0 });
      self.positions.insert(key, i);
      let mut i = i;
      while i > 0 {
        let parent = (i - 1) / 2;
        if self.heap[parent].count <= self.heap[i].count {
          break;
        }
        self.swap(i, parent);
        i = parent;
      }
    } else {
      let min = &self.heap[0];
      let error = min.count;
      self.positions.remove(&min.key);
      self.heap[0] =
        Entry { key, label: text.0, count: error.saturating_add(1), error };
      self.positions.insert(key, 0);
      self.replacements = self.replacements.saturating_add(1);
      self.sift_down(0);
    }
  }

  fn swap(&mut self, a: usize, b: usize) {
    self.heap.swap(a, b);
    *self.positions.get_mut(&self.heap[a].key).unwrap() = a;
    *self.positions.get_mut(&self.heap[b].key).unwrap() = b;
  }

  fn sift_down(&mut self, mut i: usize) {
    loop {
      let left = 2 * i + 1;
      if left >= self.heap.len() {
        return;
      }
      let right = left + 1;
      let child = if right < self.heap.len()
        && self.heap[right].count < self.heap[left].count
      {
        right
      } else {
        left
      };
      if self.heap[i].count <= self.heap[child].count {
        return;
      }
      self.swap(i, child);
      i = child;
    }
  }

  pub(crate) fn clear(&mut self) {
    self.positions.clear();
    self.heap.clear();
    self.events = 0;
    self.replacements = 0;
  }

  pub(crate) fn summary(&self) -> String {
    if self.heap.is_empty() {
      return String::new();
    }
    let mut entries: Vec<_> = self.heap.iter().collect();
    entries.sort_unstable_by(|a, b| {
      b.count.cmp(&a.count).then_with(|| a.label.cmp(&b.label))
    });
    let mut out = format!(
      "[hot misses] events={} tracked={}/{} replacements={}; top {}; counts are [lower, upper] bounds, not exact after replacement:\n",
      self.events,
      entries.len(),
      MAX_ENTRIES,
      self.replacements,
      entries.len().min(25)
    );
    if self.events == u64::MAX {
      out.push_str("  counters saturated: upper bounds may be truncated\n");
    }
    for entry in entries.into_iter().take(25) {
      let _ = writeln!(
        out,
        "  [{:>8}, {:>8}]  {}",
        entry.count - entry.error,
        entry.count,
        entry.label
      );
    }
    out
  }
}

/// A UTF-8-safe bounded formatter. Returning Err stops Display writers before
/// they accumulate an arbitrarily large diagnostic string. The ellipsis is
/// included in the bound. Labels are never used as identities.
pub(crate) struct Label(String);

impl Write for Label {
  fn write_str(&mut self, s: &str) -> fmt::Result {
    let remaining = MAX_LABEL_BYTES - self.0.len();
    if s.len() <= remaining {
      self.0.push_str(s);
      return Ok(());
    }
    let prefix = self.0.len().min(MAX_LABEL_BYTES - 3);
    self.0.truncate(self.0.floor_char_boundary(prefix));
    let end = s.floor_char_boundary(MAX_LABEL_BYTES - 3 - self.0.len());
    self.0.push_str(&s[..end]);
    self.0.push_str("...");
    Err(fmt::Error)
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  fn key(a: u64) -> MissKey {
    MissKey { phase: "infer", a, b: None, context: None }
  }

  fn record(misses: &mut HotMisses, id: u64, capacity: usize) {
    misses.record_with_capacity(key(id), |s| write!(s, "uid{id}"), capacity);
  }

  fn invariant(misses: &HotMisses, exact: &FxHashMap<u64, u64>) {
    assert_eq!(misses.heap.len(), misses.positions.len());
    assert_eq!(misses.events, exact.values().sum());
    assert_eq!(misses.events, misses.heap.iter().map(|e| e.count).sum());
    for (i, e) in misses.heap.iter().enumerate() {
      assert_eq!(misses.positions[&e.key], i);
      assert!(e.count - e.error <= exact[&e.key.a]);
      assert!(exact[&e.key.a] <= e.count);
      if i > 0 {
        assert!(misses.heap[(i - 1) / 2].count <= e.count);
      }
    }
  }

  #[test]
  fn exact_until_full_and_labels_are_only_formatted_on_misses() {
    let mut misses = HotMisses::default();
    record(&mut misses, 1, 4);
    misses.record(key(1), |_| panic!("do not format an existing key"));
    record(&mut misses, 2, 4);
    assert_eq!(misses.replacements, 0);
    assert_eq!(misses.heap[misses.positions[&key(1)]].count, 2);
    assert!(misses.heap.iter().all(|e| e.error == 0));
  }

  #[test]
  fn bounded_heap_and_error_intervals_match_exact_counts() {
    for capacity in [1, 2, 7, 32] {
      let mut misses = HotMisses::default();
      let mut exact = FxHashMap::default();
      let mut random = 1u64;
      for i in 0..10_000 {
        random = random.wrapping_mul(6364136223846793005).wrapping_add(1);
        let id = if i % 3 == 0 { i % 5 } else { random >> 48 };
        record(&mut misses, id, capacity);
        *exact.entry(id).or_default() += 1;
        assert!(misses.heap.len() <= capacity);
        invariant(&misses, &exact);
      }
    }
  }

  #[test]
  fn late_hotspots_displace_cold_entries_and_reset_clears_counts() {
    let mut misses = HotMisses::default();
    for i in 0..100_000 {
      record(&mut misses, i, MAX_ENTRIES);
    }
    for _ in 0..10_000 {
      record(&mut misses, 100_001, MAX_ENTRIES);
    }
    assert_eq!(misses.heap.len(), MAX_ENTRIES);
    assert_eq!(misses.positions.len(), MAX_ENTRIES);
    let hot = &misses.heap[misses.positions[&key(100_001)]];
    assert_eq!(hot.count - hot.error, 10_000);
    assert!(misses.summary().contains("uid100001"));
    assert_eq!(misses.summary().lines().count(), 26);
    misses.clear();
    assert!(misses.summary().is_empty());
    assert!(misses.positions.is_empty());
    assert_eq!(misses.events, 0);
    assert_eq!(misses.replacements, 0);
    record(&mut misses, 1, MAX_ENTRIES);
    assert_eq!(misses.heap[0].count, 1);
    assert_eq!(misses.heap[0].error, 0);
  }

  #[test]
  fn labels_are_bounded_utf8_and_never_merge_distinct_keys() {
    let mut misses = HotMisses::default();
    for id in 0..2 {
      misses.record(key(id), |s| write!(s, "{}", "λ".repeat(100_000)));
    }
    assert_eq!(misses.heap.len(), 2);
    for e in &misses.heap {
      assert!(e.label.len() <= MAX_LABEL_BYTES);
      assert!(e.label.ends_with("..."));
    }
    let mut label = Label("λ".repeat(256));
    assert!(label.write_str("λ").is_err());
    assert!(label.0.len() <= MAX_LABEL_BYTES);
    let context = Some((blake3::hash(b"ctx"), 3));
    misses.record(MissKey { context, ..key(0) }, |s| write!(s, "context"));
    misses.record(MissKey { b: Some(0), ..key(0) }, |s| write!(s, "pair"));
    misses.record(MissKey { phase: "whnf", ..key(0) }, |s| write!(s, "phase"));
    assert_eq!(misses.heap.len(), 5);
  }
}
