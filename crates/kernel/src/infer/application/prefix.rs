//! Bounded admission history, NOT a cache of types or validity judgments.
//!
//! A repeated fingerprint nominates a prefix for ordinary inference and
//! materialization. Collisions can only nominate extra work (or forget a hot
//! prefix); actual results always use the exact, mode-separated infer caches.

use std::hash::{Hash, Hasher};

use crate::env::{Addr, CtxAddr};

const INITIAL_SLOTS: usize = 64;
const MAX_SLOTS: usize = 4096;

/// A lazily allocated, direct-mapped two-touch filter. It starts at 512 bytes;
/// collision-heavy checks grow up to 32 KiB. No expressions,
/// contexts, or type results are retained. Reset between checked members.
#[derive(Default)]
pub(crate) struct PrefixAdmission {
  seen: Vec<u64>,
  collisions: usize,
}

impl PrefixAdmission {
  pub(crate) fn observe(
    &mut self,
    key: (Addr, CtxAddr),
    infer_only: bool,
  ) -> bool {
    let mut hasher = rustc_hash::FxHasher::default();
    (key, infer_only).hash(&mut hasher);
    // Zero denotes an empty slot. The extremely rare remapping collision is
    // harmless: this is only an allocation/work admission heuristic.
    self.observe_fingerprint(hasher.finish().max(1))
  }

  fn slot(fingerprint: u64, len: usize) -> usize {
    usize::try_from(fingerprint & (len as u64 - 1))
      .expect("masked to at most MAX_SLOTS - 1")
  }

  fn observe_fingerprint(&mut self, fingerprint: u64) -> bool {
    if self.seen.is_empty() {
      self.seen.resize(INITIAL_SLOTS, 0);
    }
    let mut slot = Self::slot(fingerprint, self.seen.len());
    if self.seen[slot] == fingerprint {
      return true;
    }
    if self.seen[slot] != 0 && self.seen.len() < MAX_SLOTS {
      self.collisions += 1;
      if self.collisions == self.seen.len() {
        let next_len = self.seen.len() * 2;
        let old = std::mem::replace(&mut self.seen, vec![0; next_len]);
        for saved in old.into_iter().filter(|&f| f != 0) {
          let i = Self::slot(saved, self.seen.len());
          self.seen[i] = saved;
        }
        self.collisions = 0;
        slot = Self::slot(fingerprint, self.seen.len());
      }
    }
    self.seen[slot] = fingerprint;
    false
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn repeated_keys_are_mode_and_context_specific() {
    let mut history = PrefixAdmission::default();
    let a = (1, blake3::hash(b"a"));
    let b = (1, blake3::hash(b"b"));
    assert!(history.seen.is_empty());
    assert!(!history.observe(a, false));
    assert!(history.observe(a, false));
    assert!(!history.observe(a, true));
    assert!(history.observe(a, true));
    assert!(!history.observe(b, true));
    assert!(history.observe(b, true));
  }

  #[test]
  fn collisions_forget_history_and_growth_is_bounded() {
    let mut history = PrefixAdmission::default();
    for i in 1..100_000 {
      // All fingerprints collide, even at the maximum size.
      let f = i * MAX_SLOTS as u64;
      assert!(!history.observe_fingerprint(f));
      assert!(history.observe_fingerprint(f));
      assert!(history.seen.len() <= MAX_SLOTS);
    }
    assert_eq!(history.seen.len(), MAX_SLOTS);
    assert!(!history.observe_fingerprint(MAX_SLOTS as u64));
  }
}
