//! Field-valued counters, optionally encoded as u32 until a segment widens.
//! No mutable field references escape: even a memo hit may need a budgeted
//! allocation. Width is per segment, never inferred from trusted metadata.

use super::{
  G, HugeVec, SEG_BITS, SEG_ENTRIES, SEG_MASK, storage::segment_bytes,
};
use multi_stark::p3_field::{PrimeCharacteristicRing, PrimeField64};
use std::sync::LazyLock;

pub(super) static COMPACT: LazyLock<bool> = LazyLock::new(|| {
  std::env::var_os("IX_AIUR_COMPACT_MULTIPLICITIES").is_some_and(|s| s == "1")
});

pub(super) enum Segment {
  U32(HugeVec<u32>),
  Field(HugeVec<G>),
}

impl Segment {
  fn new(wide: bool) -> Self {
    if wide {
      Self::Field(HugeVec::with_capacity(SEG_ENTRIES))
    } else {
      Self::U32(HugeVec::with_capacity(SEG_ENTRIES))
    }
  }

  pub(super) fn width(&self) -> usize {
    match self {
      Self::U32(_) => 4,
      Self::Field(_) => 8,
    }
  }

  #[inline]
  fn at(&self, row: usize) -> G {
    match self {
      Self::U32(xs) => G::from_u32(xs.slice(row, 1)[0]),
      Self::Field(xs) => xs.slice(row, 1)[0],
    }
  }

  fn push(&mut self, value: G) {
    match self {
      Self::U32(xs) => xs
        .extend_from_slice(&[u32::try_from(value.as_canonical_u64())
          .expect("counter width checked")]),
      Self::Field(xs) => xs.extend_from_slice(&[value]),
    }
  }
}

/// A read-only growth estimate. QueryMap reserves old + replacement storage
/// before applying it, then releases the old pages' charge after copying.
pub(super) struct Plan {
  wide: bool,
  promote: bool,
  pub storage_after: u64,
  pub transient: u64,
  payload_after: usize,
}

pub(super) struct Multiplicities {
  pub segs: Vec<Segment>,
  pub entries: usize,
  compact: bool,
  storage: u64,
  payload: usize,
}

impl Multiplicities {
  pub(super) fn new(compact: bool) -> Self {
    Self { segs: Vec::new(), entries: 0, compact, storage: 0, payload: 0 }
  }

  #[inline]
  pub(super) fn at(&self, i: usize) -> G {
    assert!(i < self.entries, "multiplicity index out of bounds");
    self.segs[i >> SEG_BITS].at(i & SEG_MASK)
  }

  /// The common hit path allocates nothing and makes no budget reservation.
  /// On u32 overflow, return false WITHOUT mutation; the caller must reserve
  /// a widening before retrying. Full-width counters keep field arithmetic,
  /// including modular wrap (never integer saturation or u32 wrap).
  #[inline]
  pub(super) fn try_bump(&mut self, i: usize) -> bool {
    assert!(i < self.entries, "multiplicity index out of bounds");
    match &mut self.segs[i >> SEG_BITS] {
      Segment::U32(xs) => {
        let value = &mut xs.slice_mut(i & SEG_MASK, 1)[0];
        if let Some(next) = value.checked_add(1) {
          *value = next;
          true
        } else {
          false
        }
      },
      Segment::Field(xs) => {
        xs.slice_mut(i & SEG_MASK, 1)[0] += G::ONE;
        true
      },
    }
  }

  pub(super) fn plan_append(&self, value: G) -> Plan {
    let tail = self.entries & SEG_MASK;
    let old_width =
      if tail == 0 { 0 } else { self.segs.last().unwrap().width() };
    let wide = !self.compact
      || old_width == 8
      || u32::try_from(value.as_canonical_u64()).is_err();
    let width = if wide { 8 } else { 4 };
    let promote = tail != 0 && old_width != width;
    let old = segment_bytes(tail, old_width);
    Plan {
      wide,
      promote,
      storage_after: self
        .storage
        .saturating_sub(old)
        .saturating_add(segment_bytes(tail + 1, width)),
      transient: if promote { old } else { 0 },
      payload_after: self
        .payload
        .saturating_add(width)
        .saturating_add(if promote { tail.saturating_mul(4) } else { 0 }),
    }
  }

  /// Unlike key/output packing, hits can widen ANY segment, not just the tail.
  pub(super) fn plan_bump(&self, i: usize) -> Plan {
    assert!(i < self.entries, "multiplicity index out of bounds");
    let segment = i >> SEG_BITS;
    assert_eq!(self.segs[segment].width(), 4);
    assert_eq!(self.at(i), G::from_u32(u32::MAX));
    let rows = self.segment_rows(segment);
    let old = segment_bytes(rows, 4);
    Plan {
      wide: true,
      promote: true,
      storage_after: self
        .storage
        .saturating_sub(old)
        .saturating_add(segment_bytes(rows, 8)),
      transient: old,
      payload_after: self.payload.saturating_add(rows.saturating_mul(4)),
    }
  }

  fn promote(&mut self, segment: usize) {
    let rows = self.segment_rows(segment);
    let Segment::U32(old) = &self.segs[segment] else {
      panic!("counter segment already widened");
    };
    let mut next = HugeVec::with_capacity(SEG_ENTRIES);
    for &value in old.slice(0, rows) {
      next.extend_from_slice(&[G::from_u32(value)]);
    }
    // Only now drop the old mapping. QueryMap holds both charges until here.
    self.segs[segment] = Segment::Field(next);
  }

  // Consume plans so internal callers cannot reuse a stale growth estimate.
  #[allow(clippy::needless_pass_by_value)]
  pub(super) fn push(&mut self, value: G, plan: Plan) {
    if self.entries & SEG_MASK == 0 {
      self.segs.push(Segment::new(plan.wide));
    } else if plan.promote {
      self.promote(self.entries >> SEG_BITS);
    }
    self.segs.last_mut().unwrap().push(value);
    self.entries += 1;
    self.storage = plan.storage_after;
    self.payload = plan.payload_after;
  }

  #[allow(clippy::needless_pass_by_value)]
  pub(super) fn bump_widened(&mut self, i: usize, plan: Plan) {
    assert!(plan.promote && plan.wide);
    self.promote(i >> SEG_BITS);
    assert!(self.try_bump(i));
    self.storage = plan.storage_after;
    self.payload = plan.payload_after;
  }

  pub(super) fn segment_rows(&self, segment: usize) -> usize {
    (self.entries - (segment << SEG_BITS)).min(SEG_ENTRIES)
  }

  pub(super) fn accounted_bytes(&self) -> u64 {
    self.storage
  }

  pub(super) fn retained_bytes(&self) -> usize {
    self.payload
  }
}

#[cfg(test)]
mod tests;
