//! Read-only, fixed-size multiplicity distributions for representation studies.
//! These snapshots do not count mutations or remember past segment maxima.

use super::{
  PrimeField64,
  multiplicity::{Multiplicities, Segment},
};

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MultiplicityStats {
  /// Disjoint canonical-value bins: 0, 1, 2..255, 256..65535,
  /// 65536..u32::MAX, and larger field values.
  pub counts: [u64; 6],
  /// Segment maxima fitting in u8/u16/u32/full field, disjoint bins.
  pub segments: [u64; 4],
  /// Initialized rows in those segments (including the partial last segment).
  pub segment_rows: [u64; 4],
  pub max: u64,
  /// Sum of canonical field values, NOT a lifetime update/call count:
  /// hint initialization and modular wrap mean those are different quantities.
  pub canonical_sum: u128,
  /// Actual initialized payload, including segments kept wide after wrap.
  /// Excludes unused capacity, page rounding, and allocation metadata.
  pub stored_payload_bytes: u64,
  /// Actual segment encodings: u32, full field (not snapshot maxima).
  pub stored_segments: [u64; 2],
}

impl MultiplicityStats {
  pub(super) fn of_store(store: &Multiplicities) -> Self {
    let mut result = Self {
      stored_payload_bytes: store.retained_bytes() as u64,
      ..Default::default()
    };
    for (i, segment) in store.segs.iter().enumerate() {
      let rows = store.segment_rows(i);
      let mut max = 0;
      let mut observe = |value: u64| {
        let bin = match value {
          0 => 0,
          1 => 1,
          2..=255 => 2,
          256..=65535 => 3,
          65536..=0xffff_ffff => 4,
          _ => 5,
        };
        result.counts[bin] += 1;
        result.canonical_sum += u128::from(value);
        max = max.max(value);
      };
      match segment {
        Segment::U32(xs) => {
          for &value in xs.slice(0, rows) {
            observe(u64::from(value));
          }
          result.stored_segments[0] += 1;
        },
        Segment::Field(xs) => {
          for value in xs.slice(0, rows) {
            observe(value.as_canonical_u64());
          }
          result.stored_segments[1] += 1;
        },
      }
      let bin = match max {
        0..=255 => 0,
        256..=65535 => 1,
        65536..=0xffff_ffff => 2,
        _ => 3,
      };
      result.segments[bin] += 1;
      result.segment_rows[bin] += u64::try_from(rows).expect("segment rows");
      result.max = result.max.max(max);
    }
    debug_assert_eq!(result.rows(), store.entries as u64);
    result
  }

  pub fn rows(&self) -> u64 {
    self.counts.iter().sum()
  }

  /// Equivalent full-field payload, excluding allocator/page rounding.
  pub fn full_payload_bytes(&self) -> u64 {
    self.rows() * 8
  }

  /// Hypothetical segment-wide u8/u16/u32/field encoding of this snapshot.
  /// A lower bound, not a measured allocation: ignores spare capacity,
  /// metadata, page rounding and historical widening before field wrap.
  pub fn adaptive_payload_bytes(&self) -> u64 {
    self.segment_rows.iter().zip([1, 2, 4, 8]).map(|(n, b)| n * b).sum()
  }

  /// Same snapshot lower bound for u32 segments promoted to full fields.
  pub fn u32_payload_bytes(&self) -> u64 {
    (self.rows() - self.segment_rows[3]) * 4 + self.segment_rows[3] * 8
  }

  pub fn merge(&mut self, other: &Self) {
    for (a, b) in self.counts.iter_mut().zip(&other.counts) {
      *a += b;
    }
    for (a, b) in self.segments.iter_mut().zip(&other.segments) {
      *a += b;
    }
    for (a, b) in self.segment_rows.iter_mut().zip(&other.segment_rows) {
      *a += b;
    }
    self.max = self.max.max(other.max);
    self.canonical_sum += other.canonical_sum;
    self.stored_payload_bytes += other.stored_payload_bytes;
    for (a, b) in self.stored_segments.iter_mut().zip(&other.stored_segments) {
      *a += b;
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::{
    G,
    querymap::{QueryMap, SEG_ENTRIES},
  };
  use multi_stark::p3_field::PrimeCharacteristicRing;

  #[test]
  fn empty_and_boundary_values_use_disjoint_canonical_bins() {
    let mut store = Multiplicities::new(true);
    assert_eq!(
      MultiplicityStats::of_store(&store),
      MultiplicityStats::default()
    );
    let values = [
      0,
      1,
      2,
      255,
      256,
      65535,
      65536,
      0xffff_ffff,
      0x1_0000_0000,
      G::ORDER_U64 - 1,
      G::ORDER_U64 + 1,
    ];
    for value in values {
      let value = G::new(value);
      store.push(value, store.plan_append(value));
    }
    let stats = MultiplicityStats::of_store(&store);
    assert_eq!(stats.counts, [1, 2, 2, 2, 2, 2]);
    assert_eq!(stats.segments, [0, 0, 0, 1]);
    assert_eq!(stats.segment_rows, [0, 0, 0, 11]);
    assert_eq!(stats.max, G::ORDER_U64 - 1);
    assert_eq!(
      stats.canonical_sum,
      values.into_iter().map(|v| u128::from(v % G::ORDER_U64)).sum::<u128>()
    );
    assert_eq!(stats.full_payload_bytes(), 88);
    assert_eq!(stats.adaptive_payload_bytes(), 88);
    assert_eq!(stats.u32_payload_bytes(), 88);
  }

  #[test]
  fn segment_boundaries_and_late_counter_updates_are_observed() {
    let mut store = Multiplicities::new(true);
    let boundary = G::from_u32(u32::MAX);
    store.push(boundary, store.plan_append(boundary));
    for _ in 1..SEG_ENTRIES {
      store.push(G::ONE, store.plan_append(G::ONE));
    }
    let value = G::from_u16(256);
    store.push(value, store.plan_append(value));
    let stats = MultiplicityStats::of_store(&store);
    let full = u64::try_from(SEG_ENTRIES).unwrap();
    assert_eq!(stats.segments, [0, 1, 1, 0]);
    assert_eq!(stats.segment_rows, [0, 1, full, 0]);
    assert_eq!(stats.adaptive_payload_bytes(), full * 4 + 2);
    assert_eq!(stats.u32_payload_bytes(), (full + 1) * 4);
    assert!(!store.try_bump(0));
    store.bump_widened(0, store.plan_bump(0));
    let wide = MultiplicityStats::of_store(&store);
    assert_eq!(wide.segments, [0, 1, 0, 1]);
    assert_eq!(wide.segment_rows, [0, 1, 0, full]);
    assert_eq!(wide.u32_payload_bytes(), full * 8 + 4);
    assert_eq!(wide.stored_payload_bytes, full * 8 + 4);
    store.push(G::NEG_ONE, store.plan_append(G::NEG_ONE));
    assert!(store.try_bump(SEG_ENTRIES + 1));
    let wrapped = MultiplicityStats::of_store(&store);
    // Snapshot maxima shrink after wrap, but allocated widths do not.
    assert_eq!(wrapped.segment_rows, [0, 2, 0, full]);
    assert_eq!(wrapped.stored_segments, [0, 2]);
    assert_eq!(wrapped.stored_payload_bytes, (full + 2) * 8);
    assert_eq!(wrapped.u32_payload_bytes(), full * 8 + 2 * 4);
  }

  #[test]
  fn snapshots_observe_all_mutation_apis_without_changing_queries() {
    let mut map = QueryMap::new(1);
    map.insert(&[G::ZERO], &[G::ONE], G::ZERO).unwrap();
    map.insert(&[G::ONE], &[G::TWO], G::from_u8(255)).unwrap();
    map.finish(&[G::ZERO], &[G::ONE], true).unwrap();
    map.bump_multiplicity(1).unwrap();
    map.insert(&[G::TWO], &[G::ZERO], G::NEG_ONE).unwrap();
    map.bump_multiplicity(2).unwrap();
    let before = map
      .iter()
      .map(|(k, r)| (k.to_vec(), r.output.to_vec(), r.multiplicity))
      .collect::<Vec<_>>();
    let stats = map.multiplicity_stats();
    assert_eq!(stats.counts, [1, 1, 0, 1, 0, 0]);
    assert_eq!(stats.segment_rows, [0, 3, 0, 0]);
    assert_eq!(stats.canonical_sum, 257);
    assert_eq!(
      before,
      map
        .iter()
        .map(|(k, r)| (k.to_vec(), r.output.to_vec(), r.multiplicity))
        .collect::<Vec<_>>()
    );
    let mut aggregate = MultiplicityStats::default();
    aggregate.merge(&stats);
    aggregate.merge(&stats);
    assert_eq!(aggregate.counts, [2, 2, 0, 2, 0, 0]);
    assert_eq!(aggregate.segment_rows, [0, 6, 0, 0]);
    assert_eq!(aggregate.canonical_sum, 514);
    assert_eq!(aggregate.stored_payload_bytes, 2 * stats.stored_payload_bytes);
    assert_eq!(aggregate.max, 256);
  }
}
