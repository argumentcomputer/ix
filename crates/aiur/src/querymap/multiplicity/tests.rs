use super::*;
use crate::{
  execute::budget::ExecutionBudget,
  querymap::{QueryKey, QueryMap},
};

fn append(store: &mut Multiplicities, value: G) {
  store.push(value, store.plan_append(value));
}

fn bump(store: &mut Multiplicities, i: usize) {
  if !store.try_bump(i) {
    store.bump_widened(i, store.plan_bump(i));
  }
}

#[test]
fn canonical_boundaries_and_field_wrap_match_full_width_counters() {
  for initial in [
    G::ZERO,
    G::ONE,
    G::from_u16(255),
    G::from_u16(65535),
    G::from_u32(u32::MAX - 1),
    G::from_u32(u32::MAX),
    G::from_u64(1 << 32),
    G::NEG_ONE,
    G::new(G::ORDER_U64 + 7),
  ] {
    let mut compact = Multiplicities::new(true);
    let mut full = Multiplicities::new(false);
    append(&mut compact, initial);
    append(&mut full, initial);
    let narrow = u32::try_from(initial.as_canonical_u64()).is_ok();
    assert_eq!(compact.retained_bytes(), if narrow { 4 } else { 8 });
    for _ in 0..5 {
      assert_eq!(compact.at(0), full.at(0));
      bump(&mut compact, 0);
      bump(&mut full, 0);
    }
    assert_eq!(compact.at(0), initial + G::from_u8(5));
    if initial == G::NEG_ONE {
      assert_eq!(compact.segs[0].width(), 8, "do not shrink after field wrap");
    }
  }
}

#[test]
fn overflow_probe_is_read_only_until_widening_is_applied() {
  let mut store = Multiplicities::new(true);
  append(&mut store, G::from_u32(u32::MAX));
  append(&mut store, G::ONE);
  let bytes = store.accounted_bytes();
  for _ in 0..3 {
    assert!(!store.try_bump(0));
    let plan = store.plan_bump(0);
    assert_eq!(store.at(0), G::from_u32(u32::MAX));
    assert_eq!(store.at(1), G::ONE);
    assert_eq!(store.retained_bytes(), 8);
    assert_eq!(store.accounted_bytes(), bytes);
    assert_eq!(plan.transient, bytes);
  }
  bump(&mut store, 0);
  assert_eq!(store.at(0), G::from_u64(1 << 32));
  assert_eq!(store.at(1), G::ONE);
  assert_eq!(store.retained_bytes(), 16);
}

#[test]
fn old_full_and_partial_segments_widen_independently() {
  let mut store = Multiplicities::new(true);
  for i in 0..2 * SEG_ENTRIES + 3 {
    let value = if i == 0 || i == 2 * SEG_ENTRIES - 1 {
      G::from_u32(u32::MAX)
    } else {
      G::ONE
    };
    append(&mut store, value);
  }
  assert_eq!(store.retained_bytes(), (2 * SEG_ENTRIES + 3) * 4);
  // Appending an arbitrary field widens only the partial final segment.
  append(&mut store, G::NEG_ONE);
  assert_eq!(
    store.segs.iter().map(Segment::width).collect::<Vec<_>>(),
    [4, 4, 8]
  );
  bump(&mut store, 0);
  assert_eq!(
    store.segs.iter().map(Segment::width).collect::<Vec<_>>(),
    [8, 4, 8]
  );
  bump(&mut store, 2 * SEG_ENTRIES - 1);
  bump(&mut store, 2 * SEG_ENTRIES + 3);
  assert_eq!(store.retained_bytes(), (2 * SEG_ENTRIES + 4) * 8);
  for i in 0..store.entries {
    let expected = if i == 0 || i == 2 * SEG_ENTRIES - 1 {
      G::from_u64(1 << 32)
    } else if i == 2 * SEG_ENTRIES + 3 {
      G::ZERO
    } else {
      G::ONE
    };
    assert_eq!(store.at(i), expected, "row {i}");
  }
  assert_eq!(
    store.accounted_bytes(),
    2 * segment_bytes(SEG_ENTRIES, 8) + segment_bytes(4, 8)
  );
}

#[test]
fn a_wide_segment_does_not_force_new_segments_to_be_wide() {
  let mut store = Multiplicities::new(true);
  for _ in 0..SEG_ENTRIES - 1 {
    append(&mut store, G::ONE);
  }
  append(&mut store, G::NEG_ONE);
  append(&mut store, G::ZERO);
  assert_eq!(store.segs.iter().map(Segment::width).collect::<Vec<_>>(), [8, 4]);
  assert_eq!(store.retained_bytes(), SEG_ENTRIES * 8 + 4);
  assert_eq!(store.at(SEG_ENTRIES - 2), G::ONE);
  assert_eq!(store.at(SEG_ENTRIES - 1), G::NEG_ONE);
  assert_eq!(store.at(SEG_ENTRIES), G::ZERO);
}

fn rows(map: &QueryMap) -> Vec<(Vec<G>, Vec<G>, G)> {
  map
    .iter()
    .map(|(k, r)| (k.to_vec(), r.output.to_vec(), r.multiplicity))
    .collect()
}

#[test]
fn failed_insert_and_hit_widening_preserve_rows_layout_and_both_budgets() {
  let initial = G::from_u32(u32::MAX);
  let mut reference = QueryMap::with_encodings(1, None, true, true);
  reference.implicit_output = true;
  reference.insert(&[G::ZERO], &[G::ZERO], initial).unwrap();
  let steady = reference.accounted_bytes();
  for shared_failure in [false, true] {
    let limit = steady + (1 << 20); // Not enough for the replacement segment.
    let shared = ExecutionBudget::new(
      if shared_failure { limit } else { 1 << 30 },
      "shared".into(),
      None,
    );
    let local = ExecutionBudget::new(
      if shared_failure { 1 << 30 } else { limit },
      "record".into(),
      Some(shared.clone()),
    );
    let mut map = QueryMap::with_encodings(1, Some(local.clone()), true, true);
    map.implicit_output = true;
    map.insert(&[G::ZERO], &[G::ZERO], initial).unwrap();
    let charged = local.used();
    let payload = map.mults.retained_bytes();
    for operation in 0..3 {
      let error = match operation {
        0 => map.bump_multiplicity(0).unwrap_err(),
        1 => map
          .finish_prehashed(&QueryKey::new([G::ZERO]), &[G::ZERO], true)
          .unwrap_err(),
        _ => map.insert(&[G::ONE], &[G::ONE], G::NEG_ONE).unwrap_err(),
      };
      assert_eq!(error.shared, shared_failure);
      assert_eq!(rows(&map), rows(&reference));
      assert_eq!(map.mults.segs[0].width(), 4);
      assert_eq!(map.mults.retained_bytes(), payload);
      assert_eq!(map.get_index_of(&[G::ONE]), None);
      assert_eq!((local.used(), shared.used()), (charged, charged));
      // An unconstrained cache return still needs no allocation or bump.
      map.finish(&[G::ZERO], &[G::ZERO], false).unwrap();
    }
    drop(map);
    assert_eq!((local.used(), shared.used()), (0, 0));
  }
}

#[test]
fn successful_promotion_accounts_for_coexisting_segments_then_releases_them() {
  let shared = ExecutionBudget::new(1 << 30, "shared".into(), None);
  let budget =
    ExecutionBudget::new(1 << 30, "record".into(), Some(shared.clone()));
  let mut map = QueryMap::with_encodings(1, Some(budget.clone()), true, true);
  for i in 0..1024 {
    map.insert(&[G::from_usize(i)], &[], G::from_u32(u32::MAX)).unwrap();
  }
  let before = budget.used();
  let plan = map.mults.plan_bump(0);
  let expected_peak =
    before - map.mults.accounted_bytes() + plan.storage_after + plan.transient;
  map.bump_multiplicity(0).unwrap();
  assert!(budget.peak() >= expected_peak);
  assert_eq!(budget.used(), map.accounted_bytes());
  assert_eq!(shared.used(), budget.used());
  for i in 0..1024 {
    assert_eq!(map.get_index_of(&[G::from_usize(i)]), Some(i));
    assert_eq!(map.mult_at(i), G::from_u32(u32::MAX) + G::from_bool(i == 0));
  }
  drop(map);
  assert_eq!((budget.used(), shared.used()), (0, 0));
}

#[test]
fn mixed_hint_and_constrained_updates_match_full_records_and_memory_ids() {
  for memory in [false, true] {
    let mut compact = QueryMap::with_encodings(1, None, true, true);
    let mut full = QueryMap::with_encodings(1, None, true, false);
    compact.implicit_output = memory;
    full.implicit_output = memory;
    for i in 0..4096 {
      let key = QueryKey::new([G::from_usize(i)]);
      let out = [G::from_usize(i)];
      let initial = match i % 7 {
        0 => G::ZERO,
        1 => G::from_u32(u32::MAX),
        2 => G::NEG_ONE,
        _ => G::new(G::ORDER_U64 + 1),
      };
      for map in [&mut compact, &mut full] {
        map.insert_prehashed(&key, &out, initial).unwrap();
        map.finish_prehashed(&key, &out, false).unwrap();
        map.finish_prehashed(&key, &out, true).unwrap();
        map.bump_multiplicity(i).unwrap();
        assert_eq!(map.get_prehashed(&key), Some(i));
      }
    }
    assert_eq!(rows(&compact), rows(&full));
    assert_eq!(compact.mults.retained_bytes(), full.mults.retained_bytes());
  }
}

#[test]
#[ignore = "matched counter insertion/random-hit throughput; run explicitly in release mode"]
fn counter_storage_and_update_throughput() {
  use std::{hint::black_box, time::Instant};
  for round in 0..4 {
    for compact in if round % 2 == 0 { [false, true] } else { [true, false] } {
      let mut store = Multiplicities::new(compact);
      let started = Instant::now();
      for _ in 0..4 * SEG_ENTRIES {
        append(&mut store, black_box(G::ONE));
      }
      let insert_us = started.elapsed().as_micros();
      let started = Instant::now();
      for i in 0..16 * SEG_ENTRIES {
        let index = black_box(i.wrapping_mul(7919) & (4 * SEG_ENTRIES - 1));
        assert!(store.try_bump(index));
      }
      let hit_us = started.elapsed().as_micros();
      assert!((0..store.entries).all(|i| store.at(i) == G::from_u8(5)));
      eprintln!(
        "counter round={round} compact={compact} insert_us={insert_us} hit_us={hit_us} payload={} accounted={}",
        store.retained_bytes(),
        store.accounted_bytes()
      );
    }
  }
}
