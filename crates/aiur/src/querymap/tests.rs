use super::*;

fn key(n: u64) -> [G; 16] {
  let mut fields = [G::ZERO; 16];
  for (out, byte) in fields.iter_mut().zip(n.to_le_bytes()) {
    *out = G::from_u8(byte);
  }
  fields
}

fn output(n: u64) -> [G; 9] {
  let mut fields = [G::ZERO; 9];
  for (out, byte) in fields.iter_mut().zip(n.wrapping_mul(7919).to_le_bytes()) {
    *out = G::from_u8(byte);
  }
  fields[8] = G::from_bool(n.is_multiple_of(2));
  fields
}

fn rows(map: &QueryMap) -> Vec<(Vec<G>, Vec<G>, G)> {
  map
    .iter()
    .map(|(k, r)| (k.to_vec(), r.output.to_vec(), r.multiplicity))
    .collect()
}

// Frozen pre-Q1 registration path for differential tests and timing: the
// caller probes, registration probes again, and insertion hashes once more.
fn legacy_finish(
  map: &mut QueryMap,
  key: &[G],
  output: &[G],
  constrained: bool,
) {
  if let Some(i) = map.get_index_of(key) {
    assert!(map.output_at(i).matches(output));
    if constrained {
      map.bump_multiplicity(i).unwrap();
    }
  } else {
    map.insert(key, output, G::from_bool(constrained)).unwrap();
  }
}

#[test]
fn prehashed_keys_survive_recursive_growth_and_preserve_hint_promotion() {
  let mut cached = QueryMap::new(16);
  let mut baseline = QueryMap::new(16);
  let pending = QueryKey::new(key(100_000));
  assert_eq!(cached.get_prehashed(&pending), None);
  for n in 0..8192 {
    let k = QueryKey::new(key(n));
    assert_eq!(cached.get_prehashed(&k), baseline.get_index_of(k.values()));
    cached.finish_prehashed(&k, &output(n), false).unwrap();
    legacy_finish(&mut baseline, k.values(), &output(n), false);
  }
  // Many child inserts have rehashed the table; the saved key is not a bucket.
  cached.finish_prehashed(&pending, &output(100_000), true).unwrap();
  legacy_finish(&mut baseline, pending.values(), &output(100_000), true);
  for n in (0..8192).rev() {
    let k = QueryKey::new(key(n));
    cached.finish_prehashed(&k, &output(n), true).unwrap();
    cached.finish_prehashed(&k, &output(n), true).unwrap();
    legacy_finish(&mut baseline, k.values(), &output(n), true);
    legacy_finish(&mut baseline, k.values(), &output(n), true);
  }
  assert_eq!(rows(&cached), rows(&baseline));
  assert_eq!(cached.accounted_bytes(), baseline.accounted_bytes());
}

#[test]
fn prehashed_collisions_still_compare_full_keys_after_rehash() {
  let mut map = QueryMap::new(2);
  // Exercise the internal collision path with a deliberately constant hash.
  // Public QueryKey constructors do not let callers supply a false hash.
  for n in 0..128 {
    let key = [G::from_u64(n * 256), G::NEG_ONE];
    map.insert_hashed(&key, 7, &[G::from_u64(n)], G::ZERO).unwrap();
  }
  for n in 0..128 {
    let key = [G::from_u64(n * 256), G::NEG_ONE];
    assert_eq!(
      map.get_index_of_hashed(&key, 7),
      Some(usize::try_from(n).unwrap())
    );
    map.finish_hashed(&key, 7, &[G::from_u64(n)], true).unwrap();
    assert_eq!(map.mult_at(usize::try_from(n).unwrap()), G::ONE);
  }
  assert_eq!(map.get_index_of_hashed(&[G::ONE, G::NEG_ONE], 7), None);
  assert_eq!(map.get_index_of_hashed(&[G::ZERO, G::ZERO], 7), None);
}

#[test]
fn prehashed_keys_own_values_and_canonicalize_field_representatives() {
  let mut values = [G::new(G::ORDER_U64 + 7)];
  let saved = QueryKey::new(values);
  values[0] = G::from_u16(256);
  let mut map = QueryMap::new(1);
  map.insert_prehashed(&saved, &[], G::ONE).unwrap();
  assert_eq!(map.get_prehashed(&QueryKey::new([G::from_u8(7)])), Some(0));
  assert_eq!(map.get_prehashed(&QueryKey::new(values)), None);
  let mut empty = QueryMap::new(0);
  let key = QueryKey::new([]);
  empty.finish_prehashed(&key, &[], true).unwrap();
  assert_eq!(empty.get_prehashed(&key), Some(0));
}

#[test]
fn prehashed_memory_insertion_preserves_budget_atomicity_and_pointer_ids() {
  let budget = ExecutionBudget::new(1, "tiny prehash".into(), None);
  let mut limited = QueryMap::with_memory_budget(1, Some(budget.clone()));
  let key = QueryKey::new([G::ONE]);
  assert!(limited.insert_prehashed(&key, &[G::ZERO], G::ONE).is_err());
  assert_eq!(limited.len(), 0);
  assert_eq!(limited.get_prehashed(&key), None);
  assert_eq!(budget.used(), 0);
  let mut memory = QueryMap::with_memory_budget(1, None);
  for n in 0..1024 {
    let key = QueryKey::new([G::from_usize(n)]);
    memory.insert_prehashed(&key, &[G::from_usize(n)], G::ONE).unwrap();
    assert_eq!(memory.get_prehashed(&key), Some(n));
    assert_eq!(memory.output_at(n).at(0), G::from_usize(n));
  }
}

#[test]
fn interpreter_restores_hashes_across_deep_recursive_returns_and_rehashes() {
  use crate::bytecode::{Block, Ctrl, Function, FunctionLayout, Op, Toplevel};
  let layout =
    FunctionLayout { input_size: 1, selectors: 2, auxiliaries: 1, lookups: 1 };
  let tl = Toplevel {
    functions: vec![
      Function {
        body: Block {
          ops: vec![Op::Call(1, vec![0], 1, false)],
          ctrl: Ctrl::Return(0, vec![1]),
        },
        layout,
        entry: true,
        constrained: true,
      },
      Function {
        body: Block {
          ops: vec![],
          ctrl: Ctrl::Match(
            0,
            [(G::ZERO, Block { ops: vec![], ctrl: Ctrl::Return(0, vec![0]) })]
              .into_iter()
              .collect(),
            Some(Box::new(Block {
              ops: vec![
                Op::Const(G::ONE),
                Op::Sub(0, 1),
                Op::Call(1, vec![2], 1, false),
                Op::Add(0, 3),
              ],
              ctrl: Ctrl::Return(1, vec![4]),
            })),
          ),
        },
        layout,
        entry: false,
        constrained: true,
      },
    ],
    memory_sizes: vec![],
    // Interpreter-only regression; no circuit synthesis is requested.
    circuits: vec![],
  };
  let mut io = crate::execute::IOBuffer {
    data: Default::default(),
    map: Default::default(),
  };
  let (record, out) =
    tl.execute(0, vec![G::from_u64(10_000)], &mut io).unwrap();
  assert_eq!(out, vec![G::from_u64(50_005_000)]);
  assert_eq!(record.function_queries[1].len(), 10_001);
  for n in 0..=10_000 {
    let q = record.function_queries[1].get(&[G::from_u64(n)]).unwrap();
    assert_eq!(q.output.at(0), G::from_u64(n * (n + 1) / 2));
    assert_eq!(q.multiplicity, G::ONE);
  }
}

#[test]
#[ignore = "matched query-path throughput; run explicitly in release mode"]
fn prehashed_query_paths_throughput() {
  fn bench<const N: usize>(cached: bool) -> (u128, u128, u64) {
    use std::{hint::black_box, time::Instant};
    let make_key = |n| {
      let mut key = [G::ZERO; N];
      key[0] = G::from_usize(n);
      key
    };
    let mut map = QueryMap::new(N);
    let started = Instant::now();
    for n in 0..1_000_000 {
      let values = black_box(make_key(n));
      let out = [values[0]];
      if cached {
        let key = QueryKey::new(values);
        assert!(map.get_prehashed(&key).is_none());
        map.finish_prehashed(&key, &out, true).unwrap();
      } else {
        assert!(map.get_index_of(&values).is_none());
        legacy_finish(&mut map, &values, &out, true);
      }
    }
    let insert_us = started.elapsed().as_micros();
    let started = Instant::now();
    for n in (0..1_000_000).rev() {
      let values = black_box(make_key(n));
      let i = if cached {
        map.get_prehashed(&QueryKey::new(values))
      } else {
        map.get_index_of(&values)
      }
      .unwrap();
      map.bump_multiplicity(i).unwrap();
      assert_eq!(black_box(map.output_at(i).at(0)), values[0]);
    }
    assert_eq!(map.len(), 1_000_000);
    (insert_us, started.elapsed().as_micros(), map.accounted_bytes())
  }
  for round in 0..4 {
    for cached in if round % 2 == 0 { [false, true] } else { [true, false] } {
      eprintln!(
        "prehash round={round} cached={cached} key2={:?} key16={:?} key64={:?}",
        bench::<2>(cached),
        bench::<16>(cached),
        bench::<64>(cached)
      );
    }
  }
}

#[test]
fn compact_and_full_maps_preserve_keys_outputs_order_and_promotion() {
  let mut compact = QueryMap::new(16);
  let mut full = QueryMap::with_storage(16, None, false);
  for n in 0..65_536 {
    let index = usize::try_from(n).unwrap();
    for map in [&mut compact, &mut full] {
      map.finish(&key(n), &output(n), false).unwrap();
      assert_eq!(map.mult_at(index), G::ZERO);
      map.finish(&key(n), &output(n), true).unwrap();
      map.finish(&key(n), &output(n), true).unwrap();
      assert_eq!(map.get_index_of(&key(n)), Some(index));
      assert_eq!(map.output_at(index).to_array::<9>(), output(n));
      assert_eq!(map.mult_at(index), G::TWO);
    }
  }
  assert_eq!(rows(&compact), rows(&full));
  assert_eq!(compact.retained_bytes(), 65_536 * 25);
  assert_eq!(compact.retained_bytes() * 8, full.retained_bytes());
  assert!(compact.accounted_bytes() < full.accounted_bytes());
}

#[test]
fn wide_values_are_preserved_and_never_alias_truncated_bytes() {
  let mut map = QueryMap::new(1);
  for (i, value) in [
    G::ZERO,
    G::ONE,
    G::from_u8(255),
    G::from_u16(256),
    G::from_u16(511),
    G::from_u64(1 << 56),
    G::NEG_ONE,
    G::from_u64(u64::MAX),
  ]
  .into_iter()
  .enumerate()
  {
    map.insert(&[value], &[value], G::from_u16(1000)).unwrap();
    assert_eq!(map.get_index_of(&[value]), Some(i));
    assert_eq!(map.output_at(i).to_array::<1>(), [value]);
    map.bump_multiplicity(i).unwrap();
    assert_eq!(map.mult_at(i), G::from_u16(1001));
  }
  assert_eq!(map.get_index_of(&[G::ZERO]), Some(0));
  assert_eq!(map.get_index_of(&[G::from_u16(256)]), Some(3));
  assert_eq!(map.get_index_of(&[G::from_u8(255)]), Some(2));
  assert_eq!(map.get_index_of(&[G::from_u16(511)]), Some(4));
  assert!(matches!(map.output_at(0), QuerySlice::Fields(_)));
}

#[test]
fn noncanonical_field_representatives_hit_the_same_byte_key() {
  let mut map = QueryMap::new(1);
  let alias = G::new(G::ORDER_U64 + 7);
  let canonical = G::from_u8(7);
  assert_eq!(alias, canonical);
  map.insert(&[alias], &[alias], G::ONE).unwrap();
  assert_eq!(map.get_index_of(&[canonical]), Some(0));
  assert!(matches!(map.output_at(0), QuerySlice::Bytes(_)));
  assert_eq!(map.output_at(0).at(0), alias);
  map.finish(&[canonical], &[canonical], true).unwrap();
  assert_eq!(map.len(), 1);
  assert_eq!(map.mult_at(0), G::TWO);
  // An actual wide field forces a lossless promotion; both representatives
  // must still resolve to the original row after the storage change.
  map.insert(&[G::from_u16(256)], &[G::NEG_ONE], G::ONE).unwrap();
  assert_eq!(map.get_index_of(&[alias]), Some(0));
  assert_eq!(map.get_index_of(&[canonical]), Some(0));
  assert_eq!(map.output_at(0).at(0), canonical);
}

#[test]
fn keys_and_outputs_widen_independently_without_rehashing() {
  let mut map = QueryMap::new(16);
  for n in 0..2048 {
    map.insert(&key(n), &output(n), G::ONE).unwrap();
  }
  let mut large = output(2048);
  large[3] = G::NEG_ONE;
  map.insert(&key(2048), &large, G::ZERO).unwrap();
  assert!(matches!(map.get_index(0).unwrap().0, QuerySlice::Bytes(_)));
  assert!(matches!(map.output_at(0), QuerySlice::Packed(_)));
  let mut large_key = key(2049);
  large_key[4] = G::from_u64(1 << 48);
  map.insert(&large_key, &output(2049), G::ONE).unwrap();
  assert!(matches!(map.get_index(0).unwrap().0, QuerySlice::Packed(_)));
  for n in 0..2048 {
    let index = usize::try_from(n).unwrap();
    assert_eq!(map.get_index_of(&key(n)), Some(index));
    assert_eq!(map.output_at(index).to_array::<9>(), output(n));
  }
  assert_eq!(map.get_index_of(&large_key), Some(2049));
  assert_eq!(map.output_at(2048).to_array::<9>(), large);
  let (stored_key, _) = map.get_index(2049).unwrap();
  assert!(stored_key.matches(&large_key));
  map.bump_multiplicity(2049).unwrap();
  assert_eq!(map.mult_at(2049), G::TWO);
}

#[test]
fn segment_boundary_and_late_widening_preserve_earlier_segments() {
  let mut store = PackedStore::new(1, true);
  for i in 0..SEG_ENTRIES + 3 {
    let row = [G::from_u8(u8::try_from(i % 256).unwrap())];
    let plan = store.plan(&row);
    store.push(&row, plan);
  }
  let wide = [G::from_u64(1 << 40)];
  let plan = store.plan(&wide);
  assert!(plan.transient > 0);
  store.push(&wide, plan);
  assert!(matches!(store.at(0), QuerySlice::Bytes(_)));
  assert!(matches!(store.at(SEG_ENTRIES), QuerySlice::Fields(_)));
  assert_eq!(store.at(SEG_ENTRIES - 1).at(0), G::from_u8(255));
  assert_eq!(store.at(SEG_ENTRIES + 2).at(0), G::from_u8(2));
  assert_eq!(store.at(SEG_ENTRIES + 3).at(0), wide[0]);
  assert_eq!(store.retained_bytes(), SEG_ENTRIES + 4 * 8);

  let mut late = PackedStore::new(1, true);
  for _ in 0..SEG_ENTRIES - 1 {
    let row = [G::ONE];
    let plan = late.plan(&row);
    late.push(&row, plan);
  }
  let plan = late.plan(&wide);
  assert!(plan.transient > 0);
  late.push(&wide, plan);
  assert_eq!(late.retained_bytes(), SEG_ENTRIES * 8);
  assert_eq!(late.at(0).at(0), G::ONE);
  assert_eq!(late.at(SEG_ENTRIES - 1).at(0), wide[0]);
}

#[test]
fn failed_widening_is_atomic_and_success_covers_temporary_storage() {
  let mut reference = QueryMap::new(16);
  for n in 0..4096 {
    reference.insert(&key(n), &output(n), G::ONE).unwrap();
  }
  let limit = reference.accounted_bytes() + (1 << 20);
  let budget = ExecutionBudget::new(limit, "compact".into(), None);
  let mut bounded = QueryMap::with_budget(16, Some(budget.clone()));
  for n in 0..4096 {
    bounded.insert(&key(n), &output(n), G::ONE).unwrap();
  }
  let before = budget.used();
  let mut wide_key = key(4096);
  wide_key[0] = G::NEG_ONE;
  let mut wide_out = output(4096);
  wide_out[0] = G::from_u16(256);
  assert!(bounded.insert(&wide_key, &wide_out, G::ONE).is_err());
  assert_eq!(bounded.len(), 4096);
  assert_eq!(bounded.get_index_of(&wide_key), None);
  assert!(matches!(bounded.output_at(0), QuerySlice::Bytes(_)));
  assert_eq!(rows(&bounded), rows(&reference));
  assert_eq!(budget.used(), before);
  drop(bounded);
  assert_eq!(budget.used(), 0);

  let roomy = ExecutionBudget::new(1 << 30, "wide".into(), None);
  let mut map = QueryMap::with_budget(16, Some(roomy.clone()));
  for n in 0..4096 {
    map.insert(&key(n), &output(n), G::ONE).unwrap();
  }
  map.insert(&wide_key, &wide_out, G::ONE).unwrap();
  assert_eq!(map.output_at(4096).to_array::<9>(), wide_out);
  assert_eq!(roomy.used(), map.accounted_bytes());
  assert!(
    roomy.peak() > roomy.used(),
    "both old and replacement segments were charged"
  );
  drop(map);
  assert_eq!(roomy.used(), 0);
}

#[test]
fn empty_keys_outputs_and_views_preserve_shape() {
  let mut map = QueryMap::new(0);
  map.finish(&[], &[], false).unwrap();
  map.finish(&[], &[], true).unwrap();
  assert_eq!(map.len(), 1);
  assert_eq!(map.get_index_of(&[]), Some(0));
  assert_eq!(map.output_at(0).to_array::<0>(), []);
  assert!(map.output_at(0).is_empty());
  assert_eq!(map.retained_bytes(), 0);
  assert_eq!(map.mult_at(0), G::ONE);
  let bytes = QuerySlice::Bytes(&[0, 255]);
  let fields = [G::ZERO, G::from_u8(255)];
  assert_eq!(bytes, QuerySlice::Fields(&fields));
  assert!(bytes.matches(&fields));
  assert!(!bytes.matches(&[G::ZERO, G::from_u16(511)]));
  let mut copied = [G::ONE; 2];
  bytes.copy_to_slice(&mut copied);
  assert_eq!(copied, fields);
  assert_eq!(
    bytes.iter().rev().collect::<Vec<_>>(),
    vec![fields[1], fields[0]]
  );
}

#[test]
#[ignore = "million-row storage/throughput comparison; run explicitly in release mode"]
fn million_byte_rows_storage_and_throughput() {
  for compact in [false, true] {
    let started = std::time::Instant::now();
    let mut map = QueryMap::with_storage(16, None, compact);
    for n in 0..1_000_000 {
      map.insert(&key(n), &output(n), G::ONE).unwrap();
    }
    let insert = started.elapsed();
    let read = std::time::Instant::now();
    for n in (0..1_000_000).rev() {
      let i = map.get_index_of(&key(n)).unwrap();
      assert_eq!(map.output_at(i).to_array::<9>(), output(n));
    }
    eprintln!(
      "[query-storage] compact={compact} rows={} payload={} accounted={} insert={insert:?} lookup={:?}",
      map.len(),
      map.retained_bytes(),
      map.accounted_bytes(),
      read.elapsed()
    );
  }
}

fn limb_key(n: u32) -> [G; 10] {
  let mut row = [G::ZERO; 10];
  for (out, byte) in
    row[1..9].iter_mut().zip(u64::from(n).wrapping_mul(7919).to_le_bytes())
  {
    *out = G::from_u8(byte);
  }
  row[9] = G::from_u32(n);
  row
}

#[test]
fn columns_widen_independently_at_byte_and_u32_boundaries() {
  let mut store = PackedStore::new(3, true);
  let rows = [
    [G::ONE, G::ONE, G::from_u8(255)],
    [G::ONE, G::ONE, G::from_u16(256)],
    [G::ONE, G::from_u16(256), G::from_u32(u32::MAX)],
    [G::ONE, G::from_u64(1 << 32), G::from_u32(u32::MAX)],
    [G::new(G::ORDER_U64 + 7), G::NEG_ONE, G::from_u16(256)],
  ];
  for (i, row) in rows.iter().enumerate() {
    let plan = store.plan(row);
    store.push(row, plan);
    for (j, previous) in rows[..=i].iter().enumerate() {
      assert_eq!(store.at(j).to_array::<3>(), *previous);
    }
  }
  // byte + full-field + u32, rather than widening all three columns.
  assert_eq!(store.retained_bytes(), rows.len() * 13);
  assert!(matches!(store.at(0), QuerySlice::Packed(_)));
  let mut copied = [G::ZERO; 3];
  store.at(4).copy_to_slice(&mut copied);
  assert_eq!(copied, rows[4]);
  assert_eq!(
    store.at(4).iter().rev().collect::<Vec<_>>(),
    rows[4].into_iter().rev().collect::<Vec<_>>()
  );
}

#[test]
fn mixed_keys_and_implicit_pointers_match_full_width_records() {
  let mut packed = QueryMap::with_memory_budget(10, None);
  let mut full = QueryMap::with_storage(10, None, false);
  for n in 0..65_536u32 {
    let key = limb_key(n);
    let output = [G::from_u32(n)];
    for map in [&mut packed, &mut full] {
      map.insert(&key, &output, G::ZERO).unwrap();
      let index = usize::try_from(n).unwrap();
      assert_eq!(map.get_index_of(&key), Some(index));
      assert_eq!(map.output_at(index).to_array::<1>(), output);
      map.bump_multiplicity(index).unwrap();
    }
  }
  assert_eq!(rows(&packed), rows(&full));
  assert_eq!(packed.retained_elems(), full.retained_elems());
  assert_eq!(packed.retained_bytes(), 65_536 * 13);
  assert_eq!(full.retained_bytes(), 65_536 * 88);
  assert!(packed.accounted_bytes() < full.accounted_bytes());
  assert!(matches!(packed.output_at(256), QuerySlice::Value(_)));
}

#[test]
fn implicit_pointer_invariant_is_checked_before_mutation() {
  let mut map = QueryMap::with_memory_budget(1, None);
  map.insert(&[G::from_u16(256)], &[G::ZERO], G::ZERO).unwrap();
  for bad_output in [vec![], vec![G::ZERO], vec![G::ONE, G::ONE]] {
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
      map.insert(&[G::from_u16(257)], &bad_output, G::ONE).unwrap();
    }));
    assert!(result.is_err());
    assert_eq!(map.len(), 1);
    assert_eq!(map.get_index_of(&[G::from_u16(257)]), None);
    assert_eq!(map.output_at(0).at(0), G::ZERO);
  }
  map.insert(&[G::from_u16(257)], &[G::ONE], G::ONE).unwrap();
  assert_eq!(map.output_at(1).at(0), G::ONE);
}

#[test]
fn rejected_u32_promotion_preserves_column_layout_and_accounting() {
  let mut reference = QueryMap::new(10);
  for n in 0..256u32 {
    reference.insert(&limb_key(n), &[G::from_u32(n)], G::ONE).unwrap();
  }
  let budget = ExecutionBudget::new(
    reference.accounted_bytes() + (1 << 20),
    "u32-promotion".into(),
    None,
  );
  let mut bounded = QueryMap::with_budget(10, Some(budget.clone()));
  for n in 0..256u32 {
    bounded.insert(&limb_key(n), &[G::from_u32(n)], G::ONE).unwrap();
  }
  let before = budget.used();
  assert!(bounded.insert(&limb_key(256), &[G::from_u16(256)], G::ONE).is_err());
  assert_eq!(rows(&bounded), rows(&reference));
  assert!(matches!(bounded.get_index(0).unwrap().0, QuerySlice::Bytes(_)));
  assert_eq!(budget.used(), before);
  drop(bounded);
  assert_eq!(budget.used(), 0);
}

#[test]
fn mixed_segment_boundary_preserves_finished_segment_layout() {
  let mut store = PackedStore::new(2, true);
  for _ in 0..SEG_ENTRIES {
    let row = [G::ONE, G::from_u16(256)];
    let plan = store.plan(&row);
    store.push(&row, plan);
  }
  let row = [G::ONE, G::from_u64(1 << 32)];
  let plan = store.plan(&row);
  assert_eq!(plan.transient, 0, "new segment does not copy the full one");
  store.push(&row, plan);
  assert_eq!(store.retained_bytes(), SEG_ENTRIES * 5 + 9);
  assert_eq!(store.at(SEG_ENTRIES - 1).at(1), G::from_u16(256));
  assert_eq!(store.at(SEG_ENTRIES).to_array::<2>(), row);
}

#[test]
#[ignore = "million-row mixed-key storage benchmark; run explicitly in release mode"]
fn million_mixed_memory_rows_storage_and_throughput() {
  for mode in ["full", "packed", "implicit"] {
    let mut map = match mode {
      "full" => QueryMap::with_storage(10, None, false),
      "packed" => QueryMap::new(10),
      _ => QueryMap::with_memory_budget(10, None),
    };
    let start = std::time::Instant::now();
    for n in 0..1_000_000u32 {
      map.insert(&limb_key(n), &[G::from_u32(n)], G::ONE).unwrap();
    }
    let insert = start.elapsed();
    let start = std::time::Instant::now();
    for n in (0..1_000_000u32).rev() {
      let index = map.get_index_of(&limb_key(n)).unwrap();
      assert_eq!(map.output_at(index).at(0), G::from_u32(n));
    }
    eprintln!(
      "[mixed-storage] mode={mode} rows={} payload={} accounted={} insert={insert:?} lookup={:?}",
      map.len(),
      map.retained_bytes(),
      map.accounted_bytes(),
      start.elapsed()
    );
  }
}
