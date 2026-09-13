use super::*;

const MODULUS: u64 = 0xffff_ffff_0000_0001;

#[test]
fn packed_queries_preserve_field_values_indices_and_multiplicities() {
  let values = [
    0,
    1,
    255,
    256,
    511,
    u64::from(u32::MAX),
    u64::from(u32::MAX) + 1,
    MODULUS - 1,
    u64::MAX,
  ];
  let mut packed = QueryMap::new(3);
  let mut full = QueryMap::with_storage(3, false);
  for (i, value) in values.into_iter().enumerate() {
    let key = [G::from_usize(i), G::from_u64(value), G::from_u8(17)];
    let output = [G::from_u64(value), G::from_usize(i)];
    for map in [&mut packed, &mut full] {
      map.insert(&key, &output, G::ZERO);
      map.finish(&key, &output, true);
      *map.get_mut(&key).unwrap().multiplicity += G::ONE;
      assert_eq!(map.get_index_of(&key), Some(i));
      assert_eq!(map.output_at(i).to_array::<2>(), output);
      let mut decoded = [G::ZERO; 2];
      map.output_at(i).copy_to_slice(&mut decoded);
      assert_eq!(decoded, output);
      assert_eq!(map.output_at(i).to_vec(), output);
      assert_eq!(map.get_index(i).unwrap().0.to_array::<3>(), key);
      assert_eq!(map.mult_at(i), G::from_u8(2));
    }
  }
  for ((pk, pv), (fk, fv)) in packed.iter().zip(full.iter()) {
    assert_eq!(pk, fk);
    assert_eq!(pv.output, fv.output);
    assert_eq!(pv.multiplicity, fv.multiplicity);
  }
  assert!(packed.retained_bytes() < full.retained_bytes());
  assert_eq!(packed.retained_elems(), full.retained_elems());
  assert_eq!(packed.get_index_of(&[G::from_u8(99); 3]), None);
}

#[test]
fn canonical_aliases_find_the_same_packed_key() {
  let mut map = QueryMap::new(1);
  map.insert(&[G::from_u8(7)], &[G::from_u8(29)], G::ONE);
  let alias = G::new(MODULUS + 7);
  assert_eq!(hash_g_slice(&[alias]), hash_g_slice(&[G::from_u8(7)]));
  assert_eq!(map.get_index_of(&[alias]), Some(0));
  map.finish(&[alias], &[G::from_u8(29)], true);
  assert_eq!(map.len(), 1);
  assert_eq!(map.mult_at(0), G::from_u8(2));
}

#[test]
fn hash_collisions_still_require_exact_packed_key_equality() {
  let mut map = QueryMap::new(2);
  let keys = [
    [G::ONE, G::from_u8(255)],
    [G::ONE, G::from_u64(256)],
    [G::ONE, G::from_u64(MODULUS - 1)],
    [G::from_u8(2), G::from_u64(MODULUS - 1)],
  ];
  // Use a forced collision through the insertion path as well as lookup.
  // Growing the table must reuse the same stored hashes and exact equality.
  for key in keys {
    map.insert_hashed(&key, &[], G::ONE, 7);
  }
  for i in 0..128 {
    map.insert_hashed(&[G::from_usize(i + 3), G::ZERO], &[], G::ONE, 7);
  }
  for i in 0..128 {
    assert_eq!(
      map.find_hashed(&[G::from_usize(i + 3), G::ZERO], 7),
      Some(i + keys.len())
    );
  }
  for (i, key) in keys.iter().enumerate() {
    assert_eq!(map.find_hashed(key, 7), Some(i));
  }
  assert_eq!(map.find_hashed(&[G::ONE, G::from_u64(257)], 7), None);
}

#[test]
fn mixed_columns_and_outputs_widen_independently() {
  let mut map = QueryMap::new(3);
  map.insert(
    &[G::ONE, G::from_u64(256), G::from_u64(MODULUS - 1)],
    &[G::from_u8(255)],
    G::ONE,
  );
  assert_eq!(map.retained_bytes(), 1 + 4 + 8 + 1);
  map.insert(
    &[G::from_u8(2), G::from_u64(511), G::from_u64(MODULUS - 1)],
    &[G::from_u64(256)],
    G::ONE,
  );
  assert_eq!(map.retained_bytes(), 2 * (1 + 4 + 8 + 4));
  assert_eq!(map.output_at(0).at(0), G::from_u8(255));
  map.insert(&[G::from_u64(256), G::ONE, G::ZERO], &[G::ONE], G::ONE);
  assert_eq!(map.retained_bytes(), 3 * (4 + 4 + 8 + 4));
  assert_eq!(
    map.get_index_of(&[G::ONE, G::from_u64(256), G::from_u64(MODULUS - 1)]),
    Some(0)
  );
}

#[test]
fn packed_storage_keeps_closed_segments_and_widens_the_active_segment() {
  let mut store = PackedStore::new(1, true);
  for i in 0..SEG_ENTRIES + 3 {
    store.push(&[G::from_usize(i % 256)]);
  }
  store.push(&[G::from_u64(256)]);
  assert_eq!(store.retained_bytes(), SEG_ENTRIES + 4 * 4);
  assert!(matches!(store.at(0), QuerySlice::Bytes(_)));
  store.push(&[G::from_u64(MODULUS - 1)]);
  assert_eq!(store.retained_bytes(), SEG_ENTRIES + 5 * 8);
  for i in [0, 255, SEG_ENTRIES - 1, SEG_ENTRIES, SEG_ENTRIES + 2] {
    assert_eq!(store.at(i).at(0), G::from_usize(i % 256));
  }
  assert_eq!(store.at(SEG_ENTRIES + 3).at(0), G::from_u64(256));
  assert_eq!(store.at(SEG_ENTRIES + 4).at(0), G::from_u64(MODULUS - 1));

  let mut boundary = PackedStore::new(1, true);
  for _ in 0..SEG_ENTRIES {
    boundary.push(&[G::from_u8(255)]);
  }
  boundary.push(&[G::from_u64(MODULUS - 1)]);
  assert_eq!(boundary.retained_bytes(), SEG_ENTRIES + 8);
  assert!(matches!(boundary.at(SEG_ENTRIES - 1), QuerySlice::Bytes(_)));
  assert_eq!(boundary.at(SEG_ENTRIES).at(0), G::from_u64(MODULUS - 1));
}

#[test]
fn empty_output_shape_is_fixed_and_has_no_payload() {
  let mut map = QueryMap::new(1);
  for i in 0..32 {
    map.insert(&[G::from_usize(i)], &[], G::ONE);
    assert!(map.output_at(i).is_empty());
  }
  assert_eq!(map.retained_bytes(), 32);
  assert!(
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
      map.insert(&[G::from_u8(32)], &[G::ONE], G::ONE);
    }))
    .is_err()
  );
  assert_eq!(map.len(), 32);
  let mut nullary = QueryMap::new(0);
  nullary.insert(&[], &[], G::ONE);
  assert_eq!(nullary.get_index_of(&[]), Some(0));
  assert_eq!(nullary.retained_bytes(), 0);
}

#[test]
fn widening_does_not_change_completion_or_hint_promotion_order() {
  let clock = Arc::new(AtomicU64::new(0));
  let mut parent = QueryMap::new_function(1, Arc::clone(&clock));
  let mut child = QueryMap::new_function(1, clock);
  parent.finish(&[G::ONE], &[G::from_u8(255)], false);
  child.finish(&[G::from_u64(MODULUS - 1)], &[G::from_u64(256)], true);
  parent.finish(&[G::from_u64(256)], &[G::from_u64(MODULUS - 1)], true);
  parent.finish(&[G::ONE], &[G::from_u8(255)], true);
  assert_eq!(parent.get(&[G::ONE]).unwrap().rank, 0);
  assert_eq!(parent.get(&[G::from_u64(256)]).unwrap().rank, 1);
  assert_eq!(child.get(&[G::from_u64(MODULUS - 1)]).unwrap().rank, 2);
  assert_eq!(parent.get_index_of(&[G::ONE]), Some(0));
  assert_eq!(parent.mult_at(0), G::ONE);
  assert_eq!(parent.output_at(0).at(0), G::from_u8(255));
}

#[test]
#[ignore = "standalone million-row query storage benchmark"]
fn query_storage_million_rows() {
  let compact = std::env::var("IX_QUERY_BENCH_COMPACT").as_deref() != Ok("0");
  let mut map = QueryMap::with_storage(12, compact);
  let start = std::time::Instant::now();
  for i in 0..1_000_000 {
    let mut key = [G::from_usize(i % 256); 12];
    key[0] = G::from_usize(i);
    map.insert(&key, &[G::from_usize(i % 256); 8], G::ONE);
  }
  let insert = start.elapsed();
  let start = std::time::Instant::now();
  let mut checksum = G::ZERO;
  for i in (0..1_000_000).rev() {
    let mut key = [G::from_usize(i % 256); 12];
    key[0] = G::from_usize(i);
    let row = map.get(&key).unwrap();
    checksum += row.output.at(7);
  }
  assert_eq!(checksum, G::from_u64(127_493_856));
  eprintln!(
    "compact={compact} rows={} payload_bytes={} insert_seconds={:.6} lookup_seconds={:.6}",
    map.len(),
    map.retained_bytes(),
    insert.as_secs_f64(),
    start.elapsed().as_secs_f64()
  );
}

#[test]
fn implicit_memory_outputs_preserve_pointers_advice_and_canonical_keys() {
  let mut memory = QueryMap::new_memory(3);
  let mut explicit = QueryMap::with_storage(3, false);
  let boundary = [255, 256, u64::from(u32::MAX) + 1, MODULUS - 1];
  for i in 0..513 {
    let key = [G::from_usize(i), G::from_u64(boundary[i % 4]), G::from_u8(7)];
    for map in [&mut memory, &mut explicit] {
      assert_eq!(map.intern_memory(&key, i % 2 == 0), G::from_usize(i));
      let alias = [key[0], key[1], G::new(MODULUS + 7)];
      assert_eq!(map.intern_memory(&alias, false), G::from_usize(i));
      assert_eq!(map.intern_memory(&alias, true), G::from_usize(i));
      assert_eq!(map.mult_at(i), G::from_usize(1 + usize::from(i % 2 == 0)));
      assert_eq!(
        map.get(&key).unwrap().output.to_array::<1>(),
        [G::from_usize(i)]
      );
      assert_eq!(map.get_mut(&key).unwrap().output.at(0), G::from_usize(i));
      assert_eq!(
        map.get_index(i).unwrap().1.output.to_vec(),
        vec![G::from_usize(i)]
      );
      assert_eq!(map.output_at(i), QuerySlice::Fields(&[G::from_usize(i)]));
      let mut decoded = [G::ZERO];
      map.output_at(i).copy_to_slice(&mut decoded);
      assert_eq!(decoded, [G::from_usize(i)]);
    }
  }
  for ((mk, mr), (ek, er)) in memory.iter().zip(explicit.iter()) {
    assert_eq!(mk, ek);
    assert_eq!(mr.output, er.output);
    assert_eq!(mr.multiplicity, er.multiplicity);
  }
  assert_eq!(memory.len(), 513);
  assert_eq!(memory.retained_elems(), explicit.retained_elems());
  assert_eq!(memory.retained_elems(), 513 * 4);
  assert_eq!(memory.retained_bytes(), memory.keys.retained_bytes());
  assert!(memory.retained_bytes() < explicit.retained_bytes());

  let bytes = memory.retained_bytes();
  for output in [vec![], vec![G::ONE], vec![G::from_usize(513), G::ZERO]] {
    assert!(
      std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        memory.insert(&[G::from_usize(513), G::ZERO, G::ZERO], &output, G::ONE);
      }))
      .is_err()
    );
    assert_eq!(memory.len(), 513);
    assert_eq!(memory.retained_bytes(), bytes);
  }
  assert!(
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
      memory.output_at(513);
    }))
    .is_err()
  );
}

#[test]
#[ignore = "standalone million-row implicit memory benchmark"]
fn memory_storage_million_rows() {
  let implicit = std::env::var("IX_QUERY_BENCH_IMPLICIT").as_deref() != Ok("0");
  let mut map =
    if implicit { QueryMap::new_memory(12) } else { QueryMap::new(12) };
  let start = std::time::Instant::now();
  for i in 0..1_000_000 {
    let mut key = [G::from_usize(i % 256); 12];
    key[0] = G::from_usize(i);
    let _ = std::hint::black_box(map.intern_memory(&key, true));
  }
  let insert = start.elapsed();
  let start = std::time::Instant::now();
  let mut checksum = G::ZERO;
  for i in (0..1_000_000).rev() {
    let mut key = [G::from_usize(i % 256); 12];
    key[0] = G::from_usize(i);
    checksum += map.intern_memory(&key, false);
  }
  assert_eq!(checksum, G::from_u64(499_999_500_000));
  eprintln!(
    "implicit={implicit} rows={} payload_bytes={} insert_seconds={:.6} lookup_seconds={:.6}",
    map.len(),
    map.retained_bytes(),
    insert.as_secs_f64(),
    start.elapsed().as_secs_f64()
  );
}

fn full_copy(map: &QueryMap) -> QueryMap {
  let mut copy = QueryMap::with_storage(map.keys.stride, false);
  for (key, row) in map.iter() {
    copy.insert(&key.to_vec(), &row.output.to_vec(), row.multiplicity);
  }
  if let Some(order) = &map.completion {
    let mut times = SegU64s::new();
    for i in 0..map.len() {
      times.push(order.times.at(i));
    }
    copy.completion =
      Some(CompletionOrder { clock: Arc::clone(&order.clock), times });
  }
  copy
}

#[test]
fn packed_and_full_records_have_identical_function_memory_and_lookup_witnesses()
{
  use crate::{
    bytecode::{Block, Circuit, Ctrl, Function, FunctionLayout, Toplevel},
    execute::{IOBuffer, QueryRecord},
    memory::Memory,
  };
  use multi_stark::lookup::LookupValues;
  let layout =
    FunctionLayout { input_size: 3, selectors: 1, auxiliaries: 7, lookups: 4 };
  let top = Toplevel {
    functions: vec![Function {
      body: Block { ops: vec![], ctrl: Ctrl::Return(0, vec![0, 1, 2]) },
      layout,
      entry: true,
      constrained: true,
    }],
    memory_sizes: vec![2],
    circuits: vec![Circuit { members: vec![0], layout }],
    call_components: vec![],
  };
  top.checked_claim_shapes().unwrap();
  top.validate_call_components().unwrap();
  top.validate_row_counts().unwrap();
  let (_, lookups) = top.build_constraints(0);
  let slot_widths: Vec<usize> =
    lookups.iter().map(|lookup| lookup.args.len()).collect();
  let mut record = QueryRecord::new(&top);
  for (i, value) in [255, 256, MODULUS - 1, u64::MAX].into_iter().enumerate() {
    let key = [G::from_usize(i), G::from_u64(value), G::from_u8(7)];
    record.function_queries[0].insert(&key, &key, G::from_bool(i > 1));
    record.memory_queries.get_mut(&2).unwrap().insert(
      &key[..2],
      &[G::from_usize(i)],
      G::ONE,
    );
  }
  // Promote a row after a later insertion has widened another column.
  let promoted = [G::ZERO, G::from_u8(255), G::from_u8(7)];
  record.function_queries[0].finish(&promoted, &promoted, true);
  let mut full = QueryRecord::new(&top);
  full.function_queries[0] = full_copy(&record.function_queries[0]);
  *full.memory_queries.get_mut(&2).unwrap() =
    full_copy(record.memory_queries.get(&2).unwrap());
  let io = IOBuffer { data: Default::default(), map: Default::default() };
  let (packed_trace, packed_lookups, packed_ranges) =
    top.witness_data(0, &record, &io, &slot_widths);
  let (full_trace, full_lookups, full_ranges) =
    top.witness_data(0, &full, &io, &slot_widths);
  assert_eq!(packed_trace.width, full_trace.width);
  assert_eq!(packed_trace.values, full_trace.values);
  assert_eq!(packed_ranges, full_ranges);
  let (packed_mem, packed_mem_lookups) = Memory::witness_data(2, &record, &[5]);
  let (full_mem, full_mem_lookups) = Memory::witness_data(2, &full, &[5]);
  assert_eq!(packed_mem.values, full_mem.values);
  let (packed_lookup_traces, packed_accumulators) =
    LookupValues::stage_2_traces(
      &[packed_lookups, packed_mem_lookups],
      &[1, 1],
      G::from_u64(123_456_789),
      &G::from_u64(987_654_321),
      G::ZERO,
    );
  let (full_lookup_traces, full_accumulators) = LookupValues::stage_2_traces(
    &[full_lookups, full_mem_lookups],
    &[1, 1],
    G::from_u64(123_456_789),
    &G::from_u64(987_654_321),
    G::ZERO,
  );
  assert_eq!(packed_accumulators, full_accumulators);
  for (packed, full) in packed_lookup_traces.iter().zip(full_lookup_traces) {
    assert_eq!(packed.width, full.width);
    assert_eq!(packed.values, full.values);
  }
}
