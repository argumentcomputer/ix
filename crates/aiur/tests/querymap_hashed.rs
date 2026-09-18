use aiur::{G, querymap::QueryMap};
use multi_stark::p3_field::PrimeCharacteristicRing;

#[test]
fn retained_hash_survives_nested_insertions_and_table_growth() {
  let mut map = QueryMap::new(1);
  let key = [G::from_u32(65_535)];
  let output = [G::from_u32(42)];
  let (hash, hit) = map.lookup(&key);
  assert_eq!(hit, None);
  for i in 0..4096 {
    let child = [G::from_usize(i)];
    map.insert(&child, &child, G::ONE);
  }
  map.finish_hashed(&key, &output, true, hash);
  assert_eq!(map.len(), 4097);
  assert_eq!(map.get_index_of(&key), Some(4096));
  assert_eq!(map.output_at(4096), output);
  assert_eq!(map.mult_at(4096), G::ONE);
  for i in 0..4096 {
    assert_eq!(map.get_index_of(&[G::from_usize(i)]), Some(i));
  }
}

#[test]
fn finish_rechecks_a_key_inserted_since_the_initial_miss() {
  let mut map = QueryMap::new(1);
  let key = [G::from_u32(7)];
  let output = [G::from_u32(11)];
  let (hash, hit) = map.lookup(&key);
  assert_eq!(hit, None);
  // A nested hint populated the key before its constrained caller finished.
  map.insert(&key, &output, G::ZERO);
  map.finish_hashed(&key, &output, true, hash);
  assert_eq!(map.len(), 1);
  assert_eq!(map.mult_at(0), G::ONE);
  assert_eq!(map.output_at(0), output);
  map.finish_hashed(&key, &output, false, hash);
  assert_eq!(map.mult_at(0), G::ONE);
  map.finish_hashed(&key, &output, true, hash);
  assert_eq!(map.mult_at(0), G::TWO);
}

#[test]
fn empty_keys_and_outputs_can_be_promoted() {
  let mut map = QueryMap::new(0);
  let (hash, hit) = map.lookup(&[]);
  assert_eq!(hit, None);
  map.insert_hashed(&[], &[], G::ZERO, hash);
  assert_eq!(map.lookup(&[]), (hash, Some(0)));
  map.finish_hashed(&[], &[], true, hash);
  assert_eq!(map.len(), 1);
  assert!(map.output_at(0).is_empty());
  assert_eq!(map.mult_at(0), G::ONE);
}

#[test]
fn hashed_and_regular_registration_preserve_the_same_records() {
  let mut regular = QueryMap::new(2);
  let mut hashed = QueryMap::new(2);
  for round in 0..3 {
    for i in 0..128 {
      let key = [G::from_usize(i), G::from_usize(i + 1)];
      let output = [G::from_usize(i * 2)];
      let (hash, hit) = hashed.lookup(&key);
      assert_eq!(hit, regular.get_index_of(&key));
      regular.finish(&key, &output, round != 0);
      hashed.finish_hashed(&key, &output, round != 0, hash);
    }
  }
  assert_eq!(regular.len(), hashed.len());
  for i in 0..regular.len() {
    assert_eq!(regular.get_index(i).unwrap().0, hashed.get_index(i).unwrap().0);
    assert_eq!(regular.output_at(i), hashed.output_at(i));
    assert_eq!(regular.mult_at(i), hashed.mult_at(i));
    assert_eq!(hashed.mult_at(i), G::TWO);
  }
}
