//! AssocList/HashMap roundtrip FFI functions.
//!
//! Roundtrip FFI functions for AssocList, DHashMap.Raw, and HashMap
//! (ix-specific types not covered by the lean-ffi test suite).

use ix_common::prim_addrs::PrimAddrs;
use lean_ffi::nat::Nat;
use lean_ffi::object::LeanNat;
use lean_ffi::object::{
  LeanArray, LeanBorrowed, LeanIOResult, LeanOwned, LeanProd, LeanRef,
  LeanString,
};

use crate::lean::LeanAssocList;
#[cfg(feature = "test-ffi")]
use crate::lean::LeanDHashMapRaw;

/// Expose `PrimAddrs::lean_parity_table()` to Lean as `IO (Array (String × String))`.
#[unsafe(no_mangle)]
pub extern "C" fn rs_prim_addrs_canonical() -> LeanIOResult<LeanOwned> {
  let table = PrimAddrs::lean_parity_table();
  let arr = LeanArray::alloc(table.len());
  for (i, (name, hex)) in table.iter().enumerate() {
    arr.set(i, LeanProd::new(LeanString::new(name), LeanString::new(hex)));
  }
  LeanIOResult::ok(arr)
}

// =============================================================================
// AssocList / HashMap roundtrip FFI functions
// =============================================================================

/// Round-trip an AssocList Nat Nat.
/// AssocList: nil (tag 0, 0 fields) | cons key value tail (tag 1, 3 fields)
/// Note: nil with 0 fields may be represented as lean_box(0)
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_assoclist_nat_nat(
  list: LeanAssocList<LeanBorrowed<'_>>,
) -> LeanAssocList<LeanOwned> {
  if list.inner().is_scalar() {
    return LeanAssocList::new(LeanOwned::box_usize(0));
  }
  let pairs = decode_assoc_list_nat_nat(list);
  build_assoc_list_nat_nat(&pairs)
}

/// `AssocList.cons key value tail`.
#[cfg(feature = "test-ffi")]
fn cons(
  key: &Nat,
  value: &Nat,
  tail: impl Into<LeanOwned>,
) -> LeanAssocList<LeanOwned> {
  let cons = LeanAssocList::alloc(1);
  cons.set_obj(0, LeanNat::from_nat(key));
  cons.set_obj(1, LeanNat::from_nat(value));
  cons.set_obj(2, tail);
  cons
}

#[cfg(feature = "test-ffi")]
/// Build an AssocList Nat Nat from pairs
fn build_assoc_list_nat_nat(pairs: &[(Nat, Nat)]) -> LeanAssocList<LeanOwned> {
  // Build in reverse to preserve order
  let mut list = LeanAssocList::new(LeanOwned::box_usize(0)); // nil
  for (k, v) in pairs.iter().rev() {
    list = cons(k, v, list);
  }
  list
}

/// Round-trip a DHashMap.Raw Nat Nat.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_dhashmap_raw_nat_nat(
  raw: LeanDHashMapRaw<LeanBorrowed<'_>>,
) -> LeanDHashMapRaw<LeanOwned> {
  if raw.inner().is_scalar() {
    return LeanDHashMapRaw::new(raw.inner().to_owned_ref());
  }
  roundtrip_raw_nat_nat(raw)
}

/// Round-trip a Std.HashMap Nat Nat.
///
/// IMPORTANT: Single-field structures are unboxed in Lean 4!
/// - HashMap has 1 field (inner : DHashMap)
/// - DHashMap has 1 field (inner : Raw) - wf : Prop is erased
///   So HashMap pointer points DIRECTLY to Raw!
///
/// Memory layout (after unboxing):
/// - HashMap/DHashMap/Raw all share the same pointer
/// - Raw: ctor 0, 2 fields
///   - field 0: size : Nat
///   - field 1: buckets : Array (AssocList α β)
/// - AssocList:
///   - nil: lean_box(0)
///   - cons key value tail: ctor 1, 3 fields
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_hashmap_nat_nat(
  map: LeanDHashMapRaw<LeanBorrowed<'_>>,
) -> LeanDHashMapRaw<LeanOwned> {
  roundtrip_raw_nat_nat(map)
}

/// Decode a `DHashMap.Raw Nat Nat` and rebuild it with the same size and
/// bucket count, placing each key in bucket `hash & (buckets - 1)` as Lean
/// does (a `Nat` hashes to its low 64 bits).
#[cfg(feature = "test-ffi")]
fn roundtrip_raw_nat_nat(
  raw: LeanDHashMapRaw<LeanBorrowed<'_>>,
) -> LeanDHashMapRaw<LeanOwned> {
  let size = LeanNat::to_nat(&raw.get_obj(0));
  let buckets = raw.get_obj(1).as_array();

  let mut pairs: Vec<(Nat, Nat)> = Vec::new();
  for bucket in buckets.iter() {
    pairs.extend(decode_assoc_list_nat_nat(LeanAssocList(bucket)));
  }

  let num_buckets = buckets.len();
  let new_buckets = LeanArray::alloc(num_buckets);
  let nil = LeanOwned::box_usize(0);
  for i in 0..num_buckets {
    new_buckets.set(i, nil.clone());
  }

  for (k, v) in &pairs {
    let k_u64 = k.to_u64().unwrap_or_else(|| {
      let bytes = k.to_le_bytes();
      let mut arr = [0u8; 8];
      let len = bytes.len().min(8);
      arr[..len].copy_from_slice(&bytes[..len]);
      u64::from_le_bytes(arr)
    });
    #[allow(clippy::cast_possible_truncation)]
    let bucket_idx = (k_u64 as usize) & (num_buckets - 1);

    let old_bucket = new_buckets.get(bucket_idx).to_owned_ref();
    new_buckets.set(bucket_idx, cons(k, v, old_bucket));
  }

  let result = LeanDHashMapRaw::alloc(0);
  result.set_obj(0, LeanNat::from_nat(&size));
  result.set_obj(1, new_buckets);
  result
}

/// Decode a Lean AssocList Nat Nat to Vec of pairs
/// AssocList: nil (tag 0) | cons key value tail (tag 1, 3 fields)
pub fn decode_assoc_list_nat_nat(
  list: LeanAssocList<LeanBorrowed<'_>>,
) -> Vec<(Nat, Nat)> {
  let mut result = Vec::new();
  // Each tail is held as an owned reference: a borrowed field's lifetime is
  // tied to the wrapper it was read from, which is replaced every step.
  let mut current = LeanAssocList::new(list.inner().to_owned_ref());
  while !current.inner().is_scalar() && current.inner().tag() != 0 {
    result.push((
      LeanNat::to_nat(&current.get_obj(0)),
      LeanNat::to_nat(&current.get_obj(1)),
    ));
    let tail = current.get_obj(2).to_owned_ref();
    current = LeanAssocList::new(tail);
  }
  result
}
