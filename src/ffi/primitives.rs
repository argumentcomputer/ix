//! AssocList/HashMap roundtrip FFI functions.
//!
//! Roundtrip FFI functions for AssocList, DHashMap.Raw, and HashMap
//! (ix-specific types not covered by the lean-ffi test suite).

use lean_ffi::nat::Nat;
use lean_ffi::object::{LeanArray, LeanCtor, LeanObject};

// =============================================================================
// AssocList / HashMap roundtrip FFI functions
// =============================================================================

/// Round-trip an AssocList Nat Nat.
/// AssocList: nil (tag 0, 0 fields) | cons key value tail (tag 1, 3 fields)
/// Note: nil with 0 fields may be represented as lean_box(0)
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_assoclist_nat_nat(
  list_ptr: LeanObject,
) -> LeanObject {
  if list_ptr.is_scalar() {
    return LeanObject::box_usize(0);
  }
  let pairs = decode_assoc_list_nat_nat(list_ptr);
  build_assoc_list_nat_nat(&pairs)
}

/// Build an AssocList Nat Nat from pairs
fn build_assoc_list_nat_nat(pairs: &[(Nat, Nat)]) -> LeanObject {
  // Build in reverse to preserve order
  let mut list = LeanObject::box_usize(0); // nil
  for (k, v) in pairs.iter().rev() {
    let cons = LeanCtor::alloc(1, 3, 0); // AssocList.cons
    cons.set(0, Nat::to_lean(k));
    cons.set(1, Nat::to_lean(v));
    cons.set(2, list);
    list = *cons;
  }
  list
}

/// Round-trip a DHashMap.Raw Nat Nat.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_dhashmap_raw_nat_nat(
  raw_ptr: LeanObject,
) -> LeanObject {
  if raw_ptr.is_scalar() {
    return raw_ptr;
  }

  let raw_ctor = raw_ptr.as_ctor();
  let size = Nat::from_obj(raw_ctor.get(0));
  let buckets = raw_ctor.get(1).as_array();

  // Decode and rebuild buckets
  let num_buckets = buckets.len();

  let mut all_pairs: Vec<(Nat, Nat)> = Vec::new();
  for bucket in buckets.iter() {
    let pairs = decode_assoc_list_nat_nat(bucket);
    all_pairs.extend(pairs);
  }

  // Rebuild buckets
  let new_buckets = LeanArray::alloc(num_buckets);
  let nil = LeanObject::box_usize(0);
  for i in 0..num_buckets {
    new_buckets.set(i, nil);
  }

  for (k, v) in &all_pairs {
    let k_u64 = k.to_u64().unwrap_or_else(|| {
      let bytes = k.to_le_bytes();
      let mut arr = [0u8; 8];
      let len = bytes.len().min(8);
      arr[..len].copy_from_slice(&bytes[..len]);
      u64::from_le_bytes(arr)
    });
    #[allow(clippy::cast_possible_truncation)]
    let bucket_idx = (k_u64 as usize) & (num_buckets - 1);

    let old_bucket = new_buckets.get(bucket_idx);
    let new_bucket = LeanCtor::alloc(1, 3, 0);
    new_bucket.set(0, Nat::to_lean(k));
    new_bucket.set(1, Nat::to_lean(v));
    new_bucket.set(2, old_bucket);
    new_buckets.set(bucket_idx, *new_bucket);
  }

  // Build Raw
  let raw = LeanCtor::alloc(0, 2, 0);
  raw.set(0, Nat::to_lean(&size));
  raw.set(1, *new_buckets);
  *raw
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
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_hashmap_nat_nat(
  map_ptr: LeanCtor,
) -> LeanObject {
  // Due to unboxing, map_ptr points directly to Raw
  let size = Nat::from_obj(map_ptr.get(0));
  let buckets = map_ptr.get(1).as_array();

  // Decode buckets (Array of AssocLists)
  let mut pairs: Vec<(Nat, Nat)> = Vec::new();

  for bucket in buckets.iter() {
    let bucket_pairs = decode_assoc_list_nat_nat(bucket);
    pairs.extend(bucket_pairs);
  }

  // Rebuild the HashMap with the same bucket count
  let num_buckets = buckets.len();
  let new_buckets = LeanArray::alloc(num_buckets);

  // Initialize all buckets to AssocList.nil (lean_box(0))
  let nil = LeanObject::box_usize(0);
  for i in 0..num_buckets {
    new_buckets.set(i, nil);
  }

  // Insert each pair into the appropriate bucket using Lean's hash function
  for (k, v) in &pairs {
    // Hash the key - for Nat, Lean uses the value itself as hash
    let k_u64 = k.to_u64().unwrap_or_else(|| {
      // For large nats, use low 64 bits
      let bytes = k.to_le_bytes();
      let mut arr = [0u8; 8];
      let len = bytes.len().min(8);
      arr[..len].copy_from_slice(&bytes[..len]);
      u64::from_le_bytes(arr)
    });
    // Lean uses (hash & (buckets.size - 1)) for bucket index (power of 2)
    #[allow(clippy::cast_possible_truncation)]
    let bucket_idx = (k_u64 as usize) & (num_buckets - 1);

    // Get current bucket AssocList
    let old_bucket = new_buckets.get(bucket_idx);

    // Build AssocList.cons key value tail (tag 1, 3 fields)
    let new_bucket = LeanCtor::alloc(1, 3, 0);
    new_bucket.set(0, Nat::to_lean(k));
    new_bucket.set(1, Nat::to_lean(v));
    new_bucket.set(2, old_bucket);
    new_buckets.set(bucket_idx, *new_bucket);
  }

  // Build Raw (ctor 0, 2 fields: size, buckets)
  // Due to unboxing, this IS the HashMap
  let raw = LeanCtor::alloc(0, 2, 0);
  raw.set(0, Nat::to_lean(&size));
  raw.set(1, *new_buckets);
  *raw
}

/// Decode a Lean AssocList Nat Nat to Vec of pairs
/// AssocList: nil (tag 0) | cons key value tail (tag 1, 3 fields)
pub fn decode_assoc_list_nat_nat(obj: LeanObject) -> Vec<(Nat, Nat)> {
  let mut result = Vec::new();
  let mut current = obj;

  loop {
    if current.is_scalar() {
      break;
    }

    let ctor = current.as_ctor();
    if ctor.tag() == 0 {
      break;
    }

    let k = Nat::from_obj(ctor.get(0));
    let v = Nat::from_obj(ctor.get(1));

    result.push((k, v));
    current = ctor.get(2);
  }

  result
}
