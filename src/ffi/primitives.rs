//! Basic Lean type encode/decode/roundtrip operations.
//!
//! This module provides FFI functions for primitive Lean types:
//! - Nat, String, Bool
//! - Option, Pair
//! - List, Array, ByteArray
//! - AssocList, HashMap

use lean_ffi::nat::Nat;
use lean_ffi::object::{
  LeanArray, LeanBool, LeanByteArray, LeanCtor, LeanList, LeanNat, LeanObject,
  LeanString,
};

// =============================================================================
// Nat Building
// =============================================================================

/// Build a Lean Nat from a Rust Nat.
pub fn build_nat(n: &Nat) -> LeanObject {
  // Try to get as u64 first
  if let Some(val) = n.to_u64() {
    // For small values that fit in a boxed scalar (max value is usize::MAX >> 1)
    if val <= (usize::MAX >> 1) as u64 {
      #[allow(clippy::cast_possible_truncation)]
      return LeanObject::box_usize(val as usize);
    }
    return LeanObject::from_nat_u64(val);
  }
  // For values larger than u64, convert to limbs and use GMP
  let bytes = n.to_le_bytes();
  let mut limbs: Vec<u64> = Vec::with_capacity(bytes.len().div_ceil(8));
  for chunk in bytes.chunks(8) {
    let mut arr = [0u8; 8];
    arr[..chunk.len()].copy_from_slice(chunk);
    limbs.push(u64::from_le_bytes(arr));
  }
  unsafe { lean_ffi::nat::lean_nat_from_limbs(limbs.len(), limbs.as_ptr()) }
}

// =============================================================================
// Round-trip FFI Functions for Testing
// =============================================================================

/// Round-trip a Nat: decode from Lean, re-encode to Lean.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_nat(nat_ptr: LeanNat) -> LeanObject {
  let nat = Nat::from_obj(*nat_ptr);
  build_nat(&nat)
}

/// Round-trip a String: decode from Lean, re-encode to Lean.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_string(s_ptr: LeanString) -> LeanString {
  let s = s_ptr.to_string();
  LeanString::new(&s)
}

/// Round-trip a List Nat: decode from Lean, re-encode to Lean.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_list_nat(list_ptr: LeanList) -> LeanList {
  let nats: Vec<Nat> = list_ptr.collect(Nat::from_obj);
  build_list_nat(&nats)
}

/// Round-trip an Array Nat: decode from Lean, re-encode to Lean.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_array_nat(arr_ptr: LeanArray) -> LeanArray {
  let nats: Vec<Nat> = arr_ptr.map(Nat::from_obj);
  build_array_nat(&nats)
}

/// Round-trip a ByteArray: decode from Lean, re-encode to Lean.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_bytearray(ba: LeanByteArray) -> LeanByteArray {
  LeanByteArray::from_bytes(ba.as_bytes())
}

/// Round-trip a Bool: decode from Lean, re-encode.
/// Bool in Lean is passed as unboxed scalar: false = 0, true = 1
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_bool(bool_ptr: LeanBool) -> LeanBool {
  bool_ptr
}

// =============================================================================
// Helper functions for building basic Lean types
// =============================================================================

/// Build a Lean List Nat from a Vec<Nat>.
fn build_list_nat(nats: &[Nat]) -> LeanList {
  let items: Vec<LeanObject> = nats.iter().map(build_nat).collect();
  items.into_iter().collect()
}

/// Build a Lean Array Nat from a Vec<Nat>.
fn build_array_nat(nats: &[Nat]) -> LeanArray {
  let arr = LeanArray::alloc(nats.len());
  for (i, nat) in nats.iter().enumerate() {
    arr.set(i, build_nat(nat));
  }
  arr
}

// =============================================================================
// FFI roundtrip functions for struct/inductive/HashMap
// =============================================================================

/// Round-trip a Point (structure with x, y : Nat).
/// Point is a structure, which in Lean is represented as a constructor with tag 0.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_point(point_ptr: LeanCtor) -> LeanObject {
  // Point is a structure (single constructor, tag 0) with 2 Nat fields
  let x = Nat::from_obj(point_ptr.get(0));
  let y = Nat::from_obj(point_ptr.get(1));

  // Re-encode as Point
  let point = LeanCtor::alloc(0, 2, 0);
  point.set(0, build_nat(&x));
  point.set(1, build_nat(&y));
  *point
}

/// Round-trip a NatTree (inductive with leaf : Nat → NatTree | node : NatTree → NatTree → NatTree).
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_nat_tree(tree_ptr: LeanCtor) -> LeanObject {
  roundtrip_nat_tree_recursive(tree_ptr)
}

fn roundtrip_nat_tree_recursive(ctor: LeanCtor) -> LeanObject {
  match ctor.tag() {
    0 => {
      // leaf : Nat → NatTree
      let nat = Nat::from_obj(ctor.get(0));
      let leaf = LeanCtor::alloc(0, 1, 0);
      leaf.set(0, build_nat(&nat));
      *leaf
    },
    1 => {
      // node : NatTree → NatTree → NatTree
      let left = roundtrip_nat_tree_recursive(ctor.get(0).as_ctor());
      let right = roundtrip_nat_tree_recursive(ctor.get(1).as_ctor());
      let node = LeanCtor::alloc(1, 2, 0);
      node.set(0, left);
      node.set(1, right);
      *node
    },
    _ => panic!("Invalid NatTree tag: {}", ctor.tag()),
  }
}

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
    cons.set(0, build_nat(k));
    cons.set(1, build_nat(v));
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
    new_bucket.set(0, build_nat(k));
    new_bucket.set(1, build_nat(v));
    new_bucket.set(2, old_bucket);
    new_buckets.set(bucket_idx, *new_bucket);
  }

  // Build Raw
  let raw = LeanCtor::alloc(0, 2, 0);
  raw.set(0, build_nat(&size));
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
    new_bucket.set(0, build_nat(k));
    new_bucket.set(1, build_nat(v));
    new_bucket.set(2, old_bucket);
    new_buckets.set(bucket_idx, *new_bucket);
  }

  // Build Raw (ctor 0, 2 fields: size, buckets)
  // Due to unboxing, this IS the HashMap
  let raw = LeanCtor::alloc(0, 2, 0);
  raw.set(0, build_nat(&size));
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

// =============================================================================
// Utility FFI Functions
// =============================================================================

/// Read first 8 bytes of a ByteArray as little-endian UInt64.
/// Used by Address.Hashable to match Rust's bucket hash computation.
/// This is essentially just a pointer cast - very fast.
#[unsafe(no_mangle)]
pub extern "C" fn rs_bytearray_to_u64_le(ba: LeanByteArray) -> u64 {
  let data = ba.as_bytes();
  if data.len() < 8 {
    return 0;
  }
  u64::from_le_bytes(data[..8].try_into().unwrap())
}
