//! Basic Lean type encode/decode/roundtrip operations.
//!
//! This module provides FFI functions for primitive Lean types:
//! - Nat, String, Bool
//! - Option, Pair
//! - List, Array, ByteArray
//! - AssocList, HashMap

use std::ffi::c_void;

use crate::lean::array::LeanArrayObject;
use crate::lean::nat::Nat;
use crate::lean::sarray::LeanSArrayObject;
use crate::lean::string::LeanStringObject;
use crate::lean::{
  as_ref_unsafe, lean_alloc_array, lean_alloc_ctor, lean_alloc_sarray,
  lean_array_get_core, lean_array_set_core, lean_box_fn, lean_ctor_get,
  lean_ctor_set, lean_is_scalar, lean_mk_string, lean_obj_tag,
  lean_sarray_cptr, lean_uint64_to_nat,
};

// =============================================================================
// Nat Building
// =============================================================================

/// Build a Lean Nat from a Rust Nat.
pub fn build_nat(n: &Nat) -> *mut c_void {
  // Try to get as u64 first
  if let Some(val) = n.to_u64() {
    // For small values that fit in a boxed scalar (max value is usize::MAX >> 1)
    if val <= (usize::MAX >> 1) as u64 {
      #[allow(clippy::cast_possible_truncation)]
      return lean_box_fn(val as usize);
    }
    // For larger u64 values, use lean_uint64_to_nat
    return unsafe { lean_uint64_to_nat(val) };
  }
  // For values larger than u64, convert to limbs and use GMP
  let bytes = n.to_le_bytes();
  let mut limbs: Vec<u64> = Vec::with_capacity(bytes.len().div_ceil(8));
  for chunk in bytes.chunks(8) {
    let mut arr = [0u8; 8];
    arr[..chunk.len()].copy_from_slice(chunk);
    limbs.push(u64::from_le_bytes(arr));
  }
  unsafe { crate::lean::lean_nat_from_limbs(limbs.len(), limbs.as_ptr()) }
}

// =============================================================================
// Round-trip FFI Functions for Testing
// =============================================================================

/// Round-trip a Nat: decode from Lean, re-encode to Lean.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_nat(nat_ptr: *const c_void) -> *mut c_void {
  // Decode
  let nat = Nat::from_ptr(nat_ptr);
  // Re-encode
  build_nat(&nat)
}

/// Round-trip a String: decode from Lean, re-encode to Lean.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_string(s_ptr: *const c_void) -> *mut c_void {
  // Decode
  let s_obj: &LeanStringObject = as_ref_unsafe(s_ptr.cast());
  let s = s_obj.as_string();
  // Re-encode
  unsafe {
    let cstr = crate::lean::safe_cstring(s.as_str());
    lean_mk_string(cstr.as_ptr())
  }
}

/// Round-trip a List Nat: decode from Lean, re-encode to Lean.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_list_nat(
  list_ptr: *const c_void,
) -> *mut c_void {
  // Decode list to Vec<Nat>
  let nats: Vec<Nat> = crate::lean::collect_list(list_ptr, Nat::from_ptr);
  // Re-encode as Lean List
  build_list_nat(&nats)
}

/// Round-trip an Array Nat: decode from Lean, re-encode to Lean.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_array_nat(
  arr_ptr: *const c_void,
) -> *mut c_void {
  // Decode array
  let arr_obj: &LeanArrayObject = as_ref_unsafe(arr_ptr.cast());
  let nats: Vec<Nat> =
    arr_obj.data().iter().map(|&p| Nat::from_ptr(p)).collect();
  // Re-encode as Lean Array
  build_array_nat(&nats)
}

/// Round-trip a ByteArray: decode from Lean, re-encode to Lean.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_bytearray(ba_ptr: *const c_void) -> *mut c_void {
  // Decode ByteArray (scalar array of u8)
  let sarray: &LeanSArrayObject = as_ref_unsafe(ba_ptr.cast());
  let bytes = sarray.data();
  // Re-encode
  unsafe {
    let ba = lean_alloc_sarray(1, bytes.len(), bytes.len());
    let data_ptr = lean_sarray_cptr(ba);
    std::ptr::copy_nonoverlapping(bytes.as_ptr(), data_ptr, bytes.len());
    ba
  }
}

/// Round-trip a Bool: decode from Lean, re-encode.
/// Bool in Lean is passed as unboxed scalar: false = 0, true = 1
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_bool(bool_ptr: *const c_void) -> *mut c_void {
  // Bool is passed as unboxed scalar - just return it as-is
  bool_ptr as *mut c_void
}

// =============================================================================
// Helper functions for building basic Lean types
// =============================================================================

/// Build a Lean List Nat from a Vec<Nat>.
fn build_list_nat(nats: &[Nat]) -> *mut c_void {
  unsafe {
    // Build list in reverse (cons builds from the end)
    let mut list = lean_box_fn(0); // nil
    for nat in nats.iter().rev() {
      let nat_obj = build_nat(nat);
      // cons : α → List α → List α (tag 1, 2 object fields)
      let cons = lean_alloc_ctor(1, 2, 0);
      lean_ctor_set(cons, 0, nat_obj);
      lean_ctor_set(cons, 1, list);
      list = cons;
    }
    list
  }
}

/// Build a Lean Array Nat from a Vec<Nat>.
fn build_array_nat(nats: &[Nat]) -> *mut c_void {
  unsafe {
    let arr = lean_alloc_array(nats.len(), nats.len());
    for (i, nat) in nats.iter().enumerate() {
      let nat_obj = build_nat(nat);
      lean_array_set_core(arr, i, nat_obj);
    }
    arr
  }
}

// =============================================================================
// FFI roundtrip functions for struct/inductive/HashMap
// =============================================================================

/// Round-trip a Point (structure with x, y : Nat).
/// Point is a structure, which in Lean is represented as a constructor with tag 0.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_point(point_ptr: *const c_void) -> *mut c_void {
  unsafe {
    // Point is a structure (single constructor, tag 0) with 2 Nat fields
    let x_ptr = lean_ctor_get(point_ptr as *mut _, 0);
    let y_ptr = lean_ctor_get(point_ptr as *mut _, 1);

    // Decode the Nats
    let x = Nat::from_ptr(x_ptr);
    let y = Nat::from_ptr(y_ptr);

    // Re-encode as Point
    let point = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(point, 0, build_nat(&x));
    lean_ctor_set(point, 1, build_nat(&y));
    point
  }
}

/// Round-trip a NatTree (inductive with leaf : Nat → NatTree | node : NatTree → NatTree → NatTree).
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_nat_tree(
  tree_ptr: *const c_void,
) -> *mut c_void {
  roundtrip_nat_tree_recursive(tree_ptr)
}

fn roundtrip_nat_tree_recursive(tree_ptr: *const c_void) -> *mut c_void {
  unsafe {
    let tag = lean_obj_tag(tree_ptr as *mut _);
    match tag {
      0 => {
        // leaf : Nat → NatTree
        let nat_ptr = lean_ctor_get(tree_ptr as *mut _, 0);
        let nat = Nat::from_ptr(nat_ptr);
        let leaf = lean_alloc_ctor(0, 1, 0);
        lean_ctor_set(leaf, 0, build_nat(&nat));
        leaf
      },
      1 => {
        // node : NatTree → NatTree → NatTree
        let left_ptr = lean_ctor_get(tree_ptr as *mut _, 0);
        let right_ptr = lean_ctor_get(tree_ptr as *mut _, 1);
        let left = roundtrip_nat_tree_recursive(left_ptr);
        let right = roundtrip_nat_tree_recursive(right_ptr);
        let node = lean_alloc_ctor(1, 2, 0);
        lean_ctor_set(node, 0, left);
        lean_ctor_set(node, 1, right);
        node
      },
      _ => panic!("Invalid NatTree tag: {}", tag),
    }
  }
}

/// Round-trip an AssocList Nat Nat.
/// AssocList: nil (tag 0, 0 fields) | cons key value tail (tag 1, 3 fields)
/// Note: nil with 0 fields may be represented as lean_box(0)
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_assoclist_nat_nat(
  list_ptr: *const c_void,
) -> *mut c_void {
  // Check if it's a scalar (nil represented as lean_box(0))
  if lean_is_scalar(list_ptr) {
    // Return lean_box(0) for nil
    return lean_box_fn(0);
  }
  let pairs = decode_assoc_list_nat_nat(list_ptr);
  build_assoc_list_nat_nat(&pairs)
}

/// Build an AssocList Nat Nat from pairs
fn build_assoc_list_nat_nat(pairs: &[(Nat, Nat)]) -> *mut c_void {
  unsafe {
    // Build in reverse to preserve order
    // AssocList.nil with 0 fields is represented as lean_box(0)
    let mut list = lean_box_fn(0);
    for (k, v) in pairs.iter().rev() {
      let cons = lean_alloc_ctor(1, 3, 0); // AssocList.cons
      lean_ctor_set(cons, 0, build_nat(k));
      lean_ctor_set(cons, 1, build_nat(v));
      lean_ctor_set(cons, 2, list);
      list = cons;
    }
    list
  }
}

/// Round-trip a DHashMap.Raw Nat Nat.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_dhashmap_raw_nat_nat(
  raw_ptr: *const c_void,
) -> *mut c_void {
  unsafe {
    if lean_is_scalar(raw_ptr) {
      return raw_ptr as *mut c_void;
    }

    let size_ptr = lean_ctor_get(raw_ptr as *mut _, 0);
    let buckets_ptr = lean_ctor_get(raw_ptr as *mut _, 1);

    let size = Nat::from_ptr(size_ptr);

    // Decode and rebuild buckets
    let buckets_obj: &LeanArrayObject = as_ref_unsafe(buckets_ptr.cast());
    let num_buckets = buckets_obj.data().len();

    let mut all_pairs: Vec<(Nat, Nat)> = Vec::new();
    for &bucket_ptr in buckets_obj.data() {
      let pairs = decode_assoc_list_nat_nat(bucket_ptr);
      all_pairs.extend(pairs);
    }

    // Rebuild buckets
    let new_buckets = lean_alloc_array(num_buckets, num_buckets);
    for i in 0..num_buckets {
      lean_array_set_core(new_buckets, i, lean_box_fn(0)); // AssocList.nil
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

      let old_bucket =
        lean_array_get_core(new_buckets, bucket_idx) as *mut c_void;
      let new_bucket = lean_alloc_ctor(1, 3, 0);
      lean_ctor_set(new_bucket, 0, build_nat(k));
      lean_ctor_set(new_bucket, 1, build_nat(v));
      lean_ctor_set(new_bucket, 2, old_bucket);
      lean_array_set_core(new_buckets, bucket_idx, new_bucket);
    }

    // Build Raw
    let raw = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(raw, 0, build_nat(&size));
    lean_ctor_set(raw, 1, new_buckets);

    raw
  }
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
  map_ptr: *const c_void,
) -> *mut c_void {
  unsafe {
    // Due to unboxing, map_ptr points directly to Raw
    let size_ptr = lean_ctor_get(map_ptr as *mut _, 0);
    let buckets_ptr = lean_ctor_get(map_ptr as *mut _, 1);

    let size = Nat::from_ptr(size_ptr);

    // Decode buckets (Array of AssocLists)
    let buckets_obj: &LeanArrayObject = as_ref_unsafe(buckets_ptr.cast());
    let mut pairs: Vec<(Nat, Nat)> = Vec::new();

    for &bucket_ptr in buckets_obj.data() {
      // Each bucket is an AssocList
      let bucket_pairs = decode_assoc_list_nat_nat(bucket_ptr);
      pairs.extend(bucket_pairs);
    }

    // Rebuild the HashMap with the same bucket count
    let num_buckets = buckets_obj.data().len();
    let new_buckets = lean_alloc_array(num_buckets, num_buckets);

    // Initialize all buckets to AssocList.nil (lean_box(0))
    for i in 0..num_buckets {
      lean_array_set_core(new_buckets, i, lean_box_fn(0)); // AssocList.nil
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
      let old_bucket =
        lean_array_get_core(new_buckets, bucket_idx) as *mut c_void;

      // Build AssocList.cons key value tail (tag 1, 3 fields)
      let new_bucket = lean_alloc_ctor(1, 3, 0);
      lean_ctor_set(new_bucket, 0, build_nat(k));
      lean_ctor_set(new_bucket, 1, build_nat(v));
      lean_ctor_set(new_bucket, 2, old_bucket);

      lean_array_set_core(new_buckets, bucket_idx, new_bucket);
    }

    // Build Raw (ctor 0, 2 fields: size, buckets)
    // Due to unboxing, this IS the HashMap
    let raw = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(raw, 0, build_nat(&size));
    lean_ctor_set(raw, 1, new_buckets);

    raw
  }
}

/// Decode a Lean AssocList Nat Nat to Vec of pairs
/// AssocList: nil (tag 0) | cons key value tail (tag 1, 3 fields)
pub fn decode_assoc_list_nat_nat(list_ptr: *const c_void) -> Vec<(Nat, Nat)> {
  let mut result = Vec::new();
  let mut current = list_ptr;

  loop {
    unsafe {
      // Check if scalar (shouldn't happen) or object
      if lean_is_scalar(current) {
        break;
      }

      let tag = lean_obj_tag(current as *mut _);
      if tag == 0 {
        // AssocList.nil
        break;
      }

      // AssocList.cons: 3 fields (key, value, tail)
      let key_ptr = lean_ctor_get(current as *mut _, 0);
      let value_ptr = lean_ctor_get(current as *mut _, 1);
      let tail_ptr = lean_ctor_get(current as *mut _, 2);

      let k = Nat::from_ptr(key_ptr);
      let v = Nat::from_ptr(value_ptr);

      result.push((k, v));
      current = tail_ptr;
    }
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
pub extern "C" fn rs_bytearray_to_u64_le(ba_ptr: *const c_void) -> u64 {
  unsafe {
    let arr: &LeanSArrayObject = &*(ba_ptr as *const LeanSArrayObject);
    if arr.data().len() < 8 {
      return 0;
    }
    let data_ptr = lean_sarray_cptr(ba_ptr as *mut _);
    std::ptr::read_unaligned(data_ptr as *const u64)
  }
}
