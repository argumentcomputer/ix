//! Ix.Environment build/decode/roundtrip FFI.

use std::ffi::c_void;

use rustc_hash::FxHashMap;

use crate::ix::env::{ConstantInfo, Name};
use crate::lean::array::LeanArrayObject;
use crate::lean::{
  as_ref_unsafe, lean_alloc_array, lean_alloc_ctor, lean_array_set_core, lean_box_fn,
  lean_ctor_get, lean_ctor_set, lean_is_scalar, lean_obj_tag,
};

use super::super::builder::LeanBuildCache;
use super::constant::{build_constant_info, decode_constant_info};
use super::name::{build_name, decode_ix_name};

// =============================================================================
// HashMap Building
// =============================================================================

/// Build a Lean HashMap from pre-built key-value pairs.
///
/// Lean's Std.HashMap structure (with unboxing):
/// - HashMap α β unboxes through DHashMap to Raw
/// - Raw = { size : Nat, buckets : Array (AssocList α β) }
/// - Field 0 = size (Nat), Field 1 = buckets (Array)
///
/// AssocList α β = nil | cons (key : α) (value : β) (tail : AssocList α β)
pub fn build_hashmap_from_pairs(
  pairs: Vec<(*mut c_void, *mut c_void, u64)>, // (key_obj, val_obj, hash)
) -> *mut c_void {
  let size = pairs.len();
  let bucket_count = (size * 4 / 3 + 1).next_power_of_two().max(8);

  unsafe {
    // Create array of AssocLists (initially all nil = boxed 0)
    let buckets = lean_alloc_array(bucket_count, bucket_count);
    for i in 0..bucket_count {
      lean_array_set_core(buckets, i, lean_box_fn(0)); // nil
    }

    // Insert entries
    for (key_obj, val_obj, hash) in pairs {
      let bucket_idx = usize::try_from(hash).expect("hash overflows usize") % bucket_count;

      // Get current bucket (AssocList)
      let buckets_arr = buckets.cast::<LeanArrayObject>();
      let current_tail = (*buckets_arr).data()[bucket_idx];

      // cons (key : α) (value : β) (tail : AssocList α β) -- tag 1
      let cons = lean_alloc_ctor(1, 3, 0);
      lean_ctor_set(cons, 0, key_obj);
      lean_ctor_set(cons, 1, val_obj);
      lean_ctor_set(cons, 2, current_tail as *mut c_void);

      lean_array_set_core(buckets, bucket_idx, cons);
    }

    // Build Raw { size : Nat, buckets : Array }
    // Due to unboxing, this IS the HashMap directly
    // Field 0 = size, Field 1 = buckets (2 object fields, no scalars)
    let size_obj = if size <= (usize::MAX >> 1) {
      lean_box_fn(size)
    } else {
      crate::lean::lean_uint64_to_nat(size as u64)
    };

    let raw = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(raw, 0, size_obj);
    lean_ctor_set(raw, 1, buckets);
    raw
  }
}

// =============================================================================
// Environment Building
// =============================================================================

/// Build a Ix.RawEnvironment from collected caches.
/// RawEnvironment has arrays that Lean will convert to HashMaps.
///
/// Ix.RawEnvironment = {
///   consts : Array (Name × ConstantInfo)
/// }
///
/// NOTE: RawEnvironment with a single field is UNBOXED by Lean,
/// so we return just the array, not a structure containing it.
pub fn build_raw_environment(cache: &mut LeanBuildCache, consts: &FxHashMap<Name, ConstantInfo>) -> *mut c_void {
  unsafe {
    // Build consts array: Array (Name × ConstantInfo)
    // RawEnvironment is a single-field structure that may be unboxed to just the array
    let consts_arr = lean_alloc_array(consts.len(), consts.len());
    for (i, (name, info)) in consts.iter().enumerate() {
      let key_obj = build_name(cache, name);
      let val_obj = build_constant_info(cache, info);
      // Build pair (Name × ConstantInfo)
      let pair = lean_alloc_ctor(0, 2, 0);
      lean_ctor_set(pair, 0, key_obj);
      lean_ctor_set(pair, 1, val_obj);
      lean_array_set_core(consts_arr, i, pair);
    }

    consts_arr
  }
}

// =============================================================================
// Environment Decoder
// =============================================================================

/// Decode a HashMap's AssocList and collect key-value pairs using a custom decoder.
fn decode_assoc_list<K, V, FK, FV>(
  list_ptr: *const c_void,
  decode_key: FK,
  decode_val: FV,
) -> Vec<(K, V)>
where
  FK: Fn(*const c_void) -> K,
  FV: Fn(*const c_void) -> V,
{
  let mut result = Vec::new();
  let mut current = list_ptr;

  loop {
    unsafe {
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

      result.push((decode_key(key_ptr), decode_val(value_ptr)));
      current = tail_ptr;
    }
  }

  result
}

/// Decode a Lean HashMap into a Vec of key-value pairs.
/// HashMap structure (after unboxing): Raw { size : Nat, buckets : Array (AssocList α β) }
///
/// Due to single-field struct unboxing:
/// - HashMap { inner : DHashMap } unboxes to DHashMap
/// - DHashMap { inner : Raw, wf : Prop } unboxes to Raw (Prop is erased)
/// - Raw { size : Nat, buckets : Array } - field 0 = size, field 1 = buckets
fn decode_hashmap<K, V, FK, FV>(
  map_ptr: *const c_void,
  decode_key: FK,
  decode_val: FV,
) -> Vec<(K, V)>
where
  FK: Fn(*const c_void) -> K + Copy,
  FV: Fn(*const c_void) -> V + Copy,
{
  unsafe {
    // Raw layout: field 0 = size (Nat), field 1 = buckets (Array)
    let _size_ptr = lean_ctor_get(map_ptr as *mut _, 0); // unused but needed for layout
    let buckets_ptr = lean_ctor_get(map_ptr as *mut _, 1);

    let buckets_obj: &LeanArrayObject = as_ref_unsafe(buckets_ptr.cast());

    let mut pairs = Vec::new();
    for &bucket_ptr in buckets_obj.data() {
      let bucket_pairs = decode_assoc_list(bucket_ptr, decode_key, decode_val);
      pairs.extend(bucket_pairs);
    }

    pairs
  }
}

/// Decode Ix.Environment from Lean pointer.
///
/// Ix.Environment = {
///   consts : HashMap Name ConstantInfo
/// }
///
/// NOTE: Environment with a single field is UNBOXED by Lean,
/// so the pointer IS the HashMap directly, not a structure containing it.
pub fn decode_ix_environment(ptr: *const c_void) -> FxHashMap<Name, ConstantInfo> {
  // Environment is unboxed - ptr IS the HashMap directly
  let consts_pairs = decode_hashmap(ptr, decode_ix_name, decode_constant_info);
  let mut consts: FxHashMap<Name, ConstantInfo> = FxHashMap::default();
  for (name, info) in consts_pairs {
    consts.insert(name, info);
  }
  consts
}

/// Decode Ix.RawEnvironment from Lean pointer into HashMap.
/// RawEnvironment = { consts : Array (Name × ConstantInfo) }
/// NOTE: Unboxed to just Array. This version deduplicates by name.
pub fn decode_ix_raw_environment(ptr: *const c_void) -> FxHashMap<Name, ConstantInfo> {
  unsafe {
    // RawEnvironment is a single-field structure that may be unboxed
    // Try treating ptr as the array directly first
    let arr_obj: &LeanArrayObject = as_ref_unsafe(ptr.cast());
    let mut consts: FxHashMap<Name, ConstantInfo> = FxHashMap::default();

    for &pair_ptr in arr_obj.data() {
      let name_ptr = lean_ctor_get(pair_ptr as *mut _, 0);
      let info_ptr = lean_ctor_get(pair_ptr as *mut _, 1);
      let name = decode_ix_name(name_ptr);
      let info = decode_constant_info(info_ptr);
      consts.insert(name, info);
    }

    consts
  }
}

/// Decode Ix.RawEnvironment from Lean pointer preserving array structure.
/// This version preserves all entries including duplicates.
pub fn decode_ix_raw_environment_vec(ptr: *const c_void) -> Vec<(Name, ConstantInfo)> {
  unsafe {
    let arr_obj: &LeanArrayObject = as_ref_unsafe(ptr.cast());
    let mut consts = Vec::with_capacity(arr_obj.data().len());

    for &pair_ptr in arr_obj.data() {
      let name_ptr = lean_ctor_get(pair_ptr as *mut _, 0);
      let info_ptr = lean_ctor_get(pair_ptr as *mut _, 1);
      let name = decode_ix_name(name_ptr);
      let info = decode_constant_info(info_ptr);
      consts.push((name, info));
    }

    consts
  }
}

/// Build Ix.RawEnvironment from Vec, preserving order and duplicates.
pub fn build_raw_environment_from_vec(cache: &mut LeanBuildCache, consts: &[(Name, ConstantInfo)]) -> *mut c_void {
  unsafe {
    let consts_arr = lean_alloc_array(consts.len(), consts.len());
    for (i, (name, info)) in consts.iter().enumerate() {
      let key_obj = build_name(cache, name);
      let val_obj = build_constant_info(cache, info);
      let pair = lean_alloc_ctor(0, 2, 0);
      lean_ctor_set(pair, 0, key_obj);
      lean_ctor_set(pair, 1, val_obj);
      lean_array_set_core(consts_arr, i, pair);
    }
    consts_arr
  }
}

// =============================================================================
// FFI Exports
// =============================================================================

/// Round-trip an Ix.Environment: decode from Lean, re-encode.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_environment(env_ptr: *const c_void) -> *mut c_void {
  let env = decode_ix_environment(env_ptr);
  let mut cache = LeanBuildCache::with_capacity(env.len());
  build_raw_environment(&mut cache, &env)
}

/// Round-trip an Ix.RawEnvironment: decode from Lean, re-encode.
/// Uses Vec-preserving functions to maintain array structure and order.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_raw_environment(env_ptr: *const c_void) -> *mut c_void {
  let env = decode_ix_raw_environment_vec(env_ptr);
  let mut cache = LeanBuildCache::with_capacity(env.len());
  build_raw_environment_from_vec(&mut cache, &env)
}
