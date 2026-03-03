//! Ix.Environment build/decode/roundtrip FFI.

use rustc_hash::FxHashMap;

use crate::ix::env::{ConstantInfo, Name};
use lean_sys::object::{LeanArray, LeanCtor, LeanObject};
use crate::lean::{LeanIxEnvironment, LeanIxRawEnvironment};

use crate::ffi::builder::LeanBuildCache;
use crate::ffi::ix::constant::{build_constant_info, decode_constant_info};
use crate::ffi::ix::name::{build_name, decode_ix_name};

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
  pairs: Vec<(LeanObject, LeanObject, u64)>, // (key_obj, val_obj, hash)
) -> LeanObject {
  let size = pairs.len();
  let bucket_count = (size * 4 / 3 + 1).next_power_of_two().max(8);

  // Create array of AssocLists (initially all nil = boxed 0)
  let buckets = LeanArray::alloc(bucket_count);
  let nil = LeanObject::box_usize(0);
  for i in 0..bucket_count {
    buckets.set(i, nil); // nil
  }

  // Insert entries
  for (key_obj, val_obj, hash) in pairs {
    let bucket_idx =
      usize::try_from(hash).expect("hash overflows usize") % bucket_count;

    // Get current bucket (AssocList)
    let current_tail = buckets.get(bucket_idx);

    // cons (key : α) (value : β) (tail : AssocList α β) -- tag 1
    let cons = LeanCtor::alloc(1, 3, 0);
    cons.set(0, key_obj);
    cons.set(1, val_obj);
    cons.set(2, current_tail);

    buckets.set(bucket_idx, cons);
  }

  // Build Raw { size : Nat, buckets : Array }
  // Due to unboxing, this IS the HashMap directly
  // Field 0 = size, Field 1 = buckets (2 object fields, no scalars)
  let size_obj = LeanObject::box_usize(size);

  let raw = LeanCtor::alloc(0, 2, 0);
  raw.set(0, size_obj);
  raw.set(1, buckets);
  *raw
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
pub fn build_raw_environment(
  cache: &mut LeanBuildCache,
  consts: &FxHashMap<Name, ConstantInfo>,
) -> LeanObject {
  // Build consts array: Array (Name × ConstantInfo)
  let consts_arr = LeanArray::alloc(consts.len());
  for (i, (name, info)) in consts.iter().enumerate() {
    let key_obj = build_name(cache, name);
    let val_obj = build_constant_info(cache, info);
    // Build pair (Name × ConstantInfo)
    let pair = LeanCtor::alloc(0, 2, 0);
    pair.set(0, key_obj);
    pair.set(1, val_obj);
    consts_arr.set(i, pair);
  }

  *consts_arr
}

// =============================================================================
// Environment Decoder
// =============================================================================

/// Decode a HashMap's AssocList and collect key-value pairs using a custom decoder.
fn decode_assoc_list<K, V, FK, FV>(
  obj: LeanObject,
  decode_key: FK,
  decode_val: FV,
) -> Vec<(K, V)>
where
  FK: Fn(LeanObject) -> K,
  FV: Fn(LeanObject) -> V,
{
  let mut result = Vec::new();
  let mut current = obj;

  loop {
    if current.is_scalar() {
      break;
    }

    let ctor = current.as_ctor();
    if ctor.tag() == 0 {
      // AssocList.nil
      break;
    }

    // AssocList.cons: 3 fields (key, value, tail)
    result.push((decode_key(ctor.get(0)), decode_val(ctor.get(1))));
    current = ctor.get(2);
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
  obj: LeanObject,
  decode_key: FK,
  decode_val: FV,
) -> Vec<(K, V)>
where
  FK: Fn(LeanObject) -> K + Copy,
  FV: Fn(LeanObject) -> V + Copy,
{
  let ctor = obj.as_ctor();
  // Raw layout: field 0 = size (Nat), field 1 = buckets (Array)
  let _size = ctor.get(0); // unused but needed for layout
  let buckets = ctor.get(1).as_array();

  let mut pairs = Vec::new();
  for bucket in buckets.iter() {
    let bucket_pairs = decode_assoc_list(bucket, decode_key, decode_val);
    pairs.extend(bucket_pairs);
  }

  pairs
}

/// Decode Ix.Environment from Lean object.
///
/// Ix.Environment = {
///   consts : HashMap Name ConstantInfo
/// }
///
/// NOTE: Environment with a single field is UNBOXED by Lean,
/// so the pointer IS the HashMap directly, not a structure containing it.
pub fn decode_ix_environment(obj: LeanObject) -> FxHashMap<Name, ConstantInfo> {
  // Environment is unboxed - obj IS the HashMap directly
  let consts_pairs = decode_hashmap(obj, decode_ix_name, decode_constant_info);
  let mut consts: FxHashMap<Name, ConstantInfo> = FxHashMap::default();
  for (name, info) in consts_pairs {
    consts.insert(name, info);
  }
  consts
}

/// Decode Ix.RawEnvironment from Lean object into HashMap.
/// RawEnvironment = { consts : Array (Name × ConstantInfo) }
/// NOTE: Unboxed to just Array. This version deduplicates by name.
pub fn decode_ix_raw_environment(
  obj: LeanObject,
) -> FxHashMap<Name, ConstantInfo> {
  let arr = obj.as_array();
  let mut consts: FxHashMap<Name, ConstantInfo> = FxHashMap::default();

  for pair_obj in arr.iter() {
    let pair = pair_obj.as_ctor();
    let name = decode_ix_name(pair.get(0));
    let info = decode_constant_info(pair.get(1));
    consts.insert(name, info);
  }

  consts
}

/// Decode Ix.RawEnvironment from Lean object preserving array structure.
/// This version preserves all entries including duplicates.
pub fn decode_ix_raw_environment_vec(
  obj: LeanObject,
) -> Vec<(Name, ConstantInfo)> {
  let arr = obj.as_array();
  let mut consts = Vec::with_capacity(arr.len());

  for pair_obj in arr.iter() {
    let pair = pair_obj.as_ctor();
    let name = decode_ix_name(pair.get(0));
    let info = decode_constant_info(pair.get(1));
    consts.push((name, info));
  }

  consts
}

/// Build Ix.RawEnvironment from Vec, preserving order and duplicates.
pub fn build_raw_environment_from_vec(
  cache: &mut LeanBuildCache,
  consts: &[(Name, ConstantInfo)],
) -> LeanObject {
  let consts_arr = LeanArray::alloc(consts.len());
  for (i, (name, info)) in consts.iter().enumerate() {
    let key_obj = build_name(cache, name);
    let val_obj = build_constant_info(cache, info);
    let pair = LeanCtor::alloc(0, 2, 0);
    pair.set(0, key_obj);
    pair.set(1, val_obj);
    consts_arr.set(i, pair);
  }
  *consts_arr
}

// =============================================================================
// FFI Exports
// =============================================================================

/// Round-trip an Ix.Environment: decode from Lean, re-encode.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_environment(
  env_ptr: LeanIxEnvironment,
) -> LeanIxRawEnvironment {
  let env = decode_ix_environment(*env_ptr);
  let mut cache = LeanBuildCache::with_capacity(env.len());
  build_raw_environment(&mut cache, &env).into()
}

/// Round-trip an Ix.RawEnvironment: decode from Lean, re-encode.
/// Uses Vec-preserving functions to maintain array structure and order.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_raw_environment(
  env_ptr: LeanIxRawEnvironment,
) -> LeanIxRawEnvironment {
  let env = decode_ix_raw_environment_vec(*env_ptr);
  let mut cache = LeanBuildCache::with_capacity(env.len());
  build_raw_environment_from_vec(&mut cache, &env).into()
}
