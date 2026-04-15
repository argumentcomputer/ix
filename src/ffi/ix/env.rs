//! Ix.Environment build/decode/roundtrip FFI.

use rustc_hash::FxHashMap;

use crate::ix::env::{ConstantInfo, Name};
use crate::lean::{
  LeanIxConstantInfo, LeanIxEnvironment, LeanIxName, LeanIxRawEnvironment,
};
use lean_ffi::object::{
  LeanArray, LeanBorrowed, LeanCtor, LeanOwned, LeanProd, LeanRef,
};

use crate::ffi::builder::LeanBuildCache;

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
  pairs: Vec<(LeanOwned, LeanOwned, u64)>, // (key_obj, val_obj, hash)
) -> LeanOwned {
  let size = pairs.len();
  let bucket_count = (size * 4 / 3 + 1).next_power_of_two().max(8);

  // Create array of AssocLists (initially all nil = boxed 0)
  let buckets = LeanArray::alloc(bucket_count);
  let nil = LeanOwned::box_usize(0);
  for i in 0..bucket_count {
    buckets.set(i, nil.clone()); // nil
  }

  // Insert entries
  for (key_obj, val_obj, hash) in pairs {
    let bucket_idx =
      usize::try_from(hash).expect("hash overflows usize") % bucket_count;

    // Get current bucket (AssocList)
    let current_tail = buckets.get(bucket_idx).to_owned_ref();

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
  let size_obj = LeanOwned::box_usize(size);

  let raw = LeanCtor::alloc(0, 2, 0);
  raw.set(0, size_obj);
  raw.set(1, buckets);
  raw.into()
}

// =============================================================================
// Environment Building / Decoding
// =============================================================================

/// Decode a HashMap's AssocList and collect key-value pairs using a custom decoder.
fn decode_assoc_list<K, V, FK, FV>(
  obj: LeanBorrowed<'_>,
  decode_key: FK,
  decode_val: FV,
) -> Vec<(K, V)>
where
  FK: Fn(LeanBorrowed<'_>) -> K,
  FV: Fn(LeanBorrowed<'_>) -> V,
{
  let mut result = Vec::new();
  let mut current = obj;

  while !current.is_scalar() {
    let ctor = current.as_ctor();
    if ctor.tag() == 0 {
      break; // AssocList.nil
    }
    // AssocList.cons: 3 fields (key, value, tail)
    let key = ctor.get(0);
    let val = ctor.get(1);
    let next = ctor.get(2).as_raw();
    result.push((decode_key(key), decode_val(val)));
    current = unsafe { LeanBorrowed::from_raw(next) };
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
  obj: LeanBorrowed<'_>,
  decode_key: FK,
  decode_val: FV,
) -> Vec<(K, V)>
where
  FK: Fn(LeanBorrowed<'_>) -> K + Copy,
  FV: Fn(LeanBorrowed<'_>) -> V + Copy,
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

impl LeanIxRawEnvironment<LeanOwned> {
  /// Build a Ix.RawEnvironment from collected caches.
  /// RawEnvironment has arrays that Lean will convert to HashMaps.
  ///
  /// Ix.RawEnvironment = {
  ///   consts : Array (Name × ConstantInfo)
  /// }
  ///
  /// NOTE: RawEnvironment with a single field is UNBOXED by Lean,
  /// so we return just the array, not a structure containing it.
  pub fn build(
    cache: &mut LeanBuildCache,
    consts: &FxHashMap<Name, ConstantInfo>,
  ) -> Self {
    // Build consts array: Array (Name × ConstantInfo)
    let consts_arr = LeanArray::alloc(consts.len());
    for (i, (name, info)) in consts.iter().enumerate() {
      let key_obj = LeanIxName::build(cache, name);
      let val_obj = LeanIxConstantInfo::build(cache, info);
      // Build pair (Name × ConstantInfo)
      let pair = LeanProd::new(key_obj, val_obj);
      consts_arr.set(i, pair);
    }

    Self::new(consts_arr.into())
  }

  /// Build Ix.RawEnvironment from Vec, preserving order and duplicates.
  pub fn build_from_vec(
    cache: &mut LeanBuildCache,
    consts: &[(Name, ConstantInfo)],
  ) -> Self {
    let consts_arr = LeanArray::alloc(consts.len());
    for (i, (name, info)) in consts.iter().enumerate() {
      let key_obj = LeanIxName::build(cache, name);
      let val_obj = LeanIxConstantInfo::build(cache, info);
      let pair = LeanProd::new(key_obj, val_obj);
      consts_arr.set(i, pair);
    }
    Self::new(consts_arr.into())
  }
}

impl<R: LeanRef> LeanIxRawEnvironment<R> {
  /// RawEnvironment is a single-field struct, unboxed to just Array by Lean.
  fn as_array(&self) -> LeanArray<LeanBorrowed<'_>> {
    unsafe { LeanBorrowed::from_raw(self.as_raw()) }.as_array()
  }

  /// Decode Ix.RawEnvironment from Lean object into HashMap.
  /// RawEnvironment = { consts : Array (Name × ConstantInfo) }
  /// NOTE: Unboxed to just Array. This version deduplicates by name.
  pub fn decode(&self) -> FxHashMap<Name, ConstantInfo> {
    let arr = self.as_array();
    let mut consts: FxHashMap<Name, ConstantInfo> = FxHashMap::default();
    for pair_obj in arr.iter() {
      let pair = pair_obj.as_ctor();
      let name = LeanIxName(pair.get(0)).decode();
      let info = LeanIxConstantInfo(pair.get(1)).decode();
      consts.insert(name, info);
    }
    consts
  }

  /// Decode Ix.RawEnvironment preserving array structure (including duplicates).
  pub fn decode_to_vec(&self) -> Vec<(Name, ConstantInfo)> {
    let arr = self.as_array();
    let mut consts = Vec::with_capacity(arr.len());
    for pair_obj in arr.iter() {
      let pair = pair_obj.as_ctor();
      let name = LeanIxName(pair.get(0)).decode();
      let info = LeanIxConstantInfo(pair.get(1)).decode();
      consts.push((name, info));
    }
    consts
  }
}

impl<R: LeanRef> LeanIxEnvironment<R> {
  /// Decode Ix.Environment from Lean object.
  ///
  /// Ix.Environment = {
  ///   consts : HashMap Name ConstantInfo
  /// }
  ///
  /// NOTE: Environment with a single field is UNBOXED by Lean,
  /// so the pointer IS the HashMap directly, not a structure containing it.
  pub fn decode(&self) -> FxHashMap<Name, ConstantInfo> {
    let borrowed = unsafe { LeanBorrowed::from_raw(self.as_raw()) };
    let consts_pairs = decode_hashmap(
      borrowed,
      |x| LeanIxName::new(x.to_owned_ref()).decode(),
      |x| LeanIxConstantInfo::new(x.to_owned_ref()).decode(),
    );
    let mut consts: FxHashMap<Name, ConstantInfo> = FxHashMap::default();
    for (name, info) in consts_pairs {
      consts.insert(name, info);
    }
    consts
  }
}

// =============================================================================
// FFI Exports
// =============================================================================

/// Round-trip an Ix.Environment: decode from Lean, re-encode.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_environment(
  env_ptr: LeanIxEnvironment<LeanBorrowed<'_>>,
) -> LeanIxRawEnvironment<LeanOwned> {
  let env = env_ptr.decode();
  let mut cache = LeanBuildCache::with_capacity(env.len());
  LeanIxRawEnvironment::build(&mut cache, &env)
}

/// Round-trip an Ix.RawEnvironment: decode from Lean, re-encode.
/// Uses Vec-preserving functions to maintain array structure and order.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_raw_environment(
  env_ptr: LeanIxRawEnvironment<LeanBorrowed<'_>>,
) -> LeanIxRawEnvironment<LeanOwned> {
  let env = env_ptr.decode_to_vec();
  let mut cache = LeanBuildCache::with_capacity(env.len());
  LeanIxRawEnvironment::build_from_vec(&mut cache, &env)
}
