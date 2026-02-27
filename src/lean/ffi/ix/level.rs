//! Ix.Level build/decode/roundtrip FFI.
//!
//! Ix.Level layout:
//! - Tag 0: zero (hash : Address)
//! - Tag 1: succ (x : Level) (hash : Address)
//! - Tag 2: max (x y : Level) (hash : Address)
//! - Tag 3: imax (x y : Level) (hash : Address)
//! - Tag 4: param (n : Name) (hash : Address)
//! - Tag 5: mvar (n : Name) (hash : Address)

use std::ffi::c_void;

use crate::ix::env::{Level, LevelData};
use crate::lean::lean::{
  lean_alloc_array, lean_alloc_ctor, lean_array_set_core, lean_ctor_get,
  lean_ctor_set, lean_inc, lean_obj_tag,
};

use super::super::builder::LeanBuildCache;
use super::address::build_address;
use super::name::{build_name, decode_ix_name};

/// Build a Lean Ix.Level with embedded hash.
/// Uses caching to avoid rebuilding the same level.
pub fn build_level(cache: &mut LeanBuildCache, level: &Level) -> *mut c_void {
  let hash = *level.get_hash();
  if let Some(&cached) = cache.levels.get(&hash) {
    unsafe { lean_inc(cached.cast()) };
    return cached;
  }

  let result = unsafe {
    match level.as_data() {
      LevelData::Zero(h) => {
        let obj = lean_alloc_ctor(0, 1, 0);
        lean_ctor_set(obj, 0, build_address(h).cast());
        obj.cast()
      },
      LevelData::Succ(x, h) => {
        let x_obj = build_level(cache, x);
        let obj = lean_alloc_ctor(1, 2, 0);
        lean_ctor_set(obj, 0, x_obj.cast());
        lean_ctor_set(obj, 1, build_address(h).cast());
        obj.cast()
      },
      LevelData::Max(x, y, h) => {
        let x_obj = build_level(cache, x);
        let y_obj = build_level(cache, y);
        let obj = lean_alloc_ctor(2, 3, 0);
        lean_ctor_set(obj, 0, x_obj.cast());
        lean_ctor_set(obj, 1, y_obj.cast());
        lean_ctor_set(obj, 2, build_address(h).cast());
        obj.cast()
      },
      LevelData::Imax(x, y, h) => {
        let x_obj = build_level(cache, x);
        let y_obj = build_level(cache, y);
        let obj = lean_alloc_ctor(3, 3, 0);
        lean_ctor_set(obj, 0, x_obj.cast());
        lean_ctor_set(obj, 1, y_obj.cast());
        lean_ctor_set(obj, 2, build_address(h).cast());
        obj.cast()
      },
      LevelData::Param(n, h) => {
        let n_obj = build_name(cache, n);
        let obj = lean_alloc_ctor(4, 2, 0);
        lean_ctor_set(obj, 0, n_obj.cast());
        lean_ctor_set(obj, 1, build_address(h).cast());
        obj.cast()
      },
      LevelData::Mvar(n, h) => {
        let n_obj = build_name(cache, n);
        let obj = lean_alloc_ctor(5, 2, 0);
        lean_ctor_set(obj, 0, n_obj.cast());
        lean_ctor_set(obj, 1, build_address(h).cast());
        obj.cast()
      },
    }
  };

  cache.levels.insert(hash, result);
  result
}

/// Build an Array of Levels.
pub fn build_level_array(
  cache: &mut LeanBuildCache,
  levels: &[Level],
) -> *mut c_void {
  unsafe {
    let arr = lean_alloc_array(levels.len(), levels.len());
    for (i, level) in levels.iter().enumerate() {
      let level_obj = build_level(cache, level);
      lean_array_set_core(arr, i, level_obj.cast());
    }
    arr.cast()
  }
}

/// Decode a Lean Ix.Level to Rust Level.
pub fn decode_ix_level(ptr: *const c_void) -> Level {
  unsafe {
    let tag = lean_obj_tag(ptr as *mut _);
    match tag {
      0 => Level::zero(),
      1 => {
        let x_ptr = lean_ctor_get(ptr as *mut _, 0);
        let x = decode_ix_level(x_ptr.cast());
        Level::succ(x)
      },
      2 => {
        let x_ptr = lean_ctor_get(ptr as *mut _, 0);
        let y_ptr = lean_ctor_get(ptr as *mut _, 1);
        let x = decode_ix_level(x_ptr.cast());
        let y = decode_ix_level(y_ptr.cast());
        Level::max(x, y)
      },
      3 => {
        let x_ptr = lean_ctor_get(ptr as *mut _, 0);
        let y_ptr = lean_ctor_get(ptr as *mut _, 1);
        let x = decode_ix_level(x_ptr.cast());
        let y = decode_ix_level(y_ptr.cast());
        Level::imax(x, y)
      },
      4 => {
        let n_ptr = lean_ctor_get(ptr as *mut _, 0);
        let n = decode_ix_name(n_ptr.cast());
        Level::param(n)
      },
      5 => {
        let n_ptr = lean_ctor_get(ptr as *mut _, 0);
        let n = decode_ix_name(n_ptr.cast());
        Level::mvar(n)
      },
      _ => panic!("Invalid Ix.Level tag: {}", tag),
    }
  }
}

/// Decode Array of Levels from Lean pointer.
pub fn decode_level_array(ptr: *const c_void) -> Vec<Level> {
  crate::lean::lean_array_to_vec(ptr, decode_ix_level)
}

/// Round-trip an Ix.Level: decode from Lean, re-encode via LeanBuildCache.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_level(
  level_ptr: *const c_void,
) -> *mut c_void {
  let level = decode_ix_level(level_ptr);
  let mut cache = LeanBuildCache::new();
  build_level(&mut cache, &level)
}
