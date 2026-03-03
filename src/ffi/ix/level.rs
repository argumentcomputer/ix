//! Ix.Level build/decode/roundtrip FFI.
//!
//! Ix.Level layout:
//! - Tag 0: zero (hash : Address)
//! - Tag 1: succ (x : Level) (hash : Address)
//! - Tag 2: max (x y : Level) (hash : Address)
//! - Tag 3: imax (x y : Level) (hash : Address)
//! - Tag 4: param (n : Name) (hash : Address)
//! - Tag 5: mvar (n : Name) (hash : Address)

use crate::ix::env::{Level, LevelData};
use lean_sys::object::{LeanArray, LeanCtor, LeanObject};
use crate::lean::LeanIxLevel;

use crate::ffi::builder::LeanBuildCache;
use crate::ffi::ix::address::build_address;
use crate::ffi::ix::name::{build_name, decode_ix_name};

/// Build a Lean Ix.Level with embedded hash.
/// Uses caching to avoid rebuilding the same level.
pub fn build_level(cache: &mut LeanBuildCache, level: &Level) -> LeanIxLevel {
  let hash = *level.get_hash();
  if let Some(&cached) = cache.levels.get(&hash) {
    cached.inc_ref();
    return cached;
  }

  let result = match level.as_data() {
    LevelData::Zero(h) => {
      let ctor = LeanCtor::alloc(0, 1, 0);
      ctor.set(0, build_address(h));
      LeanIxLevel::new(*ctor)
    },
    LevelData::Succ(x, h) => {
      let x_obj = build_level(cache, x);
      let ctor = LeanCtor::alloc(1, 2, 0);
      ctor.set(0, x_obj);
      ctor.set(1, build_address(h));
      LeanIxLevel::new(*ctor)
    },
    LevelData::Max(x, y, h) => {
      let x_obj = build_level(cache, x);
      let y_obj = build_level(cache, y);
      let ctor = LeanCtor::alloc(2, 3, 0);
      ctor.set(0, x_obj);
      ctor.set(1, y_obj);
      ctor.set(2, build_address(h));
      LeanIxLevel::new(*ctor)
    },
    LevelData::Imax(x, y, h) => {
      let x_obj = build_level(cache, x);
      let y_obj = build_level(cache, y);
      let ctor = LeanCtor::alloc(3, 3, 0);
      ctor.set(0, x_obj);
      ctor.set(1, y_obj);
      ctor.set(2, build_address(h));
      LeanIxLevel::new(*ctor)
    },
    LevelData::Param(n, h) => {
      let n_obj = build_name(cache, n);
      let ctor = LeanCtor::alloc(4, 2, 0);
      ctor.set(0, n_obj);
      ctor.set(1, build_address(h));
      LeanIxLevel::new(*ctor)
    },
    LevelData::Mvar(n, h) => {
      let n_obj = build_name(cache, n);
      let ctor = LeanCtor::alloc(5, 2, 0);
      ctor.set(0, n_obj);
      ctor.set(1, build_address(h));
      LeanIxLevel::new(*ctor)
    },
  };

  cache.levels.insert(hash, result);
  result
}

/// Build an Array of Levels.
pub fn build_level_array(
  cache: &mut LeanBuildCache,
  levels: &[Level],
) -> LeanArray {
  let arr = LeanArray::alloc(levels.len());
  for (i, level) in levels.iter().enumerate() {
    arr.set(i, build_level(cache, level));
  }
  arr
}

/// Decode a Lean Ix.Level to Rust Level.
pub fn decode_ix_level(obj: LeanObject) -> Level {
  let ctor = obj.as_ctor();
  match ctor.tag() {
    0 => Level::zero(),
    1 => {
      let x = decode_ix_level(ctor.get(0));
      Level::succ(x)
    },
    2 => {
      let x = decode_ix_level(ctor.get(0));
      let y = decode_ix_level(ctor.get(1));
      Level::max(x, y)
    },
    3 => {
      let x = decode_ix_level(ctor.get(0));
      let y = decode_ix_level(ctor.get(1));
      Level::imax(x, y)
    },
    4 => {
      let n = decode_ix_name(ctor.get(0));
      Level::param(n)
    },
    5 => {
      let n = decode_ix_name(ctor.get(0));
      Level::mvar(n)
    },
    _ => panic!("Invalid Ix.Level tag: {}", ctor.tag()),
  }
}

/// Decode Array of Levels from Lean pointer.
pub fn decode_level_array(obj: LeanObject) -> Vec<Level> {
  obj.as_array().map(decode_ix_level)
}

/// Round-trip an Ix.Level: decode from Lean, re-encode via LeanBuildCache.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_level(level_ptr: LeanIxLevel) -> LeanIxLevel {
  let level = decode_ix_level(*level_ptr);
  let mut cache = LeanBuildCache::new();
  build_level(&mut cache, &level)
}
