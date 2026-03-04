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
use crate::lean::{LeanIxLevel, LeanIxName};
use lean_ffi::object::{LeanArray, LeanCtor};

use crate::ffi::builder::LeanBuildCache;
use crate::lean::LeanIxAddress;

impl LeanIxLevel {
  /// Build a Lean Ix.Level with embedded hash.
  /// Uses caching to avoid rebuilding the same level.
  pub fn build(cache: &mut LeanBuildCache, level: &Level) -> Self {
    let hash = *level.get_hash();
    if let Some(&cached) = cache.levels.get(&hash) {
      cached.inc_ref();
      return cached;
    }

    let result = match level.as_data() {
      LevelData::Zero(h) => {
        let ctor = LeanCtor::alloc(0, 1, 0);
        ctor.set(0, LeanIxAddress::build_from_hash(h));
        Self::new(*ctor)
      },
      LevelData::Succ(x, h) => {
        let x_obj = Self::build(cache, x);
        let ctor = LeanCtor::alloc(1, 2, 0);
        ctor.set(0, x_obj);
        ctor.set(1, LeanIxAddress::build_from_hash(h));
        Self::new(*ctor)
      },
      LevelData::Max(x, y, h) => {
        let x_obj = Self::build(cache, x);
        let y_obj = Self::build(cache, y);
        let ctor = LeanCtor::alloc(2, 3, 0);
        ctor.set(0, x_obj);
        ctor.set(1, y_obj);
        ctor.set(2, LeanIxAddress::build_from_hash(h));
        Self::new(*ctor)
      },
      LevelData::Imax(x, y, h) => {
        let x_obj = Self::build(cache, x);
        let y_obj = Self::build(cache, y);
        let ctor = LeanCtor::alloc(3, 3, 0);
        ctor.set(0, x_obj);
        ctor.set(1, y_obj);
        ctor.set(2, LeanIxAddress::build_from_hash(h));
        Self::new(*ctor)
      },
      LevelData::Param(n, h) => {
        let n_obj = LeanIxName::build(cache, n);
        let ctor = LeanCtor::alloc(4, 2, 0);
        ctor.set(0, n_obj);
        ctor.set(1, LeanIxAddress::build_from_hash(h));
        Self::new(*ctor)
      },
      LevelData::Mvar(n, h) => {
        let n_obj = LeanIxName::build(cache, n);
        let ctor = LeanCtor::alloc(5, 2, 0);
        ctor.set(0, n_obj);
        ctor.set(1, LeanIxAddress::build_from_hash(h));
        Self::new(*ctor)
      },
    };

    cache.levels.insert(hash, result);
    result
  }

  /// Build an Array of Levels.
  pub fn build_array(
    cache: &mut LeanBuildCache,
    levels: &[Level],
  ) -> LeanArray {
    let arr = LeanArray::alloc(levels.len());
    for (i, level) in levels.iter().enumerate() {
      arr.set(i, Self::build(cache, level));
    }
    arr
  }

  /// Decode a Lean Ix.Level to Rust Level.
  pub fn decode(self) -> Level {
    let ctor = self.as_ctor();
    match ctor.tag() {
      0 => Level::zero(),
      1 => {
        let x = Self::new(ctor.get(0)).decode();
        Level::succ(x)
      },
      2 => {
        let x = Self::new(ctor.get(0)).decode();
        let y = Self::new(ctor.get(1)).decode();
        Level::max(x, y)
      },
      3 => {
        let x = Self::new(ctor.get(0)).decode();
        let y = Self::new(ctor.get(1)).decode();
        Level::imax(x, y)
      },
      4 => {
        let n = LeanIxName::new(ctor.get(0)).decode();
        Level::param(n)
      },
      5 => {
        let n = LeanIxName::new(ctor.get(0)).decode();
        Level::mvar(n)
      },
      _ => panic!("Invalid Ix.Level tag: {}", ctor.tag()),
    }
  }

  /// Decode Array of Levels from Lean pointer.
  pub fn decode_array(obj: LeanArray) -> Vec<Level> {
    obj.map(|x| Self::new(x).decode())
  }
}

/// Round-trip an Ix.Level: decode from Lean, re-encode via LeanBuildCache.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_level(level_ptr: LeanIxLevel) -> LeanIxLevel {
  let level = level_ptr.decode();
  let mut cache = LeanBuildCache::new();
  LeanIxLevel::build(&mut cache, &level)
}
