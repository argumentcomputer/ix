//! Ix.Name build/decode/roundtrip FFI.
//!
//! Ix.Name layout:
//! - Tag 0: anonymous (hash : Address)
//! - Tag 1: str (parent : Name) (s : String) (hash : Address)
//! - Tag 2: num (parent : Name) (i : Nat) (hash : Address)

use crate::ix::env::{Name, NameData};
use crate::lean::LeanIxName;
use lean_ffi::nat::Nat;
use lean_ffi::object::{
  LeanArray, LeanBorrowed, LeanOwned, LeanRef, LeanString,
};

use crate::ffi::builder::LeanBuildCache;
use crate::lean::LeanIxAddress;

impl LeanIxName<LeanOwned> {
  /// Build a Lean Ix.Name with embedded hash.
  /// Uses caching to avoid rebuilding the same name.
  pub fn build(cache: &mut LeanBuildCache, name: &Name) -> Self {
    let hash = name.get_hash();
    if let Some(cached) = cache.names.get(hash) {
      return cached.clone();
    }

    let result = match name.as_data() {
      NameData::Anonymous(h) => {
        let ctor = LeanIxName::alloc(0);
        ctor.set_obj(0, LeanIxAddress::build_from_hash(h));
        ctor
      },
      NameData::Str(parent, s, h) => {
        let parent_obj = Self::build(cache, parent);
        let s_obj = LeanString::new(s.as_str());
        let ctor = LeanIxName::alloc(1);
        ctor.set_obj(0, parent_obj);
        ctor.set_obj(1, s_obj);
        ctor.set_obj(2, LeanIxAddress::build_from_hash(h));
        ctor
      },
      NameData::Num(parent, n, h) => {
        let parent_obj = Self::build(cache, parent);
        let n_obj = Nat::to_lean(n);
        let ctor = LeanIxName::alloc(2);
        ctor.set_obj(0, parent_obj);
        ctor.set_obj(1, n_obj);
        ctor.set_obj(2, LeanIxAddress::build_from_hash(h));
        ctor
      },
    };

    cache.names.insert(*hash, result.clone());
    result
  }

  /// Build an Array of Names.
  pub fn build_array(
    cache: &mut LeanBuildCache,
    names: &[Name],
  ) -> LeanArray<LeanOwned> {
    let arr = LeanArray::alloc(names.len());
    for (i, name) in names.iter().enumerate() {
      arr.set(i, Self::build(cache, name));
    }
    arr
  }
}

impl<R: LeanRef> LeanIxName<R> {
  /// Decode a Lean Ix.Name to Rust Name.
  pub fn decode(&self) -> Name {
    let ctor = self.as_ctor();
    match ctor.tag() {
      0 => {
        // anonymous: just has hash, construct anon Name
        Name::anon()
      },
      1 => {
        // str: parent, s, hash
        let parent = LeanIxName(ctor.get(0)).decode();
        let s = ctor.get(1).as_string().to_string();
        Name::str(parent, s)
      },
      2 => {
        // num: parent, i, hash
        let parent = LeanIxName(ctor.get(0)).decode();
        let i = Nat::from_obj(&ctor.get(1));
        Name::num(parent, i)
      },
      _ => panic!("Invalid Ix.Name tag: {}", ctor.tag()),
    }
  }
}

impl LeanIxName<LeanBorrowed<'_>> {
  /// Decode Array of Names from Lean pointer.
  pub fn decode_array(obj: LeanArray<LeanBorrowed<'_>>) -> Vec<Name> {
    obj.map(|x| LeanIxName(x).decode())
  }
}

/// Round-trip an Ix.Name: decode from Lean, re-encode via LeanBuildCache.
#[cfg(feature = "test-ffi")]
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_name(
  name_ptr: LeanIxName<LeanBorrowed<'_>>,
) -> LeanIxName<LeanOwned> {
  let name = name_ptr.decode();
  let mut cache = LeanBuildCache::new();
  LeanIxName::build(&mut cache, &name)
}
