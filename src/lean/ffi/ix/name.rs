//! Ix.Name build/decode/roundtrip FFI.
//!
//! Ix.Name layout:
//! - Tag 0: anonymous (hash : Address)
//! - Tag 1: str (parent : Name) (s : String) (hash : Address)
//! - Tag 2: num (parent : Name) (i : Nat) (hash : Address)

use crate::ix::env::{Name, NameData};
use crate::lean::nat::Nat;
use crate::lean::obj::{IxName, LeanArray, LeanCtor, LeanObj, LeanString};

use crate::lean::ffi::builder::LeanBuildCache;
use crate::lean::ffi::ix::address::build_address;
use crate::lean::ffi::primitives::build_nat;

/// Build a Lean Ix.Name with embedded hash.
/// Uses caching to avoid rebuilding the same name.
pub fn build_name(cache: &mut LeanBuildCache, name: &Name) -> IxName {
  let hash = name.get_hash();
  if let Some(&cached) = cache.names.get(hash) {
    cached.inc_ref();
    return cached;
  }

  let result = match name.as_data() {
    NameData::Anonymous(h) => {
      let ctor = LeanCtor::alloc(0, 1, 0);
      ctor.set(0, build_address(h));
      IxName::new(*ctor)
    },
    NameData::Str(parent, s, h) => {
      let parent_obj = build_name(cache, parent);
      let s_obj = LeanString::from_str(s.as_str());
      let ctor = LeanCtor::alloc(1, 3, 0);
      ctor.set(0, parent_obj);
      ctor.set(1, s_obj);
      ctor.set(2, build_address(h));
      IxName::new(*ctor)
    },
    NameData::Num(parent, n, h) => {
      let parent_obj = build_name(cache, parent);
      let n_obj = build_nat(n);
      let ctor = LeanCtor::alloc(2, 3, 0);
      ctor.set(0, parent_obj);
      ctor.set(1, n_obj);
      ctor.set(2, build_address(h));
      IxName::new(*ctor)
    },
  };

  cache.names.insert(*hash, result);
  result
}

/// Build an Array of Names.
pub fn build_name_array(
  cache: &mut LeanBuildCache,
  names: &[Name],
) -> LeanArray {
  let arr = LeanArray::alloc(names.len());
  for (i, name) in names.iter().enumerate() {
    arr.set(i, build_name(cache, name));
  }
  arr
}

/// Decode a Lean Ix.Name to Rust Name.
pub fn decode_ix_name(obj: LeanObj) -> Name {
  let ctor = obj.as_ctor();
  match ctor.tag() {
    0 => {
      // anonymous: just has hash, construct anon Name
      Name::anon()
    },
    1 => {
      // str: parent, s, hash
      let parent = decode_ix_name(ctor.get(0));
      let s = ctor.get(1).as_string().to_string();
      Name::str(parent, s)
    },
    2 => {
      // num: parent, i, hash
      let parent = decode_ix_name(ctor.get(0));
      let i = Nat::from_obj(ctor.get(1));
      Name::num(parent, i)
    },
    _ => panic!("Invalid Ix.Name tag: {}", ctor.tag()),
  }
}

/// Decode Array of Names from Lean pointer.
pub fn decode_name_array(obj: LeanObj) -> Vec<Name> {
  obj.as_array().map(decode_ix_name)
}

/// Round-trip an Ix.Name: decode from Lean, re-encode via LeanBuildCache.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_name(name_ptr: IxName) -> IxName {
  let name = decode_ix_name(*name_ptr);
  let mut cache = LeanBuildCache::new();
  build_name(&mut cache, &name)
}
