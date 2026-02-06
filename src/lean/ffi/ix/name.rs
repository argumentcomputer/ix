//! Ix.Name build/decode/roundtrip FFI.
//!
//! Ix.Name layout:
//! - Tag 0: anonymous (hash : Address)
//! - Tag 1: str (parent : Name) (s : String) (hash : Address)
//! - Tag 2: num (parent : Name) (i : Nat) (hash : Address)

use std::ffi::c_void;

use crate::ix::env::{Name, NameData};
use crate::lean::nat::Nat;
use crate::lean::string::LeanStringObject;
use crate::lean::{
  as_ref_unsafe, lean_alloc_array, lean_alloc_ctor, lean_array_set_core,
  lean_ctor_get, lean_ctor_set, lean_inc, lean_mk_string, lean_obj_tag,
};

use super::super::builder::LeanBuildCache;
use super::super::primitives::build_nat;
use super::address::build_address;

/// Build a Lean Ix.Name with embedded hash.
/// Uses caching to avoid rebuilding the same name.
pub fn build_name(cache: &mut LeanBuildCache, name: &Name) -> *mut c_void {
  let hash = name.get_hash();
  if let Some(&cached) = cache.names.get(hash) {
    unsafe { lean_inc(cached) };
    return cached;
  }

  let result = unsafe {
    match name.as_data() {
      NameData::Anonymous(h) => {
        // anonymous: (hash : Address)
        let obj = lean_alloc_ctor(0, 1, 0);
        lean_ctor_set(obj, 0, build_address(h));
        obj
      },
      NameData::Str(parent, s, h) => {
        // str: (parent : Name) (s : String) (hash : Address)
        let parent_obj = build_name(cache, parent);
        let s_cstr = crate::lean::safe_cstring(s.as_str());
        let obj = lean_alloc_ctor(1, 3, 0);
        lean_ctor_set(obj, 0, parent_obj);
        lean_ctor_set(obj, 1, lean_mk_string(s_cstr.as_ptr()));
        lean_ctor_set(obj, 2, build_address(h));
        obj
      },
      NameData::Num(parent, n, h) => {
        // num: (parent : Name) (i : Nat) (hash : Address)
        let parent_obj = build_name(cache, parent);
        let n_obj = build_nat(n);
        let obj = lean_alloc_ctor(2, 3, 0);
        lean_ctor_set(obj, 0, parent_obj);
        lean_ctor_set(obj, 1, n_obj);
        lean_ctor_set(obj, 2, build_address(h));
        obj
      },
    }
  };

  cache.names.insert(*hash, result);
  result
}

/// Build an Array of Names.
pub fn build_name_array(
  cache: &mut LeanBuildCache,
  names: &[Name],
) -> *mut c_void {
  unsafe {
    let arr = lean_alloc_array(names.len(), names.len());
    for (i, name) in names.iter().enumerate() {
      let name_obj = build_name(cache, name);
      lean_array_set_core(arr, i, name_obj);
    }
    arr
  }
}

/// Decode a Lean Ix.Name to Rust Name.
pub fn decode_ix_name(ptr: *const c_void) -> Name {
  unsafe {
    let tag = lean_obj_tag(ptr as *mut _);
    match tag {
      0 => {
        // anonymous: just has hash, construct anon Name
        Name::anon()
      },
      1 => {
        // str: parent, s, hash
        let parent_ptr = lean_ctor_get(ptr as *mut _, 0);
        let s_ptr = lean_ctor_get(ptr as *mut _, 1);
        // hash at field 2 is ignored - Rust recomputes it

        let parent = decode_ix_name(parent_ptr);
        let s_obj: &LeanStringObject = as_ref_unsafe(s_ptr.cast());
        let s = s_obj.as_string();

        Name::str(parent, s)
      },
      2 => {
        // num: parent, i, hash
        let parent_ptr = lean_ctor_get(ptr as *mut _, 0);
        let i_ptr = lean_ctor_get(ptr as *mut _, 1);
        // hash at field 2 is ignored

        let parent = decode_ix_name(parent_ptr);
        let i = Nat::from_ptr(i_ptr);

        Name::num(parent, i)
      },
      _ => panic!("Invalid Ix.Name tag: {}", tag),
    }
  }
}

/// Decode Array of Names from Lean pointer.
pub fn decode_name_array(ptr: *const c_void) -> Vec<Name> {
  let arr_obj: &crate::lean::array::LeanArrayObject = as_ref_unsafe(ptr.cast());
  arr_obj.data().iter().map(|&p| decode_ix_name(p)).collect()
}

/// Round-trip an Ix.Name: decode from Lean, re-encode via LeanBuildCache.
#[unsafe(no_mangle)]
pub extern "C" fn rs_roundtrip_ix_name(name_ptr: *const c_void) -> *mut c_void {
  let name = decode_ix_name(name_ptr);
  let mut cache = LeanBuildCache::new();
  build_name(&mut cache, &name)
}
