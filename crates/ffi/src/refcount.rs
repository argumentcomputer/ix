//! Reference counting and ownership tests for the typed lean-ffi API.
//!
//! Gated behind the `test-ffi` Cargo feature.

use std::thread;

use lean_ffi::LeanShared;
use lean_ffi::nat::Nat;
use lean_ffi::object::LeanNat;
use lean_ffi::object::{
  LeanArray, LeanBorrowed, LeanOwned, LeanRef, LeanString,
};

use crate::lean::{LeanBuildCache, LeanIxName};

/// Take a borrowed Ix.Name, convert to owned via to_owned_ref, return it.
#[unsafe(no_mangle)]
pub extern "C" fn rs_refcount_borrow_to_owned_name(
  name: LeanIxName<LeanBorrowed<'_>>,
) -> LeanIxName<LeanOwned> {
  LeanIxName::new(name.inner().to_owned_ref())
}

/// Read all fields of an Ix.Name.str twice, return concatenated strings.
#[unsafe(no_mangle)]
pub extern "C" fn rs_refcount_multi_borrow_name(
  name: LeanIxName<LeanBorrowed<'_>>,
) -> LeanString<LeanOwned> {
  let ctor = name.as_ctor();
  let _parent = ctor.get(0);
  let s = ctor.get(1);
  let _hash = ctor.get(2);
  let s2 = ctor.get(1);
  let result = format!("{}|{}", s.as_string(), s2.as_string());
  LeanString::new(&result)
}

/// Take an owned Array of Names, decode them all, return count.
#[unsafe(no_mangle)]
pub extern "C" fn rs_refcount_owned_array_drop(
  arr: LeanArray<LeanOwned>,
) -> LeanOwned {
  let count = arr.len();
  for i in 0..count {
    let _ = LeanIxName(arr.get(i)).decode();
  }
  LeanNat::from_nat(&Nat::from(count as u64)).into()
}

/// Take a borrowed Name, make two owned clones, decode both,
/// verify they produce the same result. Returns 1 if equal, 0 otherwise.
#[unsafe(no_mangle)]
pub extern "C" fn rs_refcount_clone_and_compare(
  name: LeanIxName<LeanBorrowed<'_>>,
) -> LeanOwned {
  let owned1 = LeanIxName::new(name.inner().to_owned_ref());
  let owned2 = owned1.clone();
  let decoded1 = owned1.decode();
  let decoded2 = owned2.decode();
  LeanNat::from_nat(&Nat::from(if decoded1 == decoded2 { 1u64 } else { 0u64 }))
    .into()
}

/// Roundtrip an Ix.Name N times. Each iteration: decode → build → drop old.
#[unsafe(no_mangle)]
pub extern "C" fn rs_refcount_roundtrip_loop(
  name: LeanIxName<LeanBorrowed<'_>>,
  n: usize,
) -> LeanIxName<LeanOwned> {
  let mut rust_name = name.decode();
  for _ in 0..n {
    let mut cache = LeanBuildCache::new();
    let lean_name = LeanIxName::build(&mut cache, &rust_name);
    rust_name = lean_name.decode();
  }
  let mut cache = LeanBuildCache::new();
  LeanIxName::build(&mut cache, &rust_name)
}

/// Build an array of N copies of the same Name from cache.
#[unsafe(no_mangle)]
pub extern "C" fn rs_refcount_cache_dedup(
  name: LeanIxName<LeanBorrowed<'_>>,
  n: usize,
) -> LeanArray<LeanOwned> {
  let decoded = name.decode();
  let mut cache = LeanBuildCache::new();
  let arr = LeanArray::alloc(n);
  for i in 0..n {
    let lean_name = LeanIxName::build(&mut cache, &decoded);
    arr.set(i, lean_name);
  }
  arr
}

/// Check if a borrowed Name is persistent (m_rc == 0).
#[unsafe(no_mangle)]
pub extern "C" fn rs_refcount_is_persistent(
  name: LeanIxName<LeanBorrowed<'_>>,
) -> u8 {
  if name.inner().is_persistent() { 1 } else { 0 }
}

/// Decode a persistent Name and rebuild it.
#[unsafe(no_mangle)]
pub extern "C" fn rs_refcount_persistent_roundtrip(
  name: LeanIxName<LeanBorrowed<'_>>,
) -> LeanIxName<LeanOwned> {
  let decoded = name.decode();
  let mut cache = LeanBuildCache::new();
  LeanIxName::build(&mut cache, &decoded)
}

/// Build a new string from borrowed input. The output is independent.
#[unsafe(no_mangle)]
pub extern "C" fn rs_refcount_string_lifecycle(
  s: LeanString<LeanBorrowed<'_>>,
) -> LeanString<LeanOwned> {
  let rust_string = s.to_string();
  let reversed: String = rust_string.chars().rev().collect();
  LeanString::new(&reversed)
}

/// Build N Lean Names from a borrowed input, immediately drop each.
#[unsafe(no_mangle)]
pub extern "C" fn rs_refcount_alloc_drop_loop(
  name: LeanIxName<LeanBorrowed<'_>>,
  n: usize,
) -> LeanIxName<LeanOwned> {
  let decoded = name.decode();
  for _ in 0..n {
    let mut cache = LeanBuildCache::new();
    let _lean_name = LeanIxName::build(&mut cache, &decoded);
  }
  let mut cache = LeanBuildCache::new();
  LeanIxName::build(&mut cache, &decoded)
}

/// Mark an array of Ix.Names as MT, decode in parallel from N threads.
#[unsafe(no_mangle)]
pub extern "C" fn rs_mt_parallel_decode_names(
  arr: LeanArray<LeanBorrowed<'_>>,
  n_threads: usize,
) -> LeanOwned {
  let shared = LeanShared::new(arr.inner().to_owned_ref());

  let handles: Vec<_> = (0..n_threads)
    .map(|_| {
      let shared_clone = shared.clone();
      thread::spawn(move || {
        let borrowed_arr = shared_clone.borrow().as_array();
        let mut count: u64 = 0;
        for elem in borrowed_arr.iter() {
          let _name = LeanIxName(elem).decode();
          count += 1;
        }
        count
      })
    })
    .collect();

  let total: u64 = handles.into_iter().map(|h| h.join().unwrap()).sum();
  LeanNat::from_nat(&Nat::from(total)).into()
}

/// Parallel roundtrip: mark array of Names as MT, each thread decodes
/// all names and rebuilds them.
#[unsafe(no_mangle)]
pub extern "C" fn rs_mt_parallel_roundtrip_names(
  arr: LeanArray<LeanBorrowed<'_>>,
  n_threads: usize,
) -> LeanArray<LeanOwned> {
  use ix_common::env::Name;

  let shared = LeanShared::new(arr.inner().to_owned_ref());
  let len = arr.len();

  let handles: Vec<_> = (0..n_threads)
    .map(|_| {
      let shared_clone = shared.clone();
      thread::spawn(move || {
        let borrowed_arr = shared_clone.borrow().as_array();
        let mut decoded: Vec<Name> = Vec::with_capacity(len);
        for elem in borrowed_arr.iter() {
          decoded.push(LeanIxName(elem).decode());
        }
        decoded
      })
    })
    .collect();

  let all_results: Vec<Vec<Name>> =
    handles.into_iter().map(|h| h.join().unwrap()).collect();

  let first = &all_results[0];
  for result in &all_results[1..] {
    assert_eq!(first, result, "MT decode inconsistency");
  }

  let mut cache = LeanBuildCache::new();
  let out = LeanArray::alloc(first.len());
  for (i, name) in first.iter().enumerate() {
    out.set(i, LeanIxName::build(&mut cache, name));
  }
  out
}
