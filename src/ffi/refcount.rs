//! Reference counting and ownership tests for the typed lean-ffi API.
//!
//! Gated behind the `test-ffi` Cargo feature. These FFI functions exercise
//! ownership semantics that would catch double-free, use-after-free, and
//! refcount leaks:
//!
//! - Borrowed params (`@&`): must NOT lean_dec on drop
//! - to_owned_ref: must lean_inc correctly
//! - Clone on LeanOwned: must lean_inc correctly
//! - Owned drop: must lean_dec correctly
//! - Nested field access from borrowed refs
//! - Cache deduplication via Clone
//! - Repeated alloc/dealloc cycles

use std::thread;

use lean_ffi::LeanShared;
use lean_ffi::nat::Nat;
use lean_ffi::object::{
  LeanArray, LeanBorrowed, LeanList, LeanOwned, LeanRef, LeanString,
};

use crate::ffi::builder::LeanBuildCache;
use crate::lean::{LeanIxExpr, LeanIxLevel, LeanIxName};

// =============================================================================
// Borrow-to-owned: take @&, return owned copy via to_owned_ref
// =============================================================================

/// Take a borrowed Ix.Name, convert to owned via to_owned_ref, return it.
#[unsafe(no_mangle)]
pub extern "C" fn rs_refcount_borrow_to_owned_name(
  name: LeanIxName<LeanBorrowed<'_>>,
) -> LeanIxName<LeanOwned> {
  LeanIxName::new(name.inner().to_owned_ref())
}

/// Same for Ix.Level.
#[unsafe(no_mangle)]
pub extern "C" fn rs_refcount_borrow_to_owned_level(
  level: LeanIxLevel<LeanBorrowed<'_>>,
) -> LeanIxLevel<LeanOwned> {
  LeanIxLevel::new(level.inner().to_owned_ref())
}

/// Same for Ix.Expr.
#[unsafe(no_mangle)]
pub extern "C" fn rs_refcount_borrow_to_owned_expr(
  expr: LeanIxExpr<LeanBorrowed<'_>>,
) -> LeanIxExpr<LeanOwned> {
  LeanIxExpr::new(expr.inner().to_owned_ref())
}

// =============================================================================
// Multiple borrows from same parent
// =============================================================================

/// Read all fields of an Ix.Name.str twice, return concatenated strings.
/// Tests that multiple .get() calls from the same ctor don't corrupt.
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

// =============================================================================
// Deep borrow traversal
// =============================================================================

/// Count nodes in an Ix.Expr tree via borrowed traversal. Returns count as Nat.
#[unsafe(no_mangle)]
pub extern "C" fn rs_refcount_deep_borrow_expr(
  expr: LeanIxExpr<LeanBorrowed<'_>>,
) -> LeanOwned {
  fn count_nodes(expr: &LeanIxExpr<impl LeanRef>) -> u64 {
    let ctor = expr.as_ctor();
    match ctor.tag() {
      5 => {
        // app: fn, arg, hash
        let fn_expr = LeanIxExpr(ctor.get(0));
        let arg_expr = LeanIxExpr(ctor.get(1));
        1 + count_nodes(&fn_expr) + count_nodes(&arg_expr)
      },
      _ => 1,
    }
  }
  Nat::from(count_nodes(&expr)).to_lean().into()
}

// =============================================================================
// Owned drop: take owned, extract data, verify drop doesn't crash
// =============================================================================

/// Take an owned Array of Names, decode them all, return count.
/// The owned array is dropped at the end → lean_dec_ref on each element.
#[unsafe(no_mangle)]
pub extern "C" fn rs_refcount_owned_array_drop(
  arr: LeanArray<LeanOwned>,
) -> LeanOwned {
  let count = arr.len();
  for i in 0..count {
    let _ = LeanIxName(arr.get(i)).decode();
  }
  Nat::from(count as u64).to_lean().into()
}

/// Take an owned List of Exprs, consume and count.
#[unsafe(no_mangle)]
pub extern "C" fn rs_refcount_owned_list_drop(
  list: LeanList<LeanOwned>,
) -> LeanOwned {
  let mut count: u64 = 0;
  for elem in list.iter() {
    let _ = LeanIxExpr(elem).decode();
    count += 1;
  }
  Nat::from(count).to_lean().into()
}

// =============================================================================
// Clone then drop: clone an owned value, decode both independently
// =============================================================================

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
  // owned1 and owned2 both dropped → two lean_dec calls
  Nat::from(if decoded1 == decoded2 { 1u64 } else { 0u64 }).to_lean().into()
}

// =============================================================================
// Roundtrip loop: stresses alloc/dealloc cycles
// =============================================================================

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
    // lean_name dropped here → lean_dec_ref
  }
  let mut cache = LeanBuildCache::new();
  LeanIxName::build(&mut cache, &rust_name)
}

// =============================================================================
// Nested collection traversal with borrows
// =============================================================================

/// Take a borrowed Array of (Name × Level) pairs, decode all, return count.
#[unsafe(no_mangle)]
pub extern "C" fn rs_refcount_nested_borrow(
  arr: LeanArray<LeanBorrowed<'_>>,
) -> LeanOwned {
  let mut count: u64 = 0;
  for elem in arr.iter() {
    let pair = elem.as_ctor();
    let _name = LeanIxName(pair.get(0)).decode();
    let _level = LeanIxLevel(pair.get(1)).decode();
    count += 1;
  }
  Nat::from(count).to_lean().into()
}

// =============================================================================
// Cache deduplication: build same subterm multiple times
// =============================================================================

/// Build an array of N copies of the same Name from cache.
/// The LeanBuildCache deduplicates via Clone (lean_inc).
/// Each element's lean_dec on drop must work correctly.
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

// =============================================================================
// Persistent object handling
// =============================================================================

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

// =============================================================================
// String lifecycle
// =============================================================================

/// Build a new string from borrowed input. The output is independent.
#[unsafe(no_mangle)]
pub extern "C" fn rs_refcount_string_lifecycle(
  s: LeanString<LeanBorrowed<'_>>,
) -> LeanString<LeanOwned> {
  let rust_string = s.to_string();
  let reversed: String = rust_string.chars().rev().collect();
  LeanString::new(&reversed)
}

// =============================================================================
// Build and immediately discard: stress alloc then drop
// =============================================================================

/// Build N Lean Names from a borrowed input, immediately drop each.
/// Returns the input unchanged. Stresses alloc/dealloc without leaking.
#[unsafe(no_mangle)]
pub extern "C" fn rs_refcount_alloc_drop_loop(
  name: LeanIxName<LeanBorrowed<'_>>,
  n: usize,
) -> LeanIxName<LeanOwned> {
  let decoded = name.decode();
  for _ in 0..n {
    let mut cache = LeanBuildCache::new();
    let _lean_name = LeanIxName::build(&mut cache, &decoded);
    // _lean_name dropped immediately
  }
  let mut cache = LeanBuildCache::new();
  LeanIxName::build(&mut cache, &decoded)
}

// =============================================================================
// Array build and element extraction
// =============================================================================

/// Build an array of Levels, extract each via borrowed access, rebuild.
/// Tests that borrowed array elements survive while array is alive.
#[unsafe(no_mangle)]
pub extern "C" fn rs_refcount_array_element_borrow(
  arr: LeanArray<LeanBorrowed<'_>>,
) -> LeanArray<LeanOwned> {
  let len = arr.len();
  let out = LeanArray::alloc(len);
  for i in 0..len {
    let borrowed_elem = arr.get(i);
    let level = LeanIxLevel(borrowed_elem).decode();
    let mut cache = LeanBuildCache::new();
    out.set(i, LeanIxLevel::build(&mut cache, &level));
  }
  out
}

// =============================================================================
// Multi-threaded tests using LeanShared on ix domain types
// =============================================================================

/// Mark an array of Ix.Names as MT, decode in parallel from N threads.
/// Each thread decodes all names and returns the count.
/// Tests LeanShared + lean_mark_mt on complex Ix object graphs.
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
  Nat::from(total).to_lean().into()
}

/// Mark an array of Ix.Exprs as MT, decode in parallel from N threads.
/// Each thread decodes all exprs and counts nodes.
#[unsafe(no_mangle)]
pub extern "C" fn rs_mt_parallel_decode_exprs(
  arr: LeanArray<LeanBorrowed<'_>>,
  n_threads: usize,
) -> LeanOwned {
  fn count_expr_nodes(expr: &LeanIxExpr<impl LeanRef>) -> u64 {
    let ctor = expr.as_ctor();
    match ctor.tag() {
      5 => {
        // app
        1 + count_expr_nodes(&LeanIxExpr(ctor.get(0)))
          + count_expr_nodes(&LeanIxExpr(ctor.get(1)))
      },
      _ => 1,
    }
  }

  let shared = LeanShared::new(arr.inner().to_owned_ref());

  let handles: Vec<_> = (0..n_threads)
    .map(|_| {
      let shared_clone = shared.clone();
      thread::spawn(move || {
        let borrowed_arr = shared_clone.borrow().as_array();
        let mut total: u64 = 0;
        for elem in borrowed_arr.iter() {
          total += count_expr_nodes(&LeanIxExpr(elem));
        }
        total
      })
    })
    .collect();

  let total: u64 = handles.into_iter().map(|h| h.join().unwrap()).sum();
  Nat::from(total).to_lean().into()
}

/// Parallel roundtrip: mark array of Names as MT, each thread decodes
/// all names and rebuilds them. Returns an array of rebuilt names from
/// one thread. Tests that building new Lean objects while reading
/// MT-marked objects works correctly.
#[unsafe(no_mangle)]
pub extern "C" fn rs_mt_parallel_roundtrip_names(
  arr: LeanArray<LeanBorrowed<'_>>,
  n_threads: usize,
) -> LeanArray<LeanOwned> {
  use crate::ix::env::Name;

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

  // Collect results from all threads, use the first one to rebuild
  let all_results: Vec<Vec<Name>> =
    handles.into_iter().map(|h| h.join().unwrap()).collect();

  // Verify all threads decoded the same values
  let first = &all_results[0];
  for result in &all_results[1..] {
    assert_eq!(first, result, "MT decode inconsistency");
  }

  // Rebuild from the first thread's results
  let mut cache = LeanBuildCache::new();
  let out = LeanArray::alloc(first.len());
  for (i, name) in first.iter().enumerate() {
    out.set(i, LeanIxName::build(&mut cache, name));
  }
  out
}

/// Stress test: clone/drop LeanShared rapidly from many threads
/// on a complex Ix.Expr graph.
#[unsafe(no_mangle)]
pub extern "C" fn rs_mt_shared_expr_stress(
  expr: LeanIxExpr<LeanBorrowed<'_>>,
  n_threads: usize,
  clones_per_thread: usize,
) -> LeanOwned {
  let shared = LeanShared::new(expr.inner().to_owned_ref());

  let handles: Vec<_> = (0..n_threads)
    .map(|_| {
      let shared_clone = shared.clone();
      thread::spawn(move || {
        for _ in 0..clones_per_thread {
          let tmp = shared_clone.clone();
          // Borrow and read tag to ensure the object is valid
          let _ = tmp.borrow().as_ctor().tag();
          // tmp dropped → atomic lean_dec
        }
        1u64
      })
    })
    .collect();

  let total: u64 = handles.into_iter().map(|h| h.join().unwrap()).sum();
  Nat::from(total).to_lean().into()
}
