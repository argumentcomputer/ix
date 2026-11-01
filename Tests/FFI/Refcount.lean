/-
  Reference counting and ownership tests for the typed lean-ffi API.
  Gated behind the `test-ffi` Cargo feature (included by default,
  stripped in non-test builds; included via the `ix_rs_test` Lake target).

  These tests exercise ownership semantics that catch double-free,
  use-after-free, and refcount leaks by calling Rust FFI functions that:

  - Convert borrowed → owned via to_owned_ref (lean_inc)
  - Clone owned values then drop both (two lean_dec calls)
  - Take owned params and drop them (lean_dec on complex structures)
  - Traverse deeply nested borrows without inc_ref
  - Build from cache (clone-based dedup) then drop the array
  - Repeatedly alloc and immediately drop (stress alloc/dealloc)
  - Handle persistent objects (m_rc == 0, lean_inc/lean_dec are no-ops)
  - Mark objects as multi-threaded and decode from parallel threads
-/
module

public import LSpec
public import Tests.Gen.Ix
public import Ix.Environment
public import Ix.Address

open LSpec SlimCheck Gen
open Tests.Gen.Ix

namespace Tests.FFI.Refcount

/-! ## FFI declarations — gated behind test-ffi Cargo feature -/

-- Borrow-to-owned: take @&, return owned copy via to_owned_ref
@[extern "rs_refcount_borrow_to_owned_name"]
opaque borrowToOwnedName : @& Ix.Name → Ix.Name

-- Multiple borrows from same parent
@[extern "rs_refcount_multi_borrow_name"]
opaque multiBorrowName : @& Ix.Name → String

-- Owned drop (NOT @&, Rust takes ownership and drops)
@[extern "rs_refcount_owned_array_drop"]
opaque ownedArrayDrop : Array Ix.Name → Nat

-- Clone and compare
@[extern "rs_refcount_clone_and_compare"]
opaque cloneAndCompare : @& Ix.Name → Nat

-- Roundtrip loop (N decode/rebuild cycles)
@[extern "rs_refcount_roundtrip_loop"]
opaque roundtripLoop : @& Ix.Name → USize → Ix.Name

-- Cache dedup: build N copies from cache
@[extern "rs_refcount_cache_dedup"]
opaque cacheDedup : @& Ix.Name → USize → Array Ix.Name

-- Persistent object checks
@[extern "rs_refcount_is_persistent"]
opaque isPersistent : @& Ix.Name → UInt8

@[extern "rs_refcount_persistent_roundtrip"]
opaque persistentRoundtrip : @& Ix.Name → Ix.Name

-- String lifecycle
@[extern "rs_refcount_string_lifecycle"]
opaque stringLifecycle : @& String → String

-- Alloc/drop stress loop
@[extern "rs_refcount_alloc_drop_loop"]
opaque allocDropLoop : @& Ix.Name → USize → Ix.Name

-- Multi-threaded tests using LeanShared on ix domain types
@[extern "rs_mt_parallel_decode_names"]
opaque mtParallelDecodeNames : @& Array Ix.Name → USize → Nat

@[extern "rs_mt_parallel_roundtrip_names"]
opaque mtParallelRoundtripNames : @& Array Ix.Name → USize → Array Ix.Name

/-! ## Test data -/

private def testAnon : Ix.Name := Ix.Name.mkAnon
private def testStr : Ix.Name := Ix.Name.mkStr (Ix.Name.mkStr Ix.Name.mkAnon "foo") "bar"
private def testNum : Ix.Name := Ix.Name.mkNat (Ix.Name.mkStr Ix.Name.mkAnon "x") 42

-- Module-level definitions become persistent (m_rc == 0) after initialization
private def persistentName : Ix.Name := Ix.Name.mkStr Ix.Name.mkAnon "persistent"

/-! ## Borrow-to-owned tests
    Verifies that to_owned_ref (lean_inc) produces a valid owned handle.
    A refcount bug here would manifest as use-after-free or double-free. -/

def borrowToOwnedTests : TestSeq :=
  test "borrow→owned Name anonymous" (borrowToOwnedName testAnon == testAnon) ++
  test "borrow→owned Name str" (borrowToOwnedName testStr == testStr) ++
  test "borrow→owned Name num" (borrowToOwnedName testNum == testNum)

/-! ## Multiple borrows from same object
    Verifies that reading fields multiple times from the same borrowed ctor
    doesn't corrupt data (no dangling pointer from intermediate borrow). -/

def multiBorrowTests : TestSeq :=
  let name := Ix.Name.mkStr Ix.Name.mkAnon "hello"
  test "multi-borrow Name str" (multiBorrowName name == "hello|hello")

/-! ## Owned drop tests
    Passes owned (NOT @&) arrays. Rust drops each element
    on scope exit. A missing drop leaks; an extra drop crashes. -/

def ownedDropTests : TestSeq :=
  let names := #[testAnon, testStr, testNum]
  test "owned array drop 3 names" (ownedArrayDrop names == 3) ++
  test "owned array drop empty" (ownedArrayDrop #[] == 0)

/-! ## Clone tests
    Makes two owned clones of a borrowed Name, decodes both.
    After decode, both clones are dropped → two lean_dec_ref calls.
    Would double-free if clone didn't lean_inc. -/

def cloneTests : TestSeq :=
  test "clone anonymous" (cloneAndCompare testAnon == 1) ++
  test "clone str name" (cloneAndCompare testStr == 1) ++
  test "clone num name" (cloneAndCompare testNum == 1)

/-! ## Roundtrip loop tests
    Each iteration: decode borrowed → build new owned → drop old → repeat.
    Stresses N alloc/dealloc cycles. Would crash on any refcount error. -/

def roundtripLoopTests : TestSeq :=
  test "roundtrip loop 1x" (roundtripLoop testStr 1 == testStr) ++
  test "roundtrip loop 5x" (roundtripLoop testStr 5 == testStr) ++
  test "roundtrip loop 20x" (roundtripLoop testStr 20 == testStr) ++
  test "roundtrip loop anon 10x" (roundtripLoop testAnon 10 == testAnon) ++
  test "roundtrip loop num 10x" (roundtripLoop testNum 10 == testNum)

/-! ## Persistent object tests
    Module-level defs have m_rc == 0. Refcount ops are no-ops.
    Verifies that the typed API handles these correctly. -/

def persistentTests : TestSeq :=
  test "persistent name is_persistent" (isPersistent persistentName == 1) ++
  test "persistent roundtrip" (persistentRoundtrip persistentName == persistentName)

/-! ## Cache dedup tests
    Builds N copies of the same Name via LeanBuildCache, which clones
    cached entries (incrementing refcount). Dropping the array decrements
    each copy. Would crash if clone refcount was wrong. -/

def cacheDedupTests : TestSeq :=
  let duped := cacheDedup testStr 5
  test "cache dedup size 5" (duped.size == 5) ++
  test "cache dedup all equal" (duped.all (· == testStr)) ++
  let duped20 := cacheDedup testNum 20
  test "cache dedup size 20" (duped20.size == 20 && duped20.all (· == testNum))

/-! ## String lifecycle tests -/

def stringTests : TestSeq :=
  test "string lifecycle" (stringLifecycle "hello" == "olleh") ++
  test "string lifecycle empty" (stringLifecycle "" == "") ++
  test "string lifecycle unicode" (stringLifecycle "café" == "éfac")

/-! ## Alloc/drop stress tests
    Builds and immediately drops N Lean objects in a loop. -/

def allocDropTests : TestSeq :=
  test "alloc/drop 100x" (allocDropLoop testStr 100 == testStr) ++
  test "alloc/drop 1000x" (allocDropLoop testNum 1000 == testNum)

/-! ## Multi-threaded LeanShared tests
    These exercise lean_mark_mt + atomic refcounting on ix domain types
    across real OS threads. A refcount bug would cause SIGSEGV or assertion failure. -/

def mtTests : TestSeq :=
  let names := #[testAnon, testStr, testNum]
  -- Parallel decode: N threads × 3 names each
  test "MT parallel decode names 4 threads" (mtParallelDecodeNames names 4 == 12) ++
  test "MT parallel decode names 1 thread" (mtParallelDecodeNames names 1 == 3) ++
  test "MT parallel decode names empty" (mtParallelDecodeNames #[] 4 == 0) ++
  -- Parallel roundtrip: decode and rebuild from multiple threads
  test "MT parallel roundtrip names" (mtParallelRoundtripNames names 4 == names) ++
  test "MT parallel roundtrip empty" (mtParallelRoundtripNames #[] 4 == #[])

/-! ## Property tests -/

def propertyTests : TestSeq :=
  checkIO "borrow→owned Name" (∀ n : Ix.Name, borrowToOwnedName n == n) ++
  checkIO "clone always equal" (∀ n : Ix.Name, cloneAndCompare n == 1) ++
  checkIO "roundtrip loop 3x" (∀ n : Ix.Name, roundtripLoop n 3 == n)

/-! ## Test Suite -/

public def suite : List TestSeq := [
  borrowToOwnedTests,
  multiBorrowTests,
  ownedDropTests,
  cloneTests,
  roundtripLoopTests,
  persistentTests,
  cacheDedupTests,
  stringTests,
  allocDropTests,
  mtTests,
  propertyTests,
]

end Tests.FFI.Refcount
