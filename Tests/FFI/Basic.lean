/-
  AssocList / HashMap FFI roundtrip tests.
  Pattern: Lean value → Rust (decode) → Rust (re-encode via C API) → Lean value → compare
-/
module

public import LSpec
public import Tests.Gen.Basic
public import Std.Data.HashMap

open LSpec SlimCheck Gen

namespace Tests.FFI.Basic

/-! ## AssocList and HashMap roundtrips -/

-- Re-export the internal AssocList type for testing
abbrev AssocList := Std.DHashMap.Internal.AssocList

@[extern "rs_roundtrip_assoclist_nat_nat"]
opaque roundtripAssocListNatNat : @& AssocList Nat (fun _ => Nat) → AssocList Nat (fun _ => Nat)

-- DHashMap.Raw for testing the inner structure
abbrev DHashMapRaw := Std.DHashMap.Raw

@[extern "rs_roundtrip_dhashmap_raw_nat_nat"]
opaque roundtripDHashMapRawNatNat : @& DHashMapRaw Nat (fun _ => Nat) → DHashMapRaw Nat (fun _ => Nat)

@[extern "rs_roundtrip_hashmap_nat_nat"]
opaque roundtripHashMapNatNat : @& Std.HashMap Nat Nat → Std.HashMap Nat Nat

/-! ## Helper to compare HashMaps -/

def hashMapEq (m1 m2 : Std.HashMap Nat Nat) : Bool :=
  m1.size == m2.size && m1.toList.all fun (k, v) => m2.get? k == some v

def dHashMapRawEq (m1 m2 : DHashMapRaw Nat (fun _ => Nat)) : Bool :=
  m1.size == m2.size && m1.toList.all fun ⟨k, v⟩ => m2.get? k == some v

def assocListEq (l1 l2 : AssocList Nat (fun _ => Nat)) : Bool :=
  let toSimpleList (l : AssocList Nat (fun _ => Nat)) : List (Nat × Nat) :=
    l.toList.map fun ⟨k, v⟩ => (k, v)
  toSimpleList l1 == toSimpleList l2

def assocListTests : TestSeq :=
  let emptyList : AssocList Nat (fun _ => Nat) := .nil
  let single : AssocList Nat (fun _ => Nat) := .cons 1 42 .nil
  let double : AssocList Nat (fun _ => Nat) := .cons 2 99 (.cons 1 42 .nil)
  test "AssocList nil" (assocListEq (roundtripAssocListNatNat emptyList) emptyList) ++
  test "AssocList single" (assocListEq (roundtripAssocListNatNat single) single) ++
  test "AssocList double" (assocListEq (roundtripAssocListNatNat double) double)

def hashMapTests : TestSeq :=
  test "HashMap empty" (hashMapEq (roundtripHashMapNatNat {}) {}) ++
  test "HashMap single" (hashMapEq (roundtripHashMapNatNat (({} : Std.HashMap Nat Nat).insert 1 42)) (({} : Std.HashMap Nat Nat).insert 1 42))

def dHashMapRawTests : TestSeq :=
  let emptyMap : DHashMapRaw Nat (fun _ => Nat) := {}
  let single : DHashMapRaw Nat (fun _ => Nat) := ({} : DHashMapRaw Nat (fun _ => Nat)).insert 1 42
  let double : DHashMapRaw Nat (fun _ => Nat) := (({} : DHashMapRaw Nat (fun _ => Nat)).insert 1 42).insert 2 99
  test "DHashMapRaw empty" (dHashMapRawEq (roundtripDHashMapRawNatNat emptyMap) emptyMap) ++
  test "DHashMapRaw single" (dHashMapRawEq (roundtripDHashMapRawNatNat single) single) ++
  test "DHashMapRaw double" (dHashMapRawEq (roundtripDHashMapRawNatNat double) double)

/-! ## Test Suite -/

public def suite : List TestSeq := [
  assocListTests,
  hashMapTests,
  dHashMapRawTests,
  checkIO "HashMap Nat Nat roundtrip" (∀ m : Std.HashMap Nat Nat, hashMapEq (roundtripHashMapNatNat m) m),
  checkIO "DHashMapRaw Nat Nat roundtrip" (∀ m : Std.HashMap Nat Nat,
    let raw := m.toList.foldl (init := ({} : DHashMapRaw Nat (fun _ => Nat))) fun acc (k, v) => acc.insert k v
    dHashMapRawEq (roundtripDHashMapRawNatNat raw) raw),
]

end Tests.FFI.Basic
