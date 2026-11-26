/-
  AssocList / HashMap FFI roundtrip tests.
  Pattern: Lean value → Rust (decode) → Rust (re-encode via C API) → Lean value → compare
-/
module

public import LSpec
public import Tests.Gen.Basic
public import Std.Data.HashMap

open LSpec LSpec.Prop Gen

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

def assocListTests : LSpec.Spec := do
  let emptyList : AssocList Nat (fun _ => Nat) := .nil
  let single : AssocList Nat (fun _ => Nat) := .cons 1 42 .nil
  let double : AssocList Nat (fun _ => Nat) := .cons 2 99 (.cons 1 42 .nil)
  itBool "AssocList nil" (assocListEq (roundtripAssocListNatNat emptyList) emptyList)
  itBool "AssocList single" (assocListEq (roundtripAssocListNatNat single) single)
  itBool "AssocList double" (assocListEq (roundtripAssocListNatNat double) double)

def hashMapTests : LSpec.Spec := do
  itBool "HashMap empty" (hashMapEq (roundtripHashMapNatNat {}) {})
  itBool "HashMap single" (hashMapEq (roundtripHashMapNatNat (({} : Std.HashMap Nat Nat).insert 1 42)) (({} : Std.HashMap Nat Nat).insert 1 42))

def dHashMapRawTests : LSpec.Spec := do
  let emptyMap : DHashMapRaw Nat (fun _ => Nat) := {}
  let single : DHashMapRaw Nat (fun _ => Nat) := ({} : DHashMapRaw Nat (fun _ => Nat)).insert 1 42
  let double : DHashMapRaw Nat (fun _ => Nat) := (({} : DHashMapRaw Nat (fun _ => Nat)).insert 1 42).insert 2 99
  itBool "DHashMapRaw empty" (dHashMapRawEq (roundtripDHashMapRawNatNat emptyMap) emptyMap)
  itBool "DHashMapRaw single" (dHashMapRawEq (roundtripDHashMapRawNatNat single) single)
  itBool "DHashMapRaw double" (dHashMapRawEq (roundtripDHashMapRawNatNat double) double)

/-! ## Mixed-width scalar records

Every scalar width, declared out of runtime order. Lean lays the fields out
as `name count | size | wide | word | half | flag small`. -/

structure MixedScalars where
  flag : Bool
  wide : UInt64
  name : String
  small : UInt8
  half : UInt16
  word : UInt32
  size : USize
  count : Nat
  deriving BEq, Repr, Inhabited

/-- The fields as Rust reads them: the name, then the numbers in declaration
order. -/
@[extern "rs_mixed_scalars_fields"]
opaque mixedScalarsFields : @& MixedScalars → String × Array Nat

@[extern "rs_roundtrip_mixed_scalars"]
opaque roundtripMixedScalars : @& MixedScalars → MixedScalars

def mixedScalarsTests : LSpec.Spec := do
  let m : MixedScalars :=
    ⟨true, 0x0102030405060708, "mixed", 0xab, 0xcdef, 0x89abcdef, 12345, 678⟩
  let z : MixedScalars := ⟨false, 0, "", 0, 0, 0, 0, 0⟩
  itBool "MixedScalars fields read from Lean" (mixedScalarsFields m ==
    ("mixed", #[1, 0x0102030405060708, 0xab, 0xcdef, 0x89abcdef, 12345, 678]))
  itBool "MixedScalars zero fields read from Lean" (mixedScalarsFields z ==
    ("", #[0, 0, 0, 0, 0, 0, 0]))
  itBool "MixedScalars roundtrip" (roundtripMixedScalars m == m)
  itBool "MixedScalars zero roundtrip" (roundtripMixedScalars z == z)

/-! ## Test Suite -/

set_option compiler.extract_closed false in
public def suiteWith (cfg : LSpec.Prop.PropertyConfig := {}) : Spec := do
  assocListTests
  hashMapTests
  dHashMapRawTests
  mixedScalarsTests
  propWith "HashMap Nat Nat roundtrip" cfg fun (m : Std.HashMap Nat Nat) =>
    hashMapEq (roundtripHashMapNatNat m) m
  propWith "DHashMapRaw Nat Nat roundtrip" cfg fun (m : Std.HashMap Nat Nat) =>
    let raw := m.toList.foldl (init := ({} : DHashMapRaw Nat (fun _ => Nat))) fun (acc : DHashMapRaw Nat (fun _ => Nat)) (k, v) => acc.insert k v
    dHashMapRawEq (roundtripDHashMapRawNatNat raw) raw

public def suite : Spec := suiteWith {}

end Tests.FFI.Basic
