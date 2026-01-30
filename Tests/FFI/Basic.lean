/-
  Basic type FFI roundtrip tests.
  Pattern: Lean value → Rust (decode) → Rust (re-encode via C API) → Lean value → compare
-/

import LSpec
import Tests.Gen.Basic
import Std.Data.HashMap

open LSpec SlimCheck Gen

namespace Tests.FFI.Basic

/-! ## FFI declarations for round-trip tests -/

/-- Round-trip a Nat through Rust: decode then re-encode -/
@[extern "rs_roundtrip_nat"]
opaque roundtripNat : @& Nat → Nat

/-- Round-trip a String through Rust -/
@[extern "rs_roundtrip_string"]
opaque roundtripString : @& String → String

/-- Round-trip a List Nat through Rust -/
@[extern "rs_roundtrip_list_nat"]
opaque roundtripListNat : @& List Nat → List Nat

/-- Round-trip an Array Nat through Rust -/
@[extern "rs_roundtrip_array_nat"]
opaque roundtripArrayNat : @& Array Nat → Array Nat

/-- Round-trip a ByteArray through Rust -/
@[extern "rs_roundtrip_bytearray"]
opaque roundtripByteArray : @& ByteArray → ByteArray

@[extern "rs_roundtrip_bool"]
opaque roundtripBool : @& Bool → Bool

@[extern "rs_roundtrip_point"]
opaque roundtripPoint : @& Point → Point

@[extern "rs_roundtrip_nat_tree"]
opaque roundtripNatTree : @& NatTree → NatTree

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

/-! ## Simple unit tests -/

def simpleTests : TestSeq :=
  test "Nat 0" (roundtripNat 0 == 0) ++
  test "Nat 42" (roundtripNat 42 == 42) ++
  test "Nat 1000" (roundtripNat 1000 == 1000) ++
  test "String empty" (roundtripString "" == "") ++
  test "String hello" (roundtripString "hello" == "hello") ++
  test "List []" (roundtripListNat [] == []) ++
  test "List [1,2,3]" (roundtripListNat [1, 2, 3] == [1, 2, 3]) ++
  test "Array #[]" (roundtripArrayNat #[] == #[]) ++
  test "Array #[1,2,3]" (roundtripArrayNat #[1, 2, 3] == #[1, 2, 3]) ++
  test "ByteArray empty" (roundtripByteArray ⟨#[]⟩ == ⟨#[]⟩) ++
  test "ByteArray [1,2,3]" (roundtripByteArray ⟨#[1, 2, 3]⟩ == ⟨#[1, 2, 3]⟩) ++
  test "Point (0, 0)" (roundtripPoint ⟨0, 0⟩ == ⟨0, 0⟩) ++
  test "Point (42, 99)" (roundtripPoint ⟨42, 99⟩ == ⟨42, 99⟩) ++
  test "NatTree leaf" (roundtripNatTree (.leaf 42) == .leaf 42) ++
  test "NatTree node" (roundtripNatTree (.node (.leaf 1) (.leaf 2)) == .node (.leaf 1) (.leaf 2))

/-! ## Specific edge case tests -/

def largeNatTests : TestSeq :=
  let testCases : List Nat := [0, 1, 255, 256, 65535, 65536, (2^32 - 1), 2^32,
    (2^63 - 1), 2^63, (2^64 - 1), 2^64, 2^64 + 1, 2^128, 2^256]
  testCases.foldl (init := .done) fun acc n =>
    acc ++ .individualIO s!"Nat {n}" (do
      let rt := roundtripNat n
      pure (rt == n, if rt == n then none else some s!"got {rt}")) .done

/-! ## Helper to compare HashMaps -/

def hashMapEq (m1 m2 : Std.HashMap Nat Nat) : Bool :=
  m1.size == m2.size && m1.toList.all fun (k, v) => m2.get? k == some v

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

def boolTests : TestSeq :=
  test "Bool true" (roundtripBool true == true) ++
  test "Bool false" (roundtripBool false == false)

/-! ## Test Suite -/

def suite : List TestSeq := [
  simpleTests,
  largeNatTests,
  assocListTests,
  hashMapTests,
  checkIO "Nat roundtrip" (∀ n : Nat, roundtripNat n == n),
  checkIO "String roundtrip" (∀ s : String, roundtripString s == s),
  checkIO "List Nat roundtrip" (∀ xs : List Nat, roundtripListNat xs == xs),
  checkIO "Array Nat roundtrip" (∀ arr : Array Nat, roundtripArrayNat arr == arr),
  checkIO "ByteArray roundtrip" (∀ ba : ByteArray, roundtripByteArray ba == ba),
  checkIO "Point roundtrip" (∀ p : Point, roundtripPoint p == p),
  checkIO "NatTree roundtrip" (∀ t : NatTree, roundtripNatTree t == t),
  checkIO "HashMap Nat Nat roundtrip" (∀ m : Std.HashMap Nat Nat, hashMapEq (roundtripHashMapNatNat m) m),
]

end Tests.FFI.Basic
