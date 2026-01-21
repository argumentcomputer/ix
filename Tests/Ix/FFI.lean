/-
  Unit tests for two-way FFI between Lean and Rust.
  Tests that Rust can correctly decode Lean objects AND build them back using the C API.

  Pattern: Lean value → Rust (decode) → Rust (re-encode via C API) → Lean value → compare
-/

import LSpec
import Tests.Common
import Std.Data.HashMap
import Ix.Environment
import Ix.Address

open LSpec SlimCheck Gen

namespace Tests.FFI

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

/-! ## Example struct for FFI testing -/

/-- A simple 2D point struct -/
structure Point where
  x : Nat
  y : Nat
deriving Repr, BEq, DecidableEq, Inhabited

@[extern "rs_roundtrip_point"]
opaque roundtripPoint : @& Point → Point

/-! ## Example inductive for FFI testing -/

/-- A simple binary tree of Nats -/
inductive NatTree where
  | leaf : Nat → NatTree
  | node : NatTree → NatTree → NatTree
deriving Repr, BEq, DecidableEq, Inhabited

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

/-! ## Generators -/

/-- Generate Nats across the full range: small, medium, large, and huge -/
def genNat : Gen Nat := do
  let choice ← choose Nat 0 100
  if choice < 50 then
    -- 50%: small nats (0-1000)
    choose Nat 0 1000
  else if choice < 75 then
    -- 25%: medium nats (up to 2^32)
    choose Nat 0 (2^32)
  else if choice < 90 then
    -- 15%: large nats (up to 2^64)
    choose Nat 0 (2^64)
  else
    -- 10%: huge nats (up to 2^256)
    choose Nat 0 (2^256)

def genSmallNat : Gen Nat := choose Nat 0 1000

def genString : Gen String := do
  let len ← choose Nat 0 100
  let chars ← Gen.listOf (choose Nat 32 126 >>= fun n => pure (Char.ofNat n))
  pure (String.ofList (chars.take len))

def genListNat : Gen (List Nat) := do
  let len ← choose Nat 0 20
  let mut result := []
  for _ in [:len] do
    result := (← genSmallNat) :: result
  pure result.reverse

def genArrayNat : Gen (Array Nat) := do
  let list ← genListNat
  pure list.toArray

def genByteArray : Gen ByteArray := do
  let len ← choose Nat 0 100
  let mut bytes := ByteArray.emptyWithCapacity len
  for _ in [:len] do
    let b ← choose Nat 0 255
    bytes := bytes.push b.toUInt8
  pure bytes

def genPoint : Gen Point := do
  let x ← genSmallNat
  let y ← genSmallNat
  pure ⟨x, y⟩

/-- Generate a random NatTree with bounded depth -/
def genNatTree : Nat → Gen NatTree
  | 0 => do
    let n ← genSmallNat
    pure (.leaf n)
  | maxDepth + 1 => do
    let choice ← choose Nat 0 2
    if choice == 0 then
      let n ← genSmallNat
      pure (.leaf n)
    else
      let left ← genNatTree maxDepth
      let right ← genNatTree maxDepth
      pure (.node left right)

def genHashMapNatNat : Gen (Std.HashMap Nat Nat) := do
  let len ← choose Nat 0 20
  let mut map : Std.HashMap Nat Nat := {}
  for _ in [:len] do
    let k ← genSmallNat
    let v ← genSmallNat
    map := map.insert k v
  pure map

/-! ## Shrinkable/SampleableExt instances -/

instance : Shrinkable Nat where
  shrink n := if n == 0 then [] else [n / 2]

instance : SampleableExt Nat := SampleableExt.mkSelfContained genNat

instance : Shrinkable (List Nat) where
  shrink xs := match xs with
    | [] => []
    | _ :: tail => [tail]

instance : SampleableExt (List Nat) := SampleableExt.mkSelfContained genListNat

instance : Shrinkable (Array Nat) where
  shrink arr := if arr.isEmpty then [] else [arr.pop]

instance : SampleableExt (Array Nat) := SampleableExt.mkSelfContained genArrayNat

instance : Repr ByteArray where
  reprPrec ba _ := s!"ByteArray#{ba.toList}"

instance : Shrinkable ByteArray where
  shrink ba := if ba.isEmpty then [] else [ba.extract 0 (ba.size - 1)]

instance : SampleableExt ByteArray := SampleableExt.mkSelfContained genByteArray

instance : Shrinkable String where
  shrink s := if s.isEmpty then [] else [s.dropRight 1]

instance : SampleableExt String := SampleableExt.mkSelfContained genString

instance : Shrinkable Point where
  shrink p := if p.x == 0 && p.y == 0 then [] else [⟨p.x / 2, p.y / 2⟩]

instance : SampleableExt Point := SampleableExt.mkSelfContained genPoint

instance : Shrinkable NatTree where
  shrink t := match t with
    | .leaf n => if n == 0 then [] else [.leaf (n / 2)]
    | .node l r => [l, r]

instance : SampleableExt NatTree := SampleableExt.mkSelfContained (genNatTree 4)

instance : Shrinkable (Std.HashMap Nat Nat) where
  shrink m :=
    let list := m.toList
    match list with
    | [] => []
    | _ :: tail => [Std.HashMap.ofList tail]

instance : SampleableExt (Std.HashMap Nat Nat) := SampleableExt.mkSelfContained genHashMapNatNat

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

/-! ## Ix type roundtrip FFI -/

@[extern "rs_roundtrip_ix_address"]
opaque roundtripIxAddress : @& Address → Address

@[extern "rs_roundtrip_ix_name"]
opaque roundtripIxName : @& Ix.Name → Ix.Name

@[extern "rs_roundtrip_ix_level"]
opaque roundtripIxLevel : @& Ix.Level → Ix.Level

@[extern "rs_roundtrip_ix_expr"]
opaque roundtripIxExpr : @& Ix.Expr → Ix.Expr

@[extern "rs_roundtrip_ix_int"]
opaque roundtripIxInt : @& Ix.Int → Ix.Int

@[extern "rs_roundtrip_ix_substring"]
opaque roundtripIxSubstring : @& Ix.Substring → Ix.Substring

@[extern "rs_roundtrip_ix_source_info"]
opaque roundtripIxSourceInfo : @& Ix.SourceInfo → Ix.SourceInfo

@[extern "rs_roundtrip_ix_syntax_preresolved"]
opaque roundtripIxSyntaxPreresolved : @& Ix.SyntaxPreresolved → Ix.SyntaxPreresolved

@[extern "rs_roundtrip_ix_syntax"]
opaque roundtripIxSyntax : @& Ix.Syntax → Ix.Syntax

@[extern "rs_roundtrip_ix_data_value"]
opaque roundtripIxDataValue : @& Ix.DataValue → Ix.DataValue

@[extern "rs_roundtrip_bool"]
opaque roundtripBool : @& Bool → Bool

-- Need Inhabited instance for opaque declaration
instance : Inhabited Ix.ConstantInfo where
  default := .axiomInfo { cnst := { name := default, levelParams := #[], type := default }, isUnsafe := false }

@[extern "rs_roundtrip_ix_constant_info"]
opaque roundtripIxConstantInfo : @& Ix.ConstantInfo → Ix.ConstantInfo

-- Need Inhabited instance for Environment opaque declaration
instance : Inhabited Ix.Environment where
  default := { consts := {} }

instance : Inhabited Ix.RawEnvironment where
  default := { consts := #[] }

-- Rust roundtrip returns RawEnvironment (array-based), not Environment (HashMap-based)
@[extern "rs_roundtrip_ix_raw_environment"]
opaque roundtripIxRawEnvironment : @& Ix.RawEnvironment → Ix.RawEnvironment

-- Roundtrip Environment by going through RawEnvironment
@[extern "rs_roundtrip_ix_environment"]
opaque roundtripIxEnvironmentRaw : @& Ix.Environment → Ix.RawEnvironment

def roundtripIxEnvironment (env : Ix.Environment) : Ix.Environment :=
  (roundtripIxEnvironmentRaw env).toEnvironment

/-! ## Ix type generators -/

def genIxName : Nat → Gen Ix.Name
  | 0 => pure Ix.Name.mkAnon
  | fuel + 1 => Gen.frequency #[
      (1, pure Ix.Name.mkAnon),
      (3, do
        let parent ← genIxName fuel
        let len ← choose Nat 1 10
        let chars ← Gen.listOf (choose Nat 97 122 >>= fun n => pure (Char.ofNat n))
        let s := String.ofList (chars.take len)
        pure (Ix.Name.mkStr parent s)),
      (2, do
        let parent ← genIxName fuel
        let n ← choose Nat 0 100
        pure (Ix.Name.mkNat parent n))
    ] (pure Ix.Name.mkAnon)

def genIxLevel : Nat → Gen Ix.Level
  | 0 => pure Ix.Level.mkZero
  | fuel + 1 => Gen.frequency #[
      (2, pure Ix.Level.mkZero),
      (3, do
        let x ← genIxLevel fuel
        pure (Ix.Level.mkSucc x)),
      (1, do
        let x ← genIxLevel (fuel / 2)
        let y ← genIxLevel (fuel / 2)
        pure (Ix.Level.mkMax x y)),
      (1, do
        let x ← genIxLevel (fuel / 2)
        let y ← genIxLevel (fuel / 2)
        pure (Ix.Level.mkIMax x y)),
      (2, do
        let n ← genIxName 2
        pure (Ix.Level.mkParam n)),
      (1, do
        let n ← genIxName 2
        pure (Ix.Level.mkMvar n))
    ] (pure Ix.Level.mkZero)

def genIxExpr : Nat → Gen Ix.Expr
  | 0 => Gen.frequency #[
      (1, do let idx ← choose Nat 0 10; pure (Ix.Expr.mkBVar idx)),
      (1, do let u ← genIxLevel 2; pure (Ix.Expr.mkSort u))
    ] (pure (Ix.Expr.mkBVar 0))
  | fuel + 1 => Gen.frequency #[
      (2, do let idx ← choose Nat 0 10; pure (Ix.Expr.mkBVar idx)),
      (1, do let u ← genIxLevel 2; pure (Ix.Expr.mkSort u)),
      (2, do
        let n ← genIxName 2
        let us ← Gen.listOf (genIxLevel 2)
        pure (Ix.Expr.mkConst n us.toArray)),
      (3, do
        let f ← genIxExpr (fuel / 2)
        let a ← genIxExpr (fuel / 2)
        pure (Ix.Expr.mkApp f a)),
      (2, do
        let n ← genIxName 1
        let ty ← genIxExpr (fuel / 2)
        let body ← genIxExpr (fuel / 2)
        pure (Ix.Expr.mkLam n ty body .default)),
      (2, do
        let n ← genIxName 1
        let ty ← genIxExpr (fuel / 2)
        let body ← genIxExpr (fuel / 2)
        pure (Ix.Expr.mkForallE n ty body .default))
    ] (pure (Ix.Expr.mkBVar 0))

instance : Shrinkable Ix.Name where
  shrink n := match n with
    | .anonymous _ => []
    | .str p _ _ => [p]
    | .num p _ _ => [p]

instance : SampleableExt Ix.Name := SampleableExt.mkSelfContained (genIxName 3)

instance : Shrinkable Ix.Level where
  shrink l := match l with
    | .zero _ => []
    | .succ x _ => [x]
    | .max x y _ => [x, y]
    | .imax x y _ => [x, y]
    | .param _ _ => [Ix.Level.mkZero]
    | .mvar _ _ => [Ix.Level.mkZero]

instance : SampleableExt Ix.Level := SampleableExt.mkSelfContained (genIxLevel 3)

instance : Shrinkable Ix.Expr where
  shrink e := match e with
    | .bvar _ _ => []
    | .fvar _ _ => [Ix.Expr.mkBVar 0]
    | .mvar _ _ => [Ix.Expr.mkBVar 0]
    | .sort _ _ => [Ix.Expr.mkBVar 0]
    | .const _ _ _ => [Ix.Expr.mkBVar 0]
    | .app f a _ => [f, a]
    | .lam _ ty body _ _ => [ty, body]
    | .forallE _ ty body _ _ => [ty, body]
    | .letE _ ty val body _ _ => [ty, val, body]
    | .lit _ _ => [Ix.Expr.mkBVar 0]
    | .mdata _ e _ => [e]
    | .proj _ _ e _ => [e]

instance : SampleableExt Ix.Expr := SampleableExt.mkSelfContained (genIxExpr 3)

/-! ## Ix type comparison by hash -/

def ixNameEq (a b : Ix.Name) : Bool := a.getHash == b.getHash
def ixLevelEq (a b : Ix.Level) : Bool := a.getHash == b.getHash
def ixExprEq (a b : Ix.Expr) : Bool := a.getHash == b.getHash

/-! ## Ix type unit tests -/

def ixAddressEq (a b : Address) : Bool := a.hash == b.hash

-- Simple unit test for debugging
def ixAddressTests : TestSeq :=
  let addr := Address.blake3 (ByteArray.mk #[1, 2, 3])
  test "Address roundtrip" (ixAddressEq (roundtripIxAddress addr) addr)

def ixNameTests : TestSeq :=
  let anon := Ix.Name.mkAnon
  let str1 := Ix.Name.mkStr anon "test"
  let str2 := Ix.Name.mkStr str1 "nested"
  let num1 := Ix.Name.mkNat anon 42
  test "Ix.Name anon" (ixNameEq (roundtripIxName anon) anon) ++
  test "Ix.Name str" (ixNameEq (roundtripIxName str1) str1) ++
  test "Ix.Name str.str" (ixNameEq (roundtripIxName str2) str2) ++
  test "Ix.Name num" (ixNameEq (roundtripIxName num1) num1)

def ixLevelTests : TestSeq :=
  let zero := Ix.Level.mkZero
  let one := Ix.Level.mkSucc zero
  let two := Ix.Level.mkSucc one
  let maxL := Ix.Level.mkMax one two
  let imaxL := Ix.Level.mkIMax one two
  let paramL := Ix.Level.mkParam (Ix.Name.mkStr Ix.Name.mkAnon "u")
  test "Ix.Level zero" (ixLevelEq (roundtripIxLevel zero) zero) ++
  test "Ix.Level succ" (ixLevelEq (roundtripIxLevel one) one) ++
  test "Ix.Level succ succ" (ixLevelEq (roundtripIxLevel two) two) ++
  test "Ix.Level max" (ixLevelEq (roundtripIxLevel maxL) maxL) ++
  test "Ix.Level imax" (ixLevelEq (roundtripIxLevel imaxL) imaxL) ++
  test "Ix.Level param" (ixLevelEq (roundtripIxLevel paramL) paramL)

def ixIntEq (a b : Ix.Int) : Bool := a == b

def ixSubstringEq (a b : Ix.Substring) : Bool :=
  a.str == b.str && a.startPos == b.startPos && a.stopPos == b.stopPos

def ixIntTests : TestSeq :=
  let pos := Ix.Int.ofNat 42
  let zero := Ix.Int.ofNat 0
  let neg := Ix.Int.negSucc 4  -- represents -5
  test "Ix.Int positive" (ixIntEq (roundtripIxInt pos) pos) ++
  test "Ix.Int zero" (ixIntEq (roundtripIxInt zero) zero) ++
  test "Ix.Int negative" (ixIntEq (roundtripIxInt neg) neg)

def ixSubstringTests : TestSeq :=
  let sub1 : Ix.Substring := ⟨"hello world", 0, 5⟩
  let sub2 : Ix.Substring := ⟨"hello world", 6, 11⟩
  let subEmpty : Ix.Substring := ⟨"", 0, 0⟩
  test "Ix.Substring basic" (ixSubstringEq (roundtripIxSubstring sub1) sub1) ++
  test "Ix.Substring offset" (ixSubstringEq (roundtripIxSubstring sub2) sub2) ++
  test "Ix.Substring empty" (ixSubstringEq (roundtripIxSubstring subEmpty) subEmpty)

def ixSourceInfoEq (a b : Ix.SourceInfo) : Bool := a == b

def ixSyntaxPreresolvedEq (a b : Ix.SyntaxPreresolved) : Bool := a == b

def ixSourceInfoTests : TestSeq :=
  let siNone := Ix.SourceInfo.none
  let siOriginal := Ix.SourceInfo.original ⟨"  ", 0, 2⟩ 2 ⟨" ", 5, 6⟩ 6
  let siSynthetic := Ix.SourceInfo.synthetic 10 20 true
  let siSyntheticNonCanonical := Ix.SourceInfo.synthetic 0 5 false
  test "Ix.SourceInfo none" (ixSourceInfoEq (roundtripIxSourceInfo siNone) siNone) ++
  test "Ix.SourceInfo original" (ixSourceInfoEq (roundtripIxSourceInfo siOriginal) siOriginal) ++
  test "Ix.SourceInfo synthetic" (ixSourceInfoEq (roundtripIxSourceInfo siSynthetic) siSynthetic) ++
  test "Ix.SourceInfo synthetic non-canonical" (ixSourceInfoEq (roundtripIxSourceInfo siSyntheticNonCanonical) siSyntheticNonCanonical)

def ixSyntaxPreresolvedTests : TestSeq :=
  let ns := Ix.SyntaxPreresolved.namespace (Ix.Name.mkStr Ix.Name.mkAnon "Nat")
  let decl := Ix.SyntaxPreresolved.decl (Ix.Name.mkStr Ix.Name.mkAnon "foo") #["alias1", "alias2"]
  let declNoAliases := Ix.SyntaxPreresolved.decl (Ix.Name.mkStr Ix.Name.mkAnon "bar") #[]
  test "Ix.SyntaxPreresolved namespace" (ixSyntaxPreresolvedEq (roundtripIxSyntaxPreresolved ns) ns) ++
  test "Ix.SyntaxPreresolved decl" (ixSyntaxPreresolvedEq (roundtripIxSyntaxPreresolved decl) decl) ++
  test "Ix.SyntaxPreresolved decl no aliases" (ixSyntaxPreresolvedEq (roundtripIxSyntaxPreresolved declNoAliases) declNoAliases)

def ixSyntaxEq (a b : Ix.Syntax) : Bool := a == b

def ixSyntaxTests : TestSeq :=
  let synMissing := Ix.Syntax.missing
  let atom := Ix.Syntax.atom .none "hello"
  let node := Ix.Syntax.node .none (Ix.Name.mkStr Ix.Name.mkAnon "node") #[synMissing, atom]
  let ident := Ix.Syntax.ident .none ⟨"x", 0, 1⟩ (Ix.Name.mkStr Ix.Name.mkAnon "x") #[]
  let identWithPreresolved := Ix.Syntax.ident .none ⟨"Nat", 0, 3⟩
    (Ix.Name.mkStr Ix.Name.mkAnon "Nat")
    #[.namespace (Ix.Name.mkStr Ix.Name.mkAnon "Nat")]
  test "Ix.Syntax missing" (ixSyntaxEq (roundtripIxSyntax synMissing) synMissing) ++
  test "Ix.Syntax atom" (ixSyntaxEq (roundtripIxSyntax atom) atom) ++
  test "Ix.Syntax node" (ixSyntaxEq (roundtripIxSyntax node) node) ++
  test "Ix.Syntax ident" (ixSyntaxEq (roundtripIxSyntax ident) ident) ++
  test "Ix.Syntax ident with preresolved" (ixSyntaxEq (roundtripIxSyntax identWithPreresolved) identWithPreresolved)

def ixDataValueEq (a b : Ix.DataValue) : Bool := a == b

def boolTests : TestSeq :=
  test "Bool true" (roundtripBool true == true) ++
  test "Bool false" (roundtripBool false == false)

def ixDataValueTests : TestSeq :=
  let dvString := Ix.DataValue.ofString "hello"
  let dvBool := Ix.DataValue.ofBool true
  let dvBoolFalse := Ix.DataValue.ofBool false
  let dvName := Ix.DataValue.ofName (Ix.Name.mkStr Ix.Name.mkAnon "test")
  let dvNat := Ix.DataValue.ofNat 42
  let dvIntPos := Ix.DataValue.ofInt (.ofNat 10)
  let dvIntNeg := Ix.DataValue.ofInt (.negSucc 4)  -- represents -5
  let dvSyntax := Ix.DataValue.ofSyntax .missing
  test "Ix.DataValue ofString" (ixDataValueEq (roundtripIxDataValue dvString) dvString) ++
  test "Ix.DataValue ofBool true" (ixDataValueEq (roundtripIxDataValue dvBool) dvBool) ++
  test "Ix.DataValue ofBool false" (ixDataValueEq (roundtripIxDataValue dvBoolFalse) dvBoolFalse) ++
  test "Ix.DataValue ofName" (ixDataValueEq (roundtripIxDataValue dvName) dvName) ++
  test "Ix.DataValue ofNat" (ixDataValueEq (roundtripIxDataValue dvNat) dvNat) ++
  test "Ix.DataValue ofInt pos" (ixDataValueEq (roundtripIxDataValue dvIntPos) dvIntPos) ++
  test "Ix.DataValue ofInt neg" (ixDataValueEq (roundtripIxDataValue dvIntNeg) dvIntNeg) ++
  test "Ix.DataValue ofSyntax" (ixDataValueEq (roundtripIxDataValue dvSyntax) dvSyntax)

/-! ## ConstantInfo comparison and tests -/

/-- Compare ConstantInfo by comparing the hash of the underlying constant's type -/
def ixConstantInfoEq (a b : Ix.ConstantInfo) : Bool :=
  a.getCnst.type.getHash == b.getCnst.type.getHash &&
  a.getCnst.name.getHash == b.getCnst.name.getHash

def ixConstantInfoTests : TestSeq :=
  -- Simple test expressions and types
  let natType := Ix.Expr.mkConst (Ix.Name.mkStr Ix.Name.mkAnon "Nat") #[]
  let propType := Ix.Expr.mkSort Ix.Level.mkZero
  let testName := Ix.Name.mkStr Ix.Name.mkAnon "test"

  -- ConstantVal helper
  let mkCnst (n : String) (ty : Ix.Expr) : Ix.ConstantVal := {
    name := Ix.Name.mkStr Ix.Name.mkAnon n
    levelParams := #[]
    type := ty
  }

  -- AxiomVal test
  let axiomInfo := Ix.ConstantInfo.axiomInfo {
    cnst := mkCnst "myAxiom" natType
    isUnsafe := false
  }

  -- DefinitionVal test (simple identity function type: Nat → Nat)
  let fnType := Ix.Expr.mkForallE testName natType natType .default
  let defnInfo := Ix.ConstantInfo.defnInfo {
    cnst := mkCnst "myDef" fnType
    value := Ix.Expr.mkLam testName natType (Ix.Expr.mkBVar 0) .default
    hints := .abbrev
    safety := .safe
    all := #[Ix.Name.mkStr Ix.Name.mkAnon "myDef"]
  }

  -- TheoremVal test
  let thmInfo := Ix.ConstantInfo.thmInfo {
    cnst := mkCnst "myThm" propType
    value := Ix.Expr.mkSort Ix.Level.mkZero
    all := #[]
  }

  -- OpaqueVal test
  let opaqueInfo := Ix.ConstantInfo.opaqueInfo {
    cnst := mkCnst "myOpaque" natType
    value := Ix.Expr.mkLit (.natVal 42)
    isUnsafe := false
    all := #[]
  }

  -- QuotVal test (type kind)
  let quotInfo := Ix.ConstantInfo.quotInfo {
    cnst := mkCnst "myQuot" natType
    kind := .type
  }

  -- InductiveVal test
  let inductInfo := Ix.ConstantInfo.inductInfo {
    cnst := mkCnst "MyInduct" (Ix.Expr.mkSort (Ix.Level.mkSucc Ix.Level.mkZero))
    numParams := 0
    numIndices := 0
    all := #[Ix.Name.mkStr Ix.Name.mkAnon "MyInduct"]
    ctors := #[Ix.Name.mkStr Ix.Name.mkAnon "MyInduct.mk"]
    numNested := 0
    isRec := false
    isUnsafe := false
    isReflexive := false
  }

  -- ConstructorVal test
  let ctorInfo := Ix.ConstantInfo.ctorInfo {
    cnst := mkCnst "MyInduct.mk" natType
    induct := Ix.Name.mkStr Ix.Name.mkAnon "MyInduct"
    cidx := 0
    numParams := 0
    numFields := 1
    isUnsafe := false
  }

  -- RecursorVal test
  let recInfo := Ix.ConstantInfo.recInfo {
    cnst := mkCnst "MyInduct.rec" natType
    all := #[Ix.Name.mkStr Ix.Name.mkAnon "MyInduct"]
    numParams := 0
    numIndices := 0
    numMotives := 1
    numMinors := 1
    rules := #[{
      ctor := Ix.Name.mkStr Ix.Name.mkAnon "MyInduct.mk"
      nfields := 1
      rhs := Ix.Expr.mkBVar 0
    }]
    k := false
    isUnsafe := false
  }

  test "Ix.ConstantInfo axiom" (ixConstantInfoEq (roundtripIxConstantInfo axiomInfo) axiomInfo) ++
  test "Ix.ConstantInfo defn" (ixConstantInfoEq (roundtripIxConstantInfo defnInfo) defnInfo) ++
  test "Ix.ConstantInfo thm" (ixConstantInfoEq (roundtripIxConstantInfo thmInfo) thmInfo) ++
  test "Ix.ConstantInfo opaque" (ixConstantInfoEq (roundtripIxConstantInfo opaqueInfo) opaqueInfo) ++
  test "Ix.ConstantInfo quot" (ixConstantInfoEq (roundtripIxConstantInfo quotInfo) quotInfo) ++
  test "Ix.ConstantInfo induct" (ixConstantInfoEq (roundtripIxConstantInfo inductInfo) inductInfo) ++
  test "Ix.ConstantInfo ctor" (ixConstantInfoEq (roundtripIxConstantInfo ctorInfo) ctorInfo) ++
  test "Ix.ConstantInfo rec" (ixConstantInfoEq (roundtripIxConstantInfo recInfo) recInfo)

/-! ## Environment comparison and tests -/

/-- Compare Environment by checking consts map size -/
def ixEnvironmentEq (a b : Ix.Environment) : Bool :=
  a.consts.size == b.consts.size

/-- Compare RawEnvironment by checking consts array size -/
def ixRawEnvironmentEq (a b : Ix.RawEnvironment) : Bool :=
  a.consts.size == b.consts.size

def ixRawEnvironmentTests : TestSeq :=
  let emptyRaw : Ix.RawEnvironment := { consts := #[] }
  test "Ix.RawEnvironment empty" (ixRawEnvironmentEq (roundtripIxRawEnvironment emptyRaw) emptyRaw)

def ixEnvironmentTests : TestSeq :=
  let emptyEnv : Ix.Environment := { consts := {} }
  test "Ix.Environment empty" (ixEnvironmentEq (roundtripIxEnvironment emptyEnv) emptyEnv)

def ixExprTests : TestSeq :=
  let bvar0 := Ix.Expr.mkBVar 0
  let sort0 := Ix.Expr.mkSort Ix.Level.mkZero
  let constN := Ix.Expr.mkConst (Ix.Name.mkStr Ix.Name.mkAnon "Nat") #[]
  let app := Ix.Expr.mkApp constN bvar0
  let lam := Ix.Expr.mkLam (Ix.Name.mkStr Ix.Name.mkAnon "x") sort0 bvar0 .default
  let forallE := Ix.Expr.mkForallE (Ix.Name.mkStr Ix.Name.mkAnon "x") sort0 sort0 .default
  -- mdata with various DataValue types
  let keyName := Ix.Name.mkStr Ix.Name.mkAnon "key"
  let mdataString := Ix.Expr.mkMData #[(keyName, .ofString "hello")] bvar0
  let mdataBool := Ix.Expr.mkMData #[(keyName, .ofBool true)] bvar0
  let mdataName := Ix.Expr.mkMData #[(keyName, .ofName Ix.Name.mkAnon)] bvar0
  let mdataNat := Ix.Expr.mkMData #[(keyName, .ofNat 42)] bvar0
  let mdataInt := Ix.Expr.mkMData #[(keyName, .ofInt (.negSucc 4))] bvar0
  let mdataSyntax := Ix.Expr.mkMData #[(keyName, .ofSyntax .missing)] bvar0
  let mdataMulti := Ix.Expr.mkMData #[
    (Ix.Name.mkStr Ix.Name.mkAnon "a", .ofString "str"),
    (Ix.Name.mkStr Ix.Name.mkAnon "b", .ofNat 123),
    (Ix.Name.mkStr Ix.Name.mkAnon "c", .ofBool false)
  ] constN
  test "Ix.Expr bvar" (ixExprEq (roundtripIxExpr bvar0) bvar0) ++
  test "Ix.Expr sort" (ixExprEq (roundtripIxExpr sort0) sort0) ++
  test "Ix.Expr const" (ixExprEq (roundtripIxExpr constN) constN) ++
  test "Ix.Expr app" (ixExprEq (roundtripIxExpr app) app) ++
  test "Ix.Expr lam" (ixExprEq (roundtripIxExpr lam) lam) ++
  test "Ix.Expr forallE" (ixExprEq (roundtripIxExpr forallE) forallE) ++
  test "Ix.Expr mdata(string)" (ixExprEq (roundtripIxExpr mdataString) mdataString) ++
  test "Ix.Expr mdata(bool)" (ixExprEq (roundtripIxExpr mdataBool) mdataBool) ++
  test "Ix.Expr mdata(name)" (ixExprEq (roundtripIxExpr mdataName) mdataName) ++
  test "Ix.Expr mdata(nat)" (ixExprEq (roundtripIxExpr mdataNat) mdataNat) ++
  test "Ix.Expr mdata(int)" (ixExprEq (roundtripIxExpr mdataInt) mdataInt) ++
  test "Ix.Expr mdata(syntax)" (ixExprEq (roundtripIxExpr mdataSyntax) mdataSyntax) ++
  test "Ix.Expr mdata(multi)" (ixExprEq (roundtripIxExpr mdataMulti) mdataMulti)

/-! ## Property tests -/

def suite : List TestSeq := [
  simpleTests,
  largeNatTests,
  -- Basic type roundtrips
  checkIO "Nat roundtrip" (∀ n : Nat, roundtripNat n == n),
  checkIO "String roundtrip" (∀ s : String, roundtripString s == s),
  checkIO "List Nat roundtrip" (∀ xs : List Nat, roundtripListNat xs == xs),
  checkIO "Array Nat roundtrip" (∀ arr : Array Nat, roundtripArrayNat arr == arr),
  checkIO "ByteArray roundtrip" (∀ ba : ByteArray, roundtripByteArray ba == ba),
  -- Struct and inductive roundtrips
  checkIO "Point roundtrip" (∀ p : Point, roundtripPoint p == p),
  checkIO "NatTree roundtrip" (∀ t : NatTree, roundtripNatTree t == t),
  -- AssocList roundtrip
  assocListTests,
  -- HashMap roundtrip
  hashMapTests,
  checkIO "HashMap Nat Nat roundtrip" (∀ m : Std.HashMap Nat Nat, hashMapEq (roundtripHashMapNatNat m) m),
  -- Ix type roundtrips
  ixAddressTests,
  ixNameTests,
  ixLevelTests,
  ixIntTests,
  ixSubstringTests,
  ixSourceInfoTests,
  ixSyntaxPreresolvedTests,
  ixSyntaxTests,
  boolTests,
  ixDataValueTests,
  ixExprTests,
  ixConstantInfoTests,
  ixRawEnvironmentTests,
  ixEnvironmentTests,
  checkIO "Ix.Name roundtrip" (∀ n : Ix.Name, ixNameEq (roundtripIxName n) n),
  checkIO "Ix.Level roundtrip" (∀ l : Ix.Level, ixLevelEq (roundtripIxLevel l) l),
  checkIO "Ix.Expr roundtrip" (∀ e : Ix.Expr, ixExprEq (roundtripIxExpr e) e),
]

end Tests.FFI
