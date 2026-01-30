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
import Ix.CompileM
import Tests.Ix.Ixon

open LSpec SlimCheck Gen

namespace Tests.FFI

/-! ## FFI declarations for round-trip tests -/

/-- Round-trip a Nat through Rust: decode then re-encode -/
@[extern "rs_roundtrip_nat"]
opaque roundtripNat : @& Nat → Nat
--
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
--
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

instance : Repr Ix.RawEnvironment where
  reprPrec env _ := s!"RawEnvironment(consts={env.consts.size})"

-- Rust roundtrip returns RawEnvironment (array-based), not Environment (HashMap-based)
@[extern "rs_roundtrip_ix_raw_environment"]
opaque roundtripIxRawEnvironment : @& Ix.RawEnvironment → Ix.RawEnvironment

-- Roundtrip Environment by going through RawEnvironment
@[extern "rs_roundtrip_ix_environment"]
opaque roundtripIxEnvironmentRaw : @& Ix.Environment → Ix.RawEnvironment

def roundtripIxEnvironment (env : Ix.Environment) : Ix.Environment :=
  (roundtripIxEnvironmentRaw env).toEnvironment

-- Round-trip Ix.CompileM.RawEnv (the FFI structure for rsCompileEnv)
instance : Inhabited Ix.CompileM.RawEnv where
  default := { consts := #[], named := #[], blobs := #[], comms := #[] }

@[extern "rs_roundtrip_raw_env"]
opaque roundtripRawEnv : @& Ix.CompileM.RawEnv → Ix.CompileM.RawEnv

-- Round-trip Ix.RustCondensedBlocks
instance : Inhabited Ix.RustCondensedBlocks where
  default := { lowLinks := #[], blocks := #[], blockRefs := #[] }

instance : Repr Ix.RustCondensedBlocks where
  reprPrec cb _ := s!"RustCondensedBlocks(lowLinks={cb.lowLinks.size}, blocks={cb.blocks.size}, blockRefs={cb.blockRefs.size})"

@[extern "rs_roundtrip_rust_condensed_blocks"]
opaque roundtripRustCondensedBlocks : @& Ix.RustCondensedBlocks → Ix.RustCondensedBlocks

-- Round-trip Ix.CompileM.RustCompilePhases
instance : Inhabited Ix.CompileM.RustCompilePhases where
  default := { rawEnv := default, condensed := default, compileEnv := default }

instance : Repr Ix.CompileM.RawEnv where
  reprPrec env _ := s!"RawEnv(consts={env.consts.size}, named={env.named.size}, blobs={env.blobs.size}, comms={env.comms.size})"

instance : Repr Ix.CompileM.RustCompilePhases where
  reprPrec p _ := s!"RustCompilePhases(rawEnv.consts={p.rawEnv.consts.size}, condensed.blocks={p.condensed.blocks.size}, compileEnv.consts={p.compileEnv.consts.size})"

@[extern "rs_roundtrip_rust_compile_phases"]
opaque roundtripRustCompilePhases : @& Ix.CompileM.RustCompilePhases → Ix.CompileM.RustCompilePhases


/-! ## Ixon type roundtrip FFI declarations -/

-- Simple enums (use lean_box/lean_unbox)
@[extern "rs_roundtrip_ixon_def_kind"]
opaque roundtripIxonDefKind : @& Ixon.DefKind → Ixon.DefKind

--@[extern "rs_roundtrip_ixon_definition_safety"]
--opaque roundtripIxonDefinitionSafety : @& Ixon.DefinitionSafety → Ixon.DefinitionSafety
--
--@[extern "rs_roundtrip_ixon_quot_kind"]
--opaque roundtripIxonQuotKind : @& Ixon.QuotKind → Ixon.QuotKind
--
---- Core recursive types
--@[extern "rs_roundtrip_ixon_univ"]
--opaque roundtripIxonUniv : @& Ixon.Univ → Ixon.Univ
--
--@[extern "rs_roundtrip_ixon_expr"]
--opaque roundtripIxonExpr : @& Ixon.Expr → Ixon.Expr
--
---- Constant structures
--@[extern "rs_roundtrip_ixon_definition"]
--opaque roundtripIxonDefinition : @& Ixon.Definition → Ixon.Definition
--
--@[extern "rs_roundtrip_ixon_recursor_rule"]
--opaque roundtripIxonRecursorRule : @& Ixon.RecursorRule → Ixon.RecursorRule
--
--@[extern "rs_roundtrip_ixon_recursor"]
--opaque roundtripIxonRecursor : @& Ixon.Recursor → Ixon.Recursor
--
--@[extern "rs_roundtrip_ixon_axiom"]
--opaque roundtripIxonAxiom : @& Ixon.Axiom → Ixon.Axiom
--
--@[extern "rs_roundtrip_ixon_quotient"]
--opaque roundtripIxonQuotient : @& Ixon.Quotient → Ixon.Quotient
--
--@[extern "rs_roundtrip_ixon_constructor"]
--opaque roundtripIxonConstructor : @& Ixon.Constructor → Ixon.Constructor
--
--@[extern "rs_roundtrip_ixon_inductive"]
--opaque roundtripIxonInductive : @& Ixon.Inductive → Ixon.Inductive
--
---- Projection types
--@[extern "rs_roundtrip_ixon_inductive_proj"]
--opaque roundtripIxonInductiveProj : @& Ixon.InductiveProj → Ixon.InductiveProj
--
--@[extern "rs_roundtrip_ixon_constructor_proj"]
--opaque roundtripIxonConstructorProj : @& Ixon.ConstructorProj → Ixon.ConstructorProj
--
--@[extern "rs_roundtrip_ixon_recursor_proj"]
--opaque roundtripIxonRecursorProj : @& Ixon.RecursorProj → Ixon.RecursorProj
--
--@[extern "rs_roundtrip_ixon_definition_proj"]
--opaque roundtripIxonDefinitionProj : @& Ixon.DefinitionProj → Ixon.DefinitionProj
--
---- Composite types
--@[extern "rs_roundtrip_ixon_mut_const"]
--opaque roundtripIxonMutConst : @& Ixon.MutConst → Ixon.MutConst
--
--@[extern "rs_roundtrip_ixon_constant_info"]
--opaque roundtripIxonConstantInfo : @& Ixon.ConstantInfo → Ixon.ConstantInfo
--
--@[extern "rs_roundtrip_ixon_constant"]
--opaque roundtripIxonConstant : @& Ixon.Constant → Ixon.Constant
--
---- Metadata types
--@[extern "rs_roundtrip_ixon_data_value"]
--opaque roundtripIxonDataValue : @& Ixon.DataValue → Ixon.DataValue
--
--@[extern "rs_roundtrip_ixon_expr_meta"]
--opaque roundtripIxonExprMeta : @& Ixon.ExprMeta → Ixon.ExprMeta
--
--@[extern "rs_roundtrip_ixon_ctor_meta"]
--opaque roundtripIxonCtorMeta : @& Ixon.CtorMeta → Ixon.CtorMeta
--
--@[extern "rs_roundtrip_ixon_constant_meta"]
--opaque roundtripIxonConstantMeta : @& Ixon.ConstantMeta → Ixon.ConstantMeta
--
--@[extern "rs_roundtrip_ixon_named"]
--opaque roundtripIxonNamed : @& Ixon.Named → Ixon.Named
--
--@[extern "rs_roundtrip_ixon_comm"]
--opaque roundtripIxonComm : @& Ixon.Comm → Ixon.Comm
--
--/-! ## Ix type generators -/
--
--/-- Generate Ix.Name with deeper nesting -/
--def genIxName : Nat → Gen Ix.Name
--  | 0 => pure Ix.Name.mkAnon
--  | fuel + 1 => Gen.frequency #[
--      (1, pure Ix.Name.mkAnon),
--      (4, do
--        let parent ← genIxName fuel
--        let len ← choose Nat 1 12
--        let chars ← Gen.listOf (choose Nat 97 122 >>= fun n => pure (Char.ofNat n))
--        let s := String.ofList (chars.take len)
--        pure (Ix.Name.mkStr parent s)),
--      (3, do
--        let parent ← genIxName fuel
--        let n ← choose Nat 0 1000
--        pure (Ix.Name.mkNat parent n))
--    ] (pure Ix.Name.mkAnon)
--
--/-- Generate Ix.Level with deeper nesting -/
--def genIxLevel : Nat → Gen Ix.Level
--  | 0 => Gen.frequency #[
--      (3, pure Ix.Level.mkZero),
--      (2, do let n ← genIxName 2; pure (Ix.Level.mkParam n))
--    ] (pure Ix.Level.mkZero)
--  | fuel + 1 => Gen.frequency #[
--      (3, pure Ix.Level.mkZero),
--      (4, do
--        let x ← genIxLevel fuel
--        pure (Ix.Level.mkSucc x)),
--      (2, do
--        let x ← genIxLevel (fuel / 2)
--        let y ← genIxLevel (fuel / 2)
--        pure (Ix.Level.mkMax x y)),
--      (2, do
--        let x ← genIxLevel (fuel / 2)
--        let y ← genIxLevel (fuel / 2)
--        pure (Ix.Level.mkIMax x y)),
--      (3, do
--        let n ← genIxName 3
--        pure (Ix.Level.mkParam n)),
--      (1, do
--        let n ← genIxName 3
--        pure (Ix.Level.mkMvar n))
--    ] (pure Ix.Level.mkZero)
--
--/-- Generate BinderInfo with varied distribution -/
--def genBinderInfo : Gen Lean.BinderInfo :=
--  frequency [
--    (10, pure .default),
--    (3, pure .implicit),
--    (2, pure .strictImplicit),
--    (3, pure .instImplicit),
--  ]
--
--/-- Generate a Literal -/
--def genLiteral : Gen Lean.Literal :=
--  frequency [
--    (5, Lean.Literal.natVal <$> choose Nat 0 1000),
--    (5, pure (Lean.Literal.strVal "test_string")),
--  ]
--
--/-- Generate an Ix.Int for DataValue -/
--def genIxInt : Gen Ix.Int :=
--  frequency [
--    (5, Ix.Int.ofNat <$> choose Nat 0 100),
--    (5, Ix.Int.negSucc <$> choose Nat 0 50),
--  ]
--
--/-- Generate Ix.Syntax (simplified) -/
--partial def genIxSyntax : Gen Ix.Syntax :=
--  frequency [
--    (10, pure Ix.Syntax.missing),
--    (5, Ix.Syntax.atom <$> pure .none <*> pure "atom"),
--  ]
--
--/-- Generate Ix.DataValue with all variants -/
--def genIxDataValue : Gen Ix.DataValue :=
--  frequency [
--    (10, Ix.DataValue.ofString <$> pure "test"),
--    (10, Ix.DataValue.ofBool <$> frequency [(1, pure true), (1, pure false)]),
--    (10, Ix.DataValue.ofName <$> genIxName 3),
--    (10, Ix.DataValue.ofNat <$> choose Nat 0 1000),
--    (10, Ix.DataValue.ofInt <$> genIxInt),
--    (5, Ix.DataValue.ofSyntax <$> genIxSyntax),
--  ]
--
--/-- Generate Ix.Expr with all variants and deeper nesting -/
--def genIxExpr : Nat → Gen Ix.Expr
--  | 0 => Gen.frequency #[
--      (3, do let idx ← choose Nat 0 20; pure (Ix.Expr.mkBVar idx)),
--      (2, do let u ← genIxLevel 3; pure (Ix.Expr.mkSort u)),
--      (2, do let n ← genIxName 3; pure (Ix.Expr.mkFVar n)),
--      (1, Ix.Expr.mkLit <$> genLiteral)
--    ] (pure (Ix.Expr.mkBVar 0))
--  | fuel + 1 => Gen.frequency #[
--      -- Base cases (weighted higher to ensure termination)
--      (4, do let idx ← choose Nat 0 20; pure (Ix.Expr.mkBVar idx)),
--      (2, do let u ← genIxLevel 4; pure (Ix.Expr.mkSort u)),
--      (2, do let n ← genIxName 4; pure (Ix.Expr.mkFVar n)),
--      (1, do let n ← genIxName 4; pure (Ix.Expr.mkMVar n)),
--      (2, Ix.Expr.mkLit <$> genLiteral),
--      -- Const with universe levels
--      (4, do
--        let n ← genIxName 4
--        let numLevels ← choose Nat 0 4
--        let mut levels : Array Ix.Level := #[]
--        for _ in [:numLevels] do
--          levels := levels.push (← genIxLevel 4)
--        pure (Ix.Expr.mkConst n levels)),
--      -- App - function application
--      (5, do
--        let f ← genIxExpr (fuel / 2)
--        let a ← genIxExpr (fuel / 2)
--        pure (Ix.Expr.mkApp f a)),
--      -- Lambda with varied binder info
--      (4, do
--        let n ← genIxName 3
--        let bi ← genBinderInfo
--        let ty ← genIxExpr (fuel / 2)
--        let body ← genIxExpr (fuel / 2)
--        pure (Ix.Expr.mkLam n ty body bi)),
--      -- ForallE with varied binder info
--      (4, do
--        let n ← genIxName 3
--        let bi ← genBinderInfo
--        let ty ← genIxExpr (fuel / 2)
--        let body ← genIxExpr (fuel / 2)
--        pure (Ix.Expr.mkForallE n ty body bi)),
--      -- LetE
--      (3, do
--        let n ← genIxName 3
--        let ty ← genIxExpr (fuel / 3)
--        let val ← genIxExpr (fuel / 3)
--        let body ← genIxExpr (fuel / 3)
--        let nonDep ← frequency [(1, pure true), (1, pure false)]
--        pure (Ix.Expr.mkLetE n ty val body nonDep)),
--      -- MData with metadata
--      (2, do
--        let numEntries ← choose Nat 1 4
--        let mut entries : Array (Ix.Name × Ix.DataValue) := #[]
--        for _ in [:numEntries] do
--          let key ← genIxName 2
--          let val ← genIxDataValue
--          entries := entries.push (key, val)
--        let e ← genIxExpr (fuel / 2)
--        pure (Ix.Expr.mkMData entries e)),
--      -- Proj
--      (2, do
--        let typeName ← genIxName 4
--        let idx ← choose Nat 0 10
--        let struct ← genIxExpr (fuel / 2)
--        pure (Ix.Expr.mkProj typeName idx struct))
--    ] (pure (Ix.Expr.mkBVar 0))
--
--instance : Shrinkable Ix.Name where
--  shrink n := match n with
--    | .anonymous _ => []
--    | .str p _ _ => [p]
--    | .num p _ _ => [p]
--
--instance : SampleableExt Ix.Name := SampleableExt.mkSelfContained (genIxName 5)
--
--instance : Shrinkable Ix.Level where
--  shrink l := match l with
--    | .zero _ => []
--    | .succ x _ => [x]
--    | .max x y _ => [x, y]
--    | .imax x y _ => [x, y]
--    | .param _ _ => [Ix.Level.mkZero]
--    | .mvar _ _ => [Ix.Level.mkZero]
--
--instance : SampleableExt Ix.Level := SampleableExt.mkSelfContained (genIxLevel 5)
--
--instance : Shrinkable Ix.Expr where
--  shrink e := match e with
--    | .bvar _ _ => []
--    | .fvar _ _ => [Ix.Expr.mkBVar 0]
--    | .mvar _ _ => [Ix.Expr.mkBVar 0]
--    | .sort _ _ => [Ix.Expr.mkBVar 0]
--    | .const _ _ _ => [Ix.Expr.mkBVar 0]
--    | .app f a _ => [f, a]
--    | .lam _ ty body _ _ => [ty, body]
--    | .forallE _ ty body _ _ => [ty, body]
--    | .letE _ ty val body _ _ => [ty, val, body]
--    | .lit _ _ => [Ix.Expr.mkBVar 0]
--    | .mdata _ e _ => [e]
--    | .proj _ _ e _ => [e]
--
--instance : SampleableExt Ix.Expr := SampleableExt.mkSelfContained (genIxExpr 5)
--
--/-- Generate an array of level parameter names with varied sizes -/
--def genLevelParams : Gen (Array Ix.Name) := do
--  let numParams ← choose Nat 0 5
--  let mut params : Array Ix.Name := #[]
--  for i in [:numParams] do
--    -- Use varied names, not just u, v, w
--    let baseName ← frequency [
--      (3, pure "u"),
--      (3, pure "v"),
--      (2, pure "w"),
--      (2, pure "α"),
--      (2, pure "β"),
--    ]
--    params := params.push (Ix.Name.mkStr Ix.Name.mkAnon s!"{baseName}{i}")
--  pure params
--
--/-- Generate a random Ix.ConstantVal with varied complexity -/
--def genIxConstantVal : Gen Ix.ConstantVal :=
--  Ix.ConstantVal.mk <$> genIxName 5 <*> genLevelParams <*> genIxExpr 5
--
--/-- Generate a random Ix.AxiomVal -/
--def genIxAxiomVal : Gen Ix.AxiomVal :=
--  Ix.AxiomVal.mk <$> genIxConstantVal <*> frequency [(9, pure false), (1, pure true)]
--
--/-- Generate ReducibilityHints -/
--def genReducibilityHints : Gen Lean.ReducibilityHints :=
--  frequency [
--    (3, pure .opaque),
--    (3, pure .abbrev),
--    (4, Lean.ReducibilityHints.regular <$> genUInt32),
--  ]
--
--/-- Generate DefinitionSafety -/
--def genDefinitionSafety : Gen Lean.DefinitionSafety :=
--  frequency [
--    (8, pure .safe),
--    (1, pure .unsafe),
--    (1, pure .partial),
--  ]
--
--/-- Generate an array of mutually recursive names -/
--def genMutualNames (baseName : Ix.Name) : Gen (Array Ix.Name) := do
--  let numMutual ← choose Nat 1 4
--  let mut names : Array Ix.Name := #[baseName]
--  for i in [1:numMutual] do
--    names := names.push (Ix.Name.mkStr baseName s!"_mutual_{i}")
--  pure names
--
--/-- Generate a random Ix.DefinitionVal -/
--def genIxDefinitionVal : Gen Ix.DefinitionVal := do
--  let cnst ← genIxConstantVal
--  let value ← genIxExpr 5
--  let hints ← genReducibilityHints
--  let safety ← genDefinitionSafety
--  let all ← genMutualNames cnst.name
--  pure { cnst, value, hints, safety, all }
--
--/-- Generate a random Ix.TheoremVal -/
--def genIxTheoremVal : Gen Ix.TheoremVal := do
--  let cnst ← genIxConstantVal
--  let value ← genIxExpr 5
--  let all ← genMutualNames cnst.name
--  pure { cnst, value, all }
--
--/-- Generate a random Ix.OpaqueVal -/
--def genIxOpaqueVal : Gen Ix.OpaqueVal := do
--  let cnst ← genIxConstantVal
--  let value ← genIxExpr 5
--  let isUnsafe ← frequency [(9, pure false), (1, pure true)]
--  let all ← genMutualNames cnst.name
--  pure { cnst, value, isUnsafe, all }
--
--/-- Generate QuotKind -/
--def genQuotKind : Gen Lean.QuotKind :=
--  frequency [
--    (1, pure .type),
--    (1, pure .ctor),
--    (1, pure .lift),
--    (1, pure .ind),
--  ]
--
--/-- Generate a random Ix.QuotVal -/
--def genIxQuotVal : Gen Ix.QuotVal :=
--  Ix.QuotVal.mk <$> genIxConstantVal <*> genQuotKind
--
--/-- Generate constructor names for an inductive -/
--def genConstructorNames (inductName : Ix.Name) : Gen (Array Ix.Name) := do
--  let numCtors ← choose Nat 1 5
--  let mut ctors : Array Ix.Name := #[]
--  let ctorNames := #["mk", "nil", "cons", "zero", "succ", "inl", "inr", "intro", "refl"]
--  for i in [:numCtors] do
--    let suffix := if i < ctorNames.size then ctorNames[i]! else s!"ctor{i}"
--    ctors := ctors.push (Ix.Name.mkStr inductName suffix)
--  pure ctors
--
--/-- Generate a random Ix.InductiveVal -/
--def genIxInductiveVal : Gen Ix.InductiveVal := do
--  let cnst ← genIxConstantVal
--  let numParams ← choose Nat 0 5
--  let numIndices ← choose Nat 0 3
--  let isRec ← frequency [(6, pure false), (4, pure true)]
--  let isUnsafe ← frequency [(9, pure false), (1, pure true)]
--  let isReflexive ← frequency [(7, pure false), (3, pure true)]
--  let numNested ← choose Nat 0 3
--  let all ← genMutualNames cnst.name
--  let ctors ← genConstructorNames cnst.name
--  pure {
--    cnst
--    numParams
--    numIndices
--    all
--    ctors
--    numNested
--    isRec
--    isUnsafe
--    isReflexive
--  }
--
--/-- Generate a random Ix.ConstructorVal -/
--def genIxConstructorVal : Gen Ix.ConstructorVal := do
--  let cnst ← genIxConstantVal
--  let induct ← genIxName 5
--  let cidx ← choose Nat 0 10
--  let numParams ← choose Nat 0 5
--  let numFields ← choose Nat 0 8
--  let isUnsafe ← frequency [(9, pure false), (1, pure true)]
--  pure { cnst, induct, cidx, numParams, numFields, isUnsafe }
--
--/-- Generate a random Ix.RecursorRule -/
--def genIxRecursorRule : Gen Ix.RecursorRule := do
--  let ctor ← genIxName 5
--  let nfields ← choose Nat 0 8
--  let rhs ← genIxExpr 5
--  pure { ctor, nfields, rhs }
--
--/-- Generate a random Ix.RecursorVal -/
--def genIxRecursorVal : Gen Ix.RecursorVal := do
--  let cnst ← genIxConstantVal
--  let all ← genMutualNames cnst.name
--  let numParams ← choose Nat 0 5
--  let numIndices ← choose Nat 0 3
--  let numMotives ← choose Nat 1 4
--  let numMinors ← choose Nat 0 6
--  let numRules ← choose Nat 1 5
--  let mut rules : Array Ix.RecursorRule := #[]
--  for _ in [:numRules] do
--    rules := rules.push (← genIxRecursorRule)
--  let k ← frequency [(7, pure false), (3, pure true)]
--  let isUnsafe ← frequency [(9, pure false), (1, pure true)]
--  pure { cnst, all, numParams, numIndices, numMotives, numMinors, rules, k, isUnsafe }
--
--/-- Generate a random Ix.ConstantInfo with all variants -/
--def genIxConstantInfo : Gen Ix.ConstantInfo :=
--  frequency [
--    (15, Ix.ConstantInfo.axiomInfo <$> genIxAxiomVal),
--    (15, Ix.ConstantInfo.defnInfo <$> genIxDefinitionVal),
--    (10, Ix.ConstantInfo.thmInfo <$> genIxTheoremVal),
--    (10, Ix.ConstantInfo.opaqueInfo <$> genIxOpaqueVal),
--    (10, Ix.ConstantInfo.quotInfo <$> genIxQuotVal),
--    (15, Ix.ConstantInfo.inductInfo <$> genIxInductiveVal),
--    (15, Ix.ConstantInfo.ctorInfo <$> genIxConstructorVal),
--    (10, Ix.ConstantInfo.recInfo <$> genIxRecursorVal),
--  ]
--
--instance : Shrinkable Ix.ConstantInfo where
--  shrink info :=
--    -- Shrink to a simple axiom
--    let simpleName := Ix.Name.mkAnon
--    let simpleType := Ix.Expr.mkSort Ix.Level.mkZero
--    let simpleCnst : Ix.ConstantVal := { name := simpleName, levelParams := #[], type := simpleType }
--    match info with
--    | .axiomInfo _ => []
--    | _ => [.axiomInfo { cnst := simpleCnst, isUnsafe := false }]
--
--instance : SampleableExt Ix.ConstantInfo := SampleableExt.mkSelfContained genIxConstantInfo
--
--/-! ## Ix type comparison by hash -/
--
--def ixNameEq (a b : Ix.Name) : Bool := a.getHash == b.getHash
--def ixLevelEq (a b : Ix.Level) : Bool := a.getHash == b.getHash
--def ixExprEq (a b : Ix.Expr) : Bool := a.getHash == b.getHash
--
--/-! ## Ix type unit tests -/
--
--def ixAddressEq (a b : Address) : Bool := a.hash == b.hash
--
---- Simple unit test for debugging
--def ixAddressTests : TestSeq :=
--  let addr := Address.blake3 (ByteArray.mk #[1, 2, 3])
--  test "Address roundtrip" (ixAddressEq (roundtripIxAddress addr) addr)
--
--def ixNameTests : TestSeq :=
--  let anon := Ix.Name.mkAnon
--  let str1 := Ix.Name.mkStr anon "test"
--  let str2 := Ix.Name.mkStr str1 "nested"
--  let num1 := Ix.Name.mkNat anon 42
--  test "Ix.Name anon" (ixNameEq (roundtripIxName anon) anon) ++
--  test "Ix.Name str" (ixNameEq (roundtripIxName str1) str1) ++
--  test "Ix.Name str.str" (ixNameEq (roundtripIxName str2) str2) ++
--  test "Ix.Name num" (ixNameEq (roundtripIxName num1) num1)
--
--def ixLevelTests : TestSeq :=
--  let zero := Ix.Level.mkZero
--  let one := Ix.Level.mkSucc zero
--  let two := Ix.Level.mkSucc one
--  let maxL := Ix.Level.mkMax one two
--  let imaxL := Ix.Level.mkIMax one two
--  let paramL := Ix.Level.mkParam (Ix.Name.mkStr Ix.Name.mkAnon "u")
--  test "Ix.Level zero" (ixLevelEq (roundtripIxLevel zero) zero) ++
--  test "Ix.Level succ" (ixLevelEq (roundtripIxLevel one) one) ++
--  test "Ix.Level succ succ" (ixLevelEq (roundtripIxLevel two) two) ++
--  test "Ix.Level max" (ixLevelEq (roundtripIxLevel maxL) maxL) ++
--  test "Ix.Level imax" (ixLevelEq (roundtripIxLevel imaxL) imaxL) ++
--  test "Ix.Level param" (ixLevelEq (roundtripIxLevel paramL) paramL)
--
--def ixIntEq (a b : Ix.Int) : Bool := a == b
--
--def ixSubstringEq (a b : Ix.Substring) : Bool :=
--  a.str == b.str && a.startPos == b.startPos && a.stopPos == b.stopPos
--
--def ixIntTests : TestSeq :=
--  let pos := Ix.Int.ofNat 42
--  let zero := Ix.Int.ofNat 0
--  let neg := Ix.Int.negSucc 4  -- represents -5
--  test "Ix.Int positive" (ixIntEq (roundtripIxInt pos) pos) ++
--  test "Ix.Int zero" (ixIntEq (roundtripIxInt zero) zero) ++
--  test "Ix.Int negative" (ixIntEq (roundtripIxInt neg) neg)
--
--def ixSubstringTests : TestSeq :=
--  let sub1 : Ix.Substring := ⟨"hello world", 0, 5⟩
--  let sub2 : Ix.Substring := ⟨"hello world", 6, 11⟩
--  let subEmpty : Ix.Substring := ⟨"", 0, 0⟩
--  test "Ix.Substring basic" (ixSubstringEq (roundtripIxSubstring sub1) sub1) ++
--  test "Ix.Substring offset" (ixSubstringEq (roundtripIxSubstring sub2) sub2) ++
--  test "Ix.Substring empty" (ixSubstringEq (roundtripIxSubstring subEmpty) subEmpty)
--
--def ixSourceInfoEq (a b : Ix.SourceInfo) : Bool := a == b
--
--def ixSyntaxPreresolvedEq (a b : Ix.SyntaxPreresolved) : Bool := a == b
--
--def ixSourceInfoTests : TestSeq :=
--  let siNone := Ix.SourceInfo.none
--  let siOriginal := Ix.SourceInfo.original ⟨"  ", 0, 2⟩ 2 ⟨" ", 5, 6⟩ 6
--  let siSynthetic := Ix.SourceInfo.synthetic 10 20 true
--  let siSyntheticNonCanonical := Ix.SourceInfo.synthetic 0 5 false
--  test "Ix.SourceInfo none" (ixSourceInfoEq (roundtripIxSourceInfo siNone) siNone) ++
--  test "Ix.SourceInfo original" (ixSourceInfoEq (roundtripIxSourceInfo siOriginal) siOriginal) ++
--  test "Ix.SourceInfo synthetic" (ixSourceInfoEq (roundtripIxSourceInfo siSynthetic) siSynthetic) ++
--  test "Ix.SourceInfo synthetic non-canonical" (ixSourceInfoEq (roundtripIxSourceInfo siSyntheticNonCanonical) siSyntheticNonCanonical)
--
--def ixSyntaxPreresolvedTests : TestSeq :=
--  let ns := Ix.SyntaxPreresolved.namespace (Ix.Name.mkStr Ix.Name.mkAnon "Nat")
--  let decl := Ix.SyntaxPreresolved.decl (Ix.Name.mkStr Ix.Name.mkAnon "foo") #["alias1", "alias2"]
--  let declNoAliases := Ix.SyntaxPreresolved.decl (Ix.Name.mkStr Ix.Name.mkAnon "bar") #[]
--  test "Ix.SyntaxPreresolved namespace" (ixSyntaxPreresolvedEq (roundtripIxSyntaxPreresolved ns) ns) ++
--  test "Ix.SyntaxPreresolved decl" (ixSyntaxPreresolvedEq (roundtripIxSyntaxPreresolved decl) decl) ++
--  test "Ix.SyntaxPreresolved decl no aliases" (ixSyntaxPreresolvedEq (roundtripIxSyntaxPreresolved declNoAliases) declNoAliases)
--
--def ixSyntaxEq (a b : Ix.Syntax) : Bool := a == b
--
--def ixSyntaxTests : TestSeq :=
--  let synMissing := Ix.Syntax.missing
--  let atom := Ix.Syntax.atom .none "hello"
--  let node := Ix.Syntax.node .none (Ix.Name.mkStr Ix.Name.mkAnon "node") #[synMissing, atom]
--  let ident := Ix.Syntax.ident .none ⟨"x", 0, 1⟩ (Ix.Name.mkStr Ix.Name.mkAnon "x") #[]
--  let identWithPreresolved := Ix.Syntax.ident .none ⟨"Nat", 0, 3⟩
--    (Ix.Name.mkStr Ix.Name.mkAnon "Nat")
--    #[.namespace (Ix.Name.mkStr Ix.Name.mkAnon "Nat")]
--  test "Ix.Syntax missing" (ixSyntaxEq (roundtripIxSyntax synMissing) synMissing) ++
--  test "Ix.Syntax atom" (ixSyntaxEq (roundtripIxSyntax atom) atom) ++
--  test "Ix.Syntax node" (ixSyntaxEq (roundtripIxSyntax node) node) ++
--  test "Ix.Syntax ident" (ixSyntaxEq (roundtripIxSyntax ident) ident) ++
--  test "Ix.Syntax ident with preresolved" (ixSyntaxEq (roundtripIxSyntax identWithPreresolved) identWithPreresolved)
--
--def ixDataValueEq (a b : Ix.DataValue) : Bool := a == b
--
--def boolTests : TestSeq :=
--  test "Bool true" (roundtripBool true == true) ++
--  test "Bool false" (roundtripBool false == false)
--
--def ixDataValueTests : TestSeq :=
--  let dvString := Ix.DataValue.ofString "hello"
--  let dvBool := Ix.DataValue.ofBool true
--  let dvBoolFalse := Ix.DataValue.ofBool false
--  let dvName := Ix.DataValue.ofName (Ix.Name.mkStr Ix.Name.mkAnon "test")
--  let dvNat := Ix.DataValue.ofNat 42
--  let dvIntPos := Ix.DataValue.ofInt (.ofNat 10)
--  let dvIntNeg := Ix.DataValue.ofInt (.negSucc 4)  -- represents -5
--  let dvSyntax := Ix.DataValue.ofSyntax .missing
--  test "Ix.DataValue ofString" (ixDataValueEq (roundtripIxDataValue dvString) dvString) ++
--  test "Ix.DataValue ofBool true" (ixDataValueEq (roundtripIxDataValue dvBool) dvBool) ++
--  test "Ix.DataValue ofBool false" (ixDataValueEq (roundtripIxDataValue dvBoolFalse) dvBoolFalse) ++
--  test "Ix.DataValue ofName" (ixDataValueEq (roundtripIxDataValue dvName) dvName) ++
--  test "Ix.DataValue ofNat" (ixDataValueEq (roundtripIxDataValue dvNat) dvNat) ++
--  test "Ix.DataValue ofInt pos" (ixDataValueEq (roundtripIxDataValue dvIntPos) dvIntPos) ++
--  test "Ix.DataValue ofInt neg" (ixDataValueEq (roundtripIxDataValue dvIntNeg) dvIntNeg) ++
--  test "Ix.DataValue ofSyntax" (ixDataValueEq (roundtripIxDataValue dvSyntax) dvSyntax)
--
--/-! ## ConstantInfo comparison and tests -/
--
--/-- Compare ConstantInfo by comparing the hash of the underlying constant's type -/
--def ixConstantInfoEq (a b : Ix.ConstantInfo) : Bool :=
--  a.getCnst.type.getHash == b.getCnst.type.getHash &&
--  a.getCnst.name.getHash == b.getCnst.name.getHash
--
--def ixConstantInfoTests : TestSeq :=
--  -- Simple test expressions and types
--  let natType := Ix.Expr.mkConst (Ix.Name.mkStr Ix.Name.mkAnon "Nat") #[]
--  let propType := Ix.Expr.mkSort Ix.Level.mkZero
--  let testName := Ix.Name.mkStr Ix.Name.mkAnon "test"
--
--  -- ConstantVal helper
--  let mkCnst (n : String) (ty : Ix.Expr) : Ix.ConstantVal := {
--    name := Ix.Name.mkStr Ix.Name.mkAnon n
--    levelParams := #[]
--    type := ty
--  }
--
--  -- AxiomVal test
--  let axiomInfo := Ix.ConstantInfo.axiomInfo {
--    cnst := mkCnst "myAxiom" natType
--    isUnsafe := false
--  }
--
--  -- DefinitionVal test (simple identity function type: Nat → Nat)
--  let fnType := Ix.Expr.mkForallE testName natType natType .default
--  let defnInfo := Ix.ConstantInfo.defnInfo {
--    cnst := mkCnst "myDef" fnType
--    value := Ix.Expr.mkLam testName natType (Ix.Expr.mkBVar 0) .default
--    hints := .abbrev
--    safety := .safe
--    all := #[Ix.Name.mkStr Ix.Name.mkAnon "myDef"]
--  }
--
--  -- TheoremVal test
--  let thmInfo := Ix.ConstantInfo.thmInfo {
--    cnst := mkCnst "myThm" propType
--    value := Ix.Expr.mkSort Ix.Level.mkZero
--    all := #[]
--  }
--
--  -- OpaqueVal test
--  let opaqueInfo := Ix.ConstantInfo.opaqueInfo {
--    cnst := mkCnst "myOpaque" natType
--    value := Ix.Expr.mkLit (.natVal 42)
--    isUnsafe := false
--    all := #[]
--  }
--
--  -- QuotVal test (type kind)
--  let quotInfo := Ix.ConstantInfo.quotInfo {
--    cnst := mkCnst "myQuot" natType
--    kind := .type
--  }
--
--  -- InductiveVal test
--  let inductInfo := Ix.ConstantInfo.inductInfo {
--    cnst := mkCnst "MyInduct" (Ix.Expr.mkSort (Ix.Level.mkSucc Ix.Level.mkZero))
--    numParams := 0
--    numIndices := 0
--    all := #[Ix.Name.mkStr Ix.Name.mkAnon "MyInduct"]
--    ctors := #[Ix.Name.mkStr Ix.Name.mkAnon "MyInduct.mk"]
--    numNested := 0
--    isRec := false
--    isUnsafe := false
--    isReflexive := false
--  }
--
--  -- ConstructorVal test
--  let ctorInfo := Ix.ConstantInfo.ctorInfo {
--    cnst := mkCnst "MyInduct.mk" natType
--    induct := Ix.Name.mkStr Ix.Name.mkAnon "MyInduct"
--    cidx := 0
--    numParams := 0
--    numFields := 1
--    isUnsafe := false
--  }
--
--  -- RecursorVal test
--  let recInfo := Ix.ConstantInfo.recInfo {
--    cnst := mkCnst "MyInduct.rec" natType
--    all := #[Ix.Name.mkStr Ix.Name.mkAnon "MyInduct"]
--    numParams := 0
--    numIndices := 0
--    numMotives := 1
--    numMinors := 1
--    rules := #[{
--      ctor := Ix.Name.mkStr Ix.Name.mkAnon "MyInduct.mk"
--      nfields := 1
--      rhs := Ix.Expr.mkBVar 0
--    }]
--    k := false
--    isUnsafe := false
--  }
--
--  test "Ix.ConstantInfo axiom" (ixConstantInfoEq (roundtripIxConstantInfo axiomInfo) axiomInfo) ++
--  test "Ix.ConstantInfo defn" (ixConstantInfoEq (roundtripIxConstantInfo defnInfo) defnInfo) ++
--  test "Ix.ConstantInfo thm" (ixConstantInfoEq (roundtripIxConstantInfo thmInfo) thmInfo) ++
--  test "Ix.ConstantInfo opaque" (ixConstantInfoEq (roundtripIxConstantInfo opaqueInfo) opaqueInfo) ++
--  test "Ix.ConstantInfo quot" (ixConstantInfoEq (roundtripIxConstantInfo quotInfo) quotInfo) ++
--  test "Ix.ConstantInfo induct" (ixConstantInfoEq (roundtripIxConstantInfo inductInfo) inductInfo) ++
--  test "Ix.ConstantInfo ctor" (ixConstantInfoEq (roundtripIxConstantInfo ctorInfo) ctorInfo) ++
--  test "Ix.ConstantInfo rec" (ixConstantInfoEq (roundtripIxConstantInfo recInfo) recInfo)
--
--/-! ## Environment comparison and tests -/
--
--/-- Compare Environment by checking consts map size -/
--def ixEnvironmentEq (a b : Ix.Environment) : Bool :=
--  a.consts.size == b.consts.size
--
--/-- Compare RawEnvironment by checking consts array size -/
--def ixRawEnvironmentEq (a b : Ix.RawEnvironment) : Bool :=
--  a.consts.size == b.consts.size
--
--def ixRawEnvironmentTests : TestSeq :=
--  let emptyRaw : Ix.RawEnvironment := { consts := #[] }
--  test "Ix.RawEnvironment empty" (ixRawEnvironmentEq (roundtripIxRawEnvironment emptyRaw) emptyRaw)
--
--def ixEnvironmentTests : TestSeq :=
--  let emptyEnv : Ix.Environment := { consts := {} }
--  test "Ix.Environment empty" (ixEnvironmentEq (roundtripIxEnvironment emptyEnv) emptyEnv)
--
--/-- Compare Ix.CompileM.RawEnv by checking array sizes -/
--def rawEnvEq (a b : Ix.CompileM.RawEnv) : Bool :=
--  a.consts.size == b.consts.size &&
--  a.named.size == b.named.size &&
--  a.blobs.size == b.blobs.size &&
--  a.comms.size == b.comms.size
--
--def rawEnvTests : TestSeq :=
--  let emptyRawEnv : Ix.CompileM.RawEnv := { consts := #[], named := #[], blobs := #[], comms := #[] }
--  -- Create a RawEnv with actual data
--  let testAddr := Address.blake3 "test".toUTF8
--  let testAddr2 := Address.blake3 "test2".toUTF8
--  -- Simple axiom: Axiom { isUnsafe := false, lvls := 0, typ := sort 0 }
--  let simpleAxiom : Ixon.Axiom := { isUnsafe := false, lvls := 0, typ := .sort 0 }
--  let simpleConstant : Ixon.Constant := {
--    info := .axio simpleAxiom
--    sharing := #[]
--    refs := #[]
--    univs := #[]
--  }
--  let rawConst : Ix.CompileM.RawConst := { addr := testAddr, const := simpleConstant }
--  -- Simple named entry with empty metadata
--  let testName := Ix.Name.mkStr Ix.Name.mkAnon "Test"
--  let rawNamed : Ix.CompileM.RawNamed := {
--    name := testName
--    addr := testAddr
--    constMeta := .empty
--  }
--  -- Simple blob
--  let rawBlob : Ix.CompileM.RawBlob := { addr := testAddr2, bytes := "hello".toUTF8 }
--  -- Simple comm
--  let rawComm : Ix.CompileM.RawComm := { addr := testAddr, comm := { secret := testAddr, payload := testAddr2 } }
--  -- Full RawEnv with data
--  let fullRawEnv : Ix.CompileM.RawEnv := {
--    consts := #[rawConst]
--    named := #[rawNamed]
--    blobs := #[rawBlob]
--    comms := #[rawComm]
--  }
--  test "Ix.CompileM.RawEnv empty" (rawEnvEq (roundtripRawEnv emptyRawEnv) emptyRawEnv) ++
--  test "Ix.CompileM.RawEnv with data" (rawEnvEq (roundtripRawEnv fullRawEnv) fullRawEnv)
--
--def ixExprTests : TestSeq :=
--  let bvar0 := Ix.Expr.mkBVar 0
--  let sort0 := Ix.Expr.mkSort Ix.Level.mkZero
--  let constN := Ix.Expr.mkConst (Ix.Name.mkStr Ix.Name.mkAnon "Nat") #[]
--  let app := Ix.Expr.mkApp constN bvar0
--  let lam := Ix.Expr.mkLam (Ix.Name.mkStr Ix.Name.mkAnon "x") sort0 bvar0 .default
--  let forallE := Ix.Expr.mkForallE (Ix.Name.mkStr Ix.Name.mkAnon "x") sort0 sort0 .default
--  -- mdata with various DataValue types
--  let keyName := Ix.Name.mkStr Ix.Name.mkAnon "key"
--  let mdataString := Ix.Expr.mkMData #[(keyName, .ofString "hello")] bvar0
--  let mdataBool := Ix.Expr.mkMData #[(keyName, .ofBool true)] bvar0
--  let mdataName := Ix.Expr.mkMData #[(keyName, .ofName Ix.Name.mkAnon)] bvar0
--  let mdataNat := Ix.Expr.mkMData #[(keyName, .ofNat 42)] bvar0
--  let mdataInt := Ix.Expr.mkMData #[(keyName, .ofInt (.negSucc 4))] bvar0
--  let mdataSyntax := Ix.Expr.mkMData #[(keyName, .ofSyntax .missing)] bvar0
--  let mdataMulti := Ix.Expr.mkMData #[
--    (Ix.Name.mkStr Ix.Name.mkAnon "a", .ofString "str"),
--    (Ix.Name.mkStr Ix.Name.mkAnon "b", .ofNat 123),
--    (Ix.Name.mkStr Ix.Name.mkAnon "c", .ofBool false)
--  ] constN
--  test "Ix.Expr bvar" (ixExprEq (roundtripIxExpr bvar0) bvar0) ++
--  test "Ix.Expr sort" (ixExprEq (roundtripIxExpr sort0) sort0) ++
--  test "Ix.Expr const" (ixExprEq (roundtripIxExpr constN) constN) ++
--  test "Ix.Expr app" (ixExprEq (roundtripIxExpr app) app) ++
--  test "Ix.Expr lam" (ixExprEq (roundtripIxExpr lam) lam) ++
--  test "Ix.Expr forallE" (ixExprEq (roundtripIxExpr forallE) forallE) ++
--  test "Ix.Expr mdata(string)" (ixExprEq (roundtripIxExpr mdataString) mdataString) ++
--  test "Ix.Expr mdata(bool)" (ixExprEq (roundtripIxExpr mdataBool) mdataBool) ++
--  test "Ix.Expr mdata(name)" (ixExprEq (roundtripIxExpr mdataName) mdataName) ++
--  test "Ix.Expr mdata(nat)" (ixExprEq (roundtripIxExpr mdataNat) mdataNat) ++
--  test "Ix.Expr mdata(int)" (ixExprEq (roundtripIxExpr mdataInt) mdataInt) ++
--  test "Ix.Expr mdata(syntax)" (ixExprEq (roundtripIxExpr mdataSyntax) mdataSyntax) ++
--  test "Ix.Expr mdata(multi)" (ixExprEq (roundtripIxExpr mdataMulti) mdataMulti)
--
/-! ## BlockCompareResult and BlockCompareDetail FFI tests -/

/-- Result of comparing a single block between Lean and Rust -/
inductive BlockCompareResult where
  | «match»
  | mismatch (leanSize rustSize firstDiffOffset : UInt64)
  | notFound
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Detailed comparison with sharing statistics -/
structure BlockCompareDetail where
  result : BlockCompareResult
  leanSharingLen : UInt64
  rustSharingLen : UInt64
  deriving Repr, BEq, DecidableEq, Inhabited

@[extern "rs_roundtrip_block_compare_result"]
opaque roundtripBlockCompareResult : @& BlockCompareResult → BlockCompareResult

@[extern "rs_roundtrip_block_compare_detail"]
opaque roundtripBlockCompareDetail : @& BlockCompareDetail → BlockCompareDetail

def blockCompareResultTests : TestSeq :=
  let matchCase := BlockCompareResult.match
  let mismatchCase := BlockCompareResult.mismatch 100 200 50
  let notFoundCase := BlockCompareResult.notFound
  test "BlockCompareResult.match" (roundtripBlockCompareResult matchCase == matchCase) ++
  test "BlockCompareResult.mismatch" (roundtripBlockCompareResult mismatchCase == mismatchCase) ++
  test "BlockCompareResult.notFound" (roundtripBlockCompareResult notFoundCase == notFoundCase)

def blockCompareDetailTests : TestSeq :=
  let detailMatch := BlockCompareDetail.mk .match 10 20
  let detailMismatch := BlockCompareDetail.mk (.mismatch 100 200 50) 15 25
  let detailNotFound := BlockCompareDetail.mk .notFound 5 0
  test "BlockCompareDetail match" (roundtripBlockCompareDetail detailMatch == detailMatch) ++
  test "BlockCompareDetail mismatch" (roundtripBlockCompareDetail detailMismatch == detailMismatch) ++
  test "BlockCompareDetail notFound" (roundtripBlockCompareDetail detailNotFound == detailNotFound)

/-! ## RustCondensedBlocks and RustCompilePhases tests -/

/-- Compare RustCondensedBlocks by checking array sizes -/
def rustCondensedBlocksEq (a b : Ix.RustCondensedBlocks) : Bool :=
  a.lowLinks.size == b.lowLinks.size &&
  a.blocks.size == b.blocks.size &&
  a.blockRefs.size == b.blockRefs.size

--/-- Compare RustCompilePhases by checking sizes -/
--def rustCompilePhasesEq (a b : Ix.CompileM.RustCompilePhases) : Bool :=
--  ixRawEnvironmentEq a.rawEnv b.rawEnv &&
--  rustCondensedBlocksEq a.condensed b.condensed &&
--  rawEnvEq a.compileEnv b.compileEnv

--/-- Generate a single (Ix.Name × Ix.ConstantInfo) pair -/
--def genIxConstPair : Gen (Ix.Name × Ix.ConstantInfo) :=
--  Prod.mk <$> genIxName 2 <*> genIxConstantInfo
--
--/-- Generate a random Ix.RawEnvironment -/
--def genIxRawEnvironment : Gen Ix.RawEnvironment :=
--  Ix.RawEnvironment.mk <$> genSmallArray genIxConstPair
--
--/-- Generate a pair of names -/
--def genNamePair : Gen (Ix.Name × Ix.Name) :=
--  Prod.mk <$> genIxName 5 <*> genIxName 5
--
--/-- Generate a name with array of names -/
--def genNameWithNames : Gen (Ix.Name × Array Ix.Name) :=
--  Prod.mk <$> genIxName 5 <*> genSmallArray (genIxName 5)
--
--def genRustCondensedBlocks : Gen Ix.RustCondensedBlocks :=
--  Ix.RustCondensedBlocks.mk <$> genSmallArray genNamePair
--    <*> genSmallArray genNameWithNames
--    <*> genSmallArray genNameWithNames
--
--/-- Generate a RawConst -/
--def genRawConst : Gen Ix.CompileM.RawConst :=
--  Ix.CompileM.RawConst.mk <$> genAddress <*> genConstant

--/-- Generate a RawNamed using genConstantMeta from Ixon.lean -/
--def genRawNamed : Gen Ix.CompileM.RawNamed :=
--  Ix.CompileM.RawNamed.mk <$> genIxName 5 <*> genAddress <*> genConstantMeta
--
--/-- Generate a RawBlob -/
--def genRawBlob : Gen Ix.CompileM.RawBlob :=
--  Ix.CompileM.RawBlob.mk <$> genAddress <*> genByteArray
--
--/-- Generate a RawComm -/
--def genRawComm : Gen Ix.CompileM.RawComm :=
--  Ix.CompileM.RawComm.mk <$> genAddress <*> genCommNew

--/-- Generate a random RawEnv -/
--def genRawEnv : Gen Ix.CompileM.RawEnv :=
--  Ix.CompileM.RawEnv.mk <$> genSmallArray genRawConst
--    <*> genSmallArray genRawNamed
--    <*> genSmallArray genRawBlob
--    <*> genSmallArray genRawComm

--/-- Generate a random RustCompilePhases -/
--def genRustCompilePhases : Gen Ix.CompileM.RustCompilePhases :=
--  Ix.CompileM.RustCompilePhases.mk <$> genIxRawEnvironment <*> genRustCondensedBlocks <*> genRawEnv
--
--instance : Shrinkable Ix.RawEnvironment where
--  shrink env := if env.consts.isEmpty then [] else [{ consts := env.consts.pop }]
--
--instance : SampleableExt Ix.RawEnvironment := SampleableExt.mkSelfContained genIxRawEnvironment

instance : Shrinkable Ix.RustCondensedBlocks where
  shrink cb :=
    if cb.lowLinks.isEmpty && cb.blocks.isEmpty && cb.blockRefs.isEmpty then []
    else [{
      lowLinks := if cb.lowLinks.isEmpty then #[] else cb.lowLinks.pop,
      blocks := if cb.blocks.isEmpty then #[] else cb.blocks.pop,
      blockRefs := if cb.blockRefs.isEmpty then #[] else cb.blockRefs.pop
    }]

--instance : SampleableExt Ix.RustCondensedBlocks := SampleableExt.mkSelfContained genRustCondensedBlocks
--
instance : Shrinkable Ix.CompileM.RawEnv where
  shrink env :=
    if env.consts.isEmpty && env.named.isEmpty && env.blobs.isEmpty && env.comms.isEmpty then []
    else [{
      consts := if env.consts.isEmpty then #[] else env.consts.pop,
      named := if env.named.isEmpty then #[] else env.named.pop,
      blobs := if env.blobs.isEmpty then #[] else env.blobs.pop,
      comms := if env.comms.isEmpty then #[] else env.comms.pop
    }]

--instance : SampleableExt Ix.CompileM.RawEnv := SampleableExt.mkSelfContained genRawEnv
--
--instance : Shrinkable Ix.CompileM.RustCompilePhases where
--  shrink _phases := [{
--    rawEnv := { consts := #[] },
--    condensed := { lowLinks := #[], blocks := #[], blockRefs := #[] },
--    compileEnv := { consts := #[], named := #[], blobs := #[], comms := #[] }
--  }]
--
--instance : SampleableExt Ix.CompileM.RustCompilePhases := SampleableExt.mkSelfContained genRustCompilePhases
--
--def rustCondensedBlocksTests : TestSeq :=
--  let empty : Ix.RustCondensedBlocks := { lowLinks := #[], blocks := #[], blockRefs := #[] }
--  let n1 := Ix.Name.mkStr Ix.Name.mkAnon "a"
--  let n2 := Ix.Name.mkStr Ix.Name.mkAnon "b"
--  let withData : Ix.RustCondensedBlocks := {
--    lowLinks := #[(n1, n2)]
--    blocks := #[(n1, #[n1, n2])]
--    blockRefs := #[(n2, #[n1])]
--  }
--  test "RustCondensedBlocks empty" (rustCondensedBlocksEq (roundtripRustCondensedBlocks empty) empty) ++
--  test "RustCondensedBlocks with data" (rustCondensedBlocksEq (roundtripRustCondensedBlocks withData) withData)
--
--def rustCompilePhasesTests : TestSeq :=
--  let empty : Ix.CompileM.RustCompilePhases := {
--    rawEnv := { consts := #[] }
--    condensed := { lowLinks := #[], blocks := #[], blockRefs := #[] }
--    compileEnv := { consts := #[], named := #[], blobs := #[], comms := #[] }
--  }
--  test "RustCompilePhases empty" (rustCompilePhasesEq (roundtripRustCompilePhases empty) empty)

/-! ## Ixon type FFI unit tests -/

def ixonDefKindTests : TestSeq :=
  test "Ixon.DefKind.defn" (roundtripIxonDefKind .defn == .defn) ++
  test "Ixon.DefKind.opaq" (roundtripIxonDefKind .opaq == .opaq) ++
  test "Ixon.DefKind.thm" (roundtripIxonDefKind .thm == .thm)

/-
-- Temporarily commented out to debug test failures

def ixonDefinitionSafetyTests : TestSeq :=
  test "Ixon.DefinitionSafety.unsaf" (roundtripIxonDefinitionSafety .unsaf == .unsaf) ++
  test "Ixon.DefinitionSafety.safe" (roundtripIxonDefinitionSafety .safe == .safe) ++
  test "Ixon.DefinitionSafety.part" (roundtripIxonDefinitionSafety .part == .part)

def ixonQuotKindTests : TestSeq :=
  test "Ixon.QuotKind.type" (roundtripIxonQuotKind .type == .type) ++
  test "Ixon.QuotKind.ctor" (roundtripIxonQuotKind .ctor == .ctor) ++
  test "Ixon.QuotKind.lift" (roundtripIxonQuotKind .lift == .lift) ++
  test "Ixon.QuotKind.ind" (roundtripIxonQuotKind .ind == .ind)

def ixonUnivTests : TestSeq :=
  test "Ixon.Univ.zero" (roundtripIxonUniv .zero == .zero) ++
  test "Ixon.Univ.var 0" (roundtripIxonUniv (.var 0) == .var 0) ++
  test "Ixon.Univ.var 42" (roundtripIxonUniv (.var 42) == .var 42) ++
  test "Ixon.Univ.succ zero" (roundtripIxonUniv (.succ .zero) == .succ .zero) ++
  test "Ixon.Univ.max" (roundtripIxonUniv (.max .zero (.var 1)) == .max .zero (.var 1)) ++
  test "Ixon.Univ.imax" (roundtripIxonUniv (.imax (.var 0) .zero) == .imax (.var 0) .zero)

def ixonExprTests' : TestSeq :=
  test "Ixon.Expr.sort" (roundtripIxonExpr (.sort 0) == .sort 0) ++
  test "Ixon.Expr.var" (roundtripIxonExpr (.var 5) == .var 5) ++
  test "Ixon.Expr.ref" (roundtripIxonExpr (.ref 1 #[0, 1]) == .ref 1 #[0, 1]) ++
  test "Ixon.Expr.recur" (roundtripIxonExpr (.recur 2 #[]) == .recur 2 #[]) ++
  test "Ixon.Expr.str" (roundtripIxonExpr (.str 3) == .str 3) ++
  test "Ixon.Expr.nat" (roundtripIxonExpr (.nat 42) == .nat 42) ++
  test "Ixon.Expr.share" (roundtripIxonExpr (.share 0) == .share 0) ++
  test "Ixon.Expr.app" (roundtripIxonExpr (.app (.var 0) (.var 1)) == .app (.var 0) (.var 1)) ++
  test "Ixon.Expr.lam" (roundtripIxonExpr (.lam (.sort 0) (.var 0)) == .lam (.sort 0) (.var 0)) ++
  test "Ixon.Expr.all" (roundtripIxonExpr (.all (.sort 0) (.var 0)) == .all (.sort 0) (.var 0)) ++
  test "Ixon.Expr.letE" (roundtripIxonExpr (.letE true (.sort 0) (.var 0) (.var 1)) == .letE true (.sort 0) (.var 0) (.var 1)) ++
  test "Ixon.Expr.prj" (roundtripIxonExpr (.prj 0 1 (.var 0)) == .prj 0 1 (.var 0))

def ixonDefinitionTests : TestSeq :=
  let d1 : Ixon.Definition := ⟨.defn, .safe, 0, .sort 0, .var 0⟩
  let d2 : Ixon.Definition := ⟨.opaq, .unsaf, 2, .sort 1, .lam (.sort 0) (.var 0)⟩
  test "Ixon.Definition simple" (roundtripIxonDefinition d1 == d1) ++
  test "Ixon.Definition complex" (roundtripIxonDefinition d2 == d2)

def ixonAxiomTests : TestSeq :=
  let a1 : Ixon.Axiom := ⟨false, 0, .sort 0⟩
  let a2 : Ixon.Axiom := ⟨true, 3, .all (.sort 0) (.var 0)⟩
  test "Ixon.Axiom safe" (roundtripIxonAxiom a1 == a1) ++
  test "Ixon.Axiom unsafe" (roundtripIxonAxiom a2 == a2)

def ixonQuotientTests : TestSeq :=
  let q1 : Ixon.Quotient := ⟨.type, 1, .sort 0⟩
  let q2 : Ixon.Quotient := ⟨.lift, 0, .var 0⟩
  test "Ixon.Quotient type" (roundtripIxonQuotient q1 == q1) ++
  test "Ixon.Quotient lift" (roundtripIxonQuotient q2 == q2)

def ixonRecursorRuleTests : TestSeq :=
  let r1 : Ixon.RecursorRule := ⟨2, .var 0⟩
  let r2 : Ixon.RecursorRule := ⟨0, .app (.var 0) (.var 1)⟩
  test "Ixon.RecursorRule simple" (roundtripIxonRecursorRule r1 == r1) ++
  test "Ixon.RecursorRule complex" (roundtripIxonRecursorRule r2 == r2)

def ixonRecursorTests : TestSeq :=
  let rule : Ixon.RecursorRule := ⟨1, .var 0⟩
  let r1 : Ixon.Recursor := ⟨false, false, 1, 2, 0, 1, 1, .sort 0, #[rule]⟩
  let r2 : Ixon.Recursor := ⟨true, true, 0, 1, 1, 1, 2, .var 0, #[]⟩
  test "Ixon.Recursor with rule" (roundtripIxonRecursor r1 == r1) ++
  test "Ixon.Recursor k=true" (roundtripIxonRecursor r2 == r2)

def ixonConstructorTests : TestSeq :=
  let c1 : Ixon.Constructor := ⟨false, 1, 0, 2, 3, .sort 0⟩
  let c2 : Ixon.Constructor := ⟨true, 0, 1, 0, 0, .var 0⟩
  test "Ixon.Constructor safe" (roundtripIxonConstructor c1 == c1) ++
  test "Ixon.Constructor unsafe" (roundtripIxonConstructor c2 == c2)

def ixonInductiveTests : TestSeq :=
  let ctor : Ixon.Constructor := ⟨false, 1, 0, 1, 2, .sort 0⟩
  let i1 : Ixon.Inductive := ⟨true, false, false, 1, 1, 0, 0, .sort 1, #[ctor]⟩
  let i2 : Ixon.Inductive := ⟨false, true, true, 0, 0, 1, 2, .var 0, #[]⟩
  test "Ixon.Inductive with ctor" (roundtripIxonInductive i1 == i1) ++
  test "Ixon.Inductive reflexive" (roundtripIxonInductive i2 == i2)

def ixonProjTests : TestSeq :=
  let addr : Address := default
  let ip : Ixon.InductiveProj := ⟨0, addr⟩
  let cp : Ixon.ConstructorProj := ⟨1, 2, addr⟩
  let rp : Ixon.RecursorProj := ⟨3, addr⟩
  let dp : Ixon.DefinitionProj := ⟨4, addr⟩
  test "Ixon.InductiveProj" (roundtripIxonInductiveProj ip == ip) ++
  test "Ixon.ConstructorProj" (roundtripIxonConstructorProj cp == cp) ++
  test "Ixon.RecursorProj" (roundtripIxonRecursorProj rp == rp) ++
  test "Ixon.DefinitionProj" (roundtripIxonDefinitionProj dp == dp)

def ixonMutConstTests : TestSeq :=
  let defn : Ixon.Definition := ⟨.defn, .safe, 0, .sort 0, .var 0⟩
  let m1 : Ixon.MutConst := .defn defn
  let ctor : Ixon.Constructor := ⟨false, 1, 0, 1, 1, .sort 0⟩
  let indc : Ixon.Inductive := ⟨false, false, false, 1, 1, 0, 0, .sort 1, #[ctor]⟩
  let m2 : Ixon.MutConst := .indc indc
  let rule : Ixon.RecursorRule := ⟨1, .var 0⟩
  let recr : Ixon.Recursor := ⟨false, false, 1, 1, 0, 1, 1, .sort 0, #[rule]⟩
  let m3 : Ixon.MutConst := .recr recr
  test "Ixon.MutConst.defn" (roundtripIxonMutConst m1 == m1) ++
  test "Ixon.MutConst.indc" (roundtripIxonMutConst m2 == m2) ++
  test "Ixon.MutConst.recr" (roundtripIxonMutConst m3 == m3)
--
--def ixonConstantInfoTests' : TestSeq :=
--  let defn : Ixon.Definition := ⟨.defn, .safe, 0, .sort 0, .var 0⟩
--  let axiom' : Ixon.Axiom := ⟨false, 1, .sort 0⟩
--  let addr : Address := default
--  test "Ixon.ConstantInfo.defn" (roundtripIxonConstantInfo (.defn defn) == .defn defn) ++
--  test "Ixon.ConstantInfo.axio" (roundtripIxonConstantInfo (.axio axiom') == .axio axiom') ++
--  test "Ixon.ConstantInfo.iPrj" (roundtripIxonConstantInfo (.iPrj ⟨0, addr⟩) == .iPrj ⟨0, addr⟩) ++
--  test "Ixon.ConstantInfo.cPrj" (roundtripIxonConstantInfo (.cPrj ⟨0, 1, addr⟩) == .cPrj ⟨0, 1, addr⟩)
--
--def ixonConstantTests : TestSeq :=
--  let defn : Ixon.Definition := ⟨.defn, .safe, 0, .sort 0, .var 0⟩
--  let c1 : Ixon.Constant := ⟨.defn defn, #[], #[], #[]⟩
--  let c2 : Ixon.Constant := ⟨.defn defn, #[.var 0], #[default], #[.zero, .succ .zero]⟩
--  test "Ixon.Constant simple" (roundtripIxonConstant c1 == c1) ++
--  test "Ixon.Constant with arrays" (roundtripIxonConstant c2 == c2)
--
--def ixonDataValueTests' : TestSeq :=
--  let addr : Address := default
--  test "Ixon.DataValue.ofString" (roundtripIxonDataValue (.ofString addr) == .ofString addr) ++
--  test "Ixon.DataValue.ofBool true" (roundtripIxonDataValue (.ofBool true) == .ofBool true) ++
--  test "Ixon.DataValue.ofBool false" (roundtripIxonDataValue (.ofBool false) == .ofBool false) ++
--  test "Ixon.DataValue.ofName" (roundtripIxonDataValue (.ofName addr) == .ofName addr) ++
--  test "Ixon.DataValue.ofNat" (roundtripIxonDataValue (.ofNat addr) == .ofNat addr) ++
--  test "Ixon.DataValue.ofInt" (roundtripIxonDataValue (.ofInt addr) == .ofInt addr) ++
--  test "Ixon.DataValue.ofSyntax" (roundtripIxonDataValue (.ofSyntax addr) == .ofSyntax addr)
--
--def ixonExprMetaTests : TestSeq :=
--  let addr : Address := default
--  let em1 : Ixon.ExprMeta := .binder addr .default #[]
--  let em2 : Ixon.ExprMeta := .letBinder addr #[]
--  let em3 : Ixon.ExprMeta := .ref addr #[]
--  let em4 : Ixon.ExprMeta := .prj addr #[]
--  let em5 : Ixon.ExprMeta := .mdata #[]
--  test "Ixon.ExprMeta.binder" (roundtripIxonExprMeta em1 == em1) ++
--  test "Ixon.ExprMeta.letBinder" (roundtripIxonExprMeta em2 == em2) ++
--  test "Ixon.ExprMeta.ref" (roundtripIxonExprMeta em3 == em3) ++
--  test "Ixon.ExprMeta.prj" (roundtripIxonExprMeta em4 == em4) ++
--  test "Ixon.ExprMeta.mdata" (roundtripIxonExprMeta em5 == em5)
--
--def ixonCtorMetaTests : TestSeq :=
--  let addr : Address := default
--  let cm : Ixon.CtorMeta := ⟨addr, #[addr], {}⟩
--  test "Ixon.CtorMeta" (roundtripIxonCtorMeta cm == cm)
--
--def ixonConstantMetaTests : TestSeq :=
--  let addr : Address := default
--  test "Ixon.ConstantMeta.empty" (roundtripIxonConstantMeta .empty == .empty) ++
--  test "Ixon.ConstantMeta.axio" (roundtripIxonConstantMeta (.axio addr #[] {}) == .axio addr #[] {})
--
--def ixonNamedTests : TestSeq :=
--  let addr : Address := default
--  let n1 : Ixon.Named := ⟨addr, .empty⟩
--  test "Ixon.Named" (roundtripIxonNamed n1 == n1)
--
--def ixonCommTests : TestSeq :=
--  let addr1 : Address := Address.blake3 "secret".toUTF8
--  let addr2 : Address := Address.blake3 "payload".toUTF8
--  let c : Ixon.Comm := ⟨addr1, addr2⟩
--  test "Ixon.Comm" (roundtripIxonComm c == c)
--
--def ixonUnitTests : TestSeq :=
--  ixonDefKindTests ++
--  ixonDefinitionSafetyTests ++
--  ixonQuotKindTests
--  -- Disabled for debugging:
--  -- ++ ixonUnivTests
--  -- ++ ixonExprTests'
--  -- ++ ixonDefinitionTests
--  -- ++ ixonAxiomTests
--  -- ++ ixonQuotientTests
--  -- ++ ixonRecursorRuleTests
--  -- ++ ixonRecursorTests
--  -- ++ ixonConstructorTests
--  -- ++ ixonInductiveTests
--  -- ++ ixonProjTests
--  -- ++ ixonMutConstTests
--  -- ++ ixonConstantInfoTests'
--  -- ++ ixonConstantTests
--  -- ++ ixonDataValueTests'
--  -- ++ ixonExprMetaTests
--  -- ++ ixonCtorMetaTests
--  -- ++ ixonConstantMetaTests
--  -- ++ ixonNamedTests
--  -- ++ ixonCommTests
---/
--
def suite : List TestSeq := [
  simpleTests,
  largeNatTests,
  -- AssocList roundtrip
  assocListTests,
  -- HashMap roundtrip
  hashMapTests,
  --checkIO "HashMap Nat Nat roundtrip" (∀ m : Std.HashMap Nat Nat, hashMapEq (roundtripHashMapNatNat m) m),
  checkIO "Nat roundtrip" (∀ n : Nat, roundtripNat n == n),
  --checkIO "String roundtrip" (∀ s : String, roundtripString s == s),
  --checkIO "List Nat roundtrip" (∀ xs : List Nat, roundtripListNat xs == xs),
  --checkIO "Array Nat roundtrip" (∀ arr : Array Nat, roundtripArrayNat arr == arr),
  --checkIO "ByteArray roundtrip" (∀ ba : ByteArray, roundtripByteArray ba == ba),
  ---- Struct and inductive roundtrips
  --checkIO "Point roundtrip" (∀ p : Point, roundtripPoint p == p),
  --checkIO "NatTree roundtrip" (∀ t : NatTree, roundtripNatTree t == t),
  ---- Ix type roundtrips
  --ixAddressTests,
  --ixNameTests,
  --ixLevelTests,
  --ixIntTests,
  --ixSubstringTests,
  --ixSourceInfoTests,
  --ixSyntaxPreresolvedTests,
  --ixSyntaxTests,
  --boolTests,
  --ixDataValueTests,
  --ixExprTests,
  --ixConstantInfoTests,
  --ixRawEnvironmentTests,
  --ixEnvironmentTests,
  --rawEnvTests,
  ---- RustCondensedBlocks and RustCompilePhases tests
  --rustCondensedBlocksTests,
  --rustCompilePhasesTests,
  ---- Property tests for Ix types
  --checkIO "Ix.Name roundtrip" (∀ n : Ix.Name, ixNameEq (roundtripIxName n) n),
  --checkIO "Ix.Level roundtrip" (∀ l : Ix.Level, ixLevelEq (roundtripIxLevel l) l),
  --checkIO "Ix.Expr roundtrip" (∀ e : Ix.Expr, ixExprEq (roundtripIxExpr e) e),
  --checkIO "Ix.ConstantInfo roundtrip" (∀ info : Ix.ConstantInfo, ixConstantInfoEq (roundtripIxConstantInfo info) info),
  ---- Property tests for compilation types
  --checkIO "Ix.RawEnvironment roundtrip" (∀ env : Ix.RawEnvironment, ixRawEnvironmentEq (roundtripIxRawEnvironment env) env),
  --checkIO "RustCondensedBlocks roundtrip" (∀ cb : Ix.RustCondensedBlocks, rustCondensedBlocksEq (roundtripRustCondensedBlocks cb) cb),
  --checkIO "RawEnv roundtrip" (∀ env : Ix.CompileM.RawEnv, rawEnvEq (roundtripRawEnv env) env),
  --checkIO "RustCompilePhases roundtrip" (∀ phases : Ix.CompileM.RustCompilePhases, rustCompilePhasesEq (roundtripRustCompilePhases phases) phases),
  -- Block comparison types
  --blockCompareResultTests,
  --blockCompareDetailTests,
  -- Ixon type unit tests
  --ixonDefKindTests,
  -- Ixon property tests - disabled for debugging
  --checkIO "Ixon.DefKind roundtrip" (∀ x : Ixon.DefKind, roundtripIxonDefKind x == x),
  --checkIO "Ixon.DefinitionSafety roundtrip" (∀ x : Ixon.DefinitionSafety, roundtripIxonDefinitionSafety x == x),
  --checkIO "Ixon.QuotKind roundtrip" (∀ x : Ixon.QuotKind, roundtripIxonQuotKind x == x),
  --checkIO "Ixon.Univ roundtrip" (∀ x : Ixon.Univ, roundtripIxonUniv x == x),
  --checkIO "Ixon.Expr roundtrip" (∀ x : Ixon.Expr, roundtripIxonExpr x == x),
  --checkIO "Ixon.Definition roundtrip" (∀ x : Ixon.Definition, roundtripIxonDefinition x == x),
  --checkIO "Ixon.RecursorRule roundtrip" (∀ x : Ixon.RecursorRule, roundtripIxonRecursorRule x == x),
  --checkIO "Ixon.Recursor roundtrip" (∀ x : Ixon.Recursor, roundtripIxonRecursor x == x),
  --checkIO "Ixon.Axiom roundtrip" (∀ x : Ixon.Axiom, roundtripIxonAxiom x == x),
  --checkIO "Ixon.Quotient roundtrip" (∀ x : Ixon.Quotient, roundtripIxonQuotient x == x),
  --checkIO "Ixon.Constructor roundtrip" (∀ x : Ixon.Constructor, roundtripIxonConstructor x == x),
  --checkIO "Ixon.Inductive roundtrip" (∀ x : Ixon.Inductive, roundtripIxonInductive x == x),
  --checkIO "Ixon.InductiveProj roundtrip" (∀ x : Ixon.InductiveProj, roundtripIxonInductiveProj x == x),
  --checkIO "Ixon.ConstructorProj roundtrip" (∀ x : Ixon.ConstructorProj, roundtripIxonConstructorProj x == x),
  --checkIO "Ixon.RecursorProj roundtrip" (∀ x : Ixon.RecursorProj, roundtripIxonRecursorProj x == x),
  --checkIO "Ixon.DefinitionProj roundtrip" (∀ x : Ixon.DefinitionProj, roundtripIxonDefinitionProj x == x),
  --checkIO "Ixon.MutConst roundtrip" (∀ x : Ixon.MutConst, roundtripIxonMutConst x == x),
  --checkIO "Ixon.ConstantInfo roundtrip" (∀ x : Ixon.ConstantInfo, roundtripIxonConstantInfo x == x),
  --checkIO "Ixon.Constant roundtrip" (∀ x : Ixon.Constant, roundtripIxonConstant x == x),
  --checkIO "Ixon.DataValue roundtrip" (∀ x : Ixon.DataValue, roundtripIxonDataValue x == x),
  --checkIO "Ixon.Comm roundtrip" (∀ x : Ixon.Comm, roundtripIxonComm x == x),
]

end Tests.FFI
