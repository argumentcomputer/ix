import Ix.Ixon
import Tests.Common

open LSpec SlimCheck Gen

def genAddress : Gen Address :=
  pure (Address.mk (Blake3.hash "foobar".toUTF8).val)

def genNat : Gen Nat := USize.toNat <$> genUSize

def genBool : Gen Bool := choose Bool .false true

-- aggressively reduce size parameter to avoid tree blow-up
def genList (n: Gen α) : Gen (List α) :=
  resize (fun s => if s > 8 then 8 else s / 2) $ listOf n

def genDefKind : Gen Ix.DefKind :=
  elements #[.definition, .opaque, .theorem]

def genDefinitionSafety : Gen Lean.DefinitionSafety :=
  elements #[.unsafe, .safe, .partial]

def genDefinition : Gen Ixon.Definition :=
  .mk <$> genDefKind <*> genDefinitionSafety <*> genNat <*> genAddress <*> genAddress

def genAxiom : Gen Ixon.Axiom :=
  .mk <$> genBool <*> genNat <*> genAddress

def genQuotKind : Gen Lean.QuotKind :=
  elements #[.type, .ctor, .lift, .ind]

def genQuotient : Gen Ixon.Quotient :=
  .mk <$> genQuotKind <*> genNat <*> genAddress

def genConstructorProj : Gen Ixon.ConstructorProj :=
  .mk <$> genNat <*> genNat <*> genAddress

def genRecursorProj : Gen Ixon.RecursorProj :=
  .mk <$> genNat <*> genNat <*> genAddress

def genInductiveProj : Gen Ixon.InductiveProj :=
  .mk <$> genNat <*> genAddress

def genDefinitionProj : Gen Ixon.DefinitionProj :=
  .mk <$> genNat <*> genAddress

def genRecursorRule : Gen Ixon.RecursorRule :=
  .mk <$> genNat <*> genAddress

def genRecursor : Gen Ixon.Recursor :=
  .mk <$> genBool <*> genBool <*> genNat <*> genNat <*> genNat <*> genNat <*> genNat
    <*> genAddress <*> genList genRecursorRule

def genConstructor : Gen Ixon.Constructor :=
  .mk <$> genBool <*> genNat <*> genNat <*> genNat <*> genNat <*> genAddress

def genInductive : Gen Ixon.Inductive :=
  .mk <$> genBool <*> genBool <*> genBool <*> genNat <*> genNat <*> genNat <*> genNat
    <*> genAddress <*> genList genConstructor <*> genList genRecursor

def genEvalClaim : Gen Ixon.EvalClaim :=
  .mk <$> genAddress <*> genAddress <*> genAddress <*> genAddress

def genCheckClaim : Gen Ixon.CheckClaim :=
  .mk <$> genAddress <*> genAddress <*> genAddress

def genClaim : Gen Ixon.Claim :=
  frequency [(10, .evals <$> genEvalClaim), (10, .checks <$> genCheckClaim)]

def genProof : Gen Ixon.Proof :=
  .mk <$> genClaim <*> pure "foobar".toUTF8

def genComm : Gen Ixon.Comm :=
  .mk <$> genAddress <*> genAddress

def genMetaAddress : Gen MetaAddress :=
  .mk <$> genAddress <*> genAddress

def genEnv : Gen Ixon.Env :=
  .mk <$> genList genMetaAddress

def genBinderInfo : Gen Lean.BinderInfo :=
  elements #[.default, .implicit, .strictImplicit, .instImplicit]

def genReducibilityHints : Gen Lean.ReducibilityHints :=
  frequency [
    (10, pure .opaque),
    (10, pure .abbrev),
    (10, .regular <$> genUInt32),
  ]

def genDataValue : Gen Ixon.DataValue :=
  frequency [
    (10, .ofString <$> genAddress),
    (10, .ofBool <$> genBool),
    (10, .ofName <$> genAddress),
    (10, .ofNat <$> genAddress),
    (10, .ofInt <$> genAddress),
    (10, .ofSyntax <$> genAddress),
  ]

def genMetadatum : Gen Ixon.Metadatum :=
  frequency [
    (10, .name <$> genAddress),
    (10, .info <$> genBinderInfo),
    (10, .link <$> genAddress),
    (10, .hints <$> genReducibilityHints),
    (10, .all <$> genList genAddress),
    (10, .kvmap <$> genList (Prod.mk <$> genAddress <*> genDataValue)),
  ]

def genMetadata : Gen Ixon.Metadata :=
  .mk <$> genList genMetadatum

partial def genIxon : Gen Ixon.Ixon :=
  frequency [
    (10, pure .nanon),
    (10, .nstr <$> genAddress <*> genAddress),
    (10, .nnum <$> genAddress <*> genAddress),
    (10, pure .uzero),
    (10, .usucc <$> genAddress),
    (10, .umax <$> genAddress <*> genAddress),
    (10, .uimax <$> genAddress <*> genAddress),
    (10, .uvar <$> genNat),
    (10, .evar <$> genNat),
    (10, .eref <$> genAddress <*> genList genAddress),
    (10, .erec <$> genNat <*> genList genAddress),
    (10, .eprj <$> genAddress <*> genNat <*> genAddress),
    (10, .esort <$> genAddress),
    (10, .estr <$> genAddress),
    (10, .enat <$> genAddress),
    (10, .eapp <$> genAddress <*> genAddress),
    (10, .elam <$> genAddress <*> genAddress),
    (10, .eall <$> genAddress <*> genAddress),
    (10, .elet <$> genBool <*> genAddress <*> genAddress <*> genAddress),
    (10, .list <$> genList genIxon),
    (10, .defn <$> genDefinition),
    (10, .axio <$> genAxiom),
    (10, .quot <$> genQuotient),
    (10, .cprj <$> genConstructorProj),
    (10, .rprj <$> genRecursorProj),
    (10, .iprj <$> genInductiveProj),
    (10, .dprj <$> genDefinitionProj),
    (10, .inds <$> genList genInductive),
    (10, .defs <$> genList genDefinition),
    (10, .prof <$> genProof),
    (10, .eval <$> genEvalClaim),
    (10, .chck <$> genCheckClaim),
    (10, .comm <$> genComm),
    (10, .envn <$> genEnv),
    (10, .meta <$> genMetadata),
  ]

instance : Shrinkable Ixon.Ixon where
  shrink _ := []

instance : SampleableExt Ixon.Ixon := SampleableExt.mkSelfContained genIxon

def ixonSerde (ixon : Ixon.Ixon) : Bool :=
  let bytes := Ixon.ser ixon
  match Ixon.de bytes with
  | .ok ixon' => ixon == ixon'
  | .error _ => false

def Tests.Ixon.suite := [
  check "Ixon serde roundtrips" (∀ ixon : Ixon.Ixon, ixonSerde ixon)
]

-- import Ix.Ixon
-- import Ix.Claim
-- import Ix.Ixon.Serialize
-- import Ix.Ixon.Univ
-- import LSpec.SlimCheck.Gen
-- import LSpec

-- import Tests.Common
-- import Tests.Ix.Common

-- open LSpec
-- open SlimCheck
-- open SlimCheck.Gen
-- open Ixon

-- -- Univ
-- namespace Ixon

-- def genUniv : Gen Ixon.Univ := getSize >>= go
--   where
--     go : Nat -> Gen Ixon.Univ
--     | 0 => return .const 0
--     | Nat.succ f =>
--       frequency [
--         (100, .const <$> genUInt64),
--         (100, .var <$> genUInt64),
--         (50, .add <$> genUInt64 <*> go f),
--         (25, .max <$> go f <*> go f),
--         (25, .imax <$> go f <*> go f)
--       ]

-- instance : Shrinkable Univ where
--   shrink _ := []

-- instance : SampleableExt Univ := SampleableExt.mkSelfContained genUniv

-- -- Expr

-- def genExpr : SlimCheck.Gen Ixon := getSize >>= go
--   where
--     go : Nat -> SlimCheck.Gen Ixon
--     | 0 => return .vari 0
--     | Nat.succ f =>
--       frequency [
--         (100, .vari <$> genUInt64),
--         (100, .sort <$> genUniv),
--         (100, .refr <$> genAddress <*> genList genUniv),
--         (100, .recr <$> genUInt64 <*> genList genUniv),
--         (15, .apps <$> go f <*> go f <*> genList (go f)),
--         (15, .lams <$> genList (go f) <*> go f),
--         (15, .alls <$> genList (go f) <*> go f),
--         (15, .letE .true <$> go f <*> go f <*> go f),
--         (15, .letE .false <$> go f <*> go f <*> go f),
--         (50, .proj <$> genAddress <*> genUInt64 <*> go f),
--         (100, .strl <$> genString),
--         (100, .natl <$> chooseAny Nat)
--       ]

-- structure IxonExpr where
--   ixon : Ixon
-- deriving BEq, Repr

-- instance : Serialize IxonExpr where
--   put x := Serialize.put x.ixon
--   get := .mk <$> Serialize.get

-- -- TODO: useful shrinking
-- instance : Shrinkable IxonExpr where
--   shrink _ := []

-- instance : SampleableExt IxonExpr :=
--   SampleableExt.mkSelfContained (IxonExpr.mk <$> genExpr)

-- -- Metadata
-- def genMetadatum : Gen Ixon.Metadatum :=
--   frequency [
--     (50, .name <$> genName),
--     (100, .info <$> genBinderInfo),
--     (100, .link <$> genAddress),
--     (100, .hints <$> genReducibilityHints),
--     (10, .all <$> genList genName),
--   ]

-- instance : Shrinkable Metadatum where
--   shrink _ := []

-- instance : SampleableExt Metadatum :=
--   SampleableExt.mkSelfContained genMetadatum

-- def genMetaNode : Gen (List Metadatum) := genList genMetadatum

-- def genMetadata : Gen Metadata := do
--   let xs ← genList genMetaNode
--   return .mk ((List.range xs.length).zip xs)

-- instance : Shrinkable Metadata where
--   shrink _ := []

-- instance : SampleableExt Metadata :=
--   SampleableExt.mkSelfContained genMetadata

-- -- Const
-- def genAxiom : Gen Axiom := .mk <$> genBool <*> genNat <*> genAddress

-- -- TODO: useful shrinking
-- instance : Shrinkable Axiom where
--   shrink _ := []

-- instance : SampleableExt Axiom
--   := SampleableExt.mkSelfContained genAxiom

-- def genDefinition : Gen Definition := do
--   let lvls <- genNat
--   let type <- genAddress
--   let kind <- genDefKind
--   let value <- genAddress
--   let safety <- oneOf #[pure .safe, pure .unsafe, pure .partial]
--   return .mk kind safety lvls type value

-- def genConstructor : Gen Constructor :=
--   .mk <$> genBool <*> genNat <*> genNat <*> genNat <*> genNat <*> genAddress

-- -- TODO: useful shrinking
-- instance : Shrinkable Constructor where
--   shrink _ := []

-- instance : SampleableExt Constructor
--   := SampleableExt.mkSelfContained genConstructor

-- def genRecursorRule : Gen RecursorRule := .mk <$> genNat <*> genAddress

-- -- TODO: useful shrinking
-- instance : Shrinkable RecursorRule where
--   shrink _ := []

-- instance : SampleableExt RecursorRule
--   := SampleableExt.mkSelfContained genRecursorRule

-- def genRecursor : Gen Recursor :=
--   .mk <$> genBool <*> genBool <*> genNat <*> genNat <*> genNat <*> genNat
--     <*> genNat <*> genAddress <*> genList genRecursorRule

-- -- TODO: useful shrinking
-- instance : Shrinkable Recursor where
--   shrink _ := []

-- instance : SampleableExt Recursor
--   := SampleableExt.mkSelfContained genRecursor

-- def genInductive : Gen Inductive :=
--   .mk <$> genBool <*> genBool <*> genBool
--     <*> genNat <*> genNat <*> genNat <*> genNat
--     <*> genAddress <*> genList genConstructor <*> genList genRecursor

-- -- TODO: useful shrinking
-- instance : Shrinkable Inductive where
--   shrink _ := []

-- instance : SampleableExt Inductive
--   := SampleableExt.mkSelfContained genInductive

-- def genConstructorProj : Gen ConstructorProj :=
--   .mk <$> genNat <*> genNat <*> genAddress

-- def genRecursorProj : Gen RecursorProj :=
--   .mk <$> genNat <*> genNat <*> genAddress

-- def genDefinitionProj : Gen DefinitionProj :=
--   .mk <$> genNat <*> genAddress

-- def genInductiveProj : Gen InductiveProj :=
--   .mk <$> genNat <*> genAddress

-- def genCheckClaim : Gen CheckClaim :=
--   .mk <$> genAddress <*> genAddress <*> genAddress

-- def genEvalClaim : Gen EvalClaim :=
--   .mk <$> genAddress <*> genAddress <*> genAddress <*> genAddress

-- def genClaim: Gen Claim :=
--   oneOf #[.checks <$> genCheckClaim, .evals <$> genEvalClaim]

-- -- TODO: different dummy ByteArray perhaps
-- def genProof: Gen Proof := .mk <$> genClaim <*> (Address.hash <$> genAddress)

-- def genComm: Gen Comm := .mk <$> genAddress <*> genAddress

-- def genEnvn: Gen Env := .mk <$> genList ((·,·) <$> genAddress <*> genAddress)

-- def genConst : Gen Ixon := getSize >>= go
--   where
--     go : Nat -> Gen Ixon
--     | 0 => .axio <$> genAxiom
--     | Nat.succ _ =>
--       frequency [
--         (100, .axio <$> genAxiom),
--         (100, .defn <$> genDefinition),
--         (100, .cprj <$> genConstructorProj),
--         (100, .rprj <$> genRecursorProj),
--         (100, .iprj <$> genInductiveProj),
--         (100, .dprj <$> genDefinitionProj),
--         (100, .defs <$> genList genDefinition),
--         (100, .inds <$> genList genInductive),
--         (100, .meta <$> genMetadata),
--         (100, .prof <$> genProof),
--         (100, .eval <$> genEvalClaim),
--         (100, .chck <$> genCheckClaim),
--         (100, .comm <$> genComm),
--         (100, .envn <$> genEnvn),
--       ]

-- structure IxonConst where
--   ixon : Ixon
-- deriving BEq, Repr

-- instance : Serialize IxonConst where
--   put x := Serialize.put x.ixon
--   get := .mk <$> Serialize.get

-- -- TODO: useful shrinking
-- instance : Shrinkable IxonConst where
--   shrink _ := []

-- instance : SampleableExt IxonConst
--   := SampleableExt.mkSelfContained (IxonConst.mk <$> genConst)

-- -- TODO: useful shrinking
-- instance : Shrinkable Claim where
--   shrink _ := []

-- instance : SampleableExt Claim
--   := SampleableExt.mkSelfContained genClaim

-- /--
-- Whether the provided IxonFFI term, reconstructed and serialized in Rust, matches
-- the provided bytes.
-- -/
-- @[extern "rs_eq_lean_rust_serialization"]
-- opaque eqLeanRustSerialization : @& IxonFFI -> @& ByteArray -> Bool

-- end Ixon
