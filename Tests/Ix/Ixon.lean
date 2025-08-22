import Ix.Ixon
import Ix.Ixon.Serialize
import Ix.Ixon.Univ
import LSpec.SlimCheck.Gen
import LSpec

import Tests.Common
import Tests.Ix.Common

open LSpec
open SlimCheck
open SlimCheck.Gen
open Ixon

-- Univ

namespace Ixon

def genUniv : Gen Ixon.Univ := getSize >>= go
  where
    go : Nat -> Gen Ixon.Univ
    | 0 => return .const 0
    | Nat.succ f =>
      frequency [
        (100, .const <$> genUInt64),
        (100, .var <$> genUInt64),
        (50, .add <$> genUInt64 <*> go f),
        (25, .max <$> go f <*> go f),
        (25, .imax <$> go f <*> go f)
      ]

instance : Shrinkable Univ where
  shrink _ := []

instance : SampleableExt Univ := SampleableExt.mkSelfContained genUniv

-- Expr

def genExpr : SlimCheck.Gen Ixon := getSize >>= go
  where
    go : Nat -> SlimCheck.Gen Ixon
    | 0 => return .vari 0
    | Nat.succ f =>
      frequency [
        (100, .vari <$> genUInt64),
        (100, .sort <$> genUniv),
        (100, .refr <$> genAddress <*> resizeListOf genUniv),
        (100, .recr <$> genUInt64 <*> resizeListOf genUniv),
        (30, .apps <$> go f <*> go f <*> resizeListOf (go f)),
        (30, .lams <$> resizeListOf (go f) <*> go f),
        (30, .alls <$> resizeListOf (go f) <*> go f),
        (15, .letE .true <$> go f <*> go f <*> go f),
        (15, .letE .false <$> go f <*> go f <*> go f),
        (50, .proj <$> genAddress <*> genUInt64 <*> go f),
        (100, .strl <$> genString),
        (100, .natl <$> chooseAny Nat)
      ]

structure IxonExpr where
  ixon : Ixon
deriving BEq, Repr

instance : Serialize IxonExpr where
  put x := Serialize.put x.ixon
  get := .mk <$> Serialize.get

-- TODO: useful shrinking
instance : Shrinkable IxonExpr where
  shrink _ := []

instance : SampleableExt IxonExpr := 
  SampleableExt.mkSelfContained (IxonExpr.mk <$> genExpr)

-- Metadata
def genMetadatum : Gen Ixon.Metadatum := 
  frequency [
    (100, .name <$> genName),
    (100, .info <$> genBinderInfo),
    (100, .link <$> genAddress),
    (100, .hints <$> genReducibilityHints),
    (25, .all <$> genList' genName),
  ]

instance : Shrinkable Metadatum where
  shrink _ := []

instance : SampleableExt Metadatum :=
  SampleableExt.mkSelfContained genMetadatum

def genMetaNode : Gen (List Metadatum) := 
  genList' genMetadatum

def genMetadata : Gen Metadata := do
  let xs ← genList' genMetaNode
  return .mk (Batteries.RBMap.ofList ((List.range xs.length).zip xs) compare)

-- Const
def genAxiom : Gen Axiom := .mk <$> genNat' <*> genAddress <*> genBool

-- TODO: useful shrinking
instance : Shrinkable Axiom where
  shrink _ := []

instance : SampleableExt Axiom 
  := SampleableExt.mkSelfContained genAxiom

def genDefinition : Gen Definition := do
  let lvls <- genNat'
  let type <- genAddress
  let mode <- genDefKind
  let value <- genAddress
  let safety <- oneOf #[pure .safe, pure .unsafe, pure .partial]
  return .mk lvls type mode value safety

def genConstructor : Gen Constructor :=
  .mk <$> genNat' <*> genAddress <*> genNat' <*> genNat' <*> genNat' <*> genBool

-- TODO: useful shrinking
instance : Shrinkable Constructor where
  shrink _ := []

instance : SampleableExt Constructor
  := SampleableExt.mkSelfContained genConstructor

def genRecursorRule : Gen RecursorRule := .mk <$> genNat' <*> genAddress

-- TODO: useful shrinking
instance : Shrinkable RecursorRule where
  shrink _ := []

instance : SampleableExt RecursorRule
  := SampleableExt.mkSelfContained genRecursorRule

def genRecursor : Gen Recursor :=
  .mk <$> genNat' <*> genAddress <*> genNat' <*> genNat' <*> genNat'
    <*> genNat' <*> genList' genRecursorRule <*> genBool <*> genBool

-- TODO: useful shrinking
instance : Shrinkable Recursor where
  shrink _ := []

instance : SampleableExt Recursor
  := SampleableExt.mkSelfContained genRecursor

def genInductive : Gen Inductive :=
  .mk <$> genNat' <*> genAddress <*> genNat' <*> genNat'
    <*> genList' genConstructor <*> genList' genRecursor <*> genNat'
    <*> genBool <*> genBool <*> genBool

-- TODO: useful shrinking
instance : Shrinkable Inductive where
  shrink _ := []

instance : SampleableExt Inductive
  := SampleableExt.mkSelfContained genInductive

def genConstructorProj : Gen ConstructorProj :=
  .mk <$> genAddress <*> genNat' <*> genNat'

def genRecursorProj : Gen RecursorProj :=
  .mk <$> genAddress <*> genNat' <*> genNat'

def genDefinitionProj : Gen DefinitionProj :=
  .mk <$> genAddress <*> genNat'

def genInductiveProj : Gen InductiveProj :=
  .mk <$> genAddress <*> genNat'

def genConst : Gen Ixon := getSize >>= go
  where
    go : Nat -> Gen Ixon
    | 0 => .axio <$> genAxiom
    | Nat.succ _ =>
      frequency [
        (100, .axio <$> genAxiom),
        (100, .defn <$> genDefinition),
        (100, .cprj <$> genConstructorProj),
        (100, .rprj <$> genRecursorProj),
        (100, .iprj <$> genInductiveProj),
        (100, .dprj <$> genDefinitionProj),
        (100, .defs <$> genList' genDefinition),
        (100, .inds <$> genList' genInductive),
        (100, .meta <$> genMetadata),
      ]

structure IxonConst where
  ixon : Ixon
deriving BEq, Repr

instance : Serialize IxonConst where
  put x := Serialize.put x.ixon
  get := .mk <$> Serialize.get

-- TODO: useful shrinking
instance : Shrinkable IxonConst where
  shrink _ := []

instance : SampleableExt IxonConst 
  := SampleableExt.mkSelfContained (IxonConst.mk <$> genConst)

end Ixon
