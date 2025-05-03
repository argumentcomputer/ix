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

def genExpr : SlimCheck.Gen Ixon.Expr := getSize >>= go
  where
    go : Nat -> SlimCheck.Gen Ixon.Expr
    | 0 => return .vari 0
    | Nat.succ f =>
      frequency [
        (100, .vari <$> genUInt64),
        (100, .sort <$> genUniv),
        (100, .cnst <$> genAddress <*> resizeListOf genUniv),
        (100, .rec_ <$> genUInt64 <*> resizeListOf genUniv),
        (30, .apps <$> go f <*> go f <*> resizeListOf (go f)),
        (30, .lams <$> resizeListOf (go f) <*> go f),
        (30, .alls <$> resizeListOf (go f) <*> go f),
        (15, .let_ .true <$> go f <*> go f <*> go f),
        (15, .let_ .false <$> go f <*> go f <*> go f),
        (50, .proj <$> genAddress <*> genUInt64 <*> go f),
        (100, .strl <$> genString),
        (100, .natl <$> chooseAny Nat)
      ]

-- TODO: useful shrinking
instance : Shrinkable Expr where
  shrink _ := []

instance : SampleableExt Expr := SampleableExt.mkSelfContained genExpr

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

def genAxiom : Gen Axiom := .mk <$> genNat' <*> genExpr

def genDefinition : Gen Definition := do
  let lvls <- genNat'
  let type <- genExpr
  let mode <- genDefMode
  let value <- genExpr
  let isPartial <- genBool
  return .mk lvls type mode value isPartial

def genConstructor : Gen Constructor :=
  .mk <$> genNat' <*> genExpr <*> genNat' <*> genNat' <*> genNat'

def genRecursorRule : Gen RecursorRule := .mk <$> genNat' <*> genExpr

def genRecursor : Gen Recursor :=
  .mk <$> genNat' <*> genExpr <*> genNat' <*> genNat' <*> genNat'
    <*> genNat' <*> genList' genRecursorRule <*> genBool

def genInductive : Gen Inductive :=
  .mk <$> genNat' <*> genExpr <*> genNat' <*> genNat'
    <*> genList' genConstructor <*> genList' genRecursor <*> genNat'
    <*> genBool <*> genBool

def genConstructorProj : Gen ConstructorProj :=
  .mk <$> genAddress <*> genNat' <*> genNat'

def genRecursorProj : Gen RecursorProj :=
  .mk <$> genAddress <*> genNat' <*> genNat'

def genDefinitionProj : Gen DefinitionProj :=
  .mk <$> genAddress <*> genNat'

def genInductiveProj : Gen InductiveProj :=
  .mk <$> genAddress <*> genNat'


def genConst : Gen Ixon.Const := getSize >>= go
  where
    go : Nat -> Gen Ixon.Const
    | 0 => return .axio ⟨0, .vari 0⟩
    | Nat.succ _ =>
      frequency [
        (100, .axio <$> genAxiom),
        (100, .defn <$> genDefinition),
        --(100, .ctor <$> genConstructor),
        --(100, .recr <$> genRecursor),
        --(100, .indc <$> genInductive),
        (100, .ctorProj <$> genConstructorProj),
        (100, .recrProj <$> genRecursorProj),
        (100, .indcProj <$> genInductiveProj),
        (100, .defnProj <$> genDefinitionProj),
        (100, .mutDef <$> genList' genDefinition),
        (100, .mutInd <$> genList' genInductive),
        (100, .meta <$> genMetadata),
      ]

-- TODO: useful shrinking
instance : Shrinkable Const where
  shrink _ := []

instance : SampleableExt Const := SampleableExt.mkSelfContained genConst
end Ixon
