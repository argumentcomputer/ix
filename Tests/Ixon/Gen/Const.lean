import LSpec
import Ix.Ixon
import LSpec.SlimCheck.Gen
import LSpec

import Tests.Ixon.Gen.Common
import Tests.Ixon.Gen.Univ
import Tests.Ixon.Gen.Expr
import Tests.Ixon.Gen.Metadata

open LSpec
open SlimCheck
open SlimCheck.Gen
open Ixon

def genAxiom : Gen Axiom := .mk <$> genNat' <*> genExpr
def genTheorem : Gen Theorem := .mk <$> genNat' <*> genExpr <*> genExpr
def genOpaque : Gen Opaque := .mk <$> genNat' <*> genExpr <*> genExpr
def genDefinition : Gen Definition := 
  .mk <$> genNat' <*> genExpr <*> genExpr <*> genBool

def genConstructor : Gen Constructor :=
  .mk <$> genNat' <*> genExpr <*> genNat' <*> genNat' <*> genNat'

def genRecursorRule : Gen RecursorRule := .mk <$> genNat' <*> genExpr

def genRecursor : Gen Recursor :=
  .mk <$> genNat' <*> genExpr <*> genNat' <*> genNat' <*> genNat'
    <*> genNat' <*> genList' genRecursorRule <*> genBool <*> genBool

def genInductive : Gen Inductive :=
  .mk <$> genNat' <*> genExpr <*> genNat' <*> genNat'
    <*> genList' genConstructor <*> genList' genRecursor
    <*> genBool <*> genBool <*> genBool <*> genBool 

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
        (100, .theo <$> genTheorem),
        (100, .opaq <$> genOpaque),
        (100, .defn <$> genDefinition),
        (100, .ctor <$> genConstructor),
        (100, .recr <$> genRecursor),
        (100, .indc <$> genInductive),
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
