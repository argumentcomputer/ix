import LSpec
import Ix.Ixon
import Ix.Address
import Ix.Ixon.Serialize
import Ix.Ixon.Univ
import LSpec.SlimCheck.Gen
import LSpec
import Blake3

import Tests.Ixon.Gen
import Tests.Ixon.Gen.Common
import Tests.Ixon.Gen.Univ
import Tests.Ixon.Gen.Expr
import Tests.Ixon.Gen.Const

open LSpec
open SlimCheck
open SlimCheck.Gen
open Ixon


def serde [Serialize A] [BEq A] (x: A) : Bool :=
  match Serialize.get (Serialize.put x) with
  | .ok (y : A) => x == y
  | _ => false

instance : Serialize (List Expr) where
  put xs := runPut (putArray (putExpr <$> xs))
  get := runGet (getArray getExpr)

instance : Shrinkable (List Expr) where
  shrink _ := []
instance : SampleableExt (List Expr) := SampleableExt.mkSelfContained (genList' genExpr)

--def myConfig : SlimCheck.Configuration where
--  maxSize := 100
--  traceDiscarded := true
--  traceSuccesses := true
--  traceShrink := true
--  traceShrinkCandidates := true

--  SlimCheck.Checkable.check (∀ x: Expr, serde x) myConfig
def Tests.Ixon.suite := do
  [
    check "universe serde" (∀ x : Univ, serde x),
    check "expr serde" (∀ x : Expr, serde x),
    check "expr list serde" (∀ xs : (List Expr), serde xs),
    check "const serde" (∀ x : Const, serde x),
  ]
