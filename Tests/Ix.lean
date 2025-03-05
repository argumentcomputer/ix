import LSpec
import Ix.Ixon
import Ix.Address
import Ix.Ixon.Serialize
import Ix.Ixon.Univ
import Ix.TransportM
import LSpec.SlimCheck.Gen
import LSpec
import Blake3

import Tests.Ix.Ixon
import Tests.Ix.IR

open LSpec
open SlimCheck
open SlimCheck.Gen

def serde [Ixon.Serialize A] [BEq A] (x: A) : Bool :=
  match Ixon.Serialize.get (Ixon.Serialize.put x) with
  | .ok (y : A) => x == y
  | _ => false

open Ix.TransportM

def transportUniv (univ: Ix.Univ): Bool :=
  match EStateM.run (dematUniv univ) emptyDematState with
  | .ok ixon stt =>
    let remat := (ReaderT.run (rematUniv ixon) { meta := stt.meta})
    match EStateM.run remat emptyRematState with
    | .ok ix _ => univ == ix
    | .error _ _ => .false
  | .error _ _ => .false

def transportExpr (x: Ix.Expr): Bool :=
  match EStateM.run (dematExpr x) emptyDematState with
  | .ok ixon stt =>
    let remat := (ReaderT.run (rematExpr ixon) { meta := stt.meta})
    match EStateM.run remat emptyRematState with
    | .ok ix _ => x == ix
    | .error _ _ => .false
  | .error _ _ => .false

def myConfig : SlimCheck.Configuration where
  maxSize := 100
  traceDiscarded := true
  traceSuccesses := true
  traceShrink := true
  traceShrinkCandidates := true

def dbg := do
  SlimCheck.Checkable.check (∀ x: Ix.Univ, transportUniv x) myConfig

def Tests.Ix.suite : List LSpec.TestSeq :=
  [
    check "universe serde" (∀ x : Ixon.Univ, serde x),
    check "universe transport" (∀ x : Ix.Univ, transportUniv x),
    check "expr serde" (∀ x : Ixon.Expr, serde x),
    check "expr transport" (∀ x : Ix.Expr, transportExpr x),
    check "const serde" (∀ x : Ixon.Const, serde x),
  ]
