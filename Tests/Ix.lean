import LSpec
import Ix.Ixon
import Ix.Ixon.Metadata
import Ix.Address
import Ix.Ixon.Serialize
import Ix.Ixon.Univ
import Ix.TransportM
import LSpec.SlimCheck.Gen
import LSpec
import Blake3

import Tests.Common
import Tests.Ix.Common
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

def transportUniv (univ: Ix.Level): Bool :=
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

def transportConst (x: Ix.Const): Bool :=
  match EStateM.run (dematConst x) emptyDematState with
  | .ok ixon stt =>
    let remat := (ReaderT.run (rematConst ixon) { meta := stt.meta})
    match EStateM.run remat emptyRematState with
    | .ok ix _ => x == ix
    | .error _ _ => .false
  | .error _ _ => .false

--def transportExpr' (x: Ix.Expr): Except TransportError Bool :=
--  match EStateM.run (dematExpr x) emptyDematState with
--  | .ok ixon stt =>
--    let remat := (ReaderT.run (rematExpr ixon) { meta := stt.meta})
--    match EStateM.run remat emptyRematState with
--    | .ok ix _ => .ok (x == ix)
--    | .error e _ => .error e
--  | .error e _ => .error e
--
def myConfig : SlimCheck.Configuration where
  numInst := 10000
  maxSize := 100
  traceDiscarded := true
  traceSuccesses := true
  traceShrink := true
  traceShrinkCandidates := true

def dbg : IO UInt32 := do
   SlimCheck.Checkable.check (∀ x: Ix.Const, transportConst x) myConfig
   return 0

--def Test.Ix.unitTransport : TestSeq :=
--  testExprs.foldl (init := .done) fun tSeq x =>
--    tSeq ++ (test s!"transport {repr x}" $ Except.isOk (transportExpr' x))


def Tests.Ix.suite : List LSpec.TestSeq :=
  [
    check "metadatum serde" (∀ x : Ixon.Metadatum, serde x),
    check "universe serde" (∀ x : Ixon.Univ, serde x),
    check "universe transport" (∀ x : Ix.Level, transportUniv x),
    check "expr serde" (∀ x : Ixon.Expr, serde x),
    check "expr transport" (∀ x : Ix.Expr, transportExpr x),
    check "const serde" (∀ x : Ixon.Const, serde x),
    check "const transport" (∀ x : Ix.Const, transportConst x),
  ]
