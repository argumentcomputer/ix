import IxCC.Ixon.V3.Tc.DefEq

/-! Adapted from ix `0a31c8dbc63755924c645bf1afedc563e395e88a`, `Ix/Tc/Knot.lean`.
The anonymous checker uses the local v3 byte decoder and existing BLAKE3 interface.
See docs/ixon-v4.md for the adaptation and validation boundary. -/

namespace IxCC.Ixon.V3.Tc

open Metadata (Name)

/-- Fuel-exhausted end of the recursive method table. Every back-edge has
    the same error and error-state behavior as an exhausted `TcM.tick`. -/
def methodsOut : Methods m where
  whnf _ := throw .maxRecFuel
  whnfCore _ := throw .maxRecFuel
  whnfMode _ _ := throw .maxRecFuel
  whnfCoreFlags _ _ := throw .maxRecFuel
  infer _ := throw .maxRecFuel
  isDefEq _ _ := throw .maxRecFuel

/-- Total approximation to the recursive method knot. Each method-table
    back-edge exposes one smaller table to the recursive computation. -/
def methodsN : Nat → Methods m
  | 0 => methodsOut
  | n + 1 =>
    { whnf := fun e => (RecM.whnf e).run (methodsN n)
      whnfCore := fun e => (RecM.whnfCore e).run (methodsN n)
      whnfMode := fun e mode =>
        (RecM.whnfWithNatSuccMode e mode).run (methodsN n)
      whnfCoreFlags := fun e flags =>
        (RecM.whnfCoreWithFlags e flags).run (methodsN n)
      infer := fun e => (RecM.infer e).run (methodsN n)
      isDefEq := fun a b => (RecM.isDefEq a b).run (methodsN n) }

namespace TcM

/-- Run a recursive checker computation with method-table depth selected
    from the current state. This deliberately ignores `fuelBudget`. -/
def runRec (x : RecM m α) : TcM m α := fun s =>
  x.run (methodsN s.recFuel.toNat) s

/-- Full WHNF (public entry). -/
def whnf (e : KExpr m) : TcM m (KExpr m) :=
  runRec (RecM.whnf e)

/-- Structural WHNF (beta/iota/zeta/proj, no delta). -/
def whnfCore (e : KExpr m) : TcM m (KExpr m) :=
  runRec (RecM.whnfCore e)

/-- WHNF without delta. -/
def whnfNoDelta (e : KExpr m) : TcM m (KExpr m) :=
  runRec (RecM.whnfNoDelta e)

/-- Type inference (validating unless `withInferOnly`). -/
def infer (e : KExpr m) : TcM m (KExpr m) :=
  runRec (RecM.infer e)

/-- Definitional equality. -/
def isDefEq (a b : KExpr m) : TcM m Bool :=
  runRec (RecM.isDefEq a b)

/-- WHNF then require a sort. -/
def ensureSort (e : KExpr m) : TcM m (KUniv m) :=
  runRec (RecM.ensureSortDirect e)

/-- WHNF then require a forall; returns (domain, codomain). -/
def ensureForall (e : KExpr m) : TcM m (KExpr m × KExpr m) :=
  runRec (RecM.ensureForallDirect e)

end TcM

end IxCC.Ixon.V3.Tc
