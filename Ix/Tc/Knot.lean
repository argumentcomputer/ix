module

public import Ix.Tc.DefEq

/-!
The recursion knot. `Ix.Tc.Whnf`/`Infer`/`DefEq` define the kernel algorithms
in `RecM` (a `Methods`-reader over `TcM`); this module ties the back-edges
with a total, depth-indexed method table and exports `TcM`-level entry
points. Only the back-edges route through the record (whnf reads
infer/isDefEq); infer imports whnf directly and def-eq imports both.

The index is initialized from the *current* shared `recFuel`, not the reset
budget: public entries can run in the middle of a constant check after fuel
has already been consumed. Exhausting method-table depth throws the same
`.maxRecFuel` error as `TcM.tick`, without changing the state.
-/

public section
@[expose] section

namespace Ix.Tc

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

end Ix.Tc

end
end
