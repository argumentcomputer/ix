module

public import Ix.Tc.DefEq

/-!
The recursion knot. `Ix.Tc.Whnf`/`Infer`/`DefEq` define the kernel algorithms
in `RecM` (a `Methods`-reader over `TcM`); this module ties the back-edges
with one `partial def` and exports `TcM`-level entry points. Only the
back-edges route through the record (whnf reads infer/isDefEq); infer imports
whnf directly and def-eq imports both — no lean4lean `withFuel` third fuel,
which would change the error surface vs Rust.
-/

public section
@[expose] section

namespace Ix.Tc

/-- The tied method table. -/
partial def methods : Methods m where
  whnf e := (RecM.whnf e).run methods
  whnfCore e := (RecM.whnfCore e).run methods
  infer e := (RecM.infer e).run methods
  isDefEq a b := (RecM.isDefEq a b).run methods

namespace TcM

/-- Full WHNF (public entry). -/
def whnf (e : KExpr m) : TcM m (KExpr m) :=
  (RecM.whnf e).run methods

/-- Structural WHNF (beta/iota/zeta/proj, no delta). -/
def whnfCore (e : KExpr m) : TcM m (KExpr m) :=
  (RecM.whnfCore e).run methods

/-- WHNF without delta. -/
def whnfNoDelta (e : KExpr m) : TcM m (KExpr m) :=
  (RecM.whnfNoDelta e).run methods

/-- Type inference (validating unless `withInferOnly`). -/
def infer (e : KExpr m) : TcM m (KExpr m) :=
  (RecM.infer e).run methods

/-- Definitional equality. -/
def isDefEq (a b : KExpr m) : TcM m Bool :=
  (RecM.isDefEq a b).run methods

/-- WHNF then require a sort. -/
def ensureSort (e : KExpr m) : TcM m (KUniv m) :=
  (RecM.ensureSortDirect e).run methods

/-- WHNF then require a forall; returns (domain, codomain). -/
def ensureForall (e : KExpr m) : TcM m (KExpr m × KExpr m) :=
  (RecM.ensureForallDirect e).run methods

end TcM

end Ix.Tc

end
end
