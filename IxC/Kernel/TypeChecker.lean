module

public import IxC.Kernel.Core

@[expose] public section

/-!
# The pure knot

The core bodies (`Ix.Kernel.Core`) tied together at `CheckM`, with
no memoization: this instance is the **specification** — all semantic
verification (`IxC/Kernel/Verify/*`, `IxC/Kernel/Semantics/*`, `IxC/Kernel/Model/*`)
reasons about these
fueled entry points, and the refinement bridge (see DESIGN.md) carries
every claim over to the cached instance the checker executes
(`Ix.Kernel.Cached.CoreC`).
-/

namespace Ix.Kernel

variable (mode : CheckMode)

/-- The pure core: the bodies tied at `CheckM`, fuel in the knot. -/
def pureFns (env : Env md) : Nat → (CoreFns md) (CheckM md) :=
  coreKnot mode env id

/-- Head normalization without delta (fueled). -/
def whnfCore (env : Env md) (fuel depth : Nat) (e : Expr md) : CheckM md (Expr md) :=
  (pureFns mode env fuel).whnfCore depth e

/-- The full reduction loop (fueled). -/
def whnf (env : Env md) (fuel depth : Nat) (e : Expr md) : CheckM md (Expr md) :=
  (pureFns mode env fuel).whnf depth e

/-- Full-grade type inference (fueled): the declaration front door's
entry — official's `infer_type_core(e, infer_only = false)`. -/
def inferTypeCore (env : Env md) (fuel depth : Nat) (e : Expr md) : CheckM md (Expr md) :=
  (pureFns mode env fuel).infer depth e

/-- Type inference at the io grade (fueled): the knot's `inferIO` slot
— what every internal inference call site runs (task #170).  At a
gate-off mode this **is** `inferTypeCore` (`inferTypeIO_off`,
`Verify/Knot.lean`); at the gated mode it is the io lane
(`inferTypeIO_on`). -/
def inferTypeIO (env : Env md) (fuel depth : Nat) (e : Expr md) : CheckM md (Expr md) :=
  (pureFns mode env fuel).inferIO depth e

/-- Definitional equality (fueled). -/
def isDefEqCore (env : Env md) (fuel depth : Nat) (a b : Expr md) : CheckM md Bool :=
  (pureFns mode env fuel).defeq depth a b

/-- The annotation pass (fueled). -/
def annotateCore (env : Env md) (fuel depth : Nat) (e : Expr md) : CheckM md (Expr md) :=
  (pureFns mode env fuel).annotate depth e

/-- `ensureSort` over the pure knot (fueled). -/
def ensureSortCore (env : Env md) (fuel depth : Nat) (e : Expr md) : CheckM md Level :=
  ensureSort (pureFns mode env fuel) env depth e

end Ix.Kernel
