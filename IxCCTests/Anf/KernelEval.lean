import IxCC.Anf.Pipeline

/-!
# The middle end evaluated by the kernel

The Anf passes are on `Recheck.run`'s path, which Lean's kernel must
evaluate (roadmap D17, M1.K1). These examples run P1 and the certified steps
(`Pipeline.run`) on small Lam programs inside the kernel (`decide +kernel`,
no native evaluation) and check the resulting sizes, so a change that stops
the passes reducing (a `HashMap`, well-founded recursion, a native-only
implementation) fails to elaborate here.
-/

namespace IxCCTests.Anf.KernelEval

open IxCC
open IxCC.Lam (Term Alt Global)
open IxCC.Anf (Pipeline.run Pipeline.Step)

def natZ : Key.CtorKey := .src 100
def natS : Key.CtorKey := .src 101
def bF : Key.CtorKey := .src 200
def bT : Key.CtorKey := .src 201
def pairK : Key.CtorKey := .src 300

def lit (n : Nat) : Term := .lit (.nat n)
def v (i : Nat) : Term := .var i

/-- A Lam program over the given globals (the first is the root). -/
def prog (gs : List Term) : Lam.Program :=
  let gls : List Global := gs.zipIdx.map fun (b, i) => { key := .const i [], body := b }
  { globals := Src.NatMap.ofList (gls.zipIdx.map fun (g, i) => (i, g)), size := gs.length
    roots := [0]
    ctors := [{ key := natZ, tag := 0, arity := 0 }, { key := natS, tag := 1, arity := 1 },
              { key := bF, tag := 0, arity := 0 }, { key := bT, tag := 1, arity := 0 },
              { key := pairK, tag := 0, arity := 2 }]
    known := { natZero := natZ, natSucc := natS, boolFalse := bF, boolTrue := bT } }

/-- Globals and nodes after the pipeline, or `none` on an error. -/
def sizeAfter (cert : Anf.Pipeline.Cert) (L : Lam.Program) : Option (Nat × Nat) :=
  match Pipeline.run cert L with
  | .ok P => some (P.size, P.globalList.foldl (fun n (_, gd) => n + gd.body.nodes) 0)
  | .error _ => none

/-- `root x = add x 1` through a dictionary: `pair (λa b. a + b) 7`, projected. -/
def dict : Lam.Program := prog
  [ .lam .strict {} (.app (.app (.proj pairK 0 (.glob 1)) (v 0) .strict) (lit 1) .strict),
    .con pairK [.lam .strict {} (.lam .strict {} (.prim .natAdd [v 1, v 0])), lit 7] ]

set_option maxRecDepth 100000 in
/-- P1 alone (ModesOk checked, the root a two-argument application of a
projected CAF field). -/
example : sizeAfter {} dict = some (2, 21) := by decide +kernel

set_option maxRecDepth 100000 in
/-- P3: one inline round (the CAF dictionary into the root). -/
example : sizeAfter { steps := [.inline [(0, [1])]] } dict = some (2, 31) := by decide +kernel

set_option maxRecDepth 100000 in
/-- P3, then P2's rounds (projection of a known constructor, β, dead
bindings) and pruning: `root x = tick tick (x + 1)`. -/
example : sizeAfter { steps := [.inline [(0, [1])], .shrink [3], .prune] } dict = some (1, 7) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- A certificate asking for more rounds than the fixpoint needs changes
nothing further. -/
example : sizeAfter { steps := [.inline [(0, [1])], .shrink [9], .prune] } dict = some (1, 7) := by
  decide +kernel

/-- `root n = loop n 0`, `loop n acc = case n | 0 ⇒ acc | m+1 ⇒ loop m (f acc)` with
the step function `f` passed unchanged (a fixed higher-order parameter). -/
def loop : Lam.Program := prog
  [ .lam .strict {} (.app (.app (.app (.glob 1)
      (.lam .strict {} (.prim .natAdd [v 0, lit 2])) .strict) (v 0) .strict) (lit 0) .strict),
    .lam .strict {} (.lam .strict {} (.lam .strict {} (.case (v 1)
      [.mk natZ 0 (v 0), .mk natS 1 (.app (.app (.app (.glob 1) (v 3) .strict) (v 0) .strict)
        (.app (v 3) (v 1) .strict) .strict)] none))) ]

def specLoop : Anf.Specialize.Cert :=
  { decisions := [{ caller := 0, callee := 1, mask := [true, false, false] }] }

set_option maxRecDepth 100000 in
/-- P4: the specialisation of the loop on its step function, created and
called; the generic loop is kept. -/
example : sizeAfter { steps := [.shrink [1, 1], .specialize specLoop] } loop = some (3, 42) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- P4, P2, pruning: `root n = loop' n 0` with `loop'` adding 2 per step. -/
example : sizeAfter { steps := [.shrink [1, 1], .specialize specLoop, .shrink [2, 1, 3], .prune] }
    loop = some (2, 18) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The fixed-parameter checker rejects a mask over a parameter the loop
changes (its counter): nothing is specialised. -/
example : sizeAfter { steps := [.shrink [1, 1],
    .specialize { decisions := [{ caller := 0, callee := 1, mask := [false, true, false] }] }] }
    loop = sizeAfter { steps := [.shrink [1, 1]] } loop := by
  decide +kernel

end IxCCTests.Anf.KernelEval
