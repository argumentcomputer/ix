import CompilatrixTests.Lam.Erase

/-!
# Erasure evaluated by the kernel

Erasure is on `Recheck.run`'s path, which Lean's kernel must evaluate
(roadmap D17, M1.K1). These examples erase synthetic programs (the world of
`CompilatrixTests.Lam.Erase`, with the annotation's records and no checker
run) inside the kernel (`decide +kernel`, no native evaluation) and check
the number of globals and nodes, so a change that stops erasure reducing (a
`HashMap`, well-founded recursion, or a native-only implementation) fails to
elaborate here.
-/

namespace CompilatrixTests.Lam.KernelEval

open Compilatrix Compilatrix.Src Compilatrix.Src.Relevance CompilatrixTests.Src
open CompilatrixTests.Src.Relevance.Checker (annOf rootKeys)
open CompilatrixTests.Lam.Erase (world c lit n0 motive)

/-- Globals and nodes of the erasure of one root definition. -/
def erased (value : Term) : Option (Nat × Nat) :=
  let (bld, root) := world.bld.add (.defn .defn .safe 0 ty value)
  let p := bld.program #[root]
  let ann := annOf p (rootKeys p)
  let ch : Checked := { keys := [], reached := [], instances := [], consts := ann.consts,
                        ctors := ann.ctors }
  match Compilatrix.Lam.erase p ch with
  | .ok (_, s) => some (s.globals, s.nodes)
  | .error _ => none

/-- A declined root. -/
def declines (value : Term) : Bool := (erased value).isNone

set_option maxRecDepth 100000 in
/-- A primitive spine. -/
example : erased (lam (app (c world.b.add) [n0, lit 1])) = some (1, 4) := by decide +kernel

set_option maxRecDepth 100000 in
/-- `Nat.casesOn`: lets, the ι tick, a `case` with peeled minors. -/
example : erased (lam (appM (.const world.b.natCases [.zero]) [motive, (n0, .strict),
    (lit 10, .byName), (lam (app (c world.b.add) [n0, n0]), .byName)])) = some (1, 12) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- `Nat.rec` with a by-name IH: the root and `r⋆`. -/
example : erased (lam (appM (.const world.b.natRec [.zero]) [motive, (lit 0, .byName),
    (lams 2 (app (c world.b.add) [n0, lit 2]), .byName), (n0, .strict)])) = some (2, 38) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- A wrapper of an unsaturated primitive. -/
example : erased (lam (.app (lam (app (.var 0) [.var 1, lit 1])) (c world.b.add) .strict .rel))
    = some (2, 14) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- A constructor with a relevant parameter, projected. -/
example : erased (lam (.proj world.box 0
    (app (c world.boxMk) [n0, app (c world.b.add) [n0, lit 1]])))
    = some (1, 8) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- A subsingleton `casesOn` (fields from the index). -/
example : erased (lam (appM (.const world.isNatCases [.zero])
    [motive, (n0, .strict), (irrArg, .irr),
    (lam (app (c world.b.add) [n0, lit 1]), .byName)])) = some (1, 8) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- A saturated `lazy` spine: the by-name variant and the loop. -/
example : erased (lam (appM (c world.myIte) [(app (c world.b.beq) [n0, lit 0], .byName),
    (lit 10, .byName), (c world.loop, .byName)]))
    = some (3, 25) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- A string is declined. -/
example : declines (lam (.strLit "s")) = true := by decide +kernel

end CompilatrixTests.Lam.KernelEval
