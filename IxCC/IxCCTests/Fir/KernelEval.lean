import IxCCTests.Fir.Artifacts
import IxCC.Cfg.Lower
import IxCC.Cfg.WellFormed

/-!
# The Phase 1 lowerings evaluated by the kernel

`Fir.lower`, `Own.immortal` and `Cfg.lower` are on `Recheck.run`'s path in
style P, which Lean's kernel must evaluate (D17). These
examples re-run them with `decide +kernel` (no native evaluation) on

* the pipeline's final Anf program of each bench-k1 entry
  (`IxCCTests.Fir.Artifacts`, checked against the live pipeline by
  `tests-fir`), with the tick bound;
* small Anf programs with what K1 lacks: a recursive join point, allocation
  and projection, and a closure (declined),

so a change that stops the lowerings reducing (a `HashMap`, well-founded
recursion, a native-only implementation) fails to elaborate here. The
expected summaries were computed natively; `tests-fir` recomputes them
natively from the same table (`expected`). -/

namespace IxCCTests.Fir.KernelEval

open IxCC
open IxCC.Anf (Exp Bind Atom GDef)

/-- Functions, blocks, instructions (with terminators), back edges, and the
tick bound; `none` if the program is declined. -/
def summary (A : Anf.Program) : Option (Nat × Nat × Nat × Nat × Nat) :=
  match Cfg.ofAnf A with
  | .ok C => some (C.size, C.blocks, C.instrs, Cfg.backEdges C, Fir.tickBound A)
  | .error _ => none

/-- The summaries the kernel checks, by bench entry (computed natively). -/
def expected : List (String × Anf.Program × Nat × Nat × Nat × Nat × Nat) :=
  [("fib", Artifacts.fib, 2, 6, 12, 0, 31),
   ("sum-loop", Artifacts.sumLoop, 2, 4, 7, 1, 71),
   ("ackermann", Artifacts.ackermann, 2, 6, 11, 2, 22),
   ("tak", Artifacts.tak, 2, 6, 15, 1, 73),
   ("gcd", Artifacts.gcd, 2, 4, 6, 1, 31)]

/-! ## Small programs -/

def natZ : Key.CtorKey := .src 100
def natS : Key.CtorKey := .src 101
def bF : Key.CtorKey := .src 200
def bT : Key.CtorKey := .src 201
def pairK : Key.CtorKey := .src 300
def noneK : Key.CtorKey := .src 400
def someK : Key.CtorKey := .src 401

def b (bd : Bind) (e : Exp) : Exp := .bind Anf.freshLet bd e
def x (i : Nat) : Atom := .var i
def lit (k : Nat) : Atom := .lit (.nat k)

/-- An Anf program over the given globals (the first is the root). -/
def prog (gs : List (Nat × Exp)) : Anf.Program :=
  let gds : List GDef := gs.zipIdx.map fun ((n, body), i) =>
    { key := .const i [], ps := List.replicate n {}, body }
  { globals := Src.NatMap.ofList (gds.zipIdx.map fun (g, i) => (i, g)), size := gs.length
    roots := [0]
    ctors := [{ key := natZ, tag := 0, arity := 0 }, { key := natS, tag := 1, arity := 1 },
              { key := bF, tag := 0, arity := 0 }, { key := bT, tag := 1, arity := 0 },
              { key := pairK, tag := 0, arity := 2 }, { key := noneK, tag := 0, arity := 0 },
              { key := someK, tag := 1, arity := 1 }]
    known := { natZero := natZ, natSucc := natS, boolFalse := bF, boolTrue := bT } }

/-- `sum n` by a recursive join point whose recursive jump comes from a
nested join point, with a tick and a non-recursive exit join. -/
def loopProg : Anf.Program := prog
  [(1, .join 1 false (b (.prim .natAdd [x 0, lit 1]) (.ret (x 0)))
      (.join 2 true
        (.tick (.case (x 1) [.mk natZ 0 (.jump 1 [x 0]),
          .mk natS 1 (b (.prim .natAdd [x 1, x 2])
            (.join 2 false (.jump 0 [x 1, x 0]) (.jump 0 [x 1, x 0])))] none))
        (.jump 0 [x 0, lit 0])))]

/-- A pair allocated, passed to a callee that projects and returns an
option (allocated or field-less), cased on by the caller. -/
def allocProg : Anf.Program := prog
  [(1, b (.con pairK [x 0, lit 7]) (b (.call 1 [x 0]) (.case (x 0)
      [.mk noneK 0 (.ret (lit 0)), .mk someK 1 (.ret (x 0))] none))),
   (1, b (.proj pairK 0 (x 0)) (.case (x 0)
      [.mk natZ 0 (b (.con noneK []) (.ret (x 0))),
       .mk natS 1 (b (.proj pairK 1 (x 2)) (b (.con someK [x 0]) (.ret (x 0))))] none))]

/-- A local closure: declined until P8. -/
def closureProg : Anf.Program := prog
  [(1, b (.fn [{}] (b (.prim .natAdd [x 0, x 1]) (.ret (x 0)))) (b (.app (x 0) [lit 2]) (.ret (x 0))))]

set_option maxRecDepth 100000 in
/-- Blocks: entry, loop header (the back edge's target), two arms, the
nested join point, the exit join point last. -/
example : summary loopProg = some (1, 6, 9, 1, 4) := by decide +kernel

set_option maxRecDepth 100000 in
example : summary allocProg = some (2, 6, 13, 0, 1) := by decide +kernel

set_option maxRecDepth 100000 in
example : summary closureProg = none := by decide +kernel

/-! ## The bench-k1 entries -/

set_option maxRecDepth 100000 in
example : summary Artifacts.fib = some (2, 6, 12, 0, 31) := by decide +kernel

set_option maxRecDepth 100000 in
example : summary Artifacts.sumLoop = some (2, 4, 7, 1, 71) := by decide +kernel

set_option maxRecDepth 100000 in
example : summary Artifacts.ackermann = some (2, 6, 11, 2, 22) := by decide +kernel

set_option maxRecDepth 100000 in
example : summary Artifacts.tak = some (2, 6, 15, 1, 73) := by decide +kernel

set_option maxRecDepth 100000 in
example : summary Artifacts.gcd = some (2, 4, 6, 1, 31) := by decide +kernel

end IxCCTests.Fir.KernelEval
