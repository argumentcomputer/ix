import CompilatrixTests.Anf.Support
import CompilatrixTests.Src.Rules

/-! Anf's rules (design note 02 §6.2) on hand-written programs: atoms and
scope, constructors and checked keys, primitives, `Nat` peeling in `case`,
the default and stuck cases, function and CAF globals (free and charged),
known calls, applications under-, exactly and over-saturated (one charge
each), local closures, join points and jumps (charged; a recursive join
point is a loop), `tick` and `trap`, □ stuck under application, projection,
`case` and primitives (06 S38); clock monotonicity on random clocks. -/

namespace CompilatrixTests.Anf.Eval

open Compilatrix CompilatrixTests.Src CompilatrixTests.Anf
open Compilatrix.Anf (Exp Bind Atom Alt GDef Val JClo)
open Compilatrix.Sem (Result)
open CompilatrixTests.Src.Rules (Gen)

def natZ : Key.CtorKey := .src 100
def natS : Key.CtorKey := .src 101
def bF : Key.CtorKey := .src 200
def bT : Key.CtorKey := .src 201
def pairK : Key.CtorKey := .src 300
def otherK : Key.CtorKey := .src 301

def lit (n : Nat) : Atom := .lit (.nat n)
def x (i : Nat) : Atom := .var i
def b (bd : Bind) (e : Exp) : Exp := .bind Anf.freshLet bd e

/-- Globals: 0 the identity, 1 a diverging CAF, 2 doubling by recursion,
3 a CAF holding 7, 4 a binary adder. -/
def program : AProgram :=
  let double : Exp := .case (x 0) [.mk natZ 0 (.ret (lit 0)),
    .mk natS 1 (b (.call 2 [x 0]) (b (.prim .natAdd [x 0, lit 2]) (.ret (x 0))))] none
  let gs : List GDef :=
    [{ key := .const 0 [], ps := [{}], body := .ret (x 0) },
     { key := .const 1 [], ps := [], body := b (.glob 1) (.ret (x 0)) },
     { key := .const 2 [], ps := [{}], body := double },
     { key := .const 3 [], ps := [], body := .ret (lit 7) },
     { key := .const 4 [], ps := [{}, {}], body := b (.prim .natAdd [x 1, x 0]) (.ret (x 0)) }]
  { globals := Src.NatMap.ofList (gs.zipIdx.map fun (g, i) => (i, g)), size := gs.length
    roots := [0, 2]
    ctors := [{ key := natZ, tag := 0, arity := 0 }, { key := natS, tag := 1, arity := 1 },
              { key := bF, tag := 0, arity := 0 }, { key := bT, tag := 1, arity := 0 },
              { key := pairK, tag := 0, arity := 2 }, { key := otherK, tag := 1, arity := 2 }]
    known := { natZero := natZ, natSucc := natS, boolFalse := bF, boolTrue := bT } }

def ev (k : Nat) (e : Exp) (ρ : List Val := []) (J : List JClo := []) : Result Val :=
  Anf.eval program k ρ J e

def expectR (a : Assert) (got : Result Val) (expected : String) (msg : String) : IO Unit :=
  expect a (anfOutcome got == expected) s!"{msg}: got {anfOutcome got}, expected {expected}"

def rules (a : Assert) : IO Unit := do
  let v7 := Val.lit (.nat 7)
  -- Atoms and scope.
  expectR a (ev 0 (.ret (x 0)) [v7]) "ok lit 7" "a variable is free"
  expectR a (ev 5 (.ret (x 3))) "stuck" "a variable out of scope"
  expectR a (ev 0 (.ret .box)) "ok box" "□"
  -- Constructors and checked keys.
  let pr := b (.con pairK [lit 1, lit 2])
  expectR a (ev 0 (pr (b (.proj pairK 1 (x 0)) (.ret (x 0))))) "ok lit 2" "proj"
  expectR a (ev 0 (pr (b (.proj otherK 1 (x 0)) (.ret (x 0))))) "stuck" "proj with another key"
  expectR a (ev 0 (pr (b (.proj pairK 2 (x 0)) (.ret (x 0))))) "stuck" "proj beyond the fields"
  expectR a (ev 0 (b (.proj pairK 0 .box) (.ret (x 0)))) "stuck" "projecting □"
  expectR a (ev 0 (b (.con pairK [lit 1]) (.ret (x 0)))) "ok con/1" "con does not check arity"
  -- Primitives.
  expectR a (ev 0 (b (.prim .natSub [lit 3, lit 5]) (.ret (x 0)))) "ok lit 0" "truncated sub"
  expectR a (ev 0 (b (.prim .natBle [lit 3, lit 5]) (.ret (x 0)))) "ok con/0" "a Boolean result"
  expectR a (ev 0 (b (.prim .natAdd [.box, lit 5]) (.ret (x 0)))) "stuck" "a primitive on □"
  expectR a (ev 0 (b (.prim .natAdd [lit 5]) (.ret (x 0)))) "stuck" "an unsaturated primitive"
  -- Case: Nat peeling, the default, stuck.
  let nat := fun (s : Atom) =>
    Exp.case s [.mk natZ 0 (.ret (lit 100)), .mk natS 1 (.ret (x 0))] none
  expectR a (ev 0 (nat (lit 0))) "ok lit 100" "case on 0"
  expectR a (ev 0 (nat (lit 5))) "ok lit 4" "case on 5 binds 4"
  expectR a (ev 0 (.case (lit 5) [.mk natZ 0 (.ret (lit 1))] (some (.ret (lit 9))))) "ok lit 9"
    "the default"
  expectR a (ev 0 (.case (lit 5) [.mk natZ 0 (.ret (lit 1))] none)) "stuck" "no alternative"
  expectR a (ev 0 (.case .box [] (some (.ret (lit 9))))) "stuck" "case on □"
  expectR a (ev 0 (pr (.case (x 0) [.mk pairK 1 (.ret (lit 1))] none))) "stuck" "arity mismatch"
  expectR a (ev 0 (pr (.case (x 0) [.mk pairK 2 (.ret (x 1))] none))) "ok lit 1"
    "field 0 at index 1"
  -- Globals: a function global's closure is free; a CAF charges.
  expectR a (ev 0 (b (.glob 0) (.ret (x 0)))) "ok clos" "a function global is free"
  expectR a (ev 0 (b (.glob 3) (.ret (x 0)))) "timeout" "a CAF charges"
  expectR a (ev 1 (b (.glob 3) (.ret (x 0)))) "ok lit 7" "a CAF's value"
  expectR a (ev 50 (b (.glob 1) (.ret (x 0)))) "timeout" "a diverging CAF"
  expectR a (ev 5 (b (.glob 9) (.ret (x 0)))) "stuck" "a global out of range"
  -- Known calls charge.
  expectR a (ev 0 (b (.call 0 [lit 3]) (.ret (x 0)))) "timeout" "a call charges"
  expectR a (ev 1 (b (.call 0 [lit 3]) (.ret (x 0)))) "ok lit 3" "a call"
  expectR a (ev 9 (b (.call 0 [lit 3, lit 4]) (.ret (x 0)))) "stuck" "a call at another arity"
  expectR a (ev 3 (b (.call 2 [lit 2]) (.ret (x 0)))) "ok lit 4" "double 2 at depth 3"
  expectR a (ev 2 (b (.call 2 [lit 2]) (.ret (x 0)))) "timeout" "double 2 at depth 2"
  -- Applications: one charge per application, whatever the saturation.
  let add := b (.glob 4)
  expectR a (ev 0 (add (b (.app (x 0) [lit 1]) (.ret (x 0))))) "timeout" "under-saturated charges"
  expectR a (ev 1 (add (b (.app (x 0) [lit 1]) (.ret (x 0))))) "ok clos" "a partial application"
  expectR a (ev 1 (add (b (.app (x 0) [lit 1]) (b (.app (x 0) [lit 2]) (.ret (x 0))))))
    "ok lit 3" "completing a partial application"
  expectR a (ev 1 (add (b (.app (x 0) [lit 1, lit 2]) (.ret (x 0))))) "ok lit 3" "saturated"
  let k2 := b (.fn [{}] (b (.glob 0) (.ret (x 0))))
  expectR a (ev 1 (k2 (b (.app (x 0) [lit 1, lit 5]) (.ret (x 0))))) "ok lit 5"
    "over-saturated: the result applied to the rest"
  expectR a (ev 5 (b (.app .box [lit 1]) (.ret (x 0)))) "stuck" "applying □"
  expectR a (ev 5 (pr (b (.app (x 0) [lit 1]) (.ret (x 0))))) "stuck" "applying a constructor"
  expectR a (ev 5 (b (.app (lit 3) [lit 1]) (.ret (x 0)))) "stuck" "applying a literal"
  -- Local closures are free; a closure of no parameter is stuck.
  expectR a (ev 0 (b (.fn [{}] (.ret (x 1))) (.ret (x 0))) [v7]) "ok clos" "fn is free"
  expectR a (ev 1 (b (.fn [{}] (.ret (x 1))) (b (.app (x 0) [lit 3]) (.ret (x 0)))) [v7])
    "ok lit 7" "a closure sees its environment"
  expectR a (ev 5 (b (.fn [] (.ret (lit 1))) (.ret (x 0)))) "stuck" "fn []"
  -- Join points: jumps charge; the join body sees its own environment.
  let j := Exp.join 1 false (.ret (x 0)) (.jump 0 [lit 4])
  expectR a (ev 0 j) "timeout" "a jump charges"
  expectR a (ev 1 j) "ok lit 4" "a jump"
  expectR a (ev 1 (.join 1 false (.ret (x 0)) (.jump 0 [lit 4, lit 5]))) "stuck"
    "a jump at another arity"
  expectR a (ev 1 (.jump 0 [lit 4])) "stuck" "a jump out of scope"
  -- A recursive join point counting down: 5 jumps.
  let loop := Exp.join 1 true (.case (x 0) [.mk natZ 0 (.ret (lit 42)),
    .mk natS 1 (.jump 0 [x 0])] none) (.jump 0 [lit 4])
  expectR a (ev 4 loop) "timeout" "a loop charges per iteration"
  expectR a (ev 5 loop) "ok lit 42" "a recursive join point"
  -- Tick and trap.
  expectR a (ev 0 (.tick (.ret (lit 1)))) "timeout" "tick charges"
  expectR a (ev 1 (.tick (.ret (lit 1)))) "ok lit 1" "tick"
  expectR a (ev 0 .trap) "trap" "trap"
  -- Run: the root's value applied to the arguments (one charge).
  let r := Anf.run program 3 2 [.lit (.nat 2)]
  expectR a r "ok lit 4" "run double 2"

/-- Clock monotonicity: above a finishing clock, the result never changes. -/
def monotone (a : Assert) : IO Unit := do
  let mut g : Gen := { seed := 11 }
  for _ in [0:300] do
    let (n, g1) := g.next 12
    let (k, g2) := g1.next 40
    g := g2
    let r := Anf.run program k 2 [.lit (.nat n)]
    if anfOutcome r != "timeout" then
      for k' in [k + 1, 2 * k + 5] do
        expect a (anfOutcome (Anf.run program k' 2 [.lit (.nat n)]) == anfOutcome r)
          s!"monotonicity: double {n} at {k} and {k'}"

def run (a : Assert) : IO Unit := do
  rules a
  monotone a
  expect a (Anf.wellScoped program) "the rule program is WellScoped"

end CompilatrixTests.Anf.Eval
