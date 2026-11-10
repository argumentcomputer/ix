import IxCCTests.Lam.Support
import IxCCTests.Src.Rules

/-! Lam's rules on a hand-written program: slots and
charges, application modes, □ stuck under application, projection, `case`
and primitives, checked keys, `Nat` peeling, left-to-right order, `tick`
and `trap`; key equality (D19); and clock monotonicity on random clocks. -/

namespace IxCCTests.Lam.Eval

open IxCC IxCCTests.Src IxCCTests.Lam
open IxCC.Lam (Term Alt Val Slot Mode Prim Lit)
open IxCC.Sem (Result)
open IxCCTests.Src.Rules (Gen)

def natZ : Key.CtorKey := .src 100
def natS : Key.CtorKey := .src 101
def bF : Key.CtorKey := .src 200
def bT : Key.CtorKey := .src 201
def pairK : Key.CtorKey := .src 300
def otherK : Key.CtorKey := .src 301

def lit (n : Nat) : Term := .lit (.nat n)
def v (i : Nat) : Term := .var i

/-- Globals: 0 identity, 1 a loop, 2 doubling by recursion on `Nat`. -/
def program : LProgram :=
  let double := Term.lam .strict {} (.case (v 0)
    [.mk natZ 0 (lit 0), .mk natS 1 (.prim .natAdd [.app (.glob 2) (v 0) .strict, lit 2])] none)
  let gs : List IxCC.Lam.Global :=
    [{ key := .const 0 [], body := .lam .strict {} (v 0) },
     { key := .const 1 [], body := .glob 1 },
     { key := .const 2 [], body := double }]
  { globals := Src.NatMap.ofList (gs.zipIdx.map fun (g, i) => (i, g)), size := 3, roots := [0, 1, 2]
    ctors := [{ key := natZ, tag := 0, arity := 0 }, { key := natS, tag := 1, arity := 1 },
              { key := bF, tag := 0, arity := 0 }, { key := bT, tag := 1, arity := 0 },
              { key := pairK, tag := 0, arity := 2 }, { key := otherK, tag := 1, arity := 2 }]
    known := { natZero := natZ, natSucc := natS, boolFalse := bF, boolTrue := bT } }

def ev (k : Nat) (t : Term) (ρ : List Slot := []) : Result Val := IxCC.Lam.eval program k ρ t

def show_ (r : Result Val) : String := lamOutcome r

def expectR (a : Assert) (got : Result Val) (expected : String) (msg : String) : IO Unit :=
  expect a (show_ got == expected) s!"{msg}: got {show_ got}, expected {expected}"

def pair (x y : Term) : Term := .con pairK [x, y]

def rules (a : Assert) : IO Unit := do
  -- Slots and charges.
  expectR a (ev 0 (v 0) [.val (.lit (.nat 7))]) "ok lit 7" "var: a val slot is free"
  expectR a (ev 0 (v 0) [.name [] (lit 8)]) "timeout" "var: a name slot charges"
  expectR a (ev 1 (v 0) [.name [] (lit 8)]) "ok lit 8" "var: a name slot is forced"
  expectR a (ev 5 (v 3)) "stuck" "var out of scope"
  expectR a (ev 0 (.glob 0)) "timeout" "glob charges"
  expectR a (ev 1 (.glob 0)) "ok clos" "glob gives its body's value"
  expectR a (ev 5 (.glob 7)) "stuck" "glob out of range"
  expectR a (ev 0 (.app (.lam .strict {} (v 0)) (lit 3) .strict)) "timeout" "closure entry charges"
  expectR a (ev 1 (.app (.lam .strict {} (v 0)) (lit 3) .strict)) "ok lit 3" "β"
  -- Application modes: strict evaluates, name suspends (and ignores λ modes).
  expectR a (ev 50 (.app (.lam .strict {} (lit 9)) (.glob 1) .strict)) "timeout" "strict argument"
  expectR a (ev 5 (.app (.lam .strict {} (lit 9)) (.glob 1) .name)) "ok lit 9"
    "name argument unevaluated"
  expectR a (ev 5 (.app (.lam .name {} (v 0)) (lit 4) .name)) "ok lit 4"
    "name argument forced on read"
  expectR a (ev 1 (.app (.lam .strict {} (v 0)) (lit 4) .name)) "timeout"
    "forcing charges inside the body"
  -- □ is stuck under application, projection, case and primitives.
  expectR a (ev 5 .box) "ok box" "box"
  expectR a (ev 5 (.app .box (lit 1) .strict)) "stuck" "applying box"
  expectR a (ev 5 (.proj pairK 0 .box)) "stuck" "projecting box"
  expectR a (ev 5 (.case .box [.mk natZ 0 (lit 1)] (some (lit 2)))) "stuck" "case on box"
  expectR a (ev 5 (.prim .natAdd [.box, lit 1])) "stuck" "primitive on box"
  expectR a (ev 5 (.app (lit 3) (lit 1) .strict)) "stuck" "applying a literal"
  expectR a (ev 5 (.app (pair (lit 1) (lit 2)) (lit 1) .strict)) "stuck" "applying a constructor"
  -- Checked keys (D19).
  expectR a (ev 5 (.proj pairK 1 (pair (lit 1) (lit 2)))) "ok lit 2" "proj"
  expectR a (ev 5 (.proj otherK 1 (pair (lit 1) (lit 2)))) "stuck" "proj with another key"
  expectR a (ev 5 (.proj pairK 2 (pair (lit 1) (lit 2)))) "stuck" "proj beyond the fields"
  let alts := [Alt.mk otherK 2 (lit 0), .mk pairK 2 (.prim .natSub [v 1, v 0])]
  expectR a (ev 5 (.case (pair (lit 7) (lit 2)) alts none)) "ok lit 5"
    "case binds fields in order (field 0 outermost)"
  expectR a (ev 5 (.case (.con otherK [lit 1]) alts (some (lit 9)))) "ok lit 9"
    "case: an arity mismatch falls to the default"
  expectR a (ev 5 (.case (.con natZ []) alts none)) "stuck" "case: no alternative, no default"
  -- Nat peeling.
  let natAlts := [Alt.mk natZ 0 (lit 100), .mk natS 1 (v 0)]
  expectR a (ev 5 (.case (lit 0) natAlts none)) "ok lit 100" "Nat peeling: zero"
  expectR a (ev 5 (.case (lit 6) natAlts none)) "ok lit 5" "Nat peeling: successor"
  expectR a (ev 5 (.case (.lit (.str "s")) natAlts none)) "stuck" "a string is no constructor"
  -- Primitives.
  expectR a (ev 5 (.prim .natAdd [lit 2, lit 3])) "ok lit 5" "natAdd"
  expectR a (ev 5 (.prim .natDiv [lit 2, lit 0])) "ok lit 0" "natDiv by zero"
  expectR a (ev 5 (.prim .natMod [lit 7, lit 0])) "ok lit 7" "natMod by zero"
  expectR a (ev 5 (.prim .natBeq [lit 2, lit 2])) "ok con/0" "natBeq"
  expect a ((match ev 5 (.prim .natBlt [lit 2, lit 3]) with
    | .ok (.con c []) => c == bT | _ => false)) "natBlt 2 3 is true"
  expect a ((match ev 5 (.prim .natBle [lit 4, lit 3]) with
    | .ok (.con c []) => c == bF | _ => false)) "natBle 4 3 is false"
  expectR a (ev 5 (.prim .natAdd [lit 2])) "stuck" "unsaturated primitive"
  expectR a (ev 5 (.prim .natPred [lit 0])) "ok lit 0" "natPred"
  -- Left to right.
  expectR a (ev 50 (.con pairK [.trap, .glob 1])) "trap" "con fields left to right"
  expectR a (ev 50 (.prim .natAdd [.glob 1, .trap])) "timeout" "prim arguments left to right"
  expectR a (ev 50 (.letE { nonDep := true } .trap (.glob 1))) "trap" "let is strict"
  -- tick and trap.
  expectR a (ev 0 (.tick (lit 1))) "timeout" "tick charges"
  expectR a (ev 1 (.tick (lit 1))) "ok lit 1" "tick is otherwise transparent"
  expectR a (ev 0 .trap) "trap" "trap"
  -- Recursion through globals, and run.
  expectR a (IxCC.Lam.run program 100 2 [.lit (.nat 21)]) "ok lit 42" "doubling"
  expectR a (IxCC.Lam.run program 10 1 []) "timeout" "a loop times out"
  -- Keys: structural equality (D19).
  let k1 : Key.GKey := .spec (.const 3 [true]) [.lit 1, .con (.src 4) [.hole 0]]
  let k2 : Key.GKey := .spec (.const 3 [true]) [.lit 1, .con (.src 4) [.hole 1]]
  expect a (k1 == k1 && k1 != k2) "GKey equality is structural"
  expect a (Key.GKey.const 3 [true] != .const 3 [false]) "profiles distinguish keys"
  expect a (Key.GKey.wrapper (.prim .add) [] != .wrapper (.prim .sub) []) "wrapper heads"
  expect a (Key.CtorKey.clo (.lam (.const 1 []) [0]) 2 == .clo (.lam (.const 1 []) [0]) 2)
    "closure constructor keys"

/-- Clock monotonicity on random clocks: once a run does not time out, every
larger clock gives the same outcome. -/
def monotone (a : Assert) (P : LProgram) (root : Nat) (args : List Nat) (least : Nat)
    (g : Gen) (label : String) : IO Gen := do
  let base ← runLam P least root args
  let mut g := g
  for _ in [0:6] do
    let (d, g1) := g.next (4 * least + 8)
    g := g1
    let r ← runLam P (least + d) root args
    expect a (lamOutcome r == lamOutcome base &&
      (match r, base with
        | .ok x, .ok y => IxCC.Lam.readback P x == IxCC.Lam.readback P y
        | _, _ => true))
      s!"{label} {args}: clock {least + d} gives {lamOutcome r}, {least} gave {lamOutcome base}"
    if least > 0 then
      let (d, g2) := g.next least
      g := g2
      let r ← runLam P d root args
      expect a (lamOutcome r == "timeout") s!"{label} {args}: clock {d} below the least {least}"
  return g

/-- A program from global bodies (keys `const i []` unless given). -/
def programOf (gs : List (Key.GKey × Term)) (roots : List Nat := [0]) : LProgram :=
  { program with
    globals := Src.NatMap.ofList (gs.zipIdx.map fun ((key, body), i) => (i, { key, body }))
    size := gs.length, roots }

def modesOf (P : LProgram) : Bool := IxCC.Lam.modesOk P

/-- `WellFormed` and `ModesOk` reject what they should. -/
def static (a : Assert) : IO Unit := do
  expect a (IxCC.Lam.wellFormed program && modesOf program) "the rule program is well formed"
  let wf := fun (gs : List (Key.GKey × Term)) (roots : List Nat) =>
    IxCC.Lam.wellFormed (programOf gs roots)
  let k := fun (i : Nat) => Key.GKey.const i []
  expect a (wf [(k 0, .lam .strict {} (v 0))] [0]) "WellFormed: a closed global"
  expect a (!wf [(k 0, .lam .strict {} (v 1))] [0]) "WellFormed: a variable out of scope"
  expect a (!wf [(k 0, .glob 1)] [0]) "WellFormed: a glob out of range"
  expect a (!wf [(k 0, .con pairK [lit 1])] [0]) "WellFormed: a constructor arity"
  expect a (!wf [(k 0, .proj pairK 2 (lit 1))] [0]) "WellFormed: a projection index"
  expect a (!wf [(k 0, .case (lit 1) [.mk natZ 0 (lit 0), .mk natZ 0 (lit 1)] none)] [0])
    "WellFormed: repeated alternative keys"
  expect a (!wf [(k 0, .case (lit 1) [.mk natS 0 (lit 0)] none)] [0])
    "WellFormed: an alternative arity"
  expect a (!wf [(k 0, .prim .natAdd [lit 1])] [0]) "WellFormed: an unsaturated primitive"
  expect a (!wf [(k 0, lit 0), (k 0, lit 1)] [0]) "WellFormed: repeated global keys"
  expect a (!wf [(k 0, lit 0)] [1]) "WellFormed: a root out of range"
  expect a (decide (IxCC.Lam.WellFormed (programOf [(k 0, lit 0)])))
    "WellFormed is decidable"
  -- ModesOk.
  let modes := fun (gs : List (Key.GKey × Term)) => modesOf (programOf gs)
  let byName : Key.GKey := .byName 9 []
  let recK : Key.GKey := .recStar 9 []
  let nameId := Term.lam .name {} (v 0)
  expect a (modes [(byName, nameId), (k 1, .app (.glob 0) (lit 1) .name)])
    "ModesOk: a by-name global applied by name"
  expect a (!modes [(k 0, nameId)]) "ModesOk: a const global with a by-name binder"
  expect a (!modes [(byName, nameId), (k 1, .glob 0)]) "ModesOk: a by-name global escapes"
  expect a (!modes [(byName, nameId), (k 1, .app (.glob 0) (lit 1) .strict)])
    "ModesOk: a strict argument for a by-name binder"
  expect a (!modes [(k 0, .lam .strict {} (v 0)), (k 1, .app (.glob 0) (lit 1) .name)])
    "ModesOk: a by-name argument for a strict binder"
  expect a (!modes [(k 0, .letE { nonDep := true } nameId (lit 1))])
    "ModesOk: a by-name λ in a plain position"
  -- A recursor-like global whose minor is dispatched with a by-name IH.
  let rstar := Term.lam .name {} (.lam .strict {} (.app (.app (v 1) (v 0) .strict) (lit 0) .name))
  let call := fun (minor : Term) => Term.app (.app (.glob 0) minor .name) (lit 3) .strict
  let goodMinor := Term.lam .strict {} (.lam .name {} (v 0))
  let badMinor := Term.lam .strict {} (.lam .strict {} (v 0))
  expect a (modes [(recK, rstar), (k 1, call goodMinor)]) "ModesOk: a minor with the dispatch modes"
  expect a (!modes [(recK, rstar), (k 1, call badMinor)]) "ModesOk: a minor with other modes"
  expect a (!modes [(recK, rstar), (k 1, call (.glob 1))]) "ModesOk: a non-λ minor (S25)"
  expect a (!modes [(recK, rstar), (k 1, .glob 0)]) "ModesOk: r⋆ escapes"
  -- r⋆ over Nat: dispatch `m n (name (r⋆ m n))`, forwarding its own minor.
  let ih := Term.app (.app (.glob 0) (v 2) .name) (v 0) .strict
  let natStar := Term.lam .name {} (.lam .strict {} (.case (v 0)
    [.mk natZ 0 (lit 0), .mk natS 1 (.app (.app (v 2) (v 0) .strict) ih .name)] none))
  expect a (modes [(recK, natStar), (k 1, call goodMinor)])
    "ModesOk: a minor forwarded by name with its own dispatch"
  -- Another global that only forwards a minor has no dispatch of its own.
  let forward := Term.lam .name {} (.lam .strict {}
    (.app (.app (.glob 0) (v 1) .name) (v 0) .strict))
  expect a (!modes [(recK, rstar), (.recStar 8 [], forward)])
    "ModesOk: a forwarded minor with another dispatch (mutual recursors are declined)"

def run (a : Assert) : IO Unit := do
  rules a
  static a
  let mut g : Gen := { seed := 11 }
  for n in [0, 1, 5, 20] do
    let some least ← leastClock (fun k => do return notTimeout (← runLam program k 2 [n])) 1000
      | expect a false s!"doubling {n} has no least clock"
    expect a (least == n + 1) s!"doubling {n}: least clock {least}, expected {n + 1}"
    g ← monotone a program 2 [n] least g "doubling"

end IxCCTests.Lam.Eval
