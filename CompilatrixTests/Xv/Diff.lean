import CompilatrixTests.Xv.Support
import CompilatrixTests.Lir.Gen
import CompilatrixTests.Lir.Kernels
import CompilatrixTests.Lir.Props
import Compilatrix.Lir.SplitEdges
import Compilatrix.Lir.WellFormed

/-!
# Differential properties of selection

For each generated Lir program (split, so well-formed) that selection
accepts:

1. **Selection** is deterministic, its output is `Xv.WellFormed`, and each
   instruction's operand metadata names exactly its syntactic uses and
   definitions.
2. **Lock-step outcomes** (05 §4, `Select.correct`): unless `Lir.eval` is
   `stuck`, `Xv.eval` gives the same outcome (values, heap and context
   words, or the failure) at the clocks 0–3, 24 and 200.
3. **Same clock**: stepping both by hand spends the same number of charges,
   and a run that finishes after `c` charges finishes identically at clock
   `c` and times out at `c − 1` (the timeout clause, 06 S32).

A program selection rejects must name an unsupported form; the report
counts them by form. The kernels are checked at their exact clocks.
-/

namespace CompilatrixTests.Xv.Diff

open Compilatrix Compilatrix.Lir Compilatrix.Xv CompilatrixTests.Lir

structure Report where
  cases : Nat := 0
  selected : Nat := 0
  /-- Programs rejected, by the first unsupported form. -/
  unsupported : Std.HashMap String Nat := {}
  /-- Programs whose Lir run is `stuck` (only selection is checked). -/
  stuck : Nat := 0
  outcomes : Array Nat := Array.replicate 7 0
  /-- Programs finishing at an exact clock `c > 0` (so `c − 1` was checked). -/
  exact : Nat := 0
  charged : Nat := 0
  maxCharges : Nat := 0
  /-- Programs on which each rule fired, and its total firings. -/
  rulePrograms : Std.HashMap String Nat := {}
  ruleFirings : Std.HashMap String Nat := {}
  lirStmts : Nat := 0
  xvInsts : Nat := 0
  lirSteps : Nat := 0
  xvSteps : Nat := 0
  deriving Inhabited

def addCounts (a b : Std.HashMap String Nat) : Std.HashMap String Nat :=
  b.fold (init := a) fun acc k v => acc.insert k (acc.getD k 0 + v)

def Report.add (a b : Report) : Report :=
  { cases := a.cases + b.cases, selected := a.selected + b.selected
    unsupported := addCounts a.unsupported b.unsupported, stuck := a.stuck + b.stuck
    outcomes := (a.outcomes.zip b.outcomes).map fun (x, y) => x + y
    exact := a.exact + b.exact, charged := a.charged + b.charged
    maxCharges := max a.maxCharges b.maxCharges
    rulePrograms := addCounts a.rulePrograms b.rulePrograms
    ruleFirings := addCounts a.ruleFirings b.ruleFirings
    lirStmts := a.lirStmts + b.lirStmts, xvInsts := a.xvInsts + b.xvInsts
    lirSteps := a.lirSteps + b.lirSteps, xvSteps := a.xvSteps + b.xvSteps }

def smallClock (seed : UInt64) : Nat := (seed % 4).toNat
def midClock : Nat := 24
def bigClock : Nat := 200

/-- Steps of a Lir run by hand, with charges (as in `Lir.Props`). -/
def lirCount (p : Lir.Program) (s : Lir.State) : Outcome × Nat × Nat :=
  Props.countRun p (Lir.fuelFor p bigClock + 1) bigClock s

def programSize (p : Lir.Program) : Nat :=
  p.funcs.foldl (fun n f => n + f.blocks.foldl (fun n b => n + b.body.size) 0) 0

def xvSize (q : VProgram) : Nat :=
  q.funcs.foldl (fun n f => n + f.blocks.foldl (fun n b => n + b.body.size) 0) 0

/-- All checks on one Lir program. -/
def checkLir (p : Lir.Program) (args : List Word) (seed : UInt64) : Except String Report := do
  match Select.run p with
  | .error e =>
      return { cases := 1, unsupported := ({} : Std.HashMap String Nat).insert e.form 1 }
  | .ok (q, fired) =>
  match Select.run p with
  | .ok (q', _) => unless q == q' do throw "selection is not deterministic"
  | .error _ => throw "selection is not deterministic"
  if let .error e := q.check then throw s!"the selected program is not well formed: {e}"
  unless operandsAgree q do throw "operand metadata disagrees with the instructions' uses or definitions"
  let rules : Std.HashMap String Nat := fired.fold (init := {}) fun acc k v => if v > 0 then acc.insert k 1 else acc
  let base : Report := { cases := 1, selected := 1, rulePrograms := rules, ruleFirings := fired
                         lirStmts := programSize p, xvInsts := xvSize q }
  let mem := Region.initial seed
  let lirBig := digest (Lir.eval p bigClock args mem Region.ctx)
  if lirBig == .stuck then return { base with stuck := 1 }
  let xvBig := digest (Xv.eval q bigClock args mem Region.ctx)
  unless lirBig == xvBig do
    throw s!"at clock {bigClock}: Lir gives {lirBig.text}, Xv gives {xvBig.text}{if lirBig.light == xvBig.light then " (memory differs)" else ""}"
  for k in [smallClock seed, midClock] do
    let a := light (Lir.eval p k args mem Region.ctx)
    let b := light (Xv.eval q k args mem Region.ctx)
    unless a == b do throw s!"at clock {k}: Lir gives {a.text}, Xv gives {b.text}"
  let some ls := Lir.State.initial p args mem Region.ctx | throw "no initial Lir state"
  let some xs := Xv.State.initial q args mem Region.ctx | throw "no initial Xv state"
  let (_, lsteps, lcharges) := lirCount p ls
  let (xout, xsteps, xcharges) := countRun q (Xv.fuelFor q bigClock + 1) bigClock xs
  unless lcharges == xcharges do throw s!"Lir spends {lcharges} charges, Xv {xcharges}"
  unless light xout == xvBig.light do throw s!"stepping Xv by hand gives {(light xout).text}, eval gives {xvBig.text}"
  let mut exact := 0
  if xvBig != .timeout && xcharges > 0 then
    let atC := light (Xv.eval q xcharges args mem Region.ctx)
    unless atC == xvBig.light do throw s!"Xv at its exact clock {xcharges} gives {atC.text}"
    let before := light (Xv.eval q (xcharges - 1) args mem Region.ctx)
    unless before == .timeout do throw s!"Xv at clock {xcharges - 1} gives {before.text}, not timeout"
    exact := 1
  return { base with
    outcomes := (Array.replicate 7 0).modify xvBig.index (· + 1)
    exact, charged := if xcharges > 0 then 1 else 0, maxCharges := xcharges
    lirSteps := lsteps, xvSteps := xsteps }

/-- The checks on the generated program for `seed`, split. -/
def checkProgram (cfg : Gen.Config) (seed : UInt64) : Except String Report := do
  let (raw, _) := Gen.program cfg seed
  let p := raw.splitCriticalEdges
  if let .error e := p.check then throw s!"the split Lir program is not well formed: {e}"
  checkLir p (Gen.mainArgs raw seed) seed

/-- A failure report: the Lir program and its selection. -/
def programText (cfg : Gen.Config) (seed : UInt64) (limit : Nat := 12000) : String :=
  let p := (Gen.program cfg seed).1.splitCriticalEdges
  let sel := match Select.run p with
    | .ok (q, _) => q.text
    | .error e => e.text
  let text := s!"{p.text}\n--- Xv ---\n{sel}"
  if text.length ≤ limit then text else (text.take limit).toString ++ "\n…"

/-! ## Kernels -/

inductive KernelResult where
  | ok (checks : Nat)
  | waiting (form : String)

def expected : Kernels.Expect → Digest
  | .nat n => .ok [Kernels.tag n] [] []
  | .natOverflow => .resource .natOverflow

def checkKernel (c : Kernels.Case) : Except String KernelResult := do
  let p := Kernels.program c.func
  let name := s!"{c.kernel} {c.args}"
  match Select.run p with
  | .error e => return .waiting e.form
  | .ok (q, _) =>
  if let .error e := q.check then throw s!"{name}: selected program not well formed: {e}"
  let args := c.args.map Kernels.tag
  let mem := Region.initial 0
  let run (k : Nat) := light (Xv.eval q k args mem Region.ctx)
  let want := expected c.expect
  match c.charges with
  | some k =>
      unless run k == want do throw s!"{name}: expected {want.text} at clock {k}, got {(run k).text}"
      if k > 0 then
        unless run (k - 1) == .timeout do throw s!"{name}: clock {k - 1} should time out"
        return .ok 2
      return .ok 1
  | none =>
      let got := run 1000000
      unless got == want do throw s!"{name}: expected {want.text}, got {got.text}"
      return .ok 1

end CompilatrixTests.Xv.Diff
