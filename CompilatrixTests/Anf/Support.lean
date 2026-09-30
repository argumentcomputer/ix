import CompilatrixTests.Lam.Support
import Compilatrix.Anf.Convert
import Compilatrix.Anf.Semantics
import Compilatrix.Anf.Readback
import Compilatrix.Anf.WellFormed
import Compilatrix.Anf.Print

/-! Shared support for the Anf suite: running Lam and Anf side by side,
least clocks, tick dominance and outcome rendering. -/

namespace CompilatrixTests.Anf

open Compilatrix CompilatrixTests.Src CompilatrixTests.Lam
open Compilatrix.Sem (Result Obs)

abbrev AProgram := Compilatrix.Anf.Program
abbrev AVal := Compilatrix.Anf.Val

def anfOutcome : Result AVal → String
  | .ok v => s!"ok {v.shape}"
  | .timeout => "timeout"
  | .stuck => "stuck"
  | .trap => "trap"
  | .resource _ => "resource"

def runAnf (P : AProgram) (k : Nat) (root : Nat) (args : List Nat) : IO (Result AVal) :=
  IO.lazyPure fun _ => Compilatrix.Anf.run P k root (args.map fun n => .lit (.nat n))

/-- The Anf root for a Lam root (roots correspond by position). -/
def anfRoot (L : LProgram) (A : AProgram) (lr : Nat) : Option Nat :=
  match L.roots.idxOf? lr with
  | some i => A.roots[i]?
  | none => none

/-- Values agree up to closures: equal literals, □, and constructors with
the same key and agreeing fields; any two closures agree (they have no
observation). -/
partial def agree : LVal → AVal → Bool
  | .lit a, .lit b => a == b
  | .box, .box => true
  | .con c fs, .con c' gs => decide (c = c') && fs.length == gs.length &&
      (fs.zip gs).all fun (x, y) => agree x y
  | .clos .., .clos .. => true
  | _, _ => false

/-- Lam against Anf over many runs. -/
structure Tally where
  runs : Nat := 0
  ok : Nat := 0
  timeout : Nat := 0
  trap : Nat := 0
  stuck : Nat := 0
  /-- Successful runs whose least clocks agree. -/
  sameClock : Nat := 0
  /-- Successful runs where Anf needs a larger clock (ticks, jumps). -/
  laterClock : Nat := 0
  /-- The largest ratio of least clocks seen, in percent. -/
  maxRatio : Nat := 100
  deriving Inhabited

def Tally.render (t : Tally) : String :=
  s!"{t.runs} runs: ok {t.ok}, timeout {t.timeout}, trap {t.trap}, stuck {t.stuck}; " ++
  s!"least clocks equal {t.sameClock}, Anf later {t.laterClock} (max ratio {t.maxRatio}%)"

def Tally.add (t u : Tally) : Tally :=
  { runs := t.runs + u.runs, ok := t.ok + u.ok, timeout := t.timeout + u.timeout
    trap := t.trap + u.trap, stuck := t.stuck + u.stuck, sameClock := t.sameClock + u.sameClock
    laterClock := t.laterClock + u.laterClock, maxRatio := max t.maxRatio u.maxRatio }

/-- How much larger than Lam's clock an Anf run may need (ticks from P1,
inlining and joins; each pass may add a bounded factor). -/
def slack : Nat := 64

/-- Compare Lam and Anf on one root and argument tuple at `clock`:
* a Lam value gives an Anf value with the same readback, at a clock of at
  most `slack` times Lam's;
* a Lam trap gives an Anf trap; a Lam timeout an Anf timeout **at the same
  clock** (the timeout clause); a stuck Lam run imposes nothing;
* **tick dominance**: on a finished Lam run, Anf times out at every clock
  below Lam's least clock (checked at the least clock minus one and at
  half of it, and at every clock when it is at most 32), so Anf never
  finishes earlier;
* Anf's result is stable above its least clock (monotonicity). -/
def compareRun (a : Assert) (L : LProgram) (A : AProgram) (lr : Nat) (args : List Nat)
    (clock : Nat) (label : String) (t : Tally) : IO Tally := do
  let some ar := anfRoot L A lr | do expect a false s!"{label}: no Anf root for {lr}"; return t
  let rl ← runLam L clock lr args
  let t := { t with runs := t.runs + 1 }
  let msg := fun (s : String) => s!"{label} {args}: {s} (Lam {lamOutcome rl})"
  let dominance := fun (ll : Nat) => do
    let belows := if ll ≤ 32 then List.range ll else [ll - 1, ll / 2]
    for k in belows do
      let r ← runAnf A k ar args
      expect a (anfOutcome r == "timeout")
        (msg s!"Anf gives {anfOutcome r} at clock {k}, below Lam's least clock {ll}")
  match rl with
  | .ok v =>
    let some ll ← leastClock (fun k => do return notTimeout (← runLam L k lr args)) clock
      | do expect a false (msg "no Lam least clock"); return t
    dominance ll
    let some la ← leastClock (fun k => do return notTimeout (← runAnf A k ar args)) (slack * clock)
      | do expect a false (msg s!"Anf does not finish within {slack}× the clock"); return t
    let ra ← runAnf A la ar args
    let want := Compilatrix.Lam.readback L v
    match ra with
    | .ok w =>
      let got := Compilatrix.Anf.readback A w
      expect a (want == got) (msg s!"Anf readback {repr got}, Lam {repr want}")
      expect a (agree v w) (msg s!"values disagree (Lam {v.shape}, Anf {w.shape})")
      for k in [la + 1, 2 * la + 3] do
        let r ← runAnf A k ar args
        expect a (match r with
            | .ok x => Compilatrix.Anf.readback A x == got
            | _ => false)
          (msg s!"Anf at clock {k} gives {anfOutcome r}, at its least {la} ok")
    | r => expect a false (msg s!"Lam returns a value, Anf {anfOutcome r}")
    let ratio := if ll == 0 then 100 else la * 100 / ll
    let t := { t with ok := t.ok + 1, maxRatio := max t.maxRatio ratio }
    return if la == ll then { t with sameClock := t.sameClock + 1 }
      else { t with laterClock := t.laterClock + 1 }
  | .trap =>
    if let some ll ← leastClock (fun k => do return notTimeout (← runLam L k lr args)) clock then
      dominance ll
    let ra ← runAnf A (slack * clock) ar args
    expect a (anfOutcome ra == "trap") (msg s!"a Lam trap is Anf {anfOutcome ra}")
    return { t with trap := t.trap + 1 }
  | .timeout =>
    let ra ← runAnf A clock ar args
    expect a (anfOutcome ra == "timeout") (msg s!"timeout clause: Anf {anfOutcome ra}")
    return { t with timeout := t.timeout + 1 }
  | .stuck => return { t with stuck := t.stuck + 1 }
  | .resource _ =>
    expect a false (msg "Lam never returns a resource failure")
    return t

/-- `WellScoped` of a program, with the first bad global on failure. -/
def checkScoped (a : Assert) (A : AProgram) (label : String) : IO Unit := do
  expect a (Compilatrix.Anf.wellScoped A)
    s!"{label}: not WellScoped (first bad global {Compilatrix.Anf.firstIllScoped A})\n{A.render}"

/-- Globals and nodes of a program. -/
def size (A : AProgram) : Nat × Nat :=
  (A.size, A.globalList.foldl (fun n (_, gd) => n + gd.body.nodes) 0)

def sizeStr (A : AProgram) : String :=
  let (g, n) := size A
  s!"{g} globals/{n} nodes"

end CompilatrixTests.Anf
