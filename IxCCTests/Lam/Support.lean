import IxCCTests.Src.Support
import IxCC.Lam.Erase
import IxCC.Lam.Erase.Val
import IxCC.Lam.Readback
import IxCC.Lam.WellFormed
import IxCC.Lam.ModesOk

/-! Shared support for the Lam suite: erasing loaded packs, running Src and
Lam side by side, least clocks, and outcome rendering. -/

namespace IxCCTests.Lam

open IxCC IxCC.Src IxCCTests.Src
open IxCC.Sem (Result Obs)

abbrev LProgram := IxCC.Lam.Program
abbrev LVal := IxCC.Lam.Val

/-- A checked Src program and its erasure. -/
structure Erased where
  src : Program
  checked : Relevance.Checked
  input : IxCC.Lam.Erase.Input
  lam : LProgram
  stats : IxCC.Lam.Erase.Stats

def erase (p : Program) (c : Relevance.Checked) : Except String Erased :=
  match IxCC.Lam.erase p c with
  | .ok (lam, stats) => .ok { src := p, checked := c, input := .ofProgram p c, lam, stats }
  | .error e => .error e.render

def eraseLoaded (l : Loaded) : IO Erased := IO.ofExcept (erase l.program l.checked)

/-- The Lam root for a Src root (roots are erased in the Src root order). -/
def lamRoot (e : Erased) (c : CId) : IO Nat := do
  match (e.src.roots.map (·.2)).zip e.lam.roots |>.lookup c with
  | some g => pure g
  | none => throw (IO.userError s!"no Lam root for constant {c}")

def lamOutcome : Result LVal → String
  | .ok v => s!"ok {v.shape}"
  | .timeout => "timeout"
  | .stuck => "stuck"
  | .trap => "trap"
  | .resource _ => "resource"

def runSrc (p : Program) (k : Nat) (root : CId) (args : List Nat) : IO (Result Value) :=
  IO.lazyPure fun _ => Src.run p k root (args.map .lit)

def runLam (P : LProgram) (k : Nat) (root : Nat) (args : List Nat) : IO (Result LVal) :=
  IO.lazyPure fun _ => IxCC.Lam.run P k root (args.map fun n => .lit (.nat n))

/-- The least clock below `hi` at which `ok` holds, by bisection (clock
monotonicity makes it well defined). -/
def leastClock (ok : Nat → IO Bool) (hi : Nat) : IO (Option Nat) := do
  unless ← ok hi do return none
  let mut lo := 0
  let mut hi := hi
  if ← ok 0 then return some 0
  while lo + 1 < hi do
    let mid := (lo + hi) / 2
    if ← ok mid then hi := mid else lo := mid
  return some hi

def notTimeout {α : Type} : Result α → Bool
  | .timeout => false
  | _ => true

/-- Whether an erased program has wrapper globals: the only globals whose
charges SrcEval does not make (its `pap` accumulation is free). -/
def hasWrappers (P : LProgram) : Bool :=
  P.globalList.any fun (_, g) => g.key matches .wrapper ..

mutual
/-- The globals a term references. -/
def globsOf : IxCC.Lam.Term → List Nat
  | .glob g => [g]
  | .var _ | .lit _ | .box | .trap => []
  | .lam _ _ b | .tick b | .proj _ _ b => globsOf b
  | .app f x _ | .letE _ f x => globsOf f ++ globsOf x
  | .con _ ts | .prim _ ts => globsOfList ts
  | .case s alts d =>
    globsOf s ++ globsOfAlts alts ++ (match d with | some t => globsOf t | none => [])
def globsOfList : List IxCC.Lam.Term → List Nat
  | [] => []
  | t :: ts => globsOf t ++ globsOfList ts
def globsOfAlts : List IxCC.Lam.Alt → List Nat
  | [] => []
  | .mk _ _ b :: as => globsOf b ++ globsOfAlts as
end

/-- Whether a wrapper global is reachable from `root` (a run from it may pay
the wrapper's extra charges). -/
def reachesWrapper (P : LProgram) (root : Nat) : Bool := Id.run do
  let mut seen : Std.HashSet Nat := {}
  let mut todo := [root]
  while !todo.isEmpty do
    match todo with
    | [] => pure ()
    | g :: rest =>
      todo := rest
      if seen.contains g then continue
      seen := seen.insert g
      match P.global? g with
      | some gl =>
        if gl.key matches .wrapper .. then return true
        todo := globsOf gl.body ++ todo
      | none => pure ()
  return false

/-- SrcEval against Lam on one run. -/
structure Tally where
  runs : Nat := 0
  ok : Nat := 0
  timeout : Nat := 0
  trap : Nat := 0
  stuck : Nat := 0
  /-- Successful runs whose least clocks agree. -/
  sameClock : Nat := 0
  /-- Successful runs where Lam needs a larger clock (wrappers). -/
  laterClock : Nat := 0
  deriving Inhabited

def Tally.render (t : Tally) : String :=
  s!"{t.runs} runs: ok {t.ok}, timeout {t.timeout}, trap {t.trap}, stuck {t.stuck}; " ++
  s!"least clocks equal {t.sameClock}, Lam later {t.laterClock}"

def Tally.add (t u : Tally) : Tally :=
  { runs := t.runs + u.runs, ok := t.ok + u.ok, timeout := t.timeout + u.timeout
    trap := t.trap + u.trap, stuck := t.stuck + u.stuck, sameClock := t.sameClock + u.sameClock
    laterClock := t.laterClock + u.laterClock }

/-- The expected Lam observation of a SrcEval value (through `eraseVal`). -/
def expectedObs (e : Erased) (v : Value) : Option Obs :=
  (IxCC.Lam.Erase.eraseVal e.input v).bind (IxCC.Lam.readback e.lam)

/-- Compare SrcEval and Lam on one root and argument tuple at `clock`:
* a SrcEval value gives a Lam value with the same Lam-domain observation
  (and, for `Nat` and `Bool` results, SrcEval's own readback);
* a SrcEval trap gives a Lam trap; a SrcEval timeout a Lam timeout at the
  same clock (the timeout clause); a stuck SrcEval run imposes nothing;
* on success, Lam's least clock is never below SrcEval's, equal to it when
  no wrapper is reachable from the root, and Lam times out at SrcEval's least clock
  minus one. -/
def compareRun (a : Assert) (e : Erased) (root : CId) (args : List Nat) (clock : Nat)
    (label : String) (t : Tally) : IO Tally := do
  let g ← lamRoot e root
  let rs ← runSrc e.src clock root args
  let rl ← runLam e.lam clock g args
  let t := { t with runs := t.runs + 1 }
  let msg := fun (s : String) => s!"{label} {args}: {s} (SrcEval {outcome rs}, Lam {lamOutcome rl})"
  match rs with
  | .ok v =>
    let rl ← if notTimeout rl then pure rl else runLam e.lam (8 * clock) g args
    match rl with
    | .ok w =>
      let got := IxCC.Lam.readback e.lam w
      let want := expectedObs e v
      if want.isNone then
        -- A function result: no observation on either side.
        expect a ((v matches .clo .. || v matches .pap ..) && w matches .clos ..)
          (msg "a first-order value without an observation")
      else
        expect a (want == got) (msg s!"Lam-domain readback {repr got}, expected {repr want}")
      let srcObs := readback e.src e.checked.keeps v
      match v with
      | .lit _ => expect a (srcObs == got) (msg "Nat readback differs")
      | .con c .. =>
        if some c == e.src.known.boolTrue || some c == e.src.known.boolFalse then
          expect a (srcObs == got) (msg "Bool readback differs")
      | _ => pure ()
    | _ => expect a false (msg "SrcEval returns a value, Lam does not")
    let some sl ← leastClock (fun k => do return notTimeout (← runSrc e.src k root args)) clock
      | do expect a false (msg "no SrcEval least clock"); return t
    let some ll ← leastClock (fun k => do return notTimeout (← runLam e.lam k g args)) (8 * clock)
      | do expect a false (msg "no Lam least clock"); return t
    expect a (ll ≥ sl) (msg s!"Lam finishes earlier: least clock {ll} < {sl}")
    if !reachesWrapper e.lam g then
      expect a (ll == sl) (msg s!"least clocks differ without wrappers: Lam {ll}, SrcEval {sl}")
    -- The timeout clause below SrcEval's least clock: at every clock when it
    -- is small, else at the least clock minus one and at half of it.
    let belows := if sl ≤ 64 then List.range sl else [sl - 1, sl / 2]
    for k in belows do
      let below ← runLam e.lam k g args
      expect a (lamOutcome below == "timeout")
        (msg s!"Lam at clock {k}, below SrcEval's least {sl}")
    -- Clock monotonicity above Lam's least clock.
    let atLeast ← runLam e.lam ll g args
    for k in [ll + 1, 2 * ll + 3] do
      let r ← runLam e.lam k g args
      expect a (match r, atLeast with
          | .ok x, .ok y => IxCC.Lam.readback e.lam x == IxCC.Lam.readback e.lam y
          | _, _ => false)
        (msg s!"Lam at clock {k} gives {lamOutcome r}, at its least {ll} {lamOutcome atLeast}")
    let t := { t with ok := t.ok + 1 }
    return if ll == sl then { t with sameClock := t.sameClock + 1 }
      else { t with laterClock := t.laterClock + 1 }
  | .trap =>
    let rl ← if notTimeout rl then pure rl else runLam e.lam (8 * clock) g args
    expect a (lamOutcome rl == "trap") (msg "a SrcEval trap is not a Lam trap")
    return { t with trap := t.trap + 1 }
  | .timeout =>
    expect a (lamOutcome rl == "timeout") (msg "timeout clause")
    return { t with timeout := t.timeout + 1 }
  | .stuck => return { t with stuck := t.stuck + 1 }
  | .resource _ =>
    expect a false (msg "SrcEval never returns a resource failure")
    return t

/-- `WellFormed` and `ModesOk` of an erased program. -/
def checkStatic (a : Assert) (e : Erased) (label : String) : IO Unit := do
  expect a (IxCC.Lam.wellFormed e.lam)
    s!"{label}: not WellFormed (first bad global {IxCC.Lam.firstIllFormed e.lam})"
  match IxCC.Lam.ModesOk.run e.lam with
  | .ok () => expect a true ""
  | .error m => expect a false s!"{label}: not ModesOk: {m}"

end IxCCTests.Lam
