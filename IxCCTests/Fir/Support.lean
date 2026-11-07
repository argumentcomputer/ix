import IxCCTests.Anf.Support
import IxCC.Fir.Lower
import IxCC.Fir.Semantics
import IxCC.Fir.WellFormed
import IxCC.Fir.Print
import IxCC.Own.Semantics
import IxCC.Own.WellFormed
import IxCC.Cfg.Lower
import IxCC.Cfg.Semantics
import IxCC.Cfg.WellFormed
import IxCC.Cfg.Print

/-! Shared support for the Fir/Own/Cfg suite: the Phase 1 lowering of an Anf
program to every level, runs at each level, the value relations, and the
level-by-level comparison with its clock maps:

* **Anf → Fir** (tick erasure, 06 S31): Fir charges a subset of Anf's
  events, so an Anf value at clock `k` is a Fir value at `k` (Fir's least
  clock is at most Anf's), and Anf timing out at `N·(k + 1)` (`N =
  Fir.tickBound`) means Fir times out at `k`;
* **Fir → Own** (the immortal embedding, 03 §4.4): the same outcome at every
  clock, the Own value denoting the Fir value, under both allocation
  policies;
* **Own → Cfg** (big-step depth clock → small-step total clock, 03 §7): an
  Own value at depth `k` is the same value and heap at some Cfg clock `k' ≥
  k`, and Own timing out at `k` means Cfg times out at `k`; the step bound
  never decides a run. -/

namespace IxCCTests.Fir

open IxCC IxCCTests.Src IxCCTests.Lam IxCCTests.Anf
open IxCC.Sem (Result Obs)

abbrev FProgram := IxCC.Fir.Program
abbrev FVal := IxCC.Fir.Val
abbrev OProgram := IxCC.Own.Program
abbrev CProgram := IxCC.Cfg.Program
abbrev RVal := IxCC.Own.RVal
abbrev Heap := IxCC.Own.Heap

/-- An Anf program lowered to every Phase 1 level. -/
structure Levels where
  anf : AProgram
  fir : FProgram
  own : OProgram
  cfg : CProgram
  /-- `Fir.tickBound anf`. -/
  n : Nat

def lower (A : AProgram) : Except String Levels := do
  let F ← (IxCC.Fir.lower A).mapError (·.render)
  let O := IxCC.Own.immortal F
  pure { anf := A, fir := F, own := O, cfg := IxCC.Cfg.lower O, n := IxCC.Fir.tickBound A }

def outcome {α : Type} (shape : α → String) : Result α → String
  | .ok v => s!"ok {shape v}"
  | .timeout => "timeout"
  | .stuck => "stuck"
  | .trap => "trap"
  | .resource _ => "resource"

def firOutcome : Result FVal → String := outcome IxCC.Fir.Val.shape
def ownOutcome : Result (RVal × Heap) → String := outcome (·.1.shape)

def natArgs (args : List Nat) : List FVal := args.map fun n => .lit (.nat n)
def rArgs (args : List Nat) : List RVal := args.map fun n => .lit (.nat n)

def runFir (F : FProgram) (k f : Nat) (args : List Nat) : IO (Result FVal) :=
  IO.lazyPure fun _ => IxCC.Fir.run F k f (natArgs args)

def runOwn (pol : Own.AllocPol) (O : OProgram) (k f : Nat) (args : List Nat) :
    IO (Result (RVal × Heap)) :=
  IO.lazyPure fun _ => IxCC.Own.run pol O k f (rArgs args)

def runCfg (pol : Own.AllocPol) (C : CProgram) (k f : Nat) (args : List Nat) :
    IO (Result (RVal × Heap)) :=
  IO.lazyPure fun _ => IxCC.Cfg.run pol C k f (rArgs args)

def runCfgFuel (pol : Own.AllocPol) (C : CProgram) (fuel k f : Nat) (args : List Nat) :
    IO (Result (RVal × Heap)) :=
  IO.lazyPure fun _ => IxCC.Cfg.runFuel pol C fuel k f (rArgs args)

/-- Anf and Fir values related (03 §2.2 `ValRel`): equal literals, □ and
`erased`, a constructor and its `CtorInfo.ofKey` with related fields. -/
partial def relAF (A : AProgram) : AVal → FVal → Bool
  | .lit a, .lit b => a == b
  | .box, .erased => true
  | .con c fs, .ctor info gs =>
    decide (c = info.key) && decide (IxCC.Fir.CtorInfo.ofKey A.ctors c = some info) &&
      fs.length == gs.length && (fs.zip gs).all fun (x, y) => relAF A x y
  | _, _ => false

/-- Same outcome, and equal values (the Own value denoting the Fir one). -/
def sameFirOwn (rf : Result FVal) (ro : Result (RVal × Heap)) : Bool :=
  match rf, ro with
  | .ok v, .ok (w, H) => match H.value? w with
    | some w' => w' == v
    | none => false
  | .timeout, .timeout | .trap, .trap | .stuck, .stuck => true
  | _, _ => false

def isTimeout {α : Type} : Result α → Bool
  | .timeout => true
  | _ => false

/-- Least clock by doubling then bisection (clock monotonicity makes it well
defined); `none` above `hi`. -/
def leastUp (ok : Nat → IO Bool) (lo hi : Nat) : IO (Option Nat) := do
  if ← ok lo then return some lo
  let mut top := max (2 * lo) 1
  while !(← ok top) do
    if top ≥ hi then return none
    top := min hi (2 * top)
  leastClock ok top

/-- Per-level tallies. -/
structure Tally where
  runs : Nat := 0
  ok : Nat := 0
  timeout : Nat := 0
  trap : Nat := 0
  stuck : Nat := 0
  /-- Runs where Fir's least clock equals Anf's / is below it. -/
  firSame : Nat := 0
  firEarlier : Nat := 0
  /-- The largest Anf/Fir least-clock ratio seen, in percent. -/
  maxRatio : Nat := 100
  /-- Timeout-clause instances checked (Anf timing out at `N·(k+1)`). -/
  tickClause : Nat := 0
  /-- The largest Cfg total clock over Own's depth clock, in percent. -/
  maxCfgRatio : Nat := 100
  /-- Successful runs of programs with nothing to erase (`N = 1`), where Fir is
  clock-exact with Anf. -/
  exact : Nat := 0
  deriving Inhabited

def Tally.render (t : Tally) : String :=
  s!"{t.runs} runs: ok {t.ok}, timeout {t.timeout}, trap {t.trap}, stuck {t.stuck}; " ++
  s!"Fir least clock = Anf's {t.firSame}, below {t.firEarlier} (max Anf/Fir {t.maxRatio}%); " ++
  s!"{t.tickClause} tick-bound timeouts; {t.exact} clock-exact (N = 1); " ++
  s!"max Cfg/Own clock {t.maxCfgRatio}%"

def Tally.add (t u : Tally) : Tally :=
  { runs := t.runs + u.runs, ok := t.ok + u.ok, timeout := t.timeout + u.timeout
    trap := t.trap + u.trap, stuck := t.stuck + u.stuck, firSame := t.firSame + u.firSame
    firEarlier := t.firEarlier + u.firEarlier, maxRatio := max t.maxRatio u.maxRatio
    tickClause := t.tickClause + u.tickClause, maxCfgRatio := max t.maxCfgRatio u.maxCfgRatio
    exact := t.exact + u.exact }

/-- Own against Cfg at one depth clock `k` where Own gives `ro`: a timeout
is a Cfg timeout at `k` (the identity map), a value or trap is the same
value and heap, or trap, at Cfg's least clock `k'` (and a timeout below it),
with the step bound never deciding the run; when `k` is Own's least clock,
`k' ≥ k` (a total clock is never below a depth clock). Returns `k'`. -/
def ownCfg (a : Assert) (pol : Own.AllocPol) (L : Levels) (f : Nat) (args : List Nat) (k : Nat)
    (ro : Result (RVal × Heap)) (msg : String → String) (least : Bool := false) : IO Nat := do
  match ro with
  | .timeout =>
    let rc ← runCfg pol L.cfg k f args
    expect a (isTimeout rc) (msg s!"Own times out at {k}, Cfg gives {ownOutcome rc}")
    return k
  | .stuck => return k
  | _ =>
    let some kc ← leastUp (fun c => do return !isTimeout (← runCfg pol L.cfg c f args)) 0 (1 <<< 40)
      | do expect a false (msg s!"Cfg never finishes (Own {ownOutcome ro})"); return k
    let rc ← runCfg pol L.cfg kc f args
    expect a (rc == ro) (msg s!"Cfg at {kc} gives {ownOutcome rc}, Own at {k} {ownOutcome ro}")
    -- the step bound: four times the fuel changes nothing, at kc and below it
    let fuel := 4 * IxCC.Cfg.fuelFor L.cfg kc + 100
    let rc' ← runCfgFuel pol L.cfg fuel kc f args
    expect a (rc' == rc) (msg s!"Cfg at {kc} depends on the step bound")
    if kc > 0 then
      let below ← runCfg pol L.cfg (kc - 1) f args
      let below' ← runCfgFuel pol L.cfg (4 * IxCC.Cfg.fuelFor L.cfg (kc - 1) + 100)
        (kc - 1) f args
      expect a (isTimeout below && isTimeout below')
        (msg s!"Cfg below its least clock {kc}: {ownOutcome below}")
    expect a (kc ≥ k || !least)
      (msg s!"Cfg's least clock {kc} is below Own's depth clock {k}")
    return kc

/-- Compare every level on one root and argument tuple, with Anf's outcome
at `clock` as the reference (Lam's readback checked too when given). -/
def compareRun (a : Assert) (L : Levels) (lam : Option (LProgram × Nat)) (ar : Nat)
    (args : List Nat) (clock : Nat) (label : String) (t : Tally) : IO Tally := do
  let A := L.anf
  let ra ← runAnf A clock ar args
  let t := { t with runs := t.runs + 1 }
  let msg := fun (s : String) => s!"{label} {args}: {s} (Anf {anfOutcome ra})"
  -- the timeout clause of the tick bound, at every k with N·(k+1) ≤ the given clock
  let tickClause := fun (hiClock : Nat) (t : Tally) => do
    let mut t := t
    let top := hiClock / L.n
    let ks := if top ≤ 12 then List.range top else [0, 1, top / 2, top - 2, top - 1]
    for k in ks do
      let rak ← runAnf A (L.n * (k + 1)) ar args
      if isTimeout rak then
        let rf ← runFir L.fir k ar args
        expect a (isTimeout rf) (msg s!"Anf times out at {L.n}·({k}+1), Fir at {k} gives {firOutcome rf}")
        let ro ← runOwn .immortal L.own k ar args
        expect a (isTimeout ro) (msg s!"Own at {k} gives {ownOutcome ro}")
        let rc ← runCfg .immortal L.cfg k ar args
        expect a (isTimeout rc) (msg s!"Cfg at {k} gives {ownOutcome rc}")
        t := { t with tickClause := t.tickClause + 1 }
    return t
  match ra with
  | .ok av =>
    let some la ← leastClock (fun k => do return notTimeout (← runAnf A k ar args)) clock
      | do expect a false (msg "no Anf least clock"); return t
    let want := IxCC.Anf.readback A av
    if let some (LP, lr) := lam then
      let rl ← runLam LP (64 * clock) lr args
      match rl with
      | .ok lv => expect a (IxCC.Lam.readback LP lv == want) (msg "Lam and Anf readback differ")
      | .stuck => pure ()   -- a stuck source imposes nothing
      | r => expect a false (msg s!"Lam gives {lamOutcome r}")
    -- Fir: a related value at Anf's least clock; its own least clock is no later
    let rf ← runFir L.fir la ar args
    let some lf ← leastClock (fun k => do return notTimeout (← runFir L.fir k ar args)) la
      | do expect a false (msg s!"Fir does not finish at Anf's least clock {la}: {firOutcome rf}"); return t
    let rf ← runFir L.fir lf ar args
    match rf with
    | .ok fv =>
      expect a (relAF A av fv) (msg s!"Anf and Fir values unrelated (Fir {fv.shape})")
      expect a (IxCC.Fir.readback fv == want) (msg "Fir readback differs")
    | r => expect a false (msg s!"Fir gives {firOutcome r} at its least clock {lf}")
    if lf > 0 then
      let below ← runFir L.fir (lf - 1) ar args
      expect a (isTimeout below) (msg s!"Fir below its least clock gives {firOutcome below}")
    -- the tick bound read backwards (Fir finishing at `lf` means Anf finishes by
    -- `N·(lf + 1)`), and clock exactness when nothing is erased (`N = 1`)
    expect a (la ≤ L.n * (lf + 1)) (msg s!"Anf's least clock {la} exceeds {L.n}·({lf}+1)")
    if L.n == 1 then
      expect a (la == lf) (msg s!"no tick or free jump, yet least clocks differ: Anf {la}, Fir {lf}")
    -- Own: the same outcome at Fir's least clock and just below, both policies
    let mut kc := 0
    for pol in [Own.AllocPol.immortal, .rc] do
      let ro ← runOwn pol L.own lf ar args
      expect a (sameFirOwn rf ro) (msg s!"Own ({reprStr pol}) at {lf}: {ownOutcome ro}")
      if let .ok (w, H) := ro then
        expect a (H.readback w == want) (msg "Own readback differs")
        if pol == .immortal then
          expect a H.immortalOk (msg "the final heap breaks the immortal invariant")
      if lf > 0 then
        let rb ← runOwn pol L.own (lf - 1) ar args
        expect a (isTimeout rb) (msg s!"Own below Fir's least clock: {ownOutcome rb}")
        let _ ← ownCfg a pol L ar args (lf - 1) rb msg
      let c ← ownCfg a pol L ar args lf ro msg (least := true)
      if pol == .immortal then kc := c
    let t ← tickClause la t
    let ratio := if lf == 0 then 100 else la * 100 / lf
    let cratio := if lf == 0 then 100 else kc * 100 / lf
    let t := { t with ok := t.ok + 1, maxRatio := max t.maxRatio ratio
                      exact := t.exact + (if L.n == 1 then 1 else 0)
                      maxCfgRatio := max t.maxCfgRatio cratio }
    return if la == lf then { t with firSame := t.firSame + 1 }
      else { t with firEarlier := t.firEarlier + 1 }
  | .trap =>
    let rf ← runFir L.fir clock ar args
    expect a (firOutcome rf == "trap") (msg s!"an Anf trap is Fir {firOutcome rf}")
    let ro ← runOwn .immortal L.own clock ar args
    expect a (sameFirOwn rf ro) (msg s!"Own gives {ownOutcome ro}")
    let _ ← ownCfg a .immortal L ar args clock ro msg
    return { t with trap := t.trap + 1 }
  | .timeout =>
    let t ← tickClause clock t
    -- Fir at the same clock: a timeout or (fewer charges) any outcome but stuck
    let rf ← runFir L.fir clock ar args
    let ro ← runOwn .immortal L.own clock ar args
    expect a (sameFirOwn rf ro) (msg s!"Fir {firOutcome rf}, Own {ownOutcome ro}")
    let _ ← ownCfg a .immortal L ar args clock ro msg
    return { t with timeout := t.timeout + 1 }
  | .stuck => return { t with stuck := t.stuck + 1 }
  | .resource _ =>
    expect a false (msg "Anf never returns a resource failure")
    return t

/-- Well-formedness at every level. -/
def checkLevels (a : Assert) (L : Levels) (label : String) : IO Unit := do
  checkScoped a L.anf label
  match IxCC.Fir.check L.fir with
  | .ok () => expect a true ""
  | .error e => expect a false s!"{label}: Fir not WellFormed: {e}\n{L.fir.render}"
  expect a (IxCC.Own.checkImmortal L.own) s!"{label}: Own outside the immortal fragment"
  match IxCC.Own.check L.own with
  | .ok () => expect a true ""
  | .error e => expect a false s!"{label}: Own not WellFormed: {e}"
  match IxCC.Cfg.check L.cfg with
  | .ok () => expect a true ""
  | .error e => expect a false s!"{label}: Cfg not WellFormed: {e}\n{L.cfg.render}"

/-- Sizes: functions, Fir nodes, Cfg blocks, instructions, back edges,
unreachable blocks, the tick bound. -/
def sizes (L : Levels) : String :=
  s!"{L.fir.size} functions, {L.fir.nodes} Fir nodes, {L.cfg.blocks} blocks, " ++
  s!"{L.cfg.instrs} instructions, {IxCC.Cfg.backEdges L.cfg} back edges, " ++
  s!"{IxCC.Cfg.unreachable L.cfg} unreachable, tick bound N = {L.n}"

end IxCCTests.Fir
