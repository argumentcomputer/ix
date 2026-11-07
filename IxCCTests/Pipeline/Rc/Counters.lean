import IxCCTests.Pipeline.Rc.Support

set_option autoImplicit false
namespace IxCCTests.Pipeline.Rc.Counters
open IxCC

/-- Attempts and successful executed events are separate. Free events are
observed at individual successful dec transitions, including cascading frees. -/
structure Counts where
  steps : Nat := 0
  charges : Nat := 0
  allocAttempts : Nat := 0
  allocCalls : Nat := 0
  allocations : Nat := 0
  incAttempts : Nat := 0
  incCalls : Nat := 0
  incUnits : Nat := 0
  dynamicIncUnits : Nat := 0
  decAttempts : Nat := 0
  decCalls : Nat := 0
  frees : Nat := 0
  live : Nat := 0
  peakLive : Nat := 0
  deriving BEq, Repr

def liveCells (H : Own.Heap) : Nat :=
  H.cells.foldl (fun n cell => match cell with | .live .. => n + 1 | .dead => n) 0

def heapOf : Cfg.State → Own.Heap
  | .call _ _ _ H | .run _ _ H | .ret _ _ H => H

inductive Event where
  | alloc
  | inc (value : Own.RVal) (n : Nat)
  | dec
  | other

/-- The actual instruction and decoded marker determine the candidate event.
Success is credited only after the production step returns a next state. -/
def event (P : Cfg.Rc.Program) : Cfg.State → Event
  | .run fr _ _ =>
    match fr.rest with
    | i :: _ =>
      if Cfg.Rc.reserved P.base.size i then
        match Cfg.Rc.decode P.base.size i with
        | some (_, .inc x n) => .inc ((fr.env.get? x).getD .erased) n
        | some (_, .dec _) => .dec
        | none => .other
      else match i with
        | .bind _ (.alloc ..) => .alloc
        | _ => .other
    | [] => .other
  | _ => .other

def attempt (e : Event) (c : Counts) : Counts :=
  match e with
  | .alloc => { c with allocAttempts := c.allocAttempts + 1 }
  | .inc .. => { c with incAttempts := c.incAttempts + 1 }
  | .dec => { c with decAttempts := c.decAttempts + 1 }
  | .other => c

/-- Each pair is one actual dec's before/after cell. Only a count decrease,
a final free, or an unchanged cell is allowed; body mutation is rejected. -/
def decCell (before after : Own.Cell) : Option Nat :=
  if before == after then some 0 else
  match before, after with
  | .live n .dyn _, .dead => if n > 0 then some 1 else none
  | .live n .dyn b, .live m .dyn b' => if b == b' && 0 < m && m < n then some 0 else none
  | _, _ => none

def completed (e : Event) (before after : Own.Heap) (c : Counts) : Except String Counts := do
  let mut c := c
  match e with
  | .alloc =>
    unless before.size ≤ after.size && after.size ≤ before.size + 1 &&
        after.cells.extract 0 before.size == before.cells do
      throw "allocation transition changed an existing cell or appended more than one"
    let newCells := after.cells.extract before.size after.size
    unless newCells.all (fun cell => match cell with | .live 1 .dyn _ => true | _ => false) do
      throw "allocation transition did not append a fresh unique dynamic cell"
    c := { c with
      allocCalls := c.allocCalls + 1
      allocations := c.allocations + after.size - before.size }
  | .inc value n =>
    unless Own.Rc.inc before value n == some after do
      throw "successful inc did not match the executed marker value/multiplicity"
    let dynamic := match value with
      | .loc loc => match before.cell? loc with | some (.live _ .dyn _) => n | _ => 0
      | _ => 0
    c := { c with
      incCalls := c.incCalls + 1
      incUnits := c.incUnits + n
      dynamicIncUnits := c.dynamicIncUnits + dynamic }
  | .dec =>
    unless before.size == after.size do throw "dec transition also allocated"
    let mut freed := 0
    for (a, b) in before.cells.toList.zip after.cells.toList do
      let some count := decCell a b | throw "dec changed a body, revived a cell, or increased a count"
      freed := freed + count
    c := { c with decCalls := c.decCalls + 1, frees := c.frees + freed }
  | .other => unless before == after do throw "unclassified instruction changed the heap"
  let live := liveCells after
  return { c with steps := c.steps + 1, live, peakLive := max c.peakLive live }

/-- Same fuel/clock transitions as Sem.runClocked; production Rc.step is the
only evaluator. The Except layer detects invalid instrumentation assumptions. -/
def loop (P : Cfg.Rc.Program) : (fuel k : Nat) → Cfg.State → Counts →
    Except String (Sem.Result (Own.RVal × Own.Heap) × Counts)
  | 0, _, _, c => pure (.timeout, c)
  | fuel + 1, k, state, c => do
    let e := event P state
    let c := attempt e c
    match Cfg.Rc.step P state with
    | .next next false =>
      loop P fuel k next (← completed e (heapOf state) (heapOf next) c)
    | .next next true =>
      match k with
      | 0 => pure (.timeout, { c with steps := c.steps + 1 })
      | k + 1 =>
        let c ← completed e (heapOf state) (heapOf next) c
        loop P fuel k next { c with charges := c.charges + 1 }
    | .done value => pure (.ok value, { c with steps := c.steps + 1 })
    | .fail r => pure (.resource r, { c with steps := c.steps + 1 })
    | .trap => pure (.trap, { c with steps := c.steps + 1 })
    | .stuck => pure (.stuck, { c with steps := c.steps + 1 })

def runCounted (P : Cfg.Rc.Program) (k root : Nat) (args : List Own.RVal) :
    Except String (Sem.Result (Own.RVal × Own.Heap) × Counts) :=
  loop P (Cfg.fuelFor P.base k) k (.call root args [] {}) {}

def countsLine (name : String) (n seed : Nat) (c : Counts) : String :=
  s!"{name}\t{n}\t{seed}\t{c.steps}\t{c.charges}\t{c.allocAttempts}\t{c.allocCalls}\t{c.allocations}\t{c.incAttempts}\t{c.incCalls}\t{c.incUnits}\t{c.dynamicIncUnits}\t{c.decAttempts}\t{c.decCalls}\t{c.frees}\t{c.live}\t{c.peakLive}"

def controls : IO Unit := do
  -- Independent literal cell-pair oracles for event classification.
  let body : Own.Body := { ctor := default, fields := [] }
  check "counter records a free" (decCell (.live 1 .dyn body) .dead == some 1)
  check "counter distinguishes decrement from free" (decCell (.live 2 .dyn body) (.live 1 .dyn body) == some 0)
  check "counter rejects revival" (decCell .dead (.live 1 .dyn body) == none)
  check "counter rejects count increase" (decCell (.live 1 .dyn body) (.live 2 .dyn body) == none)
  check "counter rejects static free" (decCell (.live 1 .static body) .dead == none)

def run (logs : System.FilePath) : IO Unit := do
  IxCCTests.Recheck.Rc.Fixtures.verify
  controls
  let mut report := ["root\tn\tseed\tsteps\tcharges\talloc_attempts\talloc_calls\tallocated_cells\tinc_attempts\tinc_calls\tinc_units\tdynamic_inc_units\tdec_attempts\tdec_calls\tfreed_cells\tlive\tpeak_live"]
  let counterCases := cases ++ [(8, 2)]
  for name in IxCCTests.Recheck.Rc.Fixtures.roots do
    let compiled ← compile name
    save logs compiled
    let P := compiled.artifact.front.cfg
    let some root := P.base.exports.head? | throw (IO.userError "no counter root")
    for (n, seed) in counterCases do
      let args := [Own.RVal.lit (.nat n), .lit (.nat seed)]
      let (result, c) ← IO.ofExcept (← IO.lazyPure fun _ => runCounted P clock root args)
      let plain ← IO.lazyPure fun _ => Cfg.Rc.run P clock root args
      check (name ++ ": counted outcome/value/heap differs from production Rc.run") (result == plain)
      let value ← observation name (fun (v, H) => H.readback v) result
      check (name ++ ": counted complete value") (value == expected name n seed)
      let some H := (match result with | .ok (_, H) => some H | _ => none)
        | throw (IO.userError "counter result is not successful")
      let outputCells := if name == "sharedReverse" then 2 * n + 1 else n
      check (name ++ ": exact independently expected escaping cell count") (c.live == outputCells)
      check (name ++ ": successful operation attempts differ")
        (c.allocAttempts == c.allocCalls && c.incAttempts == c.incCalls && c.decAttempts == c.decCalls)
      check (name ++ ": dynamic event conservation")
        (c.allocations == c.frees + c.live && c.allocations == H.size && c.live == liveCells H)
      check (name ++ ": bounded actual allocation/RC/free work")
        (c.allocations ≤ 4 * n + 2 && c.peakLive ≤ 4 * n + 2 &&
          c.incUnits ≤ 128 * (n + 1) && c.decCalls ≤ 128 * (n + 1) && c.frees ≤ 4 * n + 2)
      if n > 0 then
        check (name ++ ": RC operations really executed")
          (c.allocations > 0 && c.incCalls > 0 && c.decCalls > 0)
        if name != "sharedReverse" then
          check (name ++ ": intermediate list cells actually freed") (c.frees ≥ n)
      if n ≥ 2 then
        check (name ++ ": nonempty projected tail retains a dynamic cell") (c.dynamicIncUnits > 0)
      -- Clock refusals must agree exactly; no successful event is inferred
      -- from a step whose charge is refused at clock zero.
      for k in [0, 1, 2, 3] do
        let (short, _) ← IO.ofExcept (← IO.lazyPure fun _ => runCounted P k root args)
        let reference ← IO.lazyPure fun _ => Cfg.Rc.run P k root args
        check s!"{name}: exact bounded-clock differential {k}" (short == reference)
      report := report ++ [countsLine name n seed c]
      IO.println s!"PASS counters {name} {n} {seed}: alloc={c.allocations}, inc={c.incUnits}, dec={c.decCalls}, free={c.frees}, live={c.live}, peak={c.peakLive}"
  IO.FS.writeFile (logs / "counters.tsv") (String.intercalate "\n" report ++ "\n")

end IxCCTests.Pipeline.Rc.Counters
