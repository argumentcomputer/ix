import Compilatrix.Cfg.Semantics

/-! # Dynamic counters over `Cfg.step` (MT.7)

A test-side stepper (`plans/fixtures/ownership-suite.md` §5.3): it runs the
production small-step function `Cfg.step` unchanged, exactly as
`Sem.runClocked` does (same fuel, same clock, same charges), and before each
step tallies what the current state is about to do: a function entry, a
non-tail call, a tail call, a back edge, an instruction by kind, a `switch`,
a return. After each step it records the heap's size, so allocations and the
peak number of live cells come from the heap itself (cells only append;
`Own/Heap.lean`). No trusted code changes, and its final result must equal
`Cfg.run`'s (`sameAsRun`, a differential assertion).

**Phase 1.** Cfg has no reference-counting forms (`Own/Syntax.lean`), so
`inc`, `dec`, `isShared`, `takeUnique` and reuse hits and misses are always
0 here: the fields exist so that Phase 2's effect assertions
(ownership-suite §5.6) are written against this record now and hold
vacuously until the syntax gains those forms. Under the immortal policy
nothing is freed, so the live cells at the end are all the cells. -/

namespace CompilatrixTests.Own.Counters

open Compilatrix Compilatrix.Cfg
open Compilatrix.Own (RVal Heap AllocPol Cell)

structure Counts where
  /-- Small steps taken. -/
  steps : Nat := 0
  /-- Clock charges: function entries and back edges. -/
  charges : Nat := 0
  entries : Nat := 0
  calls : Nat := 0
  tailCalls : Nat := 0
  backEdges : Nat := 0
  jumps : Nat := 0
  switches : Nat := 0
  returns : Nat := 0
  /-- Instructions executed, and by kind. -/
  instrs : Nat := 0
  prims : Nat := 0
  allocInstrs : Nat := 0
  projs : Nat := 0
  /-- Heap cells allocated (an `alloc` of a field-less constructor is an
  immediate and allocates none). -/
  cells : Nat := 0
  /-- Fields of the allocated cells. -/
  fields : Nat := 0
  /-- Live cells at the end, and their largest number at any step. -/
  live : Nat := 0
  peakLive : Nat := 0
  /-- Phase 2 reference-counting events; always 0 in Phase 1. -/
  inc : Nat := 0
  dec : Nat := 0
  isShared : Nat := 0
  takeUnique : Nat := 0
  reuseHit : Nat := 0
  reuseMiss : Nat := 0
  deriving BEq, Repr, Inhabited

def Counts.render (c : Counts) : String :=
  s!"steps {c.steps}, charges {c.charges}, calls {c.calls}, tail calls {c.tailCalls}, " ++
  s!"back edges {c.backEdges}, instructions {c.instrs} (alloc {c.allocInstrs}, prim {c.prims}, " ++
  s!"proj {c.projs}), cells {c.cells} ({c.fields} fields), peak live {c.peakLive}, " ++
  s!"inc {c.inc}, dec {c.dec}, isShared {c.isShared}, takeUnique {c.takeUnique}, " ++
  s!"reuse {c.reuseHit}/{c.reuseMiss}"

def liveCells (H : Heap) : Nat :=
  H.cells.foldl (fun n c => match c with | .live .. => n + 1 | .dead => n) 0

def fieldCount (H : Heap) (from_ : Nat) : Nat :=
  (H.cells.toList.drop from_).foldl (fun n c => match c with
    | .live _ _ b => n + b.fields.length
    | .dead => n) 0

def heapOf : State → Heap
  | .call _ _ _ H | .run _ _ H | .ret _ _ H => H

/-- What the state is about to do. -/
def tally (P : Program) (s : State) (c : Counts) : Counts :=
  match s with
  | .call .. => { c with entries := c.entries + 1 }
  | .ret .. => c
  | .run fr _ _ =>
    match fr.rest with
    | .bind _ (.fir (.call ..)) :: _ => { c with instrs := c.instrs + 1, calls := c.calls + 1 }
    | .bind _ (.fir (.prim ..)) :: _ => { c with instrs := c.instrs + 1, prims := c.prims + 1 }
    | .bind _ (.alloc ..) :: _ => { c with instrs := c.instrs + 1, allocInstrs := c.allocInstrs + 1 }
    | .bind _ (.proj ..) :: _ => { c with instrs := c.instrs + 1, projs := c.projs + 1 }
    | .bind .. :: _ => { c with instrs := c.instrs + 1 }
    | [] =>
      match (P.fun? fr.fn).bind (·.block? fr.blk) with
      | some b =>
        match b.term with
        | .jump e => if e.back then { c with backEdges := c.backEdges + 1 } else { c with jumps := c.jumps + 1 }
        | .switch .. => { c with switches := c.switches + 1 }
        | .ret _ => { c with returns := c.returns + 1 }
        | .tcall .. => { c with tailCalls := c.tailCalls + 1 }
        | .trap => c
      | none => c

/-- `Sem.runClocked (Cfg.step pol P) fuel k s`, counting. -/
def loop (pol : AllocPol) (P : Program) : (fuel k : Nat) → State → Counts →
    Sem.Result (RVal × Heap) × Counts
  | 0, _, _, c => (.timeout, c)
  | fuel + 1, k, s, c =>
    let c := tally P s c
    let before := (heapOf s).size
    let note := fun (s' : State) (c : Counts) =>
      let H := heapOf s'
      let grown := H.size - before
      let live := liveCells H
      { c with steps := c.steps + 1, cells := c.cells + grown, fields := c.fields + fieldCount H before
               live, peakLive := max c.peakLive live }
    match step pol P s with
    | .next s' false => loop pol P fuel k s' (note s' c)
    | .next s' true =>
      match k with
      | 0 => (.timeout, { c with steps := c.steps + 1 })
      | k + 1 => loop pol P fuel k s' { note s' c with charges := c.charges + 1 }
    | .done v => (.ok v, { c with steps := c.steps + 1 })
    | .fail r => (.resource r, { c with steps := c.steps + 1 })
    | .trap => (.trap, { c with steps := c.steps + 1 })
    | .stuck => (.stuck, { c with steps := c.steps + 1 })

/-- Run `f` on `args` as `Cfg.run` does, with the counts. -/
def run (pol : AllocPol) (P : Program) (k : Nat) (f : Fir.FunId) (args : List RVal) :
    Sem.Result (RVal × Heap) × Counts :=
  loop pol P (fuelFor P k) k (.call f args [] {}) {}

def resultKey : Sem.Result (RVal × Heap) → String
  | .ok (v, H) => s!"ok {v.shape} {reprStr (H.readback v)} cells {H.size}"
  | .timeout => "timeout"
  | .stuck => "stuck"
  | .trap => "trap"
  | .resource r => s!"resource {reprStr r}"

/-- The stepper's result is `Cfg.run`'s: the same outcome, value and heap. -/
def sameAsRun (pol : AllocPol) (P : Program) (k : Nat) (f : Fir.FunId) (args : List RVal) :
    Bool × Counts :=
  let (r, c) := run pol P k f args
  let same := match r, Cfg.run pol P k f args with
    | .ok (v, H), .ok (v', H') => v == v' && H == H'
    | r, r' => resultKey r == resultKey r'
  (same, c)

/-- Static `alloc` instructions in a Cfg program. -/
def staticAllocs (P : Program) : Nat :=
  P.funList.foldl (fun n (_, fd) => fd.blocks.foldl (fun n b => n + (b.body.filter fun
    | .bind _ (.alloc ..) => true
    | _ => false).length) n) 0

end CompilatrixTests.Own.Counters
