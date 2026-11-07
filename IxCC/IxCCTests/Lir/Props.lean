import IxCC.Lir.WellFormed
import IxCC.Lir.SplitEdges
import IxCC.Lir.Semantics
import IxCC.Lir.Print
import IxCCTests.Lir.Gen
import IxCCTests.Lir.Kernels

/-!
# Executable properties of Lir

Checks run by `check-lir` on each generated program and each kernel:

1. **Generation.** The generator is deterministic; splitting adds exactly
   one block per critical edge, is the identity when there are none, and
   yields a `WellFormed` program; `WellFormed` rejects the raw program iff
   it has critical edges (and names one).
2. **Splitting preserves outcomes**: the raw and split programs agree
   (values, heap and context words, or the failure) at every tested clock.
3. **Clock monotonicity**: across increasing clocks, once an outcome is not
   `timeout` it never changes.
4. **Clock exactness**: a finished run that spent `c` charges gives the same
   outcome at clock `c` and `timeout` at `c − 1`.
5. **Fuel bound**: a run of `s` steps with `c` charges has
   `s ≤ (2c + 2)·(size + 1)`, so `eval`'s fuel never runs out first.
6. **Determinism**: evaluating a separately generated copy agrees.
-/

namespace IxCCTests.Lir.Props

open IxCC IxCC.Lir

/-- A comparable summary of an outcome. -/
inductive Digest where
  | ok (vals heap ctx : List Word)
  | timeout
  | resource (r : Sem.Resource)
  | trap
  | stuck
  deriving BEq, Repr, Inhabited

def digest : Outcome → Digest
  | .ok (vals, mem) => .ok vals (Region.heapWords mem) (Region.ctxWords mem)
  | .timeout => .timeout
  | .resource r => .resource r
  | .trap => .trap
  | .stuck => .stuck

/-- The outcome without the final memory, which is costly to read back
(`X86.Memory` is a chain of closures, one per byte written). -/
def light : Outcome → Digest
  | .ok (vals, _) => .ok vals [] []
  | o => digest o

def Digest.light : Digest → Digest
  | .ok vals _ _ => .ok vals [] []
  | d => d

/-- Outcome classes, for statistics. -/
def labels : Array String := #["ok", "timeout", "heap", "stack", "natOverflow", "trap", "stuck"]

def Digest.index : Digest → Nat
  | .ok .. => 0
  | .timeout => 1
  | .resource .heap => 2
  | .resource .stack => 3
  | .resource .natOverflow => 4
  | .trap => 5
  | .stuck => 6

def Digest.label (d : Digest) : String := labels[d.index]!

def Digest.text : Digest → String
  | .ok vals _ _ => s!"ok {vals.map (·.toNat)}"
  | d => d.label

/-- Run by hand with `step`: the outcome, the steps taken and the charges
spent, with at most `fuel` steps. -/
def countRun (p : Program) (fuel k : Nat) (s : State) : Outcome × Nat × Nat := Id.run do
  let mut s := s
  let mut k := k
  let mut steps := 0
  let mut charges := 0
  for _ in [:fuel] do
    steps := steps + 1
    match step p s with
    | .next s' charge =>
        if charge then
          if k == 0 then return (.timeout, steps, charges)
          k := k - 1
          charges := charges + 1
        s := s'
    | .done vals mem => return (.ok (vals, mem), steps, charges)
    | .fail r => return (.resource r, steps, charges)
    | .trap => return (.trap, steps, charges)
    | .stuck => return (.stuck, steps, charges)
  return (.timeout, steps, charges)

structure Report where
  stats : Gen.Stats := {}
  cases : Nat := 0
  critical : Nat := 0
  splitPrograms : Nat := 0
  outcomes : Array Nat := Array.replicate 7 0
  timeoutsSmall : Nat := 0
  evals : Nat := 0
  steps : Nat := 0
  maxSteps : Nat := 0
  maxCharges : Nat := 0
  /-- Programs whose run spent at least one charge. -/
  charged : Nat := 0
  /-- Programs finishing at an exact clock `c > 0` (so `c − 1` was checked). -/
  exact : Nat := 0
  /-- Mutants `WellFormed` rejected for the planted reason. -/
  mutants : Nat := 0
  deriving Inhabited

def Report.add (a b : Report) : Report :=
  { stats := a.stats.add b.stats, cases := a.cases + b.cases, critical := a.critical + b.critical
    splitPrograms := a.splitPrograms + b.splitPrograms
    outcomes := (a.outcomes.zip b.outcomes).map fun (x, y) => x + y
    timeoutsSmall := a.timeoutsSmall + b.timeoutsSmall, evals := a.evals + b.evals
    steps := a.steps + b.steps, maxSteps := max a.maxSteps b.maxSteps
    maxCharges := max a.maxCharges b.maxCharges, charged := a.charged + b.charged
    exact := a.exact + b.exact, mutants := a.mutants + b.mutants }

private def contains (text part : String) : Bool := (text.splitOn part).length > 1

/-! ## Checker mutations -/

private def modifyBlock (p : Program) (fi : FunId) (b : Label) (g : Block → Block) : Program :=
  { p with funcs := p.funcs.modify fi fun f => { f with blocks := f.blocks.modify b g } }

private def mapAddr (g : Addr → Addr) : Stmt → Stmt
  | .assign x (.load w e m) => .assign x (.load w e (g m))
  | .assign x (.addr m) => .assign x (.addr (g m))
  | .store w m a => .store w (g m) a
  | s => s

/-- One violation of `WellFormed`, chosen by `choice`, with the text the
rejection must contain; `none` if the program has no site for it. -/
def mutate (p : Program) (choice : Nat) : Option (Program × String) := do
  let fi := choice % p.funcs.size
  let f ← p.funcs[fi]?
  let last := f.blocks.size - 1
  match choice / p.funcs.size % 6 with
  | 5 =>
      -- A store to the context's `entrySp` cell.
      let body := (f.blocks[last]!.body).push (.store .w64 { base := some .ctx, disp := -64 } (.imm 0))
      some (modifyBlock p fi last ({ · with body }), "entrySp or stackLimit")
  | 0 =>
      -- A use of a register nobody defines.
      let x := 1000000
      let body := (f.blocks[last]!.body).push (.assign (x + 1) (.arg (.v x)))
      some (modifyBlock p fi last ({ · with body }), s!"v{x} is used but never defined")
  | 1 =>
      -- A second definition of the heap base, defined first in the entry.
      let .assign x _ ← f.blocks[0]!.body[0]? | none
      some (modifyBlock p fi last fun b => { b with body := b.body.push (.assign x (.arg (.imm 0))) },
        s!"v{x} is defined twice")
  | 2 =>
      -- An edge back to the entry block.
      let b ← (List.range f.blocks.size).find? fun b => !f.blocks[b]!.term.edges.isEmpty
      let t := f.blocks[b]!.term
      let edges := match t.edges with
        | e :: es => { e with target := 0, args := [] } :: es
        | [] => []
      some (modifyBlock p fi b ({ · with term := t.setEdges edges }), "edge to the entry block")
  | 3 =>
      -- One argument too many on an edge.
      let b ← (List.range f.blocks.size).find? fun b => !f.blocks[b]!.term.edges.isEmpty
      let t := f.blocks[b]!.term
      let edges := match t.edges with
        | e :: es => { e with args := e.args ++ [.imm 0] } :: es
        | [] => []
      some (modifyBlock p fi b ({ · with term := t.setEdges edges }), "arguments for")
  | _ =>
      -- A displacement that does not fit i32.
      let (b, i) ← (List.range f.blocks.size).findSome? fun b =>
        (List.range f.blocks[b]!.body.size).findSome? fun i =>
          if f.blocks[b]!.body[i]!.addrs.isEmpty then none else some (b, i)
      some (modifyBlock p fi b fun blk =>
          { blk with body := blk.body.modify i (mapAddr ({ · with disp := 2 ^ 31 })) },
        "does not fit i32")

/-- The clocks every program is run at, before the exact one. -/
def smallClock (seed : UInt64) : Nat := (seed % 4).toNat
def midClock : Nat := 24
def bigClock : Nat := 200

/-- All checks on the program generated from `seed`. -/
def checkProgram (cfg : Gen.Config) (seed : UInt64) : Except String Report := do
  let (raw, stats) := Gen.program cfg seed
  let (again, _) := Gen.program cfg seed
  unless raw == again do throw "the generator is not deterministic"
  let critical := raw.funcs.foldl (fun n f => n + f.criticalEdges.length) 0
  let split := raw.splitCriticalEdges
  let blocks (p : Program) := p.funcs.foldl (fun n f => n + f.blocks.size) 0
  unless blocks split == blocks raw + critical do
    throw s!"splitting {critical} critical edges added {blocks split - blocks raw} blocks"
  if let .error e := split.check then throw s!"the split program is not well formed: {e}"
  if critical == 0 then
    unless split == raw do throw "splitting changed a program without critical edges"
  else
    match raw.check with
    | .ok () => throw s!"WellFormed accepted {critical} critical edges"
    | .error e => unless contains e "critical edge" do throw s!"unexpected rejection: {e}"
  let mut mutants := 0
  for choice in [(seed % 1000).toNat, (seed / 1000 % 1000).toNat] do
    if let some (bad, reason) := mutate split choice then
      mutants := mutants + 1
      match bad.check with
      | .ok () => throw s!"WellFormed accepted a mutant that should fail with '{reason}'"
      | .error e => unless contains e reason do throw s!"a mutant was rejected for '{e}', expected '{reason}'"
  let args := Gen.mainArgs raw seed
  let mem := Region.initial seed
  -- Memory is compared at the largest clock; elsewhere values and outcomes.
  let run (p : Program) (k : Nat) := light (eval p k args mem Region.ctx)
  let rawBig := digest (eval raw bigClock args mem Region.ctx)
  let splitBig := digest (eval split bigClock args mem Region.ctx)
  unless rawBig == splitBig do
    throw s!"splitting changed the outcome or memory at clock {bigClock}: {rawBig.text}, then {splitBig.text}"
  let clocks := [smallClock seed, midClock]
  let rawD := clocks.map (run raw) ++ [rawBig.light]
  let splitD := clocks.map (run split) ++ [splitBig.light]
  for (k, a, b) in (clocks ++ [bigClock]).zip (rawD.zip splitD) do
    unless a == b do throw s!"splitting changed the outcome at clock {k}: {a.text}, then {b.text}"
  for (d, j) in rawD.zipIdx do
    if d != .timeout then
      for later in rawD.drop (j + 1) do
        unless later == d do throw s!"a larger clock changed {d.text} to {later.text}"
  let some s := State.initial split args mem Region.ctx | throw "no initial state"
  let (outcome, steps, charges) := countRun split (fuelFor split bigClock + 1) bigClock s
  let final := light outcome
  unless final == splitBig.light do
    throw s!"stepping by hand gives {final.text}, eval gives {splitBig.text}"
  unless steps ≤ (2 * charges + 2) * (split.size + 1) do
    throw s!"{steps} steps with {charges} charges exceed the fuel bound for size {split.size}"
  let some s := State.initial raw args mem Region.ctx | throw "no initial state"
  let (_, rawSteps, rawCharges) := countRun raw (fuelFor raw bigClock + 1) bigClock s
  unless rawCharges == charges do
    throw s!"splitting changed the charges spent from {rawCharges} to {charges}"
  unless rawSteps ≤ (2 * rawCharges + 2) * (raw.size + 1) do
    throw s!"{rawSteps} steps with {rawCharges} charges exceed the fuel bound for size {raw.size}"
  let mut evals := 2 * clocks.length + 3
  if final != .timeout then
    unless run raw charges == final do throw s!"clock {charges} (the charges spent) does not finish"
    evals := evals + 1
    if charges > 0 then
      unless run raw (charges - 1) == .timeout do throw s!"clock {charges - 1} finishes early"
      evals := evals + 1
  unless run again midClock == rawD[1]! do
    throw "evaluation is not deterministic"
  return { stats, cases := 1, critical, splitPrograms := if critical > 0 then 1 else 0
           outcomes := (Array.replicate 7 0).modify final.index (· + 1)
           timeoutsSmall := if rawD[1]! == .timeout then 1 else 0
           evals := evals + 1, steps, maxSteps := steps, maxCharges := charges
           charged := if charges > 0 then 1 else 0
           exact := if charges > 0 && final != .timeout then 1 else 0
           mutants }

/-- The program text for a failure report, truncated. -/
def programText (cfg : Gen.Config) (seed : UInt64) (limit : Nat := 12000) : String :=
  let text := (Gen.program cfg seed).1.text
  if text.length ≤ limit then text else (text.take limit).toString ++ "\n…"

/-! ## Kernels -/

def expected : Kernels.Expect → Digest
  | .nat n => .ok [Kernels.tag n] [] []
  | .natOverflow => .resource .natOverflow

/-- Only the values: kernels do not touch memory. -/
def kernelDigest : Outcome → Digest
  | .ok (vals, _) => .ok vals [] []
  | o => (digest o)

def checkKernel (c : Kernels.Case) : Except String Nat := do
  let p := Kernels.program c.func
  let name := s!"{c.kernel} {c.args}"
  if let .error e := p.check then throw s!"{name}: not well formed: {e}"
  unless p.splitCriticalEdges == p do throw s!"{name}: has critical edges"
  let args := c.args.map Kernels.tag
  let mem := Region.initial 0
  let run (k : Nat) := kernelDigest (eval p k args mem Region.ctx)
  let want := expected c.expect
  match c.charges with
  | some k =>
      unless run k == want do throw s!"{name}: expected {want.text} at clock {k}, got {(run k).text}"
      if k > 0 then
        unless run (k - 1) == .timeout do throw s!"{name}: clock {k - 1} should time out"
        return 2
      return 1
  | none =>
      let got := run 1000000
      unless got == want do throw s!"{name}: expected {want.text}, got {got.text}"
      return 1

end IxCCTests.Lir.Props
