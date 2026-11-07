import IxCCTests.Xv.Alloc.Diff
import IxCCTests.Support.Repro

/-! # Ladders for the Lir generator and the allocation mutants (MT.5)

The first-diverging-level ladders (`IxCCTests.Support.Repro`) of the
generated Lir programs (`Lir.Gen.programWith`, regalloc2-style SSA) and of
the allocation-validator mutation campaign (`Xv.Alloc.Mutate`):

* **Lir generator**: two sequences, the program's and its arguments'
  (`Gen.mainArgsWith`); the memory image is the seed's
  (`Region.initial seed`, kept, not shrunk). The reference is `Lir.eval` of
  the raw program; then the program with its critical edges split
  (`lir.split`), selected (`xv`, `Select.run`) and allocated by linear scan
  (`xl`, `Alloc.run`, validated). Every level runs at clock 200 and is
  compared on values, heap and context words (`Xv.Support.digest`), as
  `check-regalloc`'s differential does.
* **Allocation mutants**: a third sequence draws a `swap` mutant of the
  deterministic allocation (two operand locations of one instruction
  exchanged) in one function; the mutant must be rejected by the validator,
  and a mutant it accepts is run (`xl.mutant`) and must agree.

Planted bugs, applied only by `check true`: the generator's swaps the
operands of every 64-bit `sub` after splitting critical edges (a broken
`splitCriticalEdges`, level `lir.split`); the mutants' is a validator that
accepts every `swap` mutant (level `xl.mutant`). -/

namespace IxCCTests.Xv.Alloc.Shrink

open IxCC IxCC.Lir IxCC.Xv IxCCTests.Lir IxCCTests.Xv
open IxCCTests.Support (Rng RngM)
open IxCCTests.Support.Repro (Obs Failure Ladder firstDivergence)

def clock : Nat := 200

/-- A broken `splitCriticalEdges`: every `sub`'s operands swapped. -/
def plantLir (p : Lir.Program) : Lir.Program :=
  { p with funcs := p.funcs.map fun f => { f with blocks := f.blocks.map fun b =>
      { b with body := b.body.map fun
        | .assign x (.bin .sub w a c) => .assign x (.bin .sub w c a)
        | s => s } } }

/-- A level's observation: the values, and a hash of the heap and context
words (the full digest is compared through its hash; a difference in memory
alone shows as a different hash). -/
def obsOf (o : Lir.Outcome) : String :=
  match digest o with
  | .ok vals heap ctx => s!"ok {vals.map (·.toNat)} heap#{hash heap} ctx#{hash ctx}"
  | d => d.text

def config : Gen.Config := {}

/-- The program and arguments of the first two sequences, with their
normalised logs. -/
def generate (seqs : Support.Shrink.Seqs) : Lir.Program × List Word × Support.Shrink.Seqs :=
  let ((raw, _), g) := Gen.programWith config (Rng.replaying (seqs[0]?.getD #[]))
  let (args, ga) := Gen.mainArgsWith raw (Rng.replaying (seqs[1]?.getD #[]))
  (raw, args, #[g.log, ga.log])

def record (seed : Nat) : Support.Shrink.Seqs :=
  let s := UInt64.ofNat seed
  let ((raw, _), g) := Gen.programWith config (Rng.recording s)
  let (_, ga) := Gen.mainArgsWith raw (Rng.recording (Rng.derive s 1))
  #[g.log, ga.log]

def failure (args : List Word) (obs : List Obs) : Option Failure :=
  (firstDivergence obs).map fun (level, expected, got) =>
    { input := args.map (·.toNat), level, expected, got }

/-! ## The Lir generator -/

def lirCheck (planted : Bool) (aux : List Nat) (seqs : Support.Shrink.Seqs) : IO Support.Repro.Outcome := do
  let (raw, args, seqs) := generate seqs
  let text := raw.text
  let base : Support.Repro.Outcome := { seqs, size := text.length, text }
  let split := raw.splitCriticalEdges
  if split.check.isOk == false then return base
  let split := if planted then plantLir split else split
  let mem := Region.initial (UInt64.ofNat (aux.headD 0))
  let mut obs : List Obs :=
    [{ level := "lir", obs := obsOf (Lir.eval raw clock args mem Region.ctx) },
     { level := "lir.split", obs := obsOf (Lir.eval split clock args mem Region.ctx) }]
  if let .ok (q, _) := Select.run split then
    obs := obs ++ [{ level := "xv", obs := obsOf (Xv.eval q clock args mem Region.ctx) }]
    if let .ok res := IxCC.Xv.Alloc.run {} q then
      obs := obs ++ [{ level := "xl", obs := obsOf (Xl.eval res.program {} clock args mem Region.ctx) }]
  return { base with failure := failure args obs }

def lirGen : Ladder where
  generator := "lirgen"
  planted := "every sub's operands swapped after splitting critical edges (a broken splitCriticalEdges)"
  plantedLevel := "lir.split"
  aux := fun seed => [seed]
  record := record
  check := lirCheck
  ofSeed := fun seed => (Gen.program config (UInt64.ofNat seed)).1.text

/-! ## Allocation mutants -/

/-- Draw a `swap` mutant: a function, then a swap in its allocation. -/
def drawMutant (q : VProgram) (res : IxCC.Xv.Alloc.Result) : Mutate.G (Option (Nat × IxCC.Xv.Alloc.Output)) := do
  let fi ← Mutate.rand (RngM.below res.outs.length)
  let some f := q.funcs[fi]? | return none
  let some o := res.outs[fi]? | return none
  return (← Mutate.mutate "swap" {} f o).map (fi, ·)

/-- The selected program and its deterministic allocation. -/
def allocate (raw : Lir.Program) : Option (VProgram × IxCC.Xv.Alloc.Result) := do
  let split := raw.splitCriticalEdges
  if split.check.isOk == false then none
  let (q, _) ← (Select.run split).toOption
  let res ← (IxCC.Xv.Alloc.run {} q).toOption
  return (q, res)

def mutantCheck (planted : Bool) (aux : List Nat) (seqs : Support.Shrink.Seqs) : IO Support.Repro.Outcome := do
  let (raw, args, seqs2) := generate seqs
  let text := raw.text
  let base : Support.Repro.Outcome := { seqs := seqs2.push (seqs[2]?.getD #[]), size := text.length, text }
  let some (q, res) := allocate raw | return base
  let (m, g) := (drawMutant q res).run (Rng.replaying (seqs[2]?.getD #[]))
  let base := { base with seqs := seqs2.push g.log }
  let some (fi, o') := m | return base
  let outs' := Mutate.setAt res.outs fi fun _ => o'
  -- the validator; the planted bug accepts every swap mutant
  let accepted := planted || (Validate.program {} q outs').isOk
  if !accepted then return base
  let .ok g' := IxCC.Xv.Alloc.applyProgram q outs' | return base
  let mem := Region.initial (UInt64.ofNat (aux.headD 0))
  let obs : List Obs :=
    [{ level := "lir", obs := obsOf (Lir.eval raw clock args mem Region.ctx) },
     { level := "xv", obs := obsOf (Xv.eval q clock args mem Region.ctx) },
     { level := "xl", obs := obsOf (Xl.eval res.program {} clock args mem Region.ctx) },
     { level := "xl.mutant", obs := obsOf (Xl.eval g' {} clock args mem Region.ctx) }]
  return { base with failure := failure args obs, text := s!"{text}\n--- swap mutant of function {fi} ---" }

def mutants : Ladder where
  generator := "regalloc-mutants"
  planted := "a validator that accepts every swap mutant"
  plantedLevel := "xl.mutant"
  aux := fun seed => [seed]
  record := fun seed =>
    let seqs := record seed
    let (raw, _, _) := generate seqs
    match allocate raw with
    | some (q, res) => seqs.push ((drawMutant q res).run (Rng.recording (UInt64.ofNat seed ^^^ 0x6d757461))).2.log
    | none => seqs.push #[]
  check := mutantCheck
  ofSeed := fun seed => (Gen.program config (UInt64.ofNat seed)).1.text

end IxCCTests.Xv.Alloc.Shrink
