import IxCCTests.Xv.Alloc.Mutate
import IxCCTests.Xv.Diff
import IxCCTests.Lir.Gen
import IxCC.Lir.SplitEdges
import IxCC.Lir.WellFormed

/-!
# Allocation of generated programs

For each generated Lir program (split, selected; 05 §12 items 2–4):

1. **Deterministic allocation**, then one allocation per chaos seed (a
   `Chaos.ofSeed` configuration, and on odd seeds a smaller clobber set for
   odd callees): linear scan, validation, and the all-slots fallback on a
   failure or rejection (`Alloc.run`). Rejections are allocator bugs and are
   reported with their seeds.
2. **All slots** for every function, which must validate.
3. **Differential**: every accepted allocation runs like the Xv program at
   the clocks 0–3, 24 and 200 (outcome, heap and context words), spends the
   same charges, and finishes at Xv's exact clock and times out one below.
4. **Mutation** of the deterministic allocation (`Mutate`).
-/

namespace IxCCTests.Xv.Alloc.Diff

open IxCC IxCC.Lir IxCC.Xv IxCCTests.Lir IxCCTests.Xv IxCCTests.Support
open IxCC.Xv.Alloc (EditCounts)

structure Report where
  programs : Nat := 0
  functions : Nat := 0
  /-- Programs `stuck` at Xv (allocation and validation checked only). -/
  stuck : Nat := 0
  /-- Linear-scan allocations of functions: accepted, declined (linear scan
  failed), rejected (the validator found a bug). -/
  scanned : Nat := 0
  accepted : Nat := 0
  declined : Nat := 0
  rejected : Nat := 0
  /-- Rejections and declines, first few with their seeds. -/
  notes : Array String := #[]
  chaosScanned : Nat := 0
  chaosAccepted : Nat := 0
  chaosDeclined : Nat := 0
  chaosRejected : Nat := 0
  allSlots : Nat := 0
  /-- Differential runs that passed. -/
  differential : Nat := 0
  counts : EditCounts := {}
  chaosCounts : EditCounts := {}
  allSlotsCounts : EditCounts := {}
  slots : Nat := 0
  allSlotsSlots : Nat := 0
  xvInsts : Nat := 0
  xvSteps : Nat := 0
  xlSteps : Nat := 0
  mutation : Mutate.Stats := {}
  deriving Inhabited

def Report.add (a b : Report) : Report :=
  { programs := a.programs + b.programs, functions := a.functions + b.functions, stuck := a.stuck + b.stuck
    scanned := a.scanned + b.scanned, accepted := a.accepted + b.accepted
    declined := a.declined + b.declined, rejected := a.rejected + b.rejected
    notes := if a.notes.size ≥ 20 then a.notes else a.notes ++ b.notes
    chaosScanned := a.chaosScanned + b.chaosScanned, chaosAccepted := a.chaosAccepted + b.chaosAccepted
    chaosDeclined := a.chaosDeclined + b.chaosDeclined, chaosRejected := a.chaosRejected + b.chaosRejected
    allSlots := a.allSlots + b.allSlots, differential := a.differential + b.differential
    counts := a.counts.add b.counts, chaosCounts := a.chaosCounts.add b.chaosCounts
    allSlotsCounts := a.allSlotsCounts.add b.allSlotsCounts
    slots := a.slots + b.slots, allSlotsSlots := a.allSlotsSlots + b.allSlotsSlots
    xvInsts := a.xvInsts + b.xvInsts, xvSteps := a.xvSteps + b.xvSteps, xlSteps := a.xlSteps + b.xlSteps
    mutation := a.mutation.add b.mutation }

structure Options where
  chaosSeeds : Nat := 4
  mutate : Bool := true

def outcomeCounts (os : List IxCC.Xv.Alloc.Outcome) : Nat × Nat × Nat :=
  os.foldl (fun (a, d, r) o => match o with
    | .scan => (a + 1, d, r)
    | .declined _ => (a, d + 1, r)
    | .rejected _ => (a, d, r + 1)) (0, 0, 0)

def notesOf (label : String) (os : List IxCC.Xv.Alloc.Outcome) : Array String :=
  (os.zipIdx.filterMap fun (o, fi) => match o with
    | .scan => none
    | .declined msg => some s!"{label} function {fi}: declined: {msg}"
    | .rejected e => some s!"{label} function {fi}: REJECTED: {e.text}").toArray

/-- All checks on one selected program. -/
def checkXv (q : VProgram) (args : List Word) (seed : UInt64) (opts : Options) : Except String Report := do
  let mem := Region.initial seed
  let stuck := digest (Xv.eval q 200 args mem Region.ctx) == .stuck
  let mut r : Report := { programs := 1, functions := q.funcs.size, stuck := if stuck then 1 else 0
                          xvInsts := IxCCTests.Xv.Diff.xvSize q }
  -- Deterministic allocation.
  let res ← match IxCC.Xv.Alloc.run {} q with
    | .ok res => pure res
    | .error e => throw s!"allocation failed: {e}"
  let (a, d, j) := outcomeCounts res.outcomes
  r := { r with scanned := q.funcs.size, accepted := a, declined := d, rejected := j
                notes := notesOf s!"seed {seed}" res.outcomes
                counts := countsOf res.outs, slots := res.outs.foldl (· + ·.numSlots) 0 }
  match differential q res.program {} args seed with
  | .ok (xs, ls) => r := { r with differential := r.differential + 1, xvSteps := xs, xlSteps := ls }
  | .error e => throw s!"deterministic allocation: {e}"
  -- Chaos.
  for k in [:opts.chaosSeeds] do
    let chaos := IxCC.Xv.Alloc.Chaos.ofSeed (Rng.derive seed (k + 1))
    let env := if k % 2 == 1 then smallClobbers else {}
    let res ← match IxCC.Xv.Alloc.run env q chaos with
      | .ok res => pure res
      | .error e => throw s!"chaos {k} allocation failed: {e}"
    let (a, d, j) := outcomeCounts res.outcomes
    r := { r with chaosScanned := r.chaosScanned + q.funcs.size, chaosAccepted := r.chaosAccepted + a
                  chaosDeclined := r.chaosDeclined + d, chaosRejected := r.chaosRejected + j
                  notes := r.notes ++ notesOf s!"seed {seed} chaos {k}" res.outcomes
                  chaosCounts := r.chaosCounts.add (countsOf res.outs) }
    match differential q res.program env args seed with
    | .ok _ => r := { r with differential := r.differential + 1 }
    | .error e => throw s!"chaos {k} ({repr chaos}): {e}"
  -- All slots.
  let all ← match IxCC.Xv.Alloc.runAllSlots {} q with
    | .ok res => pure res
    | .error e => throw s!"all slots: {e}"
  match differential q all.program {} args seed with
  | .ok _ => r := { r with differential := r.differential + 1 }
  | .error e => throw s!"all slots: {e}"
  r := { r with allSlots := 1, allSlotsCounts := countsOf all.outs
                allSlotsSlots := all.outs.foldl (· + ·.numSlots) 0 }
  -- Mutation of the deterministic allocation.
  if opts.mutate && !stuck then
    let stats ← Mutate.run q res.outs {} args seed
    r := { r with mutation := stats }
  return r

/-- The generated program for `seed`, split and selected. -/
def selectGenerated (cfg : Gen.Config) (seed : UInt64) : Except String (VProgram × List Word) := do
  let (raw, _) := Gen.program cfg seed
  let p := raw.splitCriticalEdges
  if let .error e := p.check then throw s!"the split Lir program is not well formed: {e}"
  match Select.run p with
  | .ok (q, _) => pure (q, Gen.mainArgs raw seed)
  | .error e => throw s!"selection declined: {e.text}"

def checkProgram (cfg : Gen.Config) (seed : UInt64) (opts : Options) : Except String Report := do
  let (q, args) ← selectGenerated cfg seed
  checkXv q args seed opts

/-- A failure report: the Xv program and its deterministic allocation. -/
def programText (cfg : Gen.Config) (seed : UInt64) (limit : Nat := 16000) : String :=
  match selectGenerated cfg seed with
  | .error e => e
  | .ok (q, _) =>
      let xl := match IxCC.Xv.Alloc.LinearScan.run {} q.funcs[0]! with
        | .ok o => match IxCC.Xv.Alloc.applyProgram { q with funcs := #[q.funcs[0]!] } [o] with
            | .ok g => g.text
            | .error e => e
        | .error e => e
      let text := s!"{q.text}\n--- Xl (function 0, linear scan) ---\n{xl}"
      if text.length ≤ limit then text else (text.take limit).toString ++ "\n…"

end IxCCTests.Xv.Alloc.Diff
