import IxCCTests.Xv.Alloc.Diff
import IxCCTests.Xv.Alloc.Kernels
import IxCCTests.Xv.Alloc.Cases

/-!
# `check-regalloc`

Generated testing of allocation: the Lir kernels through linear scan
and all slots at their exact clocks, with their spill, reload and move
counts; then generated programs (`programs × seeds`, the full Lir
generator through selection), each allocated deterministically and under
`--chaos K` chaos seeds, and by all slots, with every allocation validated,
run differentially against Xv, and the deterministic one mutated. Prints
counts, the mutation table and any rejection; fails on a differential
mismatch, an unsound validator acceptance, a failed fallback, or (with
`--strict`, the default) any rejection or decline of linear scan.

Usage: `check-regalloc [--programs N] [--seeds S1,S2,…] [--chaos K] [--max-blocks B] [--no-mutate] [--lenient]`. -/

namespace IxCCTests.Xv.Alloc

open IxCC IxCC.Lir IxCCTests.Lir IxCCTests.Support

structure Options where
  programs : Nat := 500
  seeds : List UInt64 := [0xa11c0001, 0xa11c0002, 0xa11c0003, 0xa11c0004]
  chaos : Nat := 4
  maxBlocks : Nat := 200
  mutate : Bool := true
  strict : Bool := true
  verbose : Bool := false

def parseNat (flag n : String) : Except String Nat :=
  match n.toNat? with
  | some n => pure n
  | none => throw s!"bad {flag} {n}"

def parseOptions : List String → Except String Options
  | [] => pure {}
  | "--programs" :: n :: rest => do return { (← parseOptions rest) with programs := ← parseNat "--programs" n }
  | "--chaos" :: n :: rest => do return { (← parseOptions rest) with chaos := ← parseNat "--chaos" n }
  | "--max-blocks" :: n :: rest => do
      return { (← parseOptions rest) with maxBlocks := ← parseNat "--max-blocks" n }
  | "--no-mutate" :: rest => do return { (← parseOptions rest) with mutate := false }
  | "--lenient" :: rest => do return { (← parseOptions rest) with strict := false }
  | "--verbose" :: rest => do return { (← parseOptions rest) with verbose := true }
  | "--seeds" :: s :: rest => do
      let o ← parseOptions rest
      let seeds ← (s.splitOn ",").mapM fun t => UInt64.ofNat <$> parseNat "seed" t
      pure { o with seeds }
  | arg :: _ => throw s!"unknown argument {arg}"

def countsText (c : IxCC.Xv.Alloc.EditCounts) : String := s!"{c.spills} spills, {c.reloads} reloads, {c.moves} moves"

def runKernels (verbose : Bool) : IO Bool := do
  match Kernels.check with
  | .error e =>
      IO.eprintln s!"check-regalloc: kernel failed: {e}"
      return false
  | .ok (rows, checks) =>
      IO.println s!"kernels: {rows.length} allocated both ways, {checks} outcome checks at exact clocks"
      IO.println "  kernel: Xv instructions; linear scan: spills, reloads, moves, slots; all slots: the same"
      for r in rows do
        IO.println s!"  {r.kernel}: {r.insts}; {r.scan.spills}, {r.scan.reloads}, {r.scan.moves}, {r.scanSlots}; {r.allSlots.spills}, {r.allSlots.reloads}, {r.allSlots.moves}, {r.allSlotsSlots}"
      if verbose then
        for r in rows do IO.println s!"--- {r.kernel} (linear scan) ---\n{r.xl}"
      return true

def runGenerated (o : Options) : IO (Option Diff.Report) := do
  let cfg : Gen.Config := { maxBlocks := o.maxBlocks }
  let opts : Diff.Options := { chaosSeeds := o.chaos, mutate := o.mutate }
  let mut total : Diff.Report := {}
  for seed in o.seeds do
    let start ← IO.monoMsNow
    let mut report : Diff.Report := {}
    for n in [:o.programs] do
      let programSeed := Rng.derive seed n
      match Diff.checkProgram cfg programSeed opts with
      | .ok r => report := report.add r
      | .error e =>
          IO.eprintln s!"check-regalloc: program {n} of seed {seed} (program seed {programSeed}) failed: {e}"
          IO.eprintln (Diff.programText cfg programSeed)
          return none
    IO.println s!"seed {seed}: {report.programs} programs, {(← IO.monoMsNow) - start} ms"
    total := total.add report
  return some total

private def percent (part whole : Nat) : String :=
  if whole == 0 then "0%" else s!"{(100 * part + whole / 2) / whole}%"

def printReport (r : Diff.Report) : IO Unit := do
  IO.println s!"generated: {r.programs} programs, {r.functions} functions, {r.xvInsts} Xv instructions; {r.stuck} stuck at Xv (allocation and validation only)"
  IO.println s!"  linear scan: {r.accepted}/{r.scanned} functions accepted, {r.declined} declined, {r.rejected} rejected; {countsText r.counts}; {r.slots} slots"
  IO.println s!"  chaos: {r.chaosAccepted}/{r.chaosScanned} accepted, {r.chaosDeclined} declined, {r.chaosRejected} rejected; {countsText r.chaosCounts}"
  IO.println s!"  all slots: {r.allSlots} programs accepted; {countsText r.allSlotsCounts}; {r.allSlotsSlots} slots"
  IO.println s!"  differential: {r.differential} allocations agree with Xv; steps Xv {r.xvSteps}, Xl {r.xlSteps} (deterministic allocation)"
  let m := r.mutation
  IO.println "  mutation (planted / rejected / accepted as equivalent):"
  for c in Mutate.classes do
    IO.println s!"    {c}: {m.planted.getD c 0} / {m.rejected.getD c 0} / {m.equivalent.getD c 0}"
  let codes := (m.codes.toList.toArray.qsort (·.1 < ·.1)).toList
  IO.println s!"  rejection codes: {", ".intercalate (codes.map fun (k, n) => s!"{k} {n}")}"
  for note in r.notes do IO.println s!"  note: {note}"

def run (args : List String) : IO Bool := do
  match parseOptions args with
  | .error e =>
      IO.eprintln s!"check-regalloc: {e}"
      return false
  | .ok o =>
      let start ← IO.monoMsNow
      unless ← runKernels o.verbose do return false
      let some r ← runGenerated o | return false
      printReport r
      if o.strict && r.rejected + r.chaosRejected + r.declined + r.chaosDeclined > 0 then
        IO.eprintln s!"check-regalloc: linear scan was rejected or declined ({r.rejected + r.chaosRejected} rejected, {r.declined + r.chaosDeclined} declined)"
        return false
      let unrejected := Mutate.classes.foldl (fun n c =>
        n + (r.mutation.planted.getD c 0 - r.mutation.rejected.getD c 0 - r.mutation.equivalent.getD c 0)) 0
      if unrejected > 0 then
        IO.eprintln s!"check-regalloc: {unrejected} mutants neither rejected nor equivalent"
        return false
      IO.println s!"check-regalloc: ok ({(← IO.monoMsNow) - start} ms)"
      return true

end IxCCTests.Xv.Alloc
