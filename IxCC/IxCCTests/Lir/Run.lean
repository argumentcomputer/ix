import IxCCTests.Lir.Props
import IxCCTests.Lir.Cases

/-!
# `check-lir`

Runs the kernels, then the generator over `programs × seeds` programs with
every property of `Props`, and prints counts. A failure prints the seed, the
property and the generated program, and fails the run.

Usage: `check-lir [--programs N] [--seeds S1,S2,…] [--max-blocks B] [--profile]`.
-/

namespace IxCCTests.Lir

open IxCC IxCC.Lir

structure Options where
  programs : Nat := 2000
  seeds : List UInt64 := [0x5eed0001, 0x5eed0002, 0x5eed0003, 0x5eed0004]
  maxBlocks : Nat := 200
  /-- Print the slowest programs of each seed. -/
  profile : Bool := false

def parseOptions : List String → Except String Options
  | [] => pure {}
  | "--profile" :: rest => do return { (← parseOptions rest) with profile := true }
  | "--programs" :: n :: rest => do
      let o ← parseOptions rest
      match n.toNat? with
      | some n => pure { o with programs := n }
      | none => throw s!"bad --programs {n}"
  | "--seeds" :: s :: rest => do
      let o ← parseOptions rest
      let seeds ← (s.splitOn ",").mapM fun t =>
        match t.toNat? with
        | some n => pure (UInt64.ofNat n)
        | none => throw s!"bad seed {t}"
      pure { o with seeds }
  | "--max-blocks" :: n :: rest => do
      let o ← parseOptions rest
      match n.toNat? with
      | some n => pure { o with maxBlocks := n }
      | none => throw s!"bad --max-blocks {n}"
  | arg :: _ => throw s!"unknown argument {arg}"

private def percent (part whole : Nat) : String :=
  if whole == 0 then "0%" else s!"{(100 * part + whole / 2) / whole}%"

def runKernels : IO Bool := do
  let mut checks := 0
  for c in Kernels.cases do
    match Props.checkKernel c with
    | .ok n => checks := checks + n
    | .error e =>
        IO.eprintln s!"check-lir: kernel failed: {e}"
        return false
  IO.println s!"kernels: {Kernels.cases.length} cases, {checks} outcome checks (fib, sumLoop, sumFrom, gcd, natAdd, natSub, natDiv, natMod)"
  return true

def runGenerated (o : Options) : IO Bool := do
  let cfg : Gen.Config := { maxBlocks := o.maxBlocks }
  let mut total : Props.Report := {}
  for seed in o.seeds do
    let start ← IO.monoMsNow
    let mut report : Props.Report := {}
    let mut slowest : Array (Nat × UInt64 × Nat × Nat) := #[]
    for n in [:o.programs] do
      let programSeed := Support.Rng.derive seed n
      let before ← IO.monoNanosNow
      match Props.checkProgram cfg programSeed with
      | .ok r =>
          report := report.add r
          if o.profile then
            let us := ((← IO.monoNanosNow) - before) / 1000
            slowest := (slowest.push (us, programSeed, r.stats.blocks, r.steps)).qsort (·.1 > ·.1) |>.take 5
      | .error e =>
          IO.eprintln s!"check-lir: generated program {n} of seed {seed} (program seed {programSeed}) failed: {e}"
          IO.eprintln (Props.programText cfg programSeed)
          return false
    let elapsed := (← IO.monoMsNow) - start
    IO.println s!"seed {seed}: {report.cases} programs, {report.stats.blocks} blocks, {report.critical} critical edges split, {report.evals} evaluations, {elapsed} ms"
    for (us, s, blocks, steps) in slowest do
      IO.println s!"  slow: program seed {s}: {us} µs, {blocks} blocks, {steps} steps"
    total := total.add report
  let s := total.stats
  IO.println s!"generated: {total.cases} programs ({s.funcs} functions, {s.recursive} recursive, {s.relabelled} relabelled, {s.wild} wild)"
  IO.println s!"  blocks: {s.blocks} total, {s.minBlocks}–{s.maxBlocks} per program; sizes 1: {s.sizes[0]!}, 2–16: {s.sizes[1]!}, 17–64: {s.sizes[2]!}, 65+: {s.sizes[3]!}"
  IO.println s!"  statements {s.stmts}, block parameters {s.params}, loops {s.loops}, calls {s.calls}, tail calls {s.tails}, brOvf {s.brOvfs}, exits {s.exits}"
  IO.println s!"  loads {s.loads}, stores {s.stores}, divisions {s.divs}, shifts {s.shifts}"
  IO.println s!"  critical edges split: {total.critical} in {total.splitPrograms} programs; {total.mutants} WellFormed mutants rejected for their planted reason"
  let outcomes := (Props.labels.zip total.outcomes).toList.map fun (l, n) => s!"{l} {n} ({percent n total.cases})"
  IO.println s!"  outcomes at clock {Props.bigClock}: {", ".intercalate outcomes}"
  IO.println s!"  clocks: {total.charged} programs spend charges, {total.exact} checked at their exact clock c and c − 1, {total.timeoutsSmall} time out at {Props.midClock}; max charges {total.maxCharges}"
  IO.println s!"  steps {total.steps} (max {total.maxSteps}), evaluations {total.evals}"
  return true

def run (args : List String) : IO Bool := do
  match parseOptions args with
  | .error e =>
      IO.eprintln s!"check-lir: {e}"
      return false
  | .ok o =>
      let start ← IO.monoMsNow
      unless ← runKernels do return false
      unless ← runGenerated o do return false
      IO.println s!"check-lir: ok ({(← IO.monoMsNow) - start} ms)"
      return true

end IxCCTests.Lir
