import IxCCTests.Xv.Diff
import IxCCTests.Xv.Cases
import IxCCTests.Xv.XlCases
import IxCCTests.Xv.KernelEval

/-!
# `check-xv-select`

Runs the edge-value sweeps, the kernels through selection, then the Lir
generator over `programs × seeds` programs with every property of `Diff`.
Every generated program must select: a declined form fails the run.
Prints counts, and each rule's firings and the programs it fired on. A
failure prints the seed, the property and both programs, and fails the
run. `--restricted` narrows the generator to the forms selection had before
M1.B1 (constant left shifts; no division, `select` or `test`).

Usage: `check-xv-select [--programs N] [--seeds S1,S2,…] [--max-blocks B] [--restricted]`.
-/

namespace IxCCTests.Xv

open IxCC IxCC.Lir IxCCTests.Lir

structure Options where
  programs : Nat := 2000
  /-- Narrow the generator to the pre-B1 forms. -/
  restricted : Bool := false
  seeds : List UInt64 := [0x5eed0001, 0x5eed0002, 0x5eed0003, 0x5eed0004]
  maxBlocks : Nat := 200

def parseNat (flag n : String) : Except String Nat :=
  match n.toNat? with
  | some n => pure n
  | none => throw s!"bad {flag} {n}"

def parseOptions : List String → Except String Options
  | [] => pure {}
  | "--programs" :: n :: rest => do return { (← parseOptions rest) with programs := ← parseNat "--programs" n }
  | "--restricted" :: rest => do return { (← parseOptions rest) with restricted := true }
  | "--max-blocks" :: n :: rest => do
      return { (← parseOptions rest) with maxBlocks := ← parseNat "--max-blocks" n }
  | "--seeds" :: s :: rest => do
      let o ← parseOptions rest
      let seeds ← (s.splitOn ",").mapM fun t => UInt64.ofNat <$> parseNat "seed" t
      pure { o with seeds }
  | arg :: _ => throw s!"unknown argument {arg}"

/-- The generator narrowed to the forms selection had before M1.B1: left
shifts by constants only; no division, `select` or `test`. -/
def restricted (maxBlocks : Nat) : Gen.Config :=
  { maxBlocks, shiftOps := #[.shl], varShifts := false, divs := false, selects := false, tests := false }

private def percent (part whole : Nat) : String :=
  if whole == 0 then "0%" else s!"{(100 * part + whole / 2) / whole}%"

def runSweeps : IO Bool := do
  for (name, sweep) in Cases.sweeps do
    unless sweep () do
      IO.eprintln s!"check-xv-select: sweep failed: {name}"
      return false
  IO.println s!"sweeps: {Cases.sweeps.length} edge-value sweeps agree"
  return true

def runKernels : IO Bool := do
  let mut checks := 0
  let mut cases := 0
  let mut waiting : List (String × String) := []
  for c in Kernels.cases do
    match Diff.checkKernel c with
    | .ok (.ok n) =>
        checks := checks + n
        cases := cases + 1
    | .ok (.waiting form) =>
        unless waiting.any (·.1 == c.kernel) do waiting := waiting ++ [(c.kernel, form)]
    | .error e =>
        IO.eprintln s!"check-xv-select: kernel failed: {e}"
        return false
  IO.println s!"kernels: {cases} cases selected and run, {checks} outcome checks at exact clocks"
  for (k, form) in waiting do
    IO.println s!"  {k}: waiting for M1.B1 ({form})"
  return true

def runGenerated (label : String) (cfg : Gen.Config) (programs : Nat) (seeds : List UInt64) :
    IO (Option Diff.Report) := do
  let mut total : Diff.Report := {}
  for seed in seeds do
    let start ← IO.monoMsNow
    let mut report : Diff.Report := {}
    for n in [:programs] do
      let programSeed := Support.Rng.derive seed n
      match Diff.checkProgram cfg programSeed with
      | .ok r => report := report.add r
      | .error e =>
          IO.eprintln s!"check-xv-select: {label} program {n} of seed {seed} (program seed {programSeed}) failed: {e}"
          IO.eprintln (Diff.programText cfg programSeed)
          return none
    IO.println s!"{label} seed {seed}: {report.cases} programs, {report.selected} selected, {(← IO.monoMsNow) - start} ms"
    total := total.add report
  return some total

def printReport (label : String) (r : Diff.Report) : IO Unit := do
  IO.println s!"{label}: {r.cases} programs, {r.selected} selected ({percent r.selected r.cases}), {r.stuck} stuck at Lir (selection checked only)"
  let outcomes := (labels.zip r.outcomes).toList.map fun (l, n) => s!"{l} {n}"
  IO.println s!"  outcomes at clock {Diff.bigClock}: {", ".intercalate outcomes}"
  IO.println s!"  clocks: {r.charged} programs spend charges, {r.exact} checked at their exact clock c and c − 1; max charges {r.maxCharges}"
  IO.println s!"  size: {r.lirStmts} Lir statements → {r.xvInsts} Xv instructions; steps: Lir {r.lirSteps}, Xv {r.xvSteps}"
  unless r.unsupported.isEmpty do
    let forms := (r.unsupported.toList.toArray.qsort (·.2 > ·.2)).toList
    IO.println s!"  declined (first unsupported form, programs): {", ".intercalate (forms.map fun (f, n) => s!"{f} {n}")}"

def printRules (r : Diff.Report) : IO Unit := do
  IO.println "rules (programs fired on / total firings):"
  for name in IxCC.Xv.Select.ruleNames do
    IO.println s!"  {name}: {r.rulePrograms.getD name 0} / {r.ruleFirings.getD name 0}"
  let unknown := r.ruleFirings.toList.filter fun (n, _) => !IxCC.Xv.Select.ruleNames.contains n
  unless unknown.isEmpty do IO.println s!"  (unlisted: {unknown})"

def run (args : List String) : IO Bool := do
  match parseOptions args with
  | .error e =>
      IO.eprintln s!"check-xv-select: {e}"
      return false
  | .ok o =>
      let start ← IO.monoMsNow
      unless ← runSweeps do return false
      unless ← runKernels do return false
      let (label, cfg) := if o.restricted then ("restricted", restricted o.maxBlocks)
        else ("generated", ({ maxBlocks := o.maxBlocks } : Gen.Config))
      let some r ← runGenerated label cfg o.programs o.seeds | return false
      printReport s!"{label} programs" r
      printRules r
      if r.selected != r.cases then
        IO.eprintln s!"check-xv-select: selection declined {r.cases - r.selected} programs"
        return false
      IO.println s!"check-xv-select: ok ({(← IO.monoMsNow) - start} ms)"
      return true

end IxCCTests.Xv
