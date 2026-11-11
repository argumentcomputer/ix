import IxCCTests.Rt.Differential
import IxCCTests.Rt.Cases
import IxCCTests.Rt.Mutants
import IxCCTests.Rt.Levels
import IxCCTests.Rt.Kernel
import IxCCTests.Rt.KernelEval
import IxCCTests.Rt.DecoderChecks

/-! The `tests-rt` suite: the primitive
sequences at their boundaries; hand-written programs, declines and
`cx_init`; planted mutations; every k1.ixe and bench-k1 root and
first-order constant, the bench entries at test sizes and generated
programs, Cfg against Lir; then the backend levels (Xv, Xl, typed x86, the
byte machine) on the bench entries, the hand-written values and a sample of
generated programs, and, with `--native`, natively, as test executables IxCC
writes (`IxCCTests.Rt.Native`). Building the suite runs `Rt.lower` in the
kernel (`IxCCTests.Rt.KernelEval`).

Usage: `tests-rt [--native] [--work DIR] [--generated N] [--sample K]`
(`--generated`: the number of generated programs, default 1000; `--sample`:
every K-th of them through the backend, default 25). `tests-rt --prims`
lists the primitives each fixture's Cfg program uses. -/

namespace IxCCTests.Rt.Run

open IxCCTests.Src

def part (a : Assert) (label : String) (action : IO (Array String)) : IO Unit := do
  let before ← a.get
  let (lines, ms) ← timed action
  IO.println s!"  {label}: {(← a.get) - before} assertions, {ms} ms"
  for line in lines do IO.println s!"    {line}"
  (← IO.getStdout).flush

structure Options where
  /-- Run natively, as test executables IxCC writes. -/
  runNative : Bool := false
  work : Option System.FilePath := none
  generated : Nat := 1000
  sample : Nat := 25
  prims : Bool := false
  /-- Only the backend and native levels. -/
  levelsOnly : Bool := false

def parseOptions : List String → Except String Options
  | [] => pure {}
  | "--native" :: rest => do return { (← parseOptions rest) with runNative := true }
  | "--work" :: d :: rest => do return { (← parseOptions rest) with work := some d }
  | "--generated" :: n :: rest => do
    let some n := n.toNat? | throw s!"bad --generated {n}"
    return { (← parseOptions rest) with generated := n }
  | "--sample" :: n :: rest => do
    let some n := n.toNat? | throw s!"bad --sample {n}"
    return { (← parseOptions rest) with sample := max n 1 }
  | "--prims" :: rest => do return { (← parseOptions rest) with prims := true }
  | "--levels-only" :: rest => do return { (← parseOptions rest) with levelsOnly := true }
  | arg :: _ => throw s!"unknown argument {arg}"

/-- The primitives each fixture's Cfg program uses (diagnostics). -/
def listPrims : IO Unit := do
  let packs := [("k1", fixtures / "k1/k1.ixe", fixtures / "k1/equations.json")] ++
    benchNames.map fun n => (n, fixtures / "bench-k1" / s!"{n}.ixe", fixtures / "bench-k1" / s!"{n}.equations.json")
  for (name, ixe, eqs) in packs do
    let (l, _) ← IxCCTests.Lam.Differential.loadWithFirstOrder ixe eqs
    let e ← IxCCTests.Lam.eraseLoaded l
    let A ← IxCCTests.Fir.Differential.finalAnf e.lam
    let L ← IO.ofExcept (IxCCTests.Fir.lower A)
    let ps := L.cfg.funList.flatMap fun (f, fd) => fd.blocks.flatMap fun b => b.body.filterMap fun
      | .bind _ (.fir (.prim op _)) => some (f, op.name)
      | _ => none
    let names := (ps.map (·.2)).eraseDups
    IO.println s!"{name}: {names}"
    for n in names do
      IO.println s!"  {n}: functions {((ps.filter (·.2 == n)).map (·.1)).eraseDups}"

/-- The summaries `KernelEval` checks in the kernel, computed natively, and
the artifacts current. -/
def kernelSummaries (a : Assert) : IO (Array String) := do
  let mut out := #[]
  let mut wrong := #[]
  for (name, A, e) in Kernel.expected do
    let (S, _) ← Differential.entry name
    expect a (A.beq S.levels.anf) s!"{name}: IxCCTests/Fir/Artifacts.lean is stale"
    let got := Kernel.summary A
    if got != some e then wrong := wrong.push s!"{name}: expected {e}, natively {got}"
    out := out.push s!"{name}: {e}"
  for (name, C, e) in Kernel.expectedCfg do
    let got := Kernel.cfgSummary C
    if got != some e then wrong := wrong.push s!"{name}: expected {e}, natively {got}"
    out := out.push s!"{name}: {e}"
  expect a wrong.isEmpty s!"the kernel's expected summaries differ natively:\n{"\n".intercalate wrong.toList}"
  return out

def suite (a : Assert) (o : Options) (tools : Option Native.Tools) : IO Unit := do
  IO.println "tests-rt"
  unless o.levelsOnly do
    part a "primitive sequences at their boundaries" (Cases.prims a)
    part a "hand-written programs, declines and cx_init" (Cases.handWritten a)
    part a "planted mutations" (Mutants.run a)
    part a "k1.ixe and bench-k1: Cfg → Lir" (Differential.packs a)
    part a "bench-k1 entries at their test sizes, at Lir" (Differential.entries a)
    part a "generated first-order programs" (Differential.generated a o.generated)
    part a "kernel summaries (the values KernelEval checks), computed natively" (kernelSummaries a)
  part a "the independent decoder of native results" (DecoderChecks.run a)
  let where_ := if tools.isSome then " and natively" else ""
  part a s!"bench-k1 entries at Xv, Xl, typed x86, the byte machine{where_}" (Levels.benches a tools)
  part a s!"hand-written values at every level{where_}" (Levels.values a tools)
  part a s!"generated programs at every level{where_}" (Levels.generated a tools o.generated o.sample)
  if let some t := tools then
    part a "deep recursion on a mapped stack" (Levels.stacks a t)

def main (args : List String) : IO UInt32 := do
  let o ← match parseOptions args with
    | .ok o => pure o
    | .error e => IO.eprintln s!"tests-rt: {e}"; return 2
  if o.prims then listPrims; return 0
  let a ← IO.mkRef 0
  try
    let go (tools : Option Native.Tools) : IO Unit := suite a o tools
    match o.runNative, o.work with
    | false, _ => go none
    | true, some work => IO.FS.createDirAll work; go (some { work })
    | true, none => IO.FS.withTempDir fun work => go (some { work })
    IO.println s!"tests-rt: {← a.get} assertions passed{if o.runNative then ", native runs agree" else ""}{← IxCCTests.Rt.Native.agreement}"
    return 0
  catch e =>
    IO.eprintln s!"tests-rt: FAILED after {← a.get} assertions: {e}"
    return 1

end IxCCTests.Rt.Run
