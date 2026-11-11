import IxCCTests.Pipeline.Compiler
import IxCCTests.Pipeline.Mutants
import IxCCTests.Pipeline.Levels
import IxCCTests.Pipeline.Twin
import IxCCTests.Pipeline.Defun

/-! The `tests-pipeline` suite: the compiler end to end.

* the `ixcc` command line on the bench-k1 closures and `k1.ixe`,
  `produce` + `run` against the stage suites' pipeline, the certificate's
  round trip, declines and rejections (`Compiler`);
* certificate mutations (`Mutants`);
* every level of every K1 program on its test input (`Levels`);
* the compiled `k1.ixe` roots against their Lean-compiled twin on generated
  inputs, with the `2⁶³` boundary (`Twin`);
* the closures step (the roots' entries and P8, `Recheck.closuresOf`) under
  chosen middle-end schedules, on the decline corpus's `composeClosure`, the K1
  fallback route and the `phase2-closures` and `phase2-arity` roots (`Defun`).

With `--native`, objects run natively, as test executables IxCC writes
(`IxCCTests.Rt.Native`).

Usage: `tests-pipeline [--native] [--work DIR] [--bin IXCC]
[--mutants N] [--twin N] [--seed S] [--full] [--only PART]...`
(`--mutants`: mutants per class per entry, default 6; `--twin`: generated
inputs per root, default 60; `--bin`: spawn this `ixcc` binary for
the command-line part instead of running it in process; `--full`: every
level at the test size, including the ones the default runs at a reduced
size to fit the CI budget; `--only`: `cli`, `same`, `json`, `declines`, `reports`,
`mutants`, `levels`, `twin`, `defun`). `tests-pipeline --level NAME LEVEL ARGS…` is
the child-process mode of `Levels`. -/

namespace IxCCTests.Pipeline.Run

open IxCCTests.Src
open System

def part (a : Assert) (label : String) (action : IO (Array String)) : IO Unit := do
  let before ← a.get
  let (lines, ms) ← timed action
  IO.println s!"  {label}: {(← a.get) - before} assertions, {ms} ms"
  for line in lines do IO.println s!"    {line}"
  (← IO.getStdout).flush

structure Options where
  /-- Run natively, as test executables IxCC writes. -/
  runNative : Bool := false
  work : Option FilePath := none
  bin : Option FilePath := none
  mutants : Nat := 6
  twin : Nat := 60
  seed : Nat := 1
  full : Bool := false
  only : List String := []
  /-- The bench entries the levels part runs (default: all five). -/
  benches : List String := []
  progress : Bool := false

def parseOptions : List String → Except String Options
  | [] => pure {}
  | "--native" :: rest => do return { (← parseOptions rest) with runNative := true }
  | "--work" :: d :: rest => do return { (← parseOptions rest) with work := some d }
  | "--bin" :: b :: rest => do return { (← parseOptions rest) with bin := some b }
  | "--mutants" :: n :: rest => do
    let some n := n.toNat? | throw s!"bad --mutants {n}"
    return { (← parseOptions rest) with mutants := n }
  | "--twin" :: n :: rest => do
    let some n := n.toNat? | throw s!"bad --twin {n}"
    return { (← parseOptions rest) with twin := n }
  | "--seed" :: n :: rest => do
    let some n := n.toNat? | throw s!"bad --seed {n}"
    return { (← parseOptions rest) with seed := n }
  | "--full" :: rest => do return { (← parseOptions rest) with full := true }
  | "--progress" :: rest => do return { (← parseOptions rest) with progress := true }
  | "--bench" :: n :: rest => do
    let o ← parseOptions rest
    return { o with benches := n :: o.benches }
  | "--only" :: p :: rest => do
    let o ← parseOptions rest
    return { o with only := p :: o.only }
  | arg :: _ => throw s!"unknown argument {arg}"

/-- The levels that run below the test size by default, and their
arguments: the typed and byte machines step one instruction at a time, and
`sum-loop` 10⁶ is about 15 million instructions (`--full` runs them all at
the test size). -/
def reduced (full : Bool) (name level : String) : Option (List Nat) :=
  if full then none else
  if level == "x86" || level == "bytes" then
    match name with
    | "fib" => some [13]
    | "sum-loop" => some [5000]
    | "ackermann" => some [3, 3]
    | "tak" => some [12, 12, 8, 4]
    | _ => none
  else none

def suite (a : Assert) (o : Options) (work : FilePath) : IO Unit := do
  let native : Option IxCCTests.Rt.Native.Tools := if o.runNative then some { work } else none
  let tools : Compiler.Tools := { native, bin := o.bin, work }
  let want := fun (p : String) => o.only.isEmpty || o.only.contains p
  let natively := if native.isSome then ", natively" else ""
  IO.println "tests-pipeline"
  if want "cli" then
    part a s!"the command line on bench-k1 and k1.ixe{natively}{if native.isSome then " at test and bench sizes" else ""}"
      (Compiler.commandLine a tools)
  if want "same" then part a "produce + run against the stage suites' pipeline" (Compiler.sameObject a)
  if want "json" then part a "certificates through JSON" (Compiler.roundTrips a)
  if want "declines" then part a "declines and rejections" (Compiler.declines a tools)
  if want "reports" then part a "the command line's parser, IR dumps, statistics and signatures" (Compiler.reports a)
  if want "mutants" then
    part a s!"certificate mutations ({o.mutants} per class per entry){if native.isSome then ", natively too" else ""}"
      (Mutants.run a o.mutants o.seed native)
  if want "levels" then
    part a s!"every level on the test inputs{natively}{if o.full then " (full)" else ""}"
      (Levels.run a (← IO.appPath) native (reduced o.full)
        (if o.benches.isEmpty then benchNames else o.benches) o.progress)
  if want "twin" then
    part a s!"k1.ixe's roots against the Lean-compiled twin ({o.twin} generated inputs per root){natively}"
      (Twin.run a native o.twin o.seed)
  if want "defun" then
    part a s!"the closures step under chosen middle-end schedules{natively}"
      (Defun.run a native)

def main (args : List String) : IO UInt32 := do
  if let "--level" :: name :: level :: xs := args then
    Levels.childMain name level (xs.map String.toNat!)
    return 0
  let o ← match parseOptions args with
    | .ok o => pure o
    | .error e => IO.eprintln s!"tests-pipeline: {e}"; return 2
  let a ← IO.mkRef 0
  try
    match o.work with
    | some work => IO.FS.createDirAll work; suite a o work
    | none => IO.FS.withTempDir fun work => suite a o work
    IO.println s!"tests-pipeline: {← a.get} assertions passed{if o.runNative then ", native runs agree" else ""}{← IxCCTests.Rt.Native.agreement}"
    return 0
  catch e =>
    IO.eprintln s!"tests-pipeline: FAILED after {← a.get} assertions: {e}"
    return 1

end IxCCTests.Pipeline.Run
