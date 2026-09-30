import CompilatrixTests.Pipeline.Compiler
import CompilatrixTests.Pipeline.Mutants

/-! The `tests-pipeline` suite (M1.I1, M1.I2): the compiler end to end.

* the `compilatrix` command line on the bench-k1 closures and `k1.ixe`,
  `produce` + `run` against the stage suites' pipeline, the certificate's
  round trip, declines and rejections (`Compiler`);
* certificate mutations (`Mutants`).

With `--cc CC`, objects are linked with `fixtures/x86/runtime_driver.c` and
run natively.

Usage: `tests-pipeline [--cc CC] [--work DIR] [--bin COMPILATRIX]
[--mutants N] [--seed S]` (`--mutants`: mutants per class per entry,
default 6; `--bin`: spawn this `compilatrix` binary for the command-line
part instead of running it in process). -/

namespace CompilatrixTests.Pipeline.Run

open CompilatrixTests.Src
open System

def part (a : Assert) (label : String) (action : IO (Array String)) : IO Unit := do
  let before ← a.get
  let (lines, ms) ← timed action
  IO.println s!"  {label}: {(← a.get) - before} assertions, {ms} ms"
  for line in lines do IO.println s!"    {line}"
  (← IO.getStdout).flush

structure Options where
  cc : Option String := none
  work : Option FilePath := none
  bin : Option FilePath := none
  mutants : Nat := 6
  seed : Nat := 1

def parseOptions : List String → Except String Options
  | [] => pure {}
  | "--cc" :: cc :: rest => do return { (← parseOptions rest) with cc := some cc }
  | "--work" :: d :: rest => do return { (← parseOptions rest) with work := some d }
  | "--bin" :: b :: rest => do return { (← parseOptions rest) with bin := some b }
  | "--mutants" :: n :: rest => do
    let some n := n.toNat? | throw s!"bad --mutants {n}"
    return { (← parseOptions rest) with mutants := n }
  | "--seed" :: n :: rest => do
    let some n := n.toNat? | throw s!"bad --seed {n}"
    return { (← parseOptions rest) with seed := n }
  | arg :: _ => throw s!"unknown argument {arg}"

def suite (a : Assert) (o : Options) (work : FilePath) : IO Unit := do
  let native : Option CompilatrixTests.Rt.Native.Tools := o.cc.map fun cc => { cc, work }
  let tools : Compiler.Tools := { native, bin := o.bin, work }
  let where_ := if native.isSome then ", natively at test and bench sizes" else ""
  IO.println "tests-pipeline"
  part a s!"the command line on bench-k1 and k1.ixe{where_}" (Compiler.commandLine a tools)
  part a "produce + run against the stage suites' pipeline" (Compiler.sameObject a)
  part a "certificates through JSON" (Compiler.roundTrips a)
  part a "declines and rejections" (Compiler.declines a tools)
  part a s!"certificate mutations ({o.mutants} per class per entry){if native.isSome then ", natively too" else ""}"
    (Mutants.run a o.mutants o.seed native)

def main (args : List String) : IO UInt32 := do
  let o ← match parseOptions args with
    | .ok o => pure o
    | .error e => IO.eprintln s!"tests-pipeline: {e}"; return 2
  let a ← IO.mkRef 0
  try
    match o.work with
    | some work => IO.FS.createDirAll work; suite a o work
    | none => IO.FS.withTempDir fun work => suite a o work
    IO.println s!"tests-pipeline: {← a.get} assertions passed{if o.cc.isSome then ", native runs agree" else ""}"
    return 0
  catch e =>
    IO.eprintln s!"tests-pipeline: FAILED after {← a.get} assertions: {e}"
    return 1

end CompilatrixTests.Pipeline.Run
