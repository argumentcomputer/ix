import CompilatrixTests.Src.Support
import Compilatrix.Tools.Check

/-! The Phase 1 compiler inputs (design note 01 §1.1): each bench-k1
closure's `entry` runs through SrcEval on the test arguments of
`benchmarks/fixtures/manifest.json` and must print `expected.txt`. Each
closure's admitted runtime set (primitives, eliminators, `case` keys,
`lazy` constants, quotient heads) is reported (phase1.md M0.4).

SrcEval is a big-step evaluator, so `sum-loop`'s loop nests native frames
per iteration: its test size (10⁶) runs in a child process of this
executable with an enlarged Lean stack (`LEAN_STACK_SIZE_KB`). -/

namespace CompilatrixTests.Src.Bench

open Compilatrix Compilatrix.Src CompilatrixTests.Src
open Compilatrix.Tools.Check (readJson strField arrField)

def manifest : System.FilePath := "benchmarks/fixtures/manifest.json"

/-- Test arguments and expected output of a benchmark fixture. -/
def testCase (name : String) : IO (List Nat × Nat) := do
  let m ← readJson manifest
  for f in ← arrField m "fixtures" do
    if (← strField f "name") == name then
      let args ← (← arrField f "test_args").toList.mapM fun j => do
        match j.getStr? with
        | .ok s => pure s.toNat!
        | .error e => throw (IO.userError e)
      let expected := (← IO.FS.readFile ("benchmarks/fixtures" / name / "expected.txt")).trimAscii
      return (args, expected.toString.toNat!)
  throw (IO.userError s!"{name} is not in the manifest")

/-- Stack for the child run of a deep entry. -/
def deepStackKb : Nat := 4 * 1024 * 1024
def deepClock : Nat := 1 <<< 40

/-- Run one entry and print its result (the child-process mode). -/
def runEntry (name : String) : IO Nat := do
  let l ← loadBench name
  let (args, _) ← testCase name
  let some root := l.root? | throw (IO.userError s!"{name}: no root")
  match ← runRoot l.program deepClock root args with
  | .ok v =>
    match l.readback v with
    | some (.nat n) => return n
    | _ => throw (IO.userError s!"{name}: result {v.shape} has no Nat readback")
  | r => throw (IO.userError s!"{name}: {outcome r}")

def runtimeSet (l : Loaded) : String :=
  let p := l.program
  let names := fun (cs : Array CId) => cs.toList.map fun c =>
    (Loaded.names l.hints (p.addr c)).getD (p.short c)
  let pinned := fun (c : CId) =>
    (Pinned.constRows.find? fun (_, hex) => Pinned.addr hex == p.addr c).map (·.1)
  let lazyName := fun (c : CId) =>
    ((Pinned.lazyRows.find? fun (_, hex, _) => Pinned.addr hex == p.addr c).map (·.1)).getD (p.short c)
  let recs := l.admitted.recursors.toList.map fun (c, k) =>
    let kind := match k with
      | .ordinary => "ordinary" | .subsingleton _ => "subsingleton" | .empty => "empty"
    s!"{(pinned c).getD (p.short c)}:{kind}"
  let cases := l.admitted.cases.toList.map fun c => (pinned c).getD (p.short c)
  s!"prims {l.admitted.prims.toList.map (·.2.name)}; recursors {recs}; case {cases}; " ++
    s!"lazy {l.admitted.lazy.toList.map lazyName}; quot {l.admitted.quotHeads.size}; " ++
    s!"eqn {names l.admitted.eqns}; kernel bodies {l.admitted.bodies.size}"

def run (a : Assert) (self : System.FilePath) : IO (Array String) := do
  let mut report := #[]
  for name in benchNames do
    let (args, expected) ← testCase name
    let l ← loadBench name
    report := report.push s!"{name}: {runtimeSet l}"
    let (got, ms) ← timed do
      if name == "sum-loop" then
        let env := #[("LEAN_STACK_SIZE_KB", some (toString deepStackKb))]
        let out ← IO.Process.output { cmd := self.toString, args := #["--entry", name], env }
        unless out.exitCode == 0 do
          throw (IO.userError s!"{name} child exited {out.exitCode}: {out.stderr}")
        pure out.stdout.trimAscii.toString.toNat!
      else runEntry name
    expectEq a got expected s!"{name} {args} through SrcEval"
    report := report.push s!"{name} {args} = {got} (expected {expected}) in {ms} ms"
  return report

end CompilatrixTests.Src.Bench
