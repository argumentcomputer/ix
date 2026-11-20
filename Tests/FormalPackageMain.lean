import Ix.Meta
import Tests.Ix.InstanceSymbols
import Tests.Ix.VMSource
import Tests.Ix.IxVM.SafeReferencesWalk
import Tests.Ix.IxVM.GuardCertificate
import Tests.Ix.IxVM.RecRunBounds
import Tests.Ix.IxVM.TwinPairRecords

/-!
Test driver for suites that import the formal `Aiur`/`IxVM`/`MultiStark`
packages or `IxVMRefinement` (and therefore Mathlib). Kept separate from
`IxTests` (`Tests/Main.lean`) so the Nix flake and merge-test builds of
`IxTests` stay free of Mathlib.

With no arguments, runs the CI checks (`instance-symbols`, `ixvm-source`).
Named arguments select individual entries (including the manual helpers).
-/

private def runNamed (getEnv : IO Lean.Environment) (name : String) : IO UInt32 := do
  let start ← IO.monoMsNow
  let code ← match name with
    | "instance-symbols" => Tests.Ix.InstanceSymbols.run
    | "ixvm-source" => do Tests.Ix.VMSource.run (← getEnv)
    | "ixvm-export-safe-walk" => Tests.Ix.IxVM.SafeReferencesWalk.exportWalkArtifact
    | "ixvm-guard-certificate" => do Tests.Ix.IxVM.GuardCertificate.run (← getEnv)
    | "ixvm-rec-run-bounds" => do Tests.Ix.IxVM.RecRunBounds.run (← getEnv)
    | "ixvm-twin-pair" => do Tests.Ix.IxVM.TwinPairRecords.run (← getEnv)
    | other =>
      IO.eprintln s!"[formal-package-tests] unknown entry: {other}"
      return 2
  let ms := (← IO.monoMsNow) - start
  if code == 0 then
    IO.println s!"[formal-package-tests] {name}: ok {ms} ms"
  else
    IO.println s!"[formal-package-tests] {name}: FAILED (exit {code}) {ms} ms"
  return code

def main (args : List String) : IO UInt32 := do
  let selected := if args.isEmpty then ["instance-symbols", "ixvm-source"] else args
  if selected.any (fun n => n != "instance-symbols" && n != "ixvm-export-safe-walk") then
    initLeanSearchPath
  let envRef ← IO.mkRef (none : Option Lean.Environment)
  let getEnv : IO Lean.Environment := do
    if let some env ← envRef.get then return env
    let env ← get_env!
    envRef.set (some env)
    return env
  let mut first : UInt32 := 0
  for name in selected do
    let code ← runNamed getEnv name
    if first == 0 && code != 0 then first := code
  return first
