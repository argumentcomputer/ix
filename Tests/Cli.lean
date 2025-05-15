-- Integration tests for the Ix CLI
import LSpec
open LSpec IO

def ixBuild : IO TestSeq := do
  let out ← Process.output { cmd := "lake", args := #["build", "ix"]}
  if out.exitCode ≠ 0 then
    eprintln s!"{out.stderr}exit {out.exitCode}"
  return test "Ix CLI build" (out.exitCode == 0)

def Tests.Cli.suiteIO : List (IO TestSeq) :=
[
  ixBuild
]
