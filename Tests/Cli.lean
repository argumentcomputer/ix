-- Integration tests for the Ix CLI
import LSpec
open LSpec IO

def ixBuild : IO TestSeq := do
  let out ← Process.output { cmd := "lake", args := #["build", "ix"]}
  --if out.exitCode ≠ 0 then
  --  eprintln out.stderr; return out.exitCode
  -- TODO: Figure out how to emit custom error message with out.stderr
  return test "Ix CLI build" (out.exitCode == 0)

def Tests.Cli.suiteIO : List (IO TestSeq) :=
[
  ixBuild
]
