import Lean

/-! Separate writer and reader processes share only persisted source/certificate
and object bytes. Building this executable is separate from running the gate. -/
set_option autoImplicit false
namespace CompilatrixTests.Recheck.Rc.FreshIO
open Lean System

def child (logs : FilePath) (label : String) (executable : FilePath) (args : Array String) : IO Unit := do
  let start ← IO.monoMsNow
  let result ← IO.Process.output {
    cmd := "timeout", args := #["--kill-after=5", "120", executable.toString] ++ args }
  let elapsed := (← IO.monoMsNow) - start
  IO.FS.writeFile (logs / s!"{label}.stdout") result.stdout
  IO.FS.writeFile (logs / s!"{label}.stderr") result.stderr
  IO.FS.writeFile (logs / s!"{label}.json") ((Json.mkObj [
    ("command", toJson executable.toString), ("args", toJson args),
    ("timeout_seconds", toJson (120 : Nat)), ("elapsed_ms", toJson elapsed),
    ("exit", toJson result.exitCode.toNat)]).pretty ++ "\n")
  IO.println s!"{label}: exit {result.exitCode}, {elapsed}ms; logs {logs}"
  unless result.exitCode == 0 do throw (IO.userError s!"{label}: inspect retained diagnostics")

def run (logs : FilePath) : IO Unit := do
  IO.FS.createDirAll logs
  let executable ← IO.appPath
  for mode in ["codec", "replay"] do
    let bundle := logs / (mode ++ "-bundle")
    let results := logs / (mode ++ "-read")
    if ← bundle.pathExists then throw (IO.userError s!"refusing to overwrite prior bundle {bundle}")
    IO.FS.createDirAll bundle
    IO.FS.createDirAll results
    child logs (mode ++ "-write") executable #[mode, "write", bundle.toString, results.toString]
    child logs (mode ++ "-read") executable #[mode, "read", bundle.toString, results.toString]
  IO.FS.writeFile (logs / "complete.txt")
    "Separate compiled writer/reader processes passed codec and complete RC replay gates.\n"

end CompilatrixTests.Recheck.Rc.FreshIO
