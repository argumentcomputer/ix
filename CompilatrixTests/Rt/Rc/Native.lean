import CompilatrixTests.Rt.Rc.Emit
import Lean

set_option autoImplicit false
namespace CompilatrixTests.Rt.Rc.Native
open Lean System

def command (logs : FilePath) (label cmd : String) (args : Array String)
    (seconds : Nat := 120) : IO Unit := do
  let start ← IO.monoMsNow
  let result ← IO.Process.output {
    cmd := "timeout", args := #["--kill-after=5", toString seconds, cmd] ++ args }
  let elapsed := (← IO.monoMsNow) - start
  IO.FS.writeFile (logs / s!"{label}.stdout") result.stdout
  IO.FS.writeFile (logs / s!"{label}.stderr") result.stderr
  IO.FS.writeFile (logs / s!"{label}.json") ((Json.mkObj [
    ("command", toJson cmd), ("args", toJson args), ("timeout_seconds", toJson seconds),
    ("elapsed_ms", toJson elapsed), ("exit", toJson result.exitCode.toNat)]).pretty ++ "\n")
  IO.println s!"{label}: exit {result.exitCode}, {elapsed}ms; logs {logs}"
  unless result.exitCode == 0 do throw (IO.userError s!"{label}: inspect retained diagnostics")

def run (logs : FilePath) : IO Unit := do
  IO.FS.createDirAll logs
  command logs "fixtures-before" "sha256sum"
    #["--status", "--check", "fixtures/rc/real-source/manifest.sha256"]
  command logs "cc-version" "cc" #["--version"]
  let object := logs / "rc.o"
  Emit.emit object
  let executable := logs / "native-controls"
  command logs "link" "cc" #["-std=c11", "-O1", "-Wall", "-Wextra", "-Werror",
    "-Wl,--fatal-warnings", "-no-pie", "-DENTRY=cx_rc_alloc2", "-I.",
    "fixtures/x86/rc-runtime-driver.c", object.toString, "-o", executable.toString]
  command logs "native" executable.toString #[] 30
  command logs "artifacts" "sha256sum" #[object.toString, executable.toString]
  command logs "fixtures-after" "sha256sum"
    #["--status", "--check", "fixtures/rc/real-source/manifest.sha256"]
  IO.FS.writeFile (logs / "complete.txt")
    "Production RC procedures emitted and executed with unchanged independent native controls.\n"

end CompilatrixTests.Rt.Rc.Native
