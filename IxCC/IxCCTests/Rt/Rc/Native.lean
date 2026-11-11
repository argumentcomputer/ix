import IxCCTests.Rt.Rc.Emit
import IxCCTests.Rt.Rc.NativeControls
import Lean

/-! `tests-rt-rc native LOGDIR`: the production RC procedures emitted as one
object and run natively in a test executable IxCC writes of it, under the
independent controls of `NativeControls` (4,393 checks), with every step's
command, output and timing retained in `LOGDIR`. -/

set_option autoImplicit false
namespace IxCCTests.Rt.Rc.Native
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
  let object := logs / "rc.o"
  Emit.emit object
  let executable := logs / "native-controls"
  match IxCCTests.Exe.TestShell.writeExe NativeControls.mem NativeControls.exports
      (← IO.FS.readBinFile object) with
  | .ok bytes =>
    IO.FS.writeBinFile executable bytes
    IO.setAccessRights executable { user := { read := true, write := true, execution := true } }
  | .error e => throw (IO.userError s!"no test executable of the RC procedures: {e}")
  let start ← IO.monoMsNow
  let (lines, n) ← NativeControls.run executable
  let elapsed := (← IO.monoMsNow) - start
  IO.FS.writeFile (logs / "native.stdout") (String.join (lines.map (· ++ "\n")))
  IO.FS.writeFile (logs / "native.json") ((Json.mkObj [
    ("executable", toJson executable.toString), ("assertions", toJson n),
    ("elapsed_ms", toJson elapsed)]).pretty ++ "\n")
  for l in lines do IO.println l
  IO.println s!"native: {n} assertions, {elapsed}ms; logs {logs}"
  command logs "artifacts" "sha256sum" #[object.toString, executable.toString]
  command logs "fixtures-after" "sha256sum"
    #["--status", "--check", "fixtures/rc/real-source/manifest.sha256"]
  IO.FS.writeFile (logs / "complete.txt")
    "Production RC procedures emitted and executed in a test executable with unchanged independent native controls.\n"

end IxCCTests.Rt.Rc.Native
