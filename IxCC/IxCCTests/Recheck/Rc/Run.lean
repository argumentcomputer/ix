import IxCCTests.Recheck.Rc.CodecIO
import IxCCTests.Recheck.Rc.ReplayIO
import IxCCTests.Recheck.Rc.FreshIO

namespace IxCCTests.Recheck.Rc
open System

def run (args : List String) : IO Unit := do
  Fixtures.verify
  match args with
  | ["fresh", logs] => FreshIO.run logs
  | [mode, phase, bundle, logs] =>
    IO.FS.createDirAll bundle
    IO.FS.createDirAll logs
    match mode, phase with
    | "codec", "write" => CodecIO.write bundle
    | "codec", "read" => CodecIO.read bundle logs
    | "replay", "write" => ReplayIO.write bundle
    | "replay", "read" => ReplayIO.read bundle logs
    | _, _ => throw (IO.userError "expected codec/replay write/read BUNDLE LOGDIR")
  | _ => throw (IO.userError "expected fresh LOGDIR or codec/replay write/read BUNDLE LOGDIR")
  Fixtures.verify

end IxCCTests.Recheck.Rc
