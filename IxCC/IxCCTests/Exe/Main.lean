import IxCCTests.Exe.Machine
import IxCCTests.Exe.FoldGuard

/-! Thin root of the `tests-exe` executable: the suite's parts, then the
numeric state machines' and the fold guard's (`fixtures/fold`).
`--session-lines` prints the oracle driver's input for the long sessions
(`IxCCTests.Exe.MachineSessions`); `--fold-root ROOT [EXE]` is the fold guard
part's child process (`IxCCTests.Exe.FoldGuard.child`). -/

def main (args : List String) : IO UInt32 := do
  if args == ["--session-lines"] then
    for line in IxCCTests.Exe.MachineSessions.oracleLines do IO.println line
    return 0
  match args with
  | ["--fold-root", root] => IxCCTests.Exe.FoldGuard.child root none
  | ["--fold-root", root, exe] => IxCCTests.Exe.FoldGuard.child root (some exe)
  | _ =>
    IxCCTests.Exe.Suite.mainWith [("numeric state machines", IxCCTests.Exe.Machine.part),
      ("fold guard (fixtures/fold)", IxCCTests.Exe.FoldGuard.part)] args
