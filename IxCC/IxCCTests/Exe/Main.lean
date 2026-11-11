import IxCCTests.Exe.Machine

/-! Thin root of the `tests-exe` executable: the suite's parts, then the
numeric state machines'. `--session-lines` prints the oracle driver's input
for the long sessions (`IxCCTests.Exe.MachineSessions`). -/

def main (args : List String) : IO UInt32 := do
  if args == ["--session-lines"] then
    for line in IxCCTests.Exe.MachineSessions.oracleLines do IO.println line
    return 0
  IxCCTests.Exe.Suite.mainWith [("numeric state machines", IxCCTests.Exe.Machine.part)] args
