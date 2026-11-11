import IxCCTests.Exe.Machine

/-! Thin root of the `tests-exe` executable: the suite's parts, then the
numeric state machines'. -/

def main (args : List String) : IO UInt32 :=
  IxCCTests.Exe.Suite.mainWith [("numeric state machines", IxCCTests.Exe.Machine.part)] args
