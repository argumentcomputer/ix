import IxCCTests.Exe.Run

/-! Thin root of the `tests-exe` executable. -/

def main (args : List String) : IO UInt32 :=
  IxCCTests.Exe.Suite.main args
