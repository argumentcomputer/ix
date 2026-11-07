import IxCCTests.Recheck.Run

/-! Thin root of the `tests-recheck` executable. -/

def main (args : List String) : IO UInt32 :=
  IxCCTests.Recheck.Run.main args
