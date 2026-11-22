import IxCCTests.Recheck.P1Twin.Run

/-! Thin root of the `tests-p1-twin` executable. -/

def main (args : List String) : IO UInt32 :=
  IxCCTests.Recheck.P1Twin.main args
