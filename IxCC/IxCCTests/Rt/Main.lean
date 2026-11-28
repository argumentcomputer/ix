import IxCCTests.Rt.Run

/-! Thin root of the `tests-rt` executable. -/

def main (args : List String) : IO UInt32 :=
  IxCCTests.Rt.Run.main args
