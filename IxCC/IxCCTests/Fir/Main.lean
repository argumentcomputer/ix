import IxCCTests.Fir.Run

/-! Thin root of the `tests-fir` executable. -/

def main (args : List String) : IO UInt32 :=
  IxCCTests.Fir.Run.main args
