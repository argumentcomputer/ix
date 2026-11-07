import IxCCTests.Src.Run

/-! Thin root of the `tests-src` executable. -/

def main (args : List String) : IO UInt32 :=
  IxCCTests.Src.Run.main args
