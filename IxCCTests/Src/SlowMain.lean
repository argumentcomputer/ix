import IxCCTests.Src.Run

/-! Thin root of the `tests-src-slow` executable (manual gate). -/

def main (args : List String) : IO UInt32 :=
  IxCCTests.Src.Run.slow args
