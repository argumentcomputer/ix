import IxCCTests.Src.Relevance.Run

/-! Thin root of the `tests-relevance` executable. -/

def main (args : List String) : IO UInt32 :=
  IxCCTests.Src.Relevance.Run.main args
