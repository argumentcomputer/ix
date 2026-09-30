import CompilatrixTests.Src.Relevance.Run

/-! Thin root of the `tests-relevance` executable. -/

def main (args : List String) : IO UInt32 :=
  CompilatrixTests.Src.Relevance.Run.main args
