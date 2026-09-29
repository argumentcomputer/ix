import CompilatrixTests.Src.Run

/-! Thin root of the `tests-src-slow` executable (manual gate). -/

def main (args : List String) : IO UInt32 :=
  CompilatrixTests.Src.Run.slow args
