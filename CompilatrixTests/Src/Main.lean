import CompilatrixTests.Src.Run

/-! Thin root of the `tests-src` executable. -/

def main (args : List String) : IO UInt32 :=
  CompilatrixTests.Src.Run.main args
