import CompilatrixTests.Fir.Run

/-! Thin root of the `tests-fir` executable. -/

def main (args : List String) : IO UInt32 :=
  CompilatrixTests.Fir.Run.main args
