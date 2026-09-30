import CompilatrixTests.Rt.Run

/-! Thin root of the `tests-rt` executable. -/

def main (args : List String) : IO UInt32 :=
  CompilatrixTests.Rt.Run.main args
