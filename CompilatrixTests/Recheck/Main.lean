import CompilatrixTests.Recheck.Run

/-! Thin root of the `tests-recheck` executable. -/

def main (args : List String) : IO UInt32 :=
  CompilatrixTests.Recheck.Run.main args
