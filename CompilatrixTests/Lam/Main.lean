import CompilatrixTests.Lam.Run

/-! Thin root of the `tests-lam` executable. -/

def main (args : List String) : IO UInt32 :=
  CompilatrixTests.Lam.Run.main args
