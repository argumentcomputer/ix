import CompilatrixTests.Anf.Run

/-! Thin root of the `tests-anf` executable. -/

def main (args : List String) : IO UInt32 :=
  CompilatrixTests.Anf.Run.main args
