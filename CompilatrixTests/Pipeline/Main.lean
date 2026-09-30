import CompilatrixTests.Pipeline.Run

/-! Thin root of the `tests-pipeline` executable. -/

def main (args : List String) : IO UInt32 :=
  CompilatrixTests.Pipeline.Run.main args
