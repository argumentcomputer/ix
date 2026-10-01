import CompilatrixTests.Pipeline.Steps

/-! Thin root of the `check-steps` executable (M3.2). -/

def main (args : List String) : IO UInt32 :=
  CompilatrixTests.Pipeline.Steps.main args
