import CompilatrixTests.Recheck.Artifact

/-! Thin root of the `gen-recheck-artifacts` executable. -/

def main (args : List String) : IO UInt32 :=
  CompilatrixTests.Recheck.Artifact.main args
