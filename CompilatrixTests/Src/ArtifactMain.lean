import CompilatrixTests.Src.Artifact

/-! Thin root of the `gen-src-artifacts` executable. -/

def main (args : List String) : IO UInt32 :=
  CompilatrixTests.Src.Artifact.main args
