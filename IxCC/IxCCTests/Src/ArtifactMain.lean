import IxCCTests.Src.Artifact

/-! Thin root of the `gen-src-artifacts` executable. -/

def main (args : List String) : IO UInt32 :=
  IxCCTests.Src.Artifact.main args
