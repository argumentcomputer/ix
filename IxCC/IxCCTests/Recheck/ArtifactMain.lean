import IxCCTests.Recheck.Artifact

/-! Thin root of the `gen-recheck-artifacts` executable. -/

def main (args : List String) : IO UInt32 :=
  IxCCTests.Recheck.Artifact.main args
