import IxCCTests.Pipeline.Steps

/-! Thin root of the `check-steps` executable. -/

def main (args : List String) : IO UInt32 :=
  IxCCTests.Pipeline.Steps.main args
