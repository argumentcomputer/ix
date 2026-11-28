import IxCCTests.Src.StepsTool

/-! Thin root of the `src-steps` executable. -/

def main (args : List String) : IO UInt32 :=
  IxCCTests.Src.StepsTool.main args
