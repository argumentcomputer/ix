import IxCCTests.Pipeline.Run

/-! Thin root of the `tests-pipeline` executable. -/

def main (args : List String) : IO UInt32 :=
  IxCCTests.Pipeline.Run.main args
