import IxCCTests.Pipeline.ShrinkSuite

/-! Thin root of the `tests-shrink` executable (MT.5). -/

def main (args : List String) : IO UInt32 :=
  IxCCTests.Pipeline.ShrinkSuite.main args
