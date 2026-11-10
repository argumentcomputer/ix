import IxCCTests.Own.Suite

/-! Thin root of the `tests-own` executable. -/

def main (args : List String) : IO UInt32 :=
  IxCCTests.Own.Suite.main args
