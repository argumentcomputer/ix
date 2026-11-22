import IxCCTests.Lam.Run

/-! Thin root of the `tests-lam` executable. -/

def main (args : List String) : IO UInt32 :=
  IxCCTests.Lam.Run.main args
