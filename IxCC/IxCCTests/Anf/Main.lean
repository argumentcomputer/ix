import IxCCTests.Anf.Run

/-! Thin root of the `tests-anf` executable. -/

def main (args : List String) : IO UInt32 :=
  IxCCTests.Anf.Run.main args
