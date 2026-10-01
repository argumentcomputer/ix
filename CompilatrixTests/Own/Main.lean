import CompilatrixTests.Own.Suite

/-! Thin root of the `tests-own` executable (MT.7). -/

def main (args : List String) : IO UInt32 :=
  CompilatrixTests.Own.Suite.main args
