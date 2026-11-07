import IxCCTests.Corpus.Run

/-! Thin root of the `tests-corpus` executable (MT.2). -/

def main (args : List String) : IO UInt32 :=
  IxCCTests.Corpus.suiteMain args
