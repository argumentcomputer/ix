import CompilatrixTests.Corpus.Run

/-! Thin root of the `tests-corpus` executable (MT.2). -/

def main (args : List String) : IO UInt32 :=
  CompilatrixTests.Corpus.main args
