import CompilatrixTests.Lir.Run

def main (args : List String) : IO UInt32 := do
  return if ← CompilatrixTests.Lir.run args then 0 else 1
