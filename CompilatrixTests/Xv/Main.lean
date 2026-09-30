import CompilatrixTests.Xv.Run

def main (args : List String) : IO UInt32 := do
  return if ← CompilatrixTests.Xv.run args then 0 else 1
