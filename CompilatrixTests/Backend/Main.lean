import CompilatrixTests.Backend.Run

def main (args : List String) : IO UInt32 := do
  return if ← CompilatrixTests.Backend.run args then 0 else 1
