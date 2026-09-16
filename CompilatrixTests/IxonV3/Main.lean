import CompilatrixTests.IxonV3.Run

def main : IO UInt32 := do
  return if ← CompilatrixTests.IxonV3.run then 0 else 1
