import CompilatrixTests.Recheck.Readback

def main : IO UInt32 := do
  let _ ← CompilatrixTests.Recheck.Readback.run
  return 0
