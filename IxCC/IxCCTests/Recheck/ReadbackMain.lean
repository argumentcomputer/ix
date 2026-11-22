import IxCCTests.Recheck.Readback

def main : IO UInt32 := do
  let _ ← IxCCTests.Recheck.Readback.run
  return 0
