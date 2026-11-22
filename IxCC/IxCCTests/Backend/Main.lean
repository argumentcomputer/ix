import IxCCTests.Backend.Run

def main (args : List String) : IO UInt32 := do
  return if ← IxCCTests.Backend.run args then 0 else 1
