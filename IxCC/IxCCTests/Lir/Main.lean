import IxCCTests.Lir.Run

def main (args : List String) : IO UInt32 := do
  return if ← IxCCTests.Lir.run args then 0 else 1
