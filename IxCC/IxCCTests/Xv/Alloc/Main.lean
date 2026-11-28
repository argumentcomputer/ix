import IxCCTests.Xv.Alloc.Run

def main (args : List String) : IO UInt32 := do
  return if ← IxCCTests.Xv.Alloc.run args then 0 else 1
