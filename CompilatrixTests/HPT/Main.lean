import CompilatrixTests.HPT.Run

def main : IO UInt32 := do
  if ← CompilatrixTests.HPT.run then
    IO.println "tests-hpt-ok"
    return 0
  return 1
