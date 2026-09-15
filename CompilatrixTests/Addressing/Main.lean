import CompilatrixTests.Addressing.Run

def main : IO UInt32 := do
  if ← CompilatrixTests.Addressing.run then
    IO.println "tests-addressing-ok"
    return 0
  return 1
