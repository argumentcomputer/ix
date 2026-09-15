import CompilatrixTests.Ixon.Run

def main : IO UInt32 := do
  if ← CompilatrixTests.Ixon.run then
    IO.println "tests-ixon-ok"
    return 0
  return 1
