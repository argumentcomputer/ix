import CompilatrixTests.Pipeline.Run

def main : IO UInt32 := do
  if ← CompilatrixTests.Pipeline.run then
    IO.println "tests-pipeline-ok"
    return 0
  return 1
