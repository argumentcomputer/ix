import CompilatrixTests.Addressing.Run
import CompilatrixTests.Pipeline.Run
import CompilatrixTests.HPT.Run
import CompilatrixTests.Ixon.Run

namespace CompilatrixTests

def runAll : IO UInt32 := do
  let mut ok := true
  let passed ← Addressing.run
  IO.println s!"tests-addressing: {passed}"
  ok := passed && ok
  let passed ← Pipeline.run
  IO.println s!"tests-pipeline: {passed}"
  ok := passed && ok
  let passed ← HPT.run
  IO.println s!"tests-hpt: {passed}"
  ok := passed && ok
  let passed ← Ixon.run
  IO.println s!"tests-ixon: {passed}"
  ok := passed && ok
  if ok then
    IO.println "tests-ok"
    return 0
  return 1

end CompilatrixTests
