import Compilatrix.Ixby.Binary
import Compilatrix.Ixby.Runtime.Chunked.Execute

/-! IO runner for a decoded full-runtime binary. Chunked execution has the
same results and logical counters as the pinned reference interpreter; see
`Chunked.execute_sim` and `Chunked.runChunk_sim`. No compiler environment or
source declarations participate in artifact execution. -/

namespace Compilatrix.Ixby.Runtime

open Ix.Ixby

private def checked (result : Except Error α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError (reprStr error))

def runArtifact (artifact : Binary.Artifact) (input : Array Value)
    (progress := true) : IO (Value × Nat) := do
  let mut state ← checked (Chunked.initialState artifact.limits artifact.program input)
  let mut steps := 0
  let mut chunks := 0
  while steps < artifact.maxSteps do
    let fuel := min 1000000 (artifact.maxSteps - steps)
    let (result, count) ← checked (Chunked.runChunk artifact.limits artifact.program fuel state 0)
    steps := steps + count
    match result with
    | .inl value => return (value.toReference, steps)
    | .inr next => state := next
    chunks := chunks + 1
    if progress && chunks % 100 == 0 then
      IO.println s!"ixby-exec transitions={steps}"
      (← IO.getStdout).flush
  throw (IO.userError (reprStr Error.outOfFuel))

end Compilatrix.Ixby.Runtime
