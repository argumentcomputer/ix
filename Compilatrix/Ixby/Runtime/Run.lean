import Compilatrix.Ixby.Binary
import Compilatrix.Ixby.Runtime.Execute

/-! IO runner for a decoded full-runtime binary. No compiler environment,
source declarations, or Stage2-specific implementation participates. -/

namespace Compilatrix.Ixby.Runtime

open Ix.Ixby

private def checked (result : Except Error α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError (reprStr error))

def runArtifact (artifact : Binary.Artifact) (input : Array Value)
    (progress := true) : IO (Value × Nat) := do
  let mut state ← checked (initialState artifact.limits artifact.program input)
  let mut steps := 0
  let mut chunks := 0
  while steps < artifact.maxSteps do
    let fuel := min 1000000 (artifact.maxSteps - steps)
    let (result, count) ← checked (runChunk artifact.limits artifact.program fuel state 0)
    steps := steps + count
    match result with
    | .inl value => return (value, steps)
    | .inr next => state := next
    chunks := chunks + 1
    if progress && chunks % 100 == 0 then
      IO.println s!"ixby-exec transitions={steps}"
      (← IO.getStdout).flush
  throw (IO.userError (reprStr Error.outOfFuel))

end Compilatrix.Ixby.Runtime
