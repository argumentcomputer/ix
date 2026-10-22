import AiurTests.U32
import Aiur.Library.U32.Goldilocks
import Aiur.Execution
import Aiur.Trace.Export

namespace U32Example
open Aiur Lean

-- IxVM and its word-library regression use the explicitly selected Goldilocks implementation.
abbrev modulus := Library.U32.Goldilocks.modulus
abbrev F := Library.U32.Goldilocks.F

def exportProgram (path : String) : IO Unit := do
  let library := Library.U32.Goldilocks.program
  let source := library.append (AiurU32Tests.client.toField F)
  let prepared ← IO.ofExcept <| Modules.prepare source AiurU32Tests.entries
  let exported ← IO.ofExcept prepared.exportExecution
  let compiled ← IO.ofExcept prepared.compileOptimized
  let program ← IO.ofExcept <| exported.toJson modulus ZMod.val
  let trace ← IO.ofExcept <| Trace.exportJson modulus ZMod.val compiled.circuit.inlined.program
    compiled.circuit.artifact exported.bytecode
  IO.FS.writeFile path (Json.mkObj [("program", program), ("trace", trace)]).compress
  IO.println s!"Exported opaque u32 regression program to {path}."

end U32Example

def main (args : List String) : IO Unit := do
  AiurU32Tests.run
  if let some path := args.head? then U32Example.exportProgram path
