import AiurTests.U8
import AiurTests.U64
import AiurTests.Blake3
import Aiur.Library.Blake3.Goldilocks
import Aiur.Execution
import Aiur.Trace.Export

open Aiur Lean

def main (args : List String) : IO Unit := do
  AiurU8Tests.run
  AiurU64Tests.run
  if let some path := args.head? then
    let source := Library.Blake3.Goldilocks.program
      |>.append (AiurU8Tests.client.toField Library.U32.Goldilocks.F)
      |>.append (AiurU64Tests.client.toField Library.U32.Goldilocks.F)
      |>.append (AiurBlake3Tests.benchmark.toField Library.U32.Goldilocks.F)
    let prepared ← IO.ofExcept <| Modules.prepare source
      (AiurU8Tests.entries ++ AiurU64Tests.entries ++ ["Benchmark::hash"])
    let exported ← IO.ofExcept prepared.exportExecution
    let compiled ← IO.ofExcept prepared.compileOptimized
    let program ← IO.ofExcept <| exported.toJson Library.U32.Goldilocks.modulus ZMod.val
    let trace ← IO.ofExcept <| Trace.exportJson Library.U32.Goldilocks.modulus ZMod.val
      compiled.circuit.inlined.program compiled.circuit.artifact exported.bytecode
    IO.FS.writeFile path (Json.mkObj [("program", program), ("trace", trace)]).compress
    IO.println s!"Exported shared byte, U64 and Blake3 regression program to {path}."
