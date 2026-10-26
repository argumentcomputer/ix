import MultiStark
import MultiStark.FunctionGroups
import Aiur.Execution.Encode
import Aiur.Trace.Export

open Aiur Lean

unsafe def main (args : List String) : IO Unit := do
  let groups := if args.contains "--ungrouped" then [] else MultiStark.functionGroups
  let mode := args.headD "check"
  unless ["check", "export", "export-trace"].contains mode do
    throw (IO.userError "usage: stark-export check|export|export-trace [output.json]")
  let aggregate := args.contains "--aggregate"
  let file := if aggregate then "Aggregate.aiur" else "Program.aiur"
  let sourcePath ← [s!"MultiStark/{file}", s!"MultiStark/MultiStark/{file}"].findM?
    fun path => (System.FilePath.mk path).pathExists
  let some sourcePath := sourcePath | throw (IO.userError "cannot locate MultiStark/Program.aiur")
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (loadExts := true) #[{module := `Aiur.Modules.Frontend}] {} 0
  IO.eprintln "Parsing and checking recursive verifier..."
  let source ← IO.ofExcept (MultiStark.parse env (← IO.FS.readFile sourcePath))
  let entry := if aggregate then "MultiStark::ix_aggr" else "MultiStark::verify_multi_stark_proof"
  let prepared ← IO.ofExcept (Modules.prepare source [entry])
  IO.eprintln "Compiling recursive verifier bytecode..."
  let exported ← IO.ofExcept prepared.exportExecution
  IO.eprintln s!"Exported {exported.bytecode.functions.length} functions."
  if mode == "check" then return
  let program ← IO.ofExcept (exported.toJson MultiStark.modulus ZMod.val)
  let trace ← if mode == "export-trace" then do
    IO.eprintln "Compiling certified circuits and witness population plans..."
    let compiled ← IO.ofExcept (prepared.compileOptimized {})
    pure <| some (← IO.ofExcept (Trace.exportJson MultiStark.modulus ZMod.val
      compiled.circuit.inlined.program compiled.circuit.artifact exported.bytecode groups))
  else pure none
  let package := Json.mkObj ([("program", program)] ++ trace.toList.map ("trace", ·))
  let path := args[1]?.getD "/tmp/ix-recursion.json"
  IO.FS.writeFile path package.compress
  IO.eprintln s!"Wrote {path}"
