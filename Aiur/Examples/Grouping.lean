import Aiur.Library.U32.Goldilocks
import Aiur.Modules.Frontend
import Aiur.Execution.Encode
import Aiur.Trace.Export

open Aiur Lean

def groupedExample : Modules.Program Nat := aiur_modules% "
module Grouped {
  fn left(x: Field) -> Field {
    match x { 0 => 9, _ => x * x * x }
  }
  fn right(x: Field) -> (Field, Field) { (x + 3, x * x) }
  fn memory(x: Field) -> Field { let p = &(x, x + 1); let (a, b) = *p; a + b }
  fn run(x: Field) -> Field {
    let a = left(0);
    let b = left(x);
    let e = left(x + 1);
    let (c, d) = right(x + 2);
    a + b + c + d + memory(x) + e
  }
}
"

def main (args : List String) : IO Unit := do
  let source := groupedExample.toField Library.U32.Goldilocks.F
  let prepared ← IO.ofExcept (Modules.prepare source ["Grouped::run"])
  let exported ← IO.ofExcept prepared.exportExecution
  let compiled ← IO.ofExcept prepared.compileOptimized
  let program ← IO.ofExcept (exported.toJson Library.U32.Goldilocks.modulus ZMod.val)
  let trace ← IO.ofExcept (Trace.exportJson Library.U32.Goldilocks.modulus ZMod.val
    compiled.circuit.inlined.program compiled.circuit.artifact exported.bytecode
    [("arithmetic_and_memory", ["Grouped::left", "Grouped::right", "Grouped::memory"])])
  let package := Json.mkObj [("program", program), ("trace", trace)]
  let path := args.headD "/tmp/aiur-grouping.json"
  if args.contains "--check" then
    let previous ← IO.FS.readFile path
    unless previous == package.compress ++ "\n" do throw (IO.userError "grouping fixture is stale")
  else IO.FS.writeFile path (package.compress ++ "\n")
