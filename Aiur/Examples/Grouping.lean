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

private def expectRejection (label : String) (result : Except String α) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError s!"grouping certificate accepted {label}")

/-- Check failures that source-constraint projection alone would miss: packet
tags, unused sends, memory words, and coverage of the original system. -/
private def auditCertificates (system : Circuit.System Library.U32.Goldilocks.F)
    (callables : List String) : IO Unit := do
  let id := fun name => if callables.contains name then .ok (callables.idxOf name)
    else .error s!"unknown callable {name}"
  let names := ["Grouped::left", "Grouped::right", "Grouped::memory"]
  let sources := system.chips.filter fun c => names.contains c.name
  let checked ← IO.ofExcept (Optimized.Grouping.compile "audit" id sources)
  let g := checked.layout
  let certify := Optimized.Grouping.certify sources id
  expectRejection "a changed channel tag" (certify
    {g with receive := .const 9 :: g.receive.drop 1})
  expectRejection "an extra enabled send" (certify
    {g with sends := g.sends ++ [⟨.const 1, []⟩]})
  expectRejection "an undersized physical row" (certify {g with width := 0})
  expectRejection "a changed memory address" (certify {g with sends := g.sends.map fun slot =>
    {slot with args := slot.args.take 2 ++
      [.add (Optimized.Grouping.word slot.args 2) (.const 1)] ++ slot.args.drop 3}})
  let packed : Optimized.Grouping.Packed _ id := ⟨sources, checked⟩
  unless !(decide (Optimized.Grouping.PlanCertificate system [] [packed])) do
    throw (IO.userError "grouping certificate accepted a missing entrypoint")

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
    let physical ← IO.ofExcept (Optimized.Physical.prepare compiled.circuit.artifact)
    auditCertificates physical.system
      (exported.bytecode.functions.map (·.name) ++ exported.bytecode.maps.map (·.name))
  else IO.FS.writeFile path (package.compress ++ "\n")
