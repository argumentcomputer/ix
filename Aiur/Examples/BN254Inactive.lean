import Aiur.Library.Field.BN254
import Aiur.Modules.Frontend
import Aiur.Artifact
import Aiur.Trace.Export

namespace BN254InactiveFixture
open Aiur
abbrev F := Library.Field.BN254.F

def source : Modules.Program Nat := aiur⟦
module Inactive {
  table inputs: (Field,) { (0,), (1,), }
  table outputs: Field { 7, 9, }
  map lookup(x: Field) -> Field = inputs => outputs;
  fn run(x: Field) -> Field { lookup(x) + 1 }
  fn unused(x: Field) -> Field { x * x }
}
⟧

def main (args : List String) : IO Unit := do
  let prepared ← IO.ofExcept (Modules.prepare (source.toField F) ["Inactive::run", "Inactive::unused"])
  let exported ← IO.ofExcept prepared.exportExecution
  let compiled ← IO.ofExcept prepared.compileOptimized
  let (exported, trace) ← IO.ofExcept (Trace.exportPlanWide Library.Field.BN254.modulus ZMod.val
    compiled.circuit.inlined.program compiled.circuit.artifact exported)
  let bytes ← IO.ofExcept (Artifact.packageWide exported Library.Field.BN254.modulus ZMod.val (some trace))
  let path := args.headD "crates/aiur/tests/fixtures/bn254-inactive.ixa"
  if args.contains "--check" then
    unless (← IO.FS.readBinFile path).data == bytes.data do
      throw (IO.userError "inactive-circuit fixture differs from its Lean export")
  else
    Artifact.write path bytes
  IO.println s!"BN254 inactive-circuit fixture: {bytes.size} bytes"

end BN254InactiveFixture

def main : List String → IO Unit := BN254InactiveFixture.main
