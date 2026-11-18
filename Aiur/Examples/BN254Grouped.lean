import Aiur.Library.Field.BN254
import Aiur.Modules.Frontend
import Aiur.Artifact
import Aiur.Trace.Export

/-! Certified grouping over BN254, including distinct result widths, branch
selectors, high field values and ROM messages in a shared physical circuit. -/

namespace BN254GroupedFixture
open Aiur

abbrev F := Library.Field.BN254.F
abbrev modulus := Library.Field.BN254.modulus

def source : Modules.Program Nat := aiur⟦
module BN254Grouped {
  fn left(x: Field) -> Field {
    match x { 0 => 9, _ => x * x * x }
  }
  fn right(x: Field) -> (Field, Field) { (x + 3, x * x) }
  fn memory(x: Field) -> Field {
    let pointer = &(x, x + 1);
    let (a, b) = *pointer;
    a + b
  }
  fn run(x: Field) -> Field {
    let a = left(0);
    let b = left(x);
    let e = left(x + 1);
    let (c, d) = right(x + 2);
    a + b + c + d + memory(x) + e
  }
}
⟧

def main (args : List String) : IO Unit := do
  let prepared ← IO.ofExcept (Modules.prepare (source.toField F) ["BN254Grouped::run"])
  for (x, expected) in [((0 : F), (29 : F)), (2, 72), (-1, 21)] do
    let (actual, _) ← IO.ofExcept (prepared.run "BN254Grouped::run" [.field x])
    unless actual == .field expected do
      throw (IO.userError "BN254 grouped source evaluator disagrees")
  let exported ← IO.ofExcept prepared.exportExecution
  let compiled ← IO.ofExcept prepared.compileOptimized
  let (exported, trace) ← IO.ofExcept (Trace.exportPlanWide modulus ZMod.val
    compiled.circuit.inlined.program compiled.circuit.artifact exported
    [("BN254Grouped::physical", ["BN254Grouped::left", "BN254Grouped::right", "BN254Grouped::memory"])])
  let bytes ← IO.ofExcept (Artifact.packageWide exported modulus ZMod.val (some trace))
  let path := args.headD "crates/aiur/tests/fixtures/bn254-grouped.ixa"
  if args.contains "--check" then
    let expected ← IO.FS.readBinFile path
    unless bytes.data == expected.data do
      throw (IO.userError "BN254 grouped fixture differs from its Lean export")
  else
    Artifact.write path bytes
  IO.println s!"BN254 grouped fixture: {bytes.size} bytes; source checks passed"

end BN254GroupedFixture

def main : List String → IO Unit := BN254GroupedFixture.main
