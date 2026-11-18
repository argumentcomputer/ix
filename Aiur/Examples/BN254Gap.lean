import Aiur.Library.Field.BN254
import Aiur.Modules.Frontend
import Aiur.Artifact
import Aiur.Trace.Export

/-! Unequal recursive subcalls over BN254 require depth gaps and both of the
production exporter's range tables. The public recursive entry also carries
its authenticated depth word. -/

namespace BN254GapFixture
open Aiur

abbrev F := Library.Field.BN254.F
abbrev modulus := Library.Field.BN254.modulus

def source : Modules.Program Nat := aiur⟦
module BN254Gap {
  fn fib(n: Field) -> Field {
    match n { 0 => 0, 1 => 1, _ => fib(n - 1) + fib(n - 2) }
  }
  fn run(n: Field, x: Field) -> Field { fib(n) + x }
}
⟧

def main (args : List String) : IO Unit := do
  let prepared ← IO.ofExcept (Modules.prepare (source.toField F)
    ["BN254Gap::run", "BN254Gap::fib"])
  for (n, x, expected) in [(0, (-1 : F), (-1 : F)), (6, -1, 7), (7, 0, 13)] do
    let (actual, _) ← IO.ofExcept (prepared.run "BN254Gap::run" [.field n, .field x])
    unless actual == .field expected do
      throw (IO.userError "BN254 gap source evaluator disagrees")
  let exported ← IO.ofExcept prepared.exportExecution
  let compiled ← IO.ofExcept prepared.compileOptimized
  let physical ← IO.ofExcept (Optimized.Physical.prepare compiled.circuit.artifact)
  let cfg ← IO.ofExcept (Trace.depthConfig modulus physical)
  unless cfg.plans.any (fun (_, plan) => plan.slots.contains .gap) && cfg.limbs == [16, 8] do
    throw (IO.userError "BN254 gap fixture requires gap slots and both production range tables")
  let (exported, trace) ← IO.ofExcept (Trace.exportPlanWide modulus ZMod.val
    compiled.circuit.inlined.program compiled.circuit.artifact exported)
  let bytes ← IO.ofExcept (Artifact.packageWide exported modulus ZMod.val (some trace))
  let path := args.headD "crates/aiur/tests/fixtures/bn254-gap.ixa"
  if args.contains "--check" then
    let expected ← IO.FS.readBinFile path
    unless bytes.data == expected.data do
      throw (IO.userError "BN254 gap fixture differs from its Lean export")
  else
    Artifact.write path bytes
  IO.println s!"BN254 gap fixture: {bytes.size} bytes; source checks passed"

end BN254GapFixture

def main : List String → IO Unit := BN254GapFixture.main
