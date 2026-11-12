import Aiur.Library.Field.BN254
import Aiur.Modules.Frontend
import Aiur.Artifact
import Aiur.Trace.Export

/-! Native BN254 execution and compiler trace fixture with recursion, fixed
maps and ROM. The entry's result is `x + n + lookup(x)` for natural `n` and
the two supported map keys. -/

namespace BN254TraceFixture
open Aiur

abbrev F := Library.Field.BN254.F
abbrev modulus := Library.Field.BN254.modulus

def source : Modules.Program Nat := aiur⟦
module BN254Trace {
  table inputs: (Field,) {
    (0,), (21888242871839275222246405745257275088548364400416034343698204186575808495616,),
  }
  table outputs: Field {
    21888242871839275222246405745257275088548364400416034343698204186575808495616,
    7,
  }
  map lookup(x: Field) -> Field = inputs => outputs;

  fn walk(n: Field, x: Field) -> Field {
    match n {
      0 => x,
      _ => walk(n - 1, x + 1),
    }
  }
  fn run(n: Field, x: Field) -> Field {
    let y = walk(n, x);
    let z = lookup(x);
    let pointer = &(y, z);
    let (a, b) = *pointer;
    a + b
  }
}
⟧

def main (args : List String) : IO Unit := do
  let prepared ← IO.ofExcept (Modules.prepare (source.toField F) ["BN254Trace::run"])
  for (n, x, expected) in [(0, (0 : F), (-1 : F)), (3, -1, 9), (5, 0, 4)] do
    let (actual, _) ← IO.ofExcept (prepared.run "BN254Trace::run" [.field n, .field x])
    unless actual == .field expected do
      throw (IO.userError "BN254 trace source evaluator disagrees")
  let exported ← IO.ofExcept prepared.exportExecution
  let compiled ← IO.ofExcept prepared.compileOptimized
  let (exported, trace) ← IO.ofExcept (Trace.exportPlanWide modulus ZMod.val
    compiled.circuit.inlined.program compiled.circuit.artifact exported)
  let bytes ← IO.ofExcept (Artifact.packageWide exported modulus ZMod.val (some trace))
  let path := args.headD "crates/aiur/tests/fixtures/bn254-trace.ixa"
  if args.contains "--check" then
    let expected ← IO.FS.readBinFile path
    unless bytes.data == expected.data do
      throw (IO.userError "BN254 trace fixture differs from its Lean export")
  else
    Artifact.write path bytes
  IO.println s!"BN254 trace fixture: {bytes.size} bytes; source checks passed"

end BN254TraceFixture

def main : List String → IO Unit := BN254TraceFixture.main
