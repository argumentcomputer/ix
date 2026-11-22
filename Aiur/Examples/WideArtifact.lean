import Aiur.Modules.Frontend
import Aiur.Artifact
import Aiur.Trace.Export
import Mathlib.Algebra.Field.Rat

/-! Cross-language transport fixture for the version-three artifact codec.
The compiler runs over Rat and every emitted coefficient must be integral;
the encoder stores its canonical residue under the BN254 scalar modulus.
This tests serialization of compiled structure, not execution or proving over
BN254, which requires a separate field backend and field instantiation. -/

open Aiur

namespace WideArtifactFixture

def modulus : Nat :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

def source : Modules.Program Nat := aiur_modules% "
module Wide {
  table inputs: (Field,) {
    (0,), (340282366920938463481821351505477763077,),
  }
  table outputs: Field {
    21888242871839275222246405745257275088548364400416034343698204186575808495616,
    340282366920938463481821351505477763077,
  }
  map lookup(x: Field) -> Field = inputs => outputs;
  fn guarded(x: Field) -> Field {
    let 21888242871839275222246405745257275088548364400416034343698204186575808495616 = x;
    x
  }
  fn choice(x: Field) -> Field {
    match x {
      340282366920938463481821351505477763077 => 0,
      _ => 21888242871839275222246405745257275088548364400416034343698204186575808495616,
    }
  }
  fn literal(x: Field) -> Field { x + 340282366920938463481821351505477763077 }
  fn run(x: Field) -> Field {
    let y = guarded(lookup(x));
    let pointer = &(choice(x), y);
    let (a, b) = *pointer;
    literal(x) + a + b
  }
}
"

private def encode (value : Rat) : Nat :=
  if value.den == 1 then (value.num % (modulus : Int)).toNat else 2 ^ 256

private def wide (value : Rat) : Bool := encode value ≥ 2 ^ 64

def main (args : List String) : IO Unit := do
  let prepared ← IO.ofExcept (Modules.prepare (source.toField Rat) ["Wide::run"])
  let exported ← IO.ofExcept prepared.exportExecution
  let instructions := exported.bytecode.functions.flatMap (·.code.toList)
  unless instructions.any (fun instruction => match instruction with
      | .literal _ value => wide value
      | _ => false) do
    throw (IO.userError "wide fixture has no multi-limb literal")
  unless instructions.any (fun instruction => match instruction with
      | .guard tests _ => tests.any (wide ∘ Prod.snd)
      | _ => false) do
    throw (IO.userError "wide fixture has no multi-limb guard")
  unless instructions.any (fun instruction => match instruction with
      | .branch tests _ => tests.any (wide ∘ Prod.snd)
      | _ => false) do
    throw (IO.userError "wide fixture has no multi-limb branch")
  unless exported.bytecode.tables.any (fun table => table.rows.any (·.any wide)) do
    throw (IO.userError "wide fixture has no multi-limb table cell")
  let compiled ← IO.ofExcept prepared.compileOptimized
  let (exported, trace) ← IO.ofExcept (Trace.exportPlanWide modulus encode
    compiled.circuit.inlined.program compiled.circuit.artifact exported)
  let bytes ← IO.ofExcept (Artifact.packageWide exported modulus encode (some trace))
  let path := args.headD "crates/aiur/tests/fixtures/bn254-wide.ixa"
  if args.contains "--check" then
    let expected ← IO.FS.readBinFile path
    unless expected.data == bytes.data do
      throw (IO.userError "wide artifact fixture differs from its Lean export")
  else
    Artifact.write path bytes
  IO.println s!"wide artifact transport fixture: {bytes.size} bytes"

end WideArtifactFixture

def main : List String → IO Unit := WideArtifactFixture.main
