import Aiur.Library.Field.BN254
import Aiur.Modules.Frontend
import Aiur.Artifact

/-! A compiled BN254 scalar-field program for the interpreter boundary.
The source evaluator and exported bytecode use the same proved `ZMod` field.
No trace or proof is produced by this fixture. -/

namespace BN254ExecutionFixture
open Aiur

abbrev F := Library.Field.BN254.F
abbrev modulus := Library.Field.BN254.modulus

def source : Modules.Program Nat := aiur⟦
module BN254 {
  table inputs: (Field,) {
    (0,), (21888242871839275222246405745257275088548364400416034343698204186575808495616,),
  }
  table outputs: Field {
    21888242871839275222246405745257275088548364400416034343698204186575808495616,
    7,
  }
  map lookup(x: Field) -> Field = inputs => outputs;

  fn add_one(x: Field) -> Field { x + 1 }
  fn inverse(x: Field) -> Field { 1 / x }
  fn minus_one() -> Field { 0 - 1 }
  fn literal_minus_one() -> Field {
    21888242871839275222246405745257275088548364400416034343698204186575808495616
  }
  fn choice(x: Field) -> Field {
    match x {
      0 => 21888242871839275222246405745257275088548364400416034343698204186575808495616,
      21888242871839275222246405745257275088548364400416034343698204186575808495616 => 1,
      _ => x,
    }
  }
  fn guarded(x: Field) -> Field {
    let 21888242871839275222246405745257275088548364400416034343698204186575808495616 = x;
    x
  }
  fn table(x: Field) -> Field { lookup(x) }
  fn memory_roundtrip(x: Field) -> Field {
    let pointer = &(x, 21888242871839275222246405745257275088548364400416034343698204186575808495616);
    let (a, b) = *pointer;
    a + b
  }
}
⟧

def entries : List String :=
  ["add_one", "inverse", "minus_one", "literal_minus_one", "choice", "guarded",
    "table", "memory_roundtrip"].map ("BN254::" ++ ·)

def main (args : List String) : IO Unit := do
  let prepared ← IO.ofExcept (Modules.prepare (source.toField F) entries)
  let expect (name : String) (args : List F) (expected : F) : IO Unit := do
    let (actual, _) ← IO.ofExcept (prepared.run ("BN254::" ++ name) (args.map .field))
    unless actual == .field expected do
      throw (IO.userError s!"BN254 source evaluator disagrees for {name}")
  expect "add_one" [0] 1
  expect "add_one" [-1] 0
  expect "inverse" [7] (7 : F)⁻¹
  expect "inverse" [-1] (-1)
  expect "minus_one" [] (-1)
  expect "literal_minus_one" [] (-1)
  expect "choice" [0] (-1)
  expect "choice" [-1] 1
  expect "choice" [7] 7
  expect "guarded" [-1] (-1)
  expect "table" [0] (-1)
  expect "table" [-1] 7
  expect "memory_roundtrip" [0] (-1)
  expect "memory_roundtrip" [7] 6
  for (name, value) in [("inverse", (0 : F)), ("guarded", 0), ("table", 1)] do
    unless (prepared.run ("BN254::" ++ name) [.field value]).toOption.isNone do
      throw (IO.userError s!"BN254 source evaluator accepted invalid {name} input")
  let exported ← IO.ofExcept prepared.exportExecution
  let bytes ← IO.ofExcept (Artifact.packageWide exported modulus ZMod.val)
  let path := args.headD "crates/aiur/tests/fixtures/bn254-execution.ixa"
  if args.contains "--check" then
    let expected ← IO.FS.readBinFile path
    unless bytes.data == expected.data do
      throw (IO.userError "BN254 execution fixture differs from its Lean export")
  else
    Artifact.write path bytes
  IO.println s!"BN254 scalar-field execution fixture: {bytes.size} bytes; source checks passed"

end BN254ExecutionFixture

def main : List String → IO Unit := BN254ExecutionFixture.main
