import Aiur.Library.Field.BN254.G1
import Aiur.Modules.Frontend
import Aiur.Artifact
import Aiur.Trace.Export

/-! Compiled G1 arithmetic, canonical scalar decomposition and transcript
encoding fixtures. Public inputs use checked raw representations; no opaque
curve value can enter the program without its constructor constraints. -/
namespace BN254G1Fixture
open Aiur

def source : Modules.Program Nat := aiur_library% (Library.Field.BN254.G1.dependencies.append
    Library.Field.BN254.G1.declarations) ⟦
module G1Test {
  fn valid(a: [Field; 9]) -> [Field; 9] { BN254G1::to_raw(BN254G1::from_raw(a)) }
  fn add(a: [Field; 9], b: [Field; 9]) -> [Field; 9] {
    BN254G1::to_raw(BN254G1::add(BN254G1::from_raw(a), BN254G1::from_raw(b)))
  }
  fn double(a: [Field; 9]) -> [Field; 9] { BN254G1::to_raw(BN254G1::double(BN254G1::from_raw(a))) }
  fn neg(a: [Field; 9]) -> [Field; 9] { BN254G1::to_raw(BN254G1::neg(BN254G1::from_raw(a))) }
  fn mul(a: [Field; 9], scalar: Field) -> [Field; 9] {
    BN254G1::to_raw(BN254G1::mul(BN254G1::from_raw(a), scalar))
  }
  fn msm2(a: [Field; 9], s: Field, b: [Field; 9], t: Field) -> [Field; 9] {
    let tail = &(Lists::Node::Nil);
    let tail = &(Lists::Node::Cons((BN254G1::from_raw(b), t), tail));
    let terms = &(Lists::Node::Cons((BN254G1::from_raw(a), s), tail));
    BN254G1::to_raw(BN254G1::msm(terms))
  }
  fn encode(a: [Field; 9]) -> [Field; 32] { BN254G1::to_bytes(BN254G1::from_raw(a)) }
  fn decode(a: [Field; 32]) -> [Field; 9] { BN254G1::to_raw(BN254G1::from_bytes(a)) }
  fn scalar(a: Field) -> [Field; 4] { BN254G1::scalar_limbs(a) }
  fn commitment2(a: [Field; 9], b: [Field; 9]) -> [Field; 88] {
    let first = &(Lists::Node::Cons(BN254G1::from_raw(a), &(Lists::Node::Nil)));
    let second = &(Lists::Node::Cons(BN254G1::from_raw(b), &(Lists::Node::Nil)));
    let rows = &(Lists::Node::Cons(first, &(Lists::Node::Cons(second, &(Lists::Node::Nil)))));
    let bytes = BN254G1::commitment_bytes(rows);
    [Lists::lookup(bytes, 0), Lists::lookup(bytes, 1), Lists::lookup(bytes, 2), Lists::lookup(bytes, 3), Lists::lookup(bytes, 4), Lists::lookup(bytes, 5), Lists::lookup(bytes, 6), Lists::lookup(bytes, 7), Lists::lookup(bytes, 8), Lists::lookup(bytes, 9), Lists::lookup(bytes, 10), Lists::lookup(bytes, 11), Lists::lookup(bytes, 12), Lists::lookup(bytes, 13), Lists::lookup(bytes, 14), Lists::lookup(bytes, 15), Lists::lookup(bytes, 16), Lists::lookup(bytes, 17), Lists::lookup(bytes, 18), Lists::lookup(bytes, 19), Lists::lookup(bytes, 20), Lists::lookup(bytes, 21), Lists::lookup(bytes, 22), Lists::lookup(bytes, 23), Lists::lookup(bytes, 24), Lists::lookup(bytes, 25), Lists::lookup(bytes, 26), Lists::lookup(bytes, 27), Lists::lookup(bytes, 28), Lists::lookup(bytes, 29), Lists::lookup(bytes, 30), Lists::lookup(bytes, 31), Lists::lookup(bytes, 32), Lists::lookup(bytes, 33), Lists::lookup(bytes, 34), Lists::lookup(bytes, 35), Lists::lookup(bytes, 36), Lists::lookup(bytes, 37), Lists::lookup(bytes, 38), Lists::lookup(bytes, 39), Lists::lookup(bytes, 40), Lists::lookup(bytes, 41), Lists::lookup(bytes, 42), Lists::lookup(bytes, 43), Lists::lookup(bytes, 44), Lists::lookup(bytes, 45), Lists::lookup(bytes, 46), Lists::lookup(bytes, 47), Lists::lookup(bytes, 48), Lists::lookup(bytes, 49), Lists::lookup(bytes, 50), Lists::lookup(bytes, 51), Lists::lookup(bytes, 52), Lists::lookup(bytes, 53), Lists::lookup(bytes, 54), Lists::lookup(bytes, 55), Lists::lookup(bytes, 56), Lists::lookup(bytes, 57), Lists::lookup(bytes, 58), Lists::lookup(bytes, 59), Lists::lookup(bytes, 60), Lists::lookup(bytes, 61), Lists::lookup(bytes, 62), Lists::lookup(bytes, 63), Lists::lookup(bytes, 64), Lists::lookup(bytes, 65), Lists::lookup(bytes, 66), Lists::lookup(bytes, 67), Lists::lookup(bytes, 68), Lists::lookup(bytes, 69), Lists::lookup(bytes, 70), Lists::lookup(bytes, 71), Lists::lookup(bytes, 72), Lists::lookup(bytes, 73), Lists::lookup(bytes, 74), Lists::lookup(bytes, 75), Lists::lookup(bytes, 76), Lists::lookup(bytes, 77), Lists::lookup(bytes, 78), Lists::lookup(bytes, 79), Lists::lookup(bytes, 80), Lists::lookup(bytes, 81), Lists::lookup(bytes, 82), Lists::lookup(bytes, 83), Lists::lookup(bytes, 84), Lists::lookup(bytes, 85), Lists::lookup(bytes, 86), Lists::lookup(bytes, 87)]
  }
}
⟧

def entries : List String := ["G1Test::valid", "G1Test::add", "G1Test::double", "G1Test::neg",
  "G1Test::mul", "G1Test::msm2", "G1Test::encode", "G1Test::decode", "G1Test::scalar", "G1Test::commitment2"]

def main (args : List String) : IO Unit := do
  let program := Library.Field.BN254.G1.program.append (source.toField Library.Field.BN254.F)
  let prepared ← IO.ofExcept (Modules.prepare program entries)
  let exported ← IO.ofExcept prepared.exportExecution
  let (exported, trace) ← Trace.exportPlanParallelWide Library.Field.BN254.modulus ZMod.val
    prepared.environment.source prepared.entries exported
  let bytes ← IO.ofExcept (Artifact.packageWide exported Library.Field.BN254.modulus ZMod.val (some trace))
  let path := args.headD "crates/aiur/tests/fixtures/bn254-g1.ixa"
  if args.contains "--check" then
    let expected ← IO.FS.readBinFile path
    unless bytes.data == expected.data do
      throw (IO.userError "BN254 G1 fixture differs from its Lean export")
  else
    Artifact.write path bytes
  IO.println s!"BN254 G1 fixture: {bytes.size} bytes"

end BN254G1Fixture

def main : List String → IO Unit := BN254G1Fixture.main
