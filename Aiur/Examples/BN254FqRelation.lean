import Aiur.Library.Field.BN254.FqRelation
import Aiur.Modules.Frontend
import Aiur.Artifact
import Aiur.Trace.Export

namespace BN254FqRelationFixture
open Aiur

def entries : List String := ["FqRelationTest::product", "FqRelationTest::double_slope",
  "FqRelationTest::add_slope", "FqRelationTest::x_coordinate", "FqRelationTest::y_coordinate",
  "FqRelationTest::curve", "FqRelationTest::max_weight", "FqRelationTest::negative_weight",
  "FqRelationTest::cancel", "FqRelationTest::constant", "FqRelationTest::product_overflow",
  "FqRelationTest::linear_overflow", "FqRelationTest::constant_overflow",
  "FqRelationTest::range17", "FqRelationTest::range89"]

def source : Modules.Program Nat := aiur_library% (Library.Field.BN254.FqRelation.dependencies.append
    Library.Field.BN254.FqRelation.declarations) ⟦
module FqRelationTest {

  fn product(a: [Field; 4], b: [Field; 4], result: [Field; 4]) -> () {
    let a = BN254Fq::from_limbs(a); let b = BN254Fq::from_limbs(b);
    let result = BN254Fq::from_limbs(result);
    BN254FqRelation::assert_zero(BN254FqRelation::sub(BN254FqRelation::product(a, b), BN254FqRelation::linear(result)))
  }

  fn double_slope(x: [Field; 4], y: [Field; 4], slope: [Field; 4]) -> () {
    let x = BN254Fq::from_limbs(x); let y = BN254Fq::from_limbs(y);
    let slope = BN254Fq::from_limbs(slope);
    BN254FqRelation::assert_zero(BN254FqRelation::sub(BN254FqRelation::twice(BN254FqRelation::product(y, slope)), BN254FqRelation::thrice(BN254FqRelation::product(x, x))))
  }

  fn add_slope(xa: [Field; 4], ya: [Field; 4], xb: [Field; 4], yb: [Field; 4], slope: [Field; 4]) -> () {
    let xa = BN254Fq::from_limbs(xa); let ya = BN254Fq::from_limbs(ya);
    let xb = BN254Fq::from_limbs(xb); let yb = BN254Fq::from_limbs(yb);
    let slope = BN254Fq::from_limbs(slope);
    let products = BN254FqRelation::sub(BN254FqRelation::product(slope, xb), BN254FqRelation::product(slope, xa));
    BN254FqRelation::assert_zero(BN254FqRelation::add(products, BN254FqRelation::sub(BN254FqRelation::linear(ya), BN254FqRelation::linear(yb))))
  }

  fn x_coordinate(slope: [Field; 4], xa: [Field; 4], xb: [Field; 4], result: [Field; 4]) -> () {
    let slope = BN254Fq::from_limbs(slope); let xa = BN254Fq::from_limbs(xa);
    let xb = BN254Fq::from_limbs(xb); let result = BN254Fq::from_limbs(result);
    let linear = BN254FqRelation::add(BN254FqRelation::add(BN254FqRelation::linear(xa), BN254FqRelation::linear(xb)), BN254FqRelation::linear(result));
    BN254FqRelation::assert_zero(BN254FqRelation::sub(BN254FqRelation::product(slope, slope), linear))
  }

  fn y_coordinate(slope: [Field; 4], xa: [Field; 4], xc: [Field; 4], ya: [Field; 4], result: [Field; 4]) -> () {
    let slope = BN254Fq::from_limbs(slope); let xa = BN254Fq::from_limbs(xa);
    let xc = BN254Fq::from_limbs(xc); let ya = BN254Fq::from_limbs(ya);
    let result = BN254Fq::from_limbs(result);
    let products = BN254FqRelation::sub(BN254FqRelation::product(slope, xa), BN254FqRelation::product(slope, xc));
    BN254FqRelation::assert_zero(BN254FqRelation::sub(products, BN254FqRelation::add(BN254FqRelation::linear(ya), BN254FqRelation::linear(result))))
  }

  fn curve(x: [Field; 4], xx: [Field; 4], y: [Field; 4]) -> () {
    let x = BN254Fq::from_limbs(x); let xx = BN254Fq::from_limbs(xx);
    let y = BN254Fq::from_limbs(y);
    BN254FqRelation::assert_zero(BN254FqRelation::sub(BN254FqRelation::product(x, x), BN254FqRelation::linear(xx)));
    BN254FqRelation::assert_zero(BN254FqRelation::add(BN254FqRelation::sub(BN254FqRelation::product(xx, x), BN254FqRelation::product(y, y)), BN254FqRelation::constant(3)))
  }

  fn max_weight(x: [Field; 4], residue: [Field; 4]) -> () {
    let x = BN254Fq::from_limbs(x); let residue = BN254Fq::from_limbs(residue);
    let expression = BN254FqRelation::add(BN254FqRelation::thrice(BN254FqRelation::product(x, x)), BN254FqRelation::thrice(BN254FqRelation::linear(x)));
    BN254FqRelation::assert_zero(BN254FqRelation::sub(BN254FqRelation::add(expression, BN254FqRelation::constant(4)), BN254FqRelation::linear(residue)))
  }

  fn negative_weight(x: [Field; 4], residue: [Field; 4]) -> () {
    let x = BN254Fq::from_limbs(x); let residue = BN254Fq::from_limbs(residue);
    let expression = BN254FqRelation::add(BN254FqRelation::thrice(BN254FqRelation::product(x, x)), BN254FqRelation::thrice(BN254FqRelation::linear(x)));
    BN254FqRelation::assert_zero(BN254FqRelation::sub(BN254FqRelation::linear(residue), BN254FqRelation::add(expression, BN254FqRelation::constant(4))))
  }

  fn cancel(x: [Field; 4]) -> () {
    let x = BN254Fq::from_limbs(x);
    let expression = BN254FqRelation::add(BN254FqRelation::thrice(BN254FqRelation::product(x, x)), BN254FqRelation::thrice(BN254FqRelation::linear(x)));
    let expression = BN254FqRelation::add(expression, BN254FqRelation::constant(4));
    BN254FqRelation::assert_zero(BN254FqRelation::sub(expression, expression))
  }

  fn constant(value: Field) -> () {
    BN254FqRelation::assert_zero(BN254FqRelation::sub(BN254FqRelation::constant(value), BN254FqRelation::constant(value)))
  }

  fn product_overflow(x: [Field; 4]) -> () {
    let x = BN254Fq::from_limbs(x);
    BN254FqRelation::assert_zero(BN254FqRelation::twice(BN254FqRelation::twice(BN254FqRelation::product(x, x))))
  }

  fn linear_overflow(x: [Field; 4]) -> () {
    BN254FqRelation::assert_zero(BN254FqRelation::twice(BN254FqRelation::twice(BN254FqRelation::linear(BN254Fq::from_limbs(x)))))
  }

  fn constant_overflow(value: Field) -> () {
    let expression = BN254FqRelation::add(BN254FqRelation::constant(value), BN254FqRelation::constant(value));
    BN254FqRelation::assert_zero(BN254FqRelation::sub(expression, expression))
  }

  fn range17(value: Field) -> () { BN254FqRelation::range17(value) }
  fn range89(value: Field) -> () { BN254FqRelation::range89(value) }
}
⟧

def main (args : List String) : IO Unit := do
  let program := Library.Field.BN254.FqRelation.program.append (source.toField Library.Field.BN254.F)
  let prepared ← IO.ofExcept (Modules.prepare program entries)
  let exported ← IO.ofExcept prepared.exportExecution
  let compiled ← IO.ofExcept prepared.compileOptimized
  let (exported, trace) ← IO.ofExcept (Trace.exportPlanWide Library.Field.BN254.modulus ZMod.val
    compiled.circuit.inlined.program compiled.circuit.artifact exported)
  let bytes ← IO.ofExcept (Artifact.packageWide exported Library.Field.BN254.modulus ZMod.val (some trace))
  let path := args.headD "crates/aiur/tests/fixtures/bn254-fq-relation.ixa"
  if args.contains "--check" then
    let expected ← IO.FS.readBinFile path
    unless bytes.data == expected.data do
      throw (IO.userError "BN254 Fq relation fixture differs from its Lean export")
  else
    Artifact.write path bytes
  IO.println s!"BN254 Fq relation fixture: {bytes.size} bytes"

end BN254FqRelationFixture

def main : List String → IO Unit := BN254FqRelationFixture.main
