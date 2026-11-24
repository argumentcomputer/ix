import Aiur.Library.Field.BN254.Pairing.FqProducts
import Aiur.Modules.Frontend
import Aiur.Artifact
import Aiur.Trace.Export

namespace BN254FqProductsFixture
open Aiur
open Library.Field.BN254

def source : Modules.Program Nat := aiur_library% (Pairing.FqProducts.dependencies.append Pairing.FqProducts.declarations) ⟦
module FqProductsTest {
  fn products(a:[Field;4],b:[Field;4],c:[Field;4],d:[Field;4],subtract:Field)->[Field;4] {
    BN254Fq::to_limbs(BN254FqProducts::reduce(BN254Fq::from_limbs(a),BN254Fq::from_limbs(b),BN254Fq::from_limbs(c),BN254Fq::from_limbs(d),subtract))
  }
  fn range86(value:Field)->() { BN254FqProducts::range86(value) }
}
⟧

def main (args : List String) : IO Unit := do
  let program := Pairing.FqProducts.program.append (source.toField Library.Field.BN254.F)
  let prepared ← IO.ofExcept (Modules.prepare program ["FqProductsTest::products","FqProductsTest::range86"])
  let exported ← IO.ofExcept prepared.exportExecution
  let compiled ← IO.ofExcept prepared.compileOptimized
  let (exported, trace) ← IO.ofExcept (Trace.exportPlanWide Library.Field.BN254.modulus ZMod.val
    compiled.circuit.inlined.program compiled.circuit.artifact exported)
  let bytes ← IO.ofExcept (Artifact.packageWide exported Library.Field.BN254.modulus ZMod.val (some trace))
  let path := args.headD "crates/aiur/tests/fixtures/bn254-fq-products.ixa"
  if args.contains "--check" then
    let expected ← IO.FS.readBinFile path
    unless bytes.data == expected.data do throw (IO.userError "Fq products fixture differs from Lean export")
  else Artifact.write path bytes
  IO.println s!"Fq products fixture: {bytes.size} bytes"

end BN254FqProductsFixture

def main : List String → IO Unit := BN254FqProductsFixture.main
