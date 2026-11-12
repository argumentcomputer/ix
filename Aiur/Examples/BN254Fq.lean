import Aiur.Library.Field.BN254.Fq
import Aiur.Modules.Frontend
import Aiur.Artifact
import Aiur.Trace.Export

/-! Compiler artifacts for canonical BN254 Fq arithmetic and bounded advice.
The Rust tests supply native advice and compare results with arkworks Fq. -/
namespace BN254FqFixture
open Aiur

def entries : List String := ["FqTest::canonical", "FqTest::add", "FqTest::sub",
  "FqTest::mul", "FqTest::inverse", "FqTest::range80", "FqTest::range84"]

def source : Modules.Program Nat := aiur_library% (Library.Field.BN254.Fq.dependencies.append
    Library.Field.BN254.Fq.declarations) ⟦
module FqTest {
  fn canonical(a: [Field; 4]) -> [Field; 4] { BN254Fq::to_limbs(BN254Fq::from_limbs(a)) }
  fn add(a: [Field; 4], b: [Field; 4]) -> [Field; 4] {
    BN254Fq::to_limbs(BN254Fq::add(BN254Fq::from_limbs(a), BN254Fq::from_limbs(b)))
  }
  fn sub(a: [Field; 4], b: [Field; 4]) -> [Field; 4] {
    BN254Fq::to_limbs(BN254Fq::sub(BN254Fq::from_limbs(a), BN254Fq::from_limbs(b)))
  }
  fn mul(a: [Field; 4], b: [Field; 4]) -> [Field; 4] {
    BN254Fq::to_limbs(BN254Fq::mul(BN254Fq::from_limbs(a), BN254Fq::from_limbs(b)))
  }
  fn inverse(a: [Field; 4]) -> [Field; 4] {
    BN254Fq::to_limbs(BN254Fq::inverse(BN254Fq::from_limbs(a)))
  }
  fn range80(a: Field) -> () { BN254Fq::range80(a) }
  fn range84(a: Field) -> () { BN254Fq::range84(a) }
}
⟧

def main (args : List String) : IO Unit := do
  let program := Library.Field.BN254.Fq.program.append (source.toField Library.Field.BN254.F)
  let prepared ← IO.ofExcept (Modules.prepare program entries)
  let exported ← IO.ofExcept prepared.exportExecution
  let compiled ← IO.ofExcept prepared.compileOptimized
  let (exported, trace) ← IO.ofExcept (Trace.exportPlanWide Library.Field.BN254.modulus ZMod.val
    compiled.circuit.inlined.program compiled.circuit.artifact exported)
  let bytes ← IO.ofExcept (Artifact.packageWide exported Library.Field.BN254.modulus ZMod.val (some trace))
  let path := args.headD "crates/aiur/tests/fixtures/bn254-fq.ixa"
  if args.contains "--check" then
    let expected ← IO.FS.readBinFile path
    unless bytes.data == expected.data do
      throw (IO.userError "BN254 Fq fixture differs from its Lean export")
  else
    Artifact.write path bytes
  IO.println s!"BN254 Fq fixture: {bytes.size} bytes"

end BN254FqFixture

def main : List String → IO Unit := BN254FqFixture.main
