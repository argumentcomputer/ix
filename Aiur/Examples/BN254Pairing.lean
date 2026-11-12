import Aiur.Library.Field.BN254.Pairing
import Aiur.Modules.Frontend
import Aiur.Artifact
import Aiur.Trace.Export

/-! Native BN254 tower and fixed-G2 pairing compiler regression artifacts. -/
namespace BN254PairingFixture
open Aiur
open Library.Field.BN254

def entries : List String := ["PairingTest::fp2_mul", "PairingTest::fp2_square", "PairingTest::fp2_inverse", "PairingTest::fp6_mul", "PairingTest::fp6_square", "PairingTest::fp6_inverse", "PairingTest::fp6_frobenius1", "PairingTest::fp6_frobenius2", "PairingTest::fp6_frobenius3", "PairingTest::fp12_mul", "PairingTest::fp12_square", "PairingTest::fp12_inverse", "PairingTest::fp12_frobenius1", "PairingTest::fp12_frobenius2", "PairingTest::fp12_frobenius3", "PairingTest::easy_final", "PairingTest::cyclotomic_square", "PairingTest::exp_neg_x", "PairingTest::final_exponentiation", "PairingTest::miller", "PairingTest::check", "PairingTest::check_chunks"]

def source : Modules.Program Nat := aiur_library% (Pairing.dependencies.append Pairing.signature) ⟦
module PairingTest {
  fn fp2_mul(a:[Field;8],b:[Field;8])->[Field;8] { BN254Fp2::to_raw(BN254Fp2::mul(BN254Fp2::from_raw(a),BN254Fp2::from_raw(b))) }
  fn fp2_square(a:[Field;8])->[Field;8] { BN254Fp2::to_raw(BN254Fp2::square(BN254Fp2::from_raw(a))) }
  fn fp2_inverse(a:[Field;8])->[Field;8] { BN254Fp2::to_raw(BN254Fp2::inverse(BN254Fp2::from_raw(a))) }
  fn fp6_mul(a:[Field;24],b:[Field;24])->[Field;24] { BN254Fp6::to_raw(BN254Fp6::mul(BN254Fp6::from_raw(a),BN254Fp6::from_raw(b))) }
  fn fp6_square(a:[Field;24])->[Field;24] { BN254Fp6::to_raw(BN254Fp6::square(BN254Fp6::from_raw(a))) }
  fn fp6_inverse(a:[Field;24])->[Field;24] { BN254Fp6::to_raw(BN254Fp6::inverse(BN254Fp6::from_raw(a))) }
  fn fp6_frobenius1(a:[Field;24])->[Field;24] { BN254Fp6::to_raw(BN254Fp6::frobenius1(BN254Fp6::from_raw(a))) }
  fn fp6_frobenius2(a:[Field;24])->[Field;24] { BN254Fp6::to_raw(BN254Fp6::frobenius2(BN254Fp6::from_raw(a))) }
  fn fp6_frobenius3(a:[Field;24])->[Field;24] { BN254Fp6::to_raw(BN254Fp6::frobenius3(BN254Fp6::from_raw(a))) }
  fn fp12_mul(a:[Field;48],b:[Field;48])->[Field;48] { BN254Fp12::to_raw(BN254Fp12::mul(BN254Fp12::from_raw(a),BN254Fp12::from_raw(b))) }
  fn fp12_square(a:[Field;48])->[Field;48] { BN254Fp12::to_raw(BN254Fp12::square(BN254Fp12::from_raw(a))) }
  fn fp12_inverse(a:[Field;48])->[Field;48] { BN254Fp12::to_raw(BN254Fp12::inverse(BN254Fp12::from_raw(a))) }
  fn fp12_frobenius1(a:[Field;48])->[Field;48] { BN254Fp12::to_raw(BN254Fp12::frobenius1(BN254Fp12::from_raw(a))) }
  fn fp12_frobenius2(a:[Field;48])->[Field;48] { BN254Fp12::to_raw(BN254Fp12::frobenius2(BN254Fp12::from_raw(a))) }
  fn fp12_frobenius3(a:[Field;48])->[Field;48] { BN254Fp12::to_raw(BN254Fp12::frobenius3(BN254Fp12::from_raw(a))) }
  fn easy_final(a:[Field;48])->[Field;48] { BN254Fp12::to_raw(BN254Fp12::easy_final(BN254Fp12::from_raw(a))) }
  fn cyclotomic_square(a:[Field;48])->[Field;48] { BN254Fp12::to_raw(BN254Fp12::cyclotomic_square(BN254Fp12::easy_final(BN254Fp12::from_raw(a)))) }
  fn exp_neg_x(a:[Field;48])->[Field;48] { BN254Fp12::to_raw(BN254Fp12::exp_neg_x(BN254Fp12::easy_final(BN254Fp12::from_raw(a)))) }
  fn final_exponentiation(a:[Field;48])->[Field;48] { BN254Fp12::to_raw(BN254Fp12::final_exponentiation(BN254Fp12::from_raw(a))) }
  fn miller(a:[Field;9],b:[Field;9])->[Field;48] { BN254Fp12::to_raw(BN254Pairing::miller(BN254G1::from_raw(a),BN254G1::from_raw(b))) }
  fn check(a:[Field;9],b:[Field;9])->() { BN254Pairing::check(BN254G1::from_raw(a),BN254G1::from_raw(b)) }
  fn check_chunks(chunks:[Field;4])->() { BN254Pairing::check_chunks(chunks) }
}
⟧

def main (args : List String) : IO Unit := do
  let linesPath := args.headD "crates/aiur/tests/fixtures/bn254-pairing-lines.txt"
  let text ← IO.FS.readFile linesPath
  let lines ← (text.splitOn "\n" |>.filter fun line => !line.isEmpty).mapM fun line =>
    (line.splitOn " ").mapM fun value => match value.toNat? with
      | some n => pure n
      | none => throw (IO.userError "invalid prepared-line field")
  let program ← IO.ofExcept (Pairing.program lines)
  let prepared ← IO.ofExcept (Modules.prepare (program.append (source.toField Library.Field.BN254.F)) entries)
  let exported ← IO.ofExcept prepared.exportExecution
  let compiled ← IO.ofExcept prepared.compileOptimized
  let (exported, trace) ← IO.ofExcept (Trace.exportPlanWide Library.Field.BN254.modulus ZMod.val
    compiled.circuit.inlined.program compiled.circuit.artifact exported)
  let bytes ← IO.ofExcept (Artifact.packageWide exported Library.Field.BN254.modulus ZMod.val (some trace))
  let path := args[1]?.getD "crates/aiur/tests/fixtures/bn254-pairing.ixa"
  if args.contains "--check" then
    let expected ← IO.FS.readBinFile path
    unless bytes.data == expected.data do throw (IO.userError "BN254 pairing fixture differs from its Lean export")
  else Artifact.write path bytes
  IO.println s!"BN254 pairing fixture: {bytes.size} bytes"

end BN254PairingFixture

def main : List String → IO Unit := BN254PairingFixture.main
