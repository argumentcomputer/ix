import Aiur.Library.Field.BN254.G1Encoding
import Aiur.Modules.Frontend
import Aiur.Artifact
import Aiur.Trace.Export

namespace BN254G1EncodingFixture
open Aiur
open Library.Field.BN254

def source : Modules.Program Nat := aiur_library% (G1Encoding.dependencies.append G1Encoding.declarations) ⟦
module G1EncodingTest {
  fn pack(a:[Field;9],b:[Field;9])->[Field;4] {
    BN254G1Encoding::to_chunks(BN254G1::from_raw(a),BN254G1::from_raw(b))
  }
  fn unpack(chunks:[Field;4])->[Field;18] {
    let points=BN254G1Encoding::from_chunks(chunks);
    let a=BN254G1::to_raw(points.0);let b=BN254G1::to_raw(points.1);
    [a[0],a[1],a[2],a[3],a[4],a[5],a[6],a[7],a[8],b[0],b[1],b[2],b[3],b[4],b[5],b[6],b[7],b[8]]
  }
  fn chunk(value:Field)->[Field;16] { BN254G1Encoding::chunk_bytes(value) }
}
⟧

def main (args : List String) : IO Unit := do
  let program := G1Encoding.program.append (source.toField Library.Field.BN254.F)
  let prepared ← IO.ofExcept (Modules.prepare program ["G1EncodingTest::pack","G1EncodingTest::unpack","G1EncodingTest::chunk"])
  let exported ← IO.ofExcept prepared.exportExecution
  let compiled ← IO.ofExcept prepared.compileOptimized
  let (exported, trace) ← IO.ofExcept (Trace.exportPlanWide Library.Field.BN254.modulus ZMod.val
    compiled.circuit.inlined.program compiled.circuit.artifact exported)
  let bytes ← IO.ofExcept (Artifact.packageWide exported Library.Field.BN254.modulus ZMod.val (some trace))
  let path := args.headD "crates/aiur/tests/fixtures/bn254-g1-encoding.ixa"
  if args.contains "--check" then
    let expected ← IO.FS.readBinFile path
    unless bytes.data == expected.data do throw (IO.userError "G1 chunk fixture differs from Lean export")
  else Artifact.write path bytes
  IO.println s!"G1 chunk fixture: {bytes.size} bytes"

end BN254G1EncodingFixture

def main : List String → IO Unit := BN254G1EncodingFixture.main
