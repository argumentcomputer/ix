import Aiur.Library.Field.Goldilocks.Emulated
import Aiur.Artifact
import Aiur.Trace.Export

/-! Compiled arithmetic and canonical-encoding boundary for Goldilocks
emulated in BN254 Fr. The trace accompanies the bytecode so the same library
can be checked by the interpreter and the generic proving adapter. -/
namespace EmulatedGoldilocksFixture
open Aiur

abbrev F := Library.Field.BN254.F
abbrev modulus := Library.Field.BN254.modulus

def dependencies : Modules.Program Nat :=
  Library.U8.templates.append Library.Field.declarations
    |>.append Library.Field.Goldilocks.Emulated.declarations

def client : Modules.Program Nat := aiur_library% dependencies ⟦
module EmulatedGL {
  inline fn bytes(raw: [Field; 8]) -> [UInt8::U8; 8] {
    let (b0, b1) = UInt8::from_fields(raw[0], raw[1]);
    let (b2, b3) = UInt8::from_fields(raw[2], raw[3]);
    let (b4, b5) = UInt8::from_fields(raw[4], raw[5]);
    let (b6, b7) = UInt8::from_fields(raw[6], raw[7]);
    [b0, b1, b2, b3, b4, b5, b6, b7]
  }
  fn add(a: Field, b: Field) -> Field { Goldilocks::gl_add(a, b) }
  fn sub(a: Field, b: Field) -> Field { Goldilocks::gl_sub(a, b) }
  fn mul(a: Field, b: Field) -> Field { Goldilocks::gl_mul(a, b) }
  fn neg(a: Field) -> Field { Goldilocks::gl_neg(a) }
  fn inverse(a: Field) -> Field { Goldilocks::gl_inverse(a) }
  fn eq(a: Field, b: Field) -> Field { Goldilocks::gl_eq(a, b) }
  fn is_zero(a: Field) -> Field { Goldilocks::gl_is_zero(a) }
  fn reduce(raw: [Field; 8]) -> Field { Goldilocks::gl_val(bytes(raw)) }
  fn decode(raw: [Field; 8]) -> Field { Goldilocks::gl_from_bytes(bytes(raw)) }
  fn encode(a: Field) -> [Field; 8] {
    let b = Goldilocks::gl_to_bytes(a);
    [UInt8::to_field(b[0]), UInt8::to_field(b[1]), UInt8::to_field(b[2]), UInt8::to_field(b[3]),
     UInt8::to_field(b[4]), UInt8::to_field(b[5]), UInt8::to_field(b[6]), UInt8::to_field(b[7])]
  }
  fn extension_mul(a: [Field; 2], b: [Field; 2]) -> [Field; 2] {
    Goldilocks::eg_mul(a, b)
  }
  fn extension_inverse(a: [Field; 2]) -> [Field; 2] { Goldilocks::eg_inverse(a) }
}
⟧

def entries : List String :=
  ["add", "sub", "mul", "neg", "inverse", "eq", "is_zero", "reduce", "decode",
    "encode", "extension_mul", "extension_inverse"].map ("EmulatedGL::" ++ ·)

def program : Modules.Program F :=
  Library.U8.source.append Library.Field.declarations
    |>.append Library.Field.Goldilocks.Emulated.declarations
    |>.append client |>.toField F

def main (args : List String) : IO Unit := do
  let prepared ← IO.ofExcept (Modules.prepare program entries)
  let exported ← IO.ofExcept prepared.exportExecution
  let compiled ← IO.ofExcept prepared.compileOptimized
  let (exported, trace) ← IO.ofExcept (Trace.exportPlanWide modulus ZMod.val
    compiled.circuit.inlined.program compiled.circuit.artifact exported)
  let bytes ← IO.ofExcept (Artifact.packageWide exported modulus ZMod.val (some trace))
  let path := args.headD "crates/aiur/tests/fixtures/goldilocks-emulated.ixa"
  if args.contains "--check" then
    let expected ← IO.FS.readBinFile path
    unless bytes.data == expected.data do
      throw (IO.userError "emulated Goldilocks fixture differs from its Lean export")
  else
    Artifact.write path bytes
  IO.println s!"emulated Goldilocks fixture: {bytes.size} bytes"

end EmulatedGoldilocksFixture

def main : List String → IO Unit := EmulatedGoldilocksFixture.main
