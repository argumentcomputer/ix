import Aiur.Library.Field.Goldilocks
import Aiur.Hints
import Aiur.Optimized.Program

namespace AiurGoldilocksTests
open Aiur

abbrev F := Library.U32.Goldilocks.F
abbrev modulus := Library.U32.Goldilocks.modulus

def library : Modules.Program Nat :=
  Library.Field.Goldilocks.dependencies.append Library.Field.Goldilocks.declarations

def client : Modules.Program Nat := aiur_library% library ⟦
module FieldClient {
  fn arithmetic(a: Field, b: Field) -> [Field; 6] {
    [Goldilocks::gl_add(a, b), Goldilocks::gl_sub(a, b),
     Goldilocks::gl_mul(a, b), Goldilocks::gl_neg(a),
     Goldilocks::gl_eq(a, b), Goldilocks::gl_is_zero(a)]
  }

  fn extension(a: [Field; 2], b: [Field; 2]) -> [Field; 2] {
    Goldilocks::eg_mul(a, b)
  }

  fn inverse(a: Field) -> Field { Goldilocks::gl_inverse(a) }

  fn extension_inverse(a: [Field; 2]) -> [Field; 2] {
    Goldilocks::eg_inverse(a)
  }

  fn decode(raw: [Field; 8]) -> Field {
    let (b0, b1) = UInt8::from_fields(raw[0], raw[1]);
    let (b2, b3) = UInt8::from_fields(raw[2], raw[3]);
    let (b4, b5) = UInt8::from_fields(raw[4], raw[5]);
    let (b6, b7) = UInt8::from_fields(raw[6], raw[7]);
    Goldilocks::gl_from_bytes([b0, b1, b2, b3, b4, b5, b6, b7])
  }

  fn roundtrip(a: Field) -> Field {
    Goldilocks::gl_from_bytes(Goldilocks::gl_to_bytes(a))
  }
}

module FieldAlgorithm<G: GoldilocksSignature> {
  fn run(a: G::Goldilocks, b: G::Goldilocks) -> G::Goldilocks {
    G::gl_mul(G::gl_add(a, b), G::gl_sub(a, b))
  }
}
module NativeFieldAlgorithm = FieldAlgorithm::<Goldilocks>;
⟧

run_cmd do
  let broken := { Library.Field.Goldilocks.declarations with
    modules := Library.Field.Goldilocks.declarations.modules.map fun module =>
      { module with body := match module.body with
        | .definitions definitions => .definitions { definitions with
            program.functions := definitions.program.functions.filter (·.name != "gl_mul") }
        | body => body } }
  unless (Modules.checkTemplates (Library.Field.Goldilocks.dependencies.append broken)).toOption.isNone do
    throwError "incomplete provider satisfied GoldilocksSignature"

private def fields (values : List F) : SourceValue F := .tuple (values.map .field)

private def bytes (value : Nat) : SourceValue F :=
  fields ((List.range 8).map fun i => ((value / 256 ^ i) % 256 : Nat))

private def hints : HintDispatcher F := fun channel key => match channel, key with
  | "goldilocks.inverse", .field value => .ok (.field value⁻¹)
  | "bytes_le", .field value =>
      .ok (.tuple ((List.range 8).map fun i => .field (((value.val / 256 ^ i) % 256 : Nat) : F)))
  | _, _ => .error .unavailable

private def directArithmetic : Modules.Program Nat := aiur⟦
module FieldClient {
  fn arithmetic(a: Field, b: Field) -> [Field; 6] {
    [a + b, a - b, a * b, 0 - a, Fields::is_zero(a - b), Fields::is_zero(a)]
  }
}
⟧

private def arithmeticCircuit (program : Modules.Program Nat) : IO (Circuit.System F) := do
  let prepared ← IO.ofExcept (Modules.prepare ((library.append program).toField F)
    ["FieldClient::arithmetic"])
  return (← IO.ofExcept prepared.compileOptimized).circuit.artifact.system

def run : IO Unit := do
  unless (← arithmeticCircuit client) == (← arithmeticCircuit directArithmetic) do
    throw (IO.userError "native Goldilocks interface changed optimized arithmetic constraints")
  let entries := ["arithmetic", "extension", "inverse", "extension_inverse", "decode", "roundtrip"]
  let source := Library.U8.source.append Library.Field.declarations
    |>.append Library.Field.Goldilocks.declarations |>.append client |>.toField F
  let prepared ← IO.ofExcept (Modules.prepare source
    ("NativeFieldAlgorithm::run" :: entries.map ("FieldClient::" ++ ·)))
  let provider := prepared.environment.source.checkedHints hints
  let expect (entry : String) (args : List (SourceValue F)) (expected : SourceValue F) := do
    let (actual, _) ← IO.ofExcept (prepared.run ("FieldClient::" ++ entry) args
      (fuel := 100000) (hints := provider))
    unless actual == expected do
      throw (IO.userError s!"Goldilocks {entry}: {repr actual} != {repr expected}")
  let cases : List F := [0, 1, 7, 2^32, modulus - 2, modulus - 1]
  let (generic, _) ← IO.ofExcept (prepared.run "NativeFieldAlgorithm::run" [.field 5, .field 7])
  unless generic == .field (-24 : F) do
    throw (IO.userError "native Goldilocks provider disagrees through its interface")
  for a in cases do
    expect "inverse" [.field a] (.field a⁻¹)
    expect "roundtrip" [.field a] (.field a)
    expect "decode" [bytes a.val] (.field a)
    for b in cases do
      expect "arithmetic" [.field a, .field b]
        (fields [a + b, a - b, a * b, -a, if a == b then 1 else 0, if a == 0 then 1 else 0])
  expect "extension" [fields [0, 1], fields [0, 1]] (fields [7, 0])
  expect "extension" [fields [3, 5], fields [7, 11]] (fields [406, 68])
  expect "extension_inverse" [fields [0, 0]] (fields [0, 0])
  expect "extension_inverse" [fields [0, 1]] (fields [0, (7 : F)⁻¹])
  for value in [modulus, modulus + 1, 2^64 - 1] do
    unless (prepared.run "FieldClient::decode" [bytes value] (hints := provider)).toOption.isNone do
      throw (IO.userError s!"noncanonical Goldilocks encoding accepted: {value}")
  unless (prepared.run "FieldClient::decode" [fields [256, 0, 0, 0, 0, 0, 0, 0]]
      (hints := provider)).toOption.isNone do
    throw (IO.userError "non-byte Goldilocks encoding accepted")
  for (value, advice) in [(0, 1), (1, 0), (7, 1)] do
    let dishonest := prepared.environment.source.checkedHints fun _ _ => .ok (.field advice)
    unless (prepared.run "FieldClient::inverse" [.field value] (hints := dishonest)).toOption.isNone do
      throw (IO.userError "dishonest Goldilocks inverse accepted")
  let aliasedZero := prepared.environment.source.checkedHints fun _ _ =>
    .ok (.tuple ((List.range 8).map fun i => .field (((modulus / 256 ^ i) % 256 : Nat) : F)))
  unless (prepared.run "FieldClient::roundtrip" [.field 0] (hints := aliasedZero)).toOption.isNone do
    throw (IO.userError "noncanonical zero encoding accepted from byte hint")
  IO.println "Passed native Goldilocks arithmetic, extension, canonical encoding and dishonest-inverse checks."

end AiurGoldilocksTests
