import Aiur.Library.U32.Correctness
import Aiur.Library.U32.Hints
import Mathlib.Algebra.Field.Rat

namespace AiurU32Tests
open Aiur

set_option maxRecDepth 10000
set_option maxHeartbeats 12000000

def client : Modules.Program Nat := aiur_library% Library.U32.templates r#"
module Words {
    fn byte(x: Field) -> Field { UInt8::to_field(UInt8::from_field(x)) }
    fn pack(raw: [Field; 4]) -> Field {
        UInt32::compact_field(UInt32::compact(UInt32::from_fields(raw)))
    }
    fn expand(value: Field) -> [Field; 4] {
        let word = UInt32::from_field(value);
        let bytes = UInt32::to_bytes(UInt32::expand(UInt32::compact(word)));
        [UInt8::to_field(bytes[0]), UInt8::to_field(bytes[1]),
         UInt8::to_field(bytes[2]), UInt8::to_field(bytes[3])]
    }
    fn add(a: [Field; 4], b: [Field; 4]) -> Field {
        UInt32::compact_field(UInt32::compact(UInt32::add(UInt32::from_fields(a), UInt32::from_fields(b))))
    }
    fn add3(a: [Field; 4], b: [Field; 4], c: [Field; 4]) -> Field {
        UInt32::compact_field(UInt32::compact(UInt32::add3(
            UInt32::from_fields(a), UInt32::from_fields(b), UInt32::from_fields(c))))
    }
    fn sub(a: [Field; 4], b: [Field; 4]) -> Field {
        UInt32::compact_field(UInt32::compact(UInt32::sub(UInt32::from_fields(a), UInt32::from_fields(b))))
    }
    fn lt(a: [Field; 4], b: [Field; 4]) -> Field {
        UInt32::less_than(UInt32::from_fields(a), UInt32::from_fields(b))
    }
    fn compact_lt(a: Field, b: Field) -> Field {
        UInt32::compact_less_than(UInt32::compact_from_field(a), UInt32::compact_from_field(b))
    }
    fn raw_lt(a: Field, b: Field) -> Field { UInt32::less_than_fields(a, b) }
    fn xor(a: [Field; 4], b: [Field; 4]) -> Field {
        UInt32::compact_field(UInt32::compact(UInt32::xor(UInt32::from_fields(a), UInt32::from_fields(b))))
    }
    fn and(a: [Field; 4], b: [Field; 4]) -> Field {
        UInt32::compact_field(UInt32::compact(UInt32::and(UInt32::from_fields(a), UInt32::from_fields(b))))
    }
    fn or(a: [Field; 4], b: [Field; 4]) -> Field {
        UInt32::compact_field(UInt32::compact(UInt32::or(UInt32::from_fields(a), UInt32::from_fields(b))))
    }
    fn rotr8(a: [Field; 4]) -> Field {
        UInt32::compact_field(UInt32::compact(UInt32::rotr8(UInt32::from_fields(a))))
    }
    fn rotr16(a: [Field; 4]) -> Field {
        UInt32::compact_field(UInt32::compact(UInt32::rotr16(UInt32::from_fields(a))))
    }
    fn xor_rotr7(a: [Field; 4], b: [Field; 4]) -> Field {
        UInt32::compact_field(UInt32::compact(UInt32::xor_rotr7(UInt32::from_fields(a), UInt32::from_fields(b))))
    }
    fn xor_rotr12(a: [Field; 4], b: [Field; 4]) -> Field {
        UInt32::compact_field(UInt32::compact(UInt32::xor_rotr12(UInt32::from_fields(a), UInt32::from_fields(b))))
    }
    fn overflow() -> Field {
        UInt32::compact_field(UInt32::compact(UInt32::add(UInt32::MAX, UInt32::ONE)))
    }
    fn overflow3() -> Field {
        UInt32::compact_field(UInt32::compact(UInt32::add3(UInt32::MAX, UInt32::MAX, UInt32::MAX)))
    }
    fn conversion() -> Field {
        UInt32::compact_field(UInt32::compact(UInt32::from_bytes(UInt32::to_bytes(UInt32::MAX))))
    }
}
"#

def entries : List String := client.modules.flatMap fun m => match m.body with
  | .definitions d => d.program.functions.map fun f => "Words::" ++ f.name
  | _ => []

def source : Modules.Program Nat := Library.U32.source.append client

run_cmd do
  let env ← Lean.getEnv
  for type in ["UInt8::U8", "UInt32::U32", "UInt32::Compact",
      "[UInt8::U8; 4]", "(Field, UInt32::U32)", "[UInt32::Compact; 0]"] do
    let .ok bad := Modules.Frontend.parse env
      s!"module Bad \{ fn run() -> {type} \{ hint::<{type}>(\"bad\", 0) } }" |
      throwError "invalid negative test syntax"
    unless (Modules.checkTemplates (Library.U32.templates.append bad)).toOption.isNone do
      throwError "hint fabricated an opaque value: {type}"

private def get {α : Type} : Except String α → IO α := IO.ofExcept

private def bytes (n : Nat) : SourceValue Rat :=
  .tuple ((List.range 4).map fun i => .field (((n / 256^i) % 256 : Nat) : Rat))

def run : IO Unit := do
  let prepared ← get <| Modules.prepare (source.toField Rat) entries
  let dispatcher := Library.U32.hints (fun (x : Rat) => x.num.toNat / x.den)
  let hints := prepared.environment.source.checkedHints dispatcher
  let expect (name : String) (args : List (SourceValue Rat)) (expected : SourceValue Rat) := do
    let (actual, _) ← get <| prepared.run ("Words::" ++ name) args (fuel := 100000) (hints := hints)
    unless actual == expected do throw (IO.userError s!"u32 {name}: {repr actual} != {repr expected}")
  let values := [0, 1, 255, 256, 65535, 65536, 2147483648, 4294967294, 4294967295]
  for a in values do
    expect "pack" [bytes a] (.field a)
    expect "expand" [.field a] (bytes a)
    for b in [0, 1, 4294967295] do
      expect "add" [bytes a, bytes b] (.field ((a+b)%Library.U32.base))
      expect "add3" [bytes a, bytes b, bytes b] (.field ((a+b+b)%Library.U32.base))
      expect "sub" [bytes a, bytes b] (.field ((a+Library.U32.base-b)%Library.U32.base))
      expect "lt" [bytes a, bytes b] (.field (if a < b then 1 else 0))
      expect "compact_lt" [.field a, .field b] (.field (if a < b then 1 else 0))
      expect "raw_lt" [.field a, .field b] (.field (if a < b then 1 else 0))
      expect "xor" [bytes a, bytes b] (.field (Nat.xor a b))
      expect "and" [bytes a, bytes b] (.field (Nat.land a b))
      expect "or" [bytes a, bytes b] (.field (Nat.lor a b))
      let x := Nat.xor a b
      expect "xor_rotr7" [bytes a, bytes b] (.field ((x / 128 + (x % 128) * 33554432 : Nat) : Rat))
      expect "xor_rotr12" [bytes a, bytes b] (.field ((x / 4096 + (x % 4096) * 1048576 : Nat) : Rat))
    expect "rotr8" [bytes a] (.field ((a / 256 + (a % 256) * 16777216 : Nat) : Rat))
    expect "rotr16" [bytes a] (.field ((a / 65536 + (a % 65536) * 65536 : Nat) : Rat))
  expect "overflow" [] 0
  expect "overflow3" [] 4294967293
  expect "conversion" [] 4294967295
  for (name, args) in [("byte", [.field 256]), ("byte", [.field (-1)]),
      ("pack", [.tuple [256, 0, 0, 0]]), ("expand", [.field 4294967296]),
      ("expand", [.field (-1)]), ("compact_lt", [.field 4294967296, .field 0]),
      ("raw_lt", [.field 4294967296, .field 0]), ("raw_lt", [.field 0, .field (-1)])] do
    unless (prepared.run ("Words::" ++ name) args (hints := hints)).toOption.isNone do
      throw (IO.userError s!"invalid u32 input accepted: {name}")
  for (name, answer) in [("overflow", [1, 0, 0, 0]),
      ("overflow", [256, 0, 0, 0]), ("overflow", [255, 255, 255, 255]),
      ("overflow3", [254, 255, 255, 255]), ("overflow3", [252, 255, 255, 255])] do
    let dishonest := prepared.environment.source.checkedHints fun _ _ =>
      .ok (.tuple (answer.map fun x => .field x))
    unless (prepared.run ("Words::" ++ name) [] (hints := dishonest)).toOption.isNone do
      throw (IO.userError s!"dishonest u32 hint accepted: {name}")
  let compiled ← get prepared.compileOptimized
  let some conversion := compiled.circuit.system.findChip? "Words::conversion" |
    throw (IO.userError "missing conversion chip")
  unless conversion.sends.isEmpty do
    throw (IO.userError "typed conversion added a lookup")
  IO.println "Passed opaque u32 arithmetic, conversion, boundary and dishonest-hint checks over Rat."

end AiurU32Tests
