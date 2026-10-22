import Aiur.Library.U64.Hints
import Mathlib.Algebra.Field.Rat

namespace AiurU64Tests
open Aiur
set_option maxRecDepth 10000

def client : Modules.Program Nat := aiur_library% Library.U64.templates r#"
module Wide {
    inline fn fields(x: UInt64::U64) -> [Field; 8] {
        [UInt8::to_field(x[0]), UInt8::to_field(x[1]), UInt8::to_field(x[2]), UInt8::to_field(x[3]), UInt8::to_field(x[4]), UInt8::to_field(x[5]), UInt8::to_field(x[6]), UInt8::to_field(x[7])]
    }
    fn add(a: [Field; 8], b: [Field; 8]) -> ([Field; 8], Field) {
        let (word, carry) = UInt64::add(UInt64::from_fields(a), UInt64::from_fields(b));
        (fields(word), UInt8::to_field(carry))
    }
    fn sub(a: [Field; 8], b: [Field; 8]) -> ([Field; 8], Field) {
        let (word, borrow) = UInt64::sub_with_borrow(UInt64::from_fields(a), UInt64::from_fields(b));
        (fields(word), borrow)
    }
    fn mul(a: [Field; 8], b: [Field; 8]) -> ([Field; 8], [Field; 8]) {
        let (lo, hi) = UInt64::mul(UInt64::from_fields(a), UInt64::from_fields(b));
        (fields(lo), fields(hi))
    }
    fn from_field(x: Field) -> [Field; 8] { fields(UInt64::from_field(x)) }
    fn to_field(x: [Field; 8]) -> Field { UInt64::to_field(UInt64::from_fields(x)) }
    fn eq(a: [Field; 8], b: [Field; 8]) -> Field { UInt64::eq(UInt64::from_fields(a), UInt64::from_fields(b)) }
    fn is_zero(a: [Field; 8]) -> Field { UInt64::is_zero(UInt64::from_fields(a)) }
    fn and(a: [Field; 8], b: [Field; 8]) -> [Field; 8] { fields(UInt64::and(UInt64::from_fields(a), UInt64::from_fields(b))) }
    fn or(a: [Field; 8], b: [Field; 8]) -> [Field; 8] { fields(UInt64::or(UInt64::from_fields(a), UInt64::from_fields(b))) }
    fn xor(a: [Field; 8], b: [Field; 8]) -> [Field; 8] { fields(UInt64::xor(UInt64::from_fields(a), UInt64::from_fields(b))) }
    fn wrapping_succ(a: [Field; 8]) -> [Field; 8] { fields(UInt64::wrapping_succ(UInt64::from_fields(a))) }
    fn saturating_pred(a: [Field; 8]) -> [Field; 8] { fields(UInt64::saturating_pred(UInt64::from_fields(a))) }
}
"#

def entries : List String := client.modules.flatMap fun m => match m.body with
  | .definitions d => (d.program.functions.filter (·.name != "fields")).map fun f => "Wide::" ++ f.name
  | _ => []

run_cmd do
  let .ok bad := Modules.Frontend.parse (← Lean.getEnv)
    "module Bad { fn run() -> UInt64::U64 { hint::<UInt64::U64>(0) } }" |
    throwError "invalid U64 opacity test"
  unless (Modules.checkTemplates (Library.U64.templates.append bad)).toOption.isNone do
    throwError "hint fabricated a word of opaque bytes"

private def bytes (n : Nat) : SourceValue Rat :=
  .tuple ((List.range 8).map fun i => .field (((n / 256^i) % 256 : Nat) : Rat))

def run : IO Unit := do
  let prepared ← IO.ofExcept <| Modules.prepare ((Library.U64.source.append client).toField Rat) entries
  let hints := prepared.environment.source.checkedHints (Library.U64.hints (fun (x : Rat) => x.num.toNat / x.den))
  let expect (name : String) (args : List (SourceValue Rat)) (expected : SourceValue Rat) := do
    let (actual, _) ← IO.ofExcept <| prepared.run ("Wide::" ++ name) args (fuel := 100000) (hints := hints)
    unless actual == expected do throw (IO.userError s!"u64 {name}: {repr actual} != {repr expected}")
  let base : Nat := 2^64
  for a in [0, 255, 256, 2^32, base-1] do
    expect "wrapping_succ" [bytes a] (bytes ((a+1)%base))
    expect "saturating_pred" [bytes a] (bytes (a-1))
    for b in [0, 1, base-1] do
      expect "add" [bytes a, bytes b] (.tuple [bytes ((a+b)%base), .field (((a+b)/base : Nat) : Rat)])
      expect "sub" [bytes a, bytes b] (.tuple [bytes ((a+base-b)%base), .field (if a < b then 1 else 0)])
      expect "mul" [bytes a, bytes b] (.tuple [bytes (a*b%base), bytes (a*b/base)])
  for a in ([0, 256, 2^56-1] : List Nat) do
    expect "from_field" [.field a] (bytes a)
    expect "to_field" [bytes a] (.field a)
  for (entry, args) in [("from_field", [.field (2^56)]), ("to_field", [bytes (2^56)]),
      ("add", [.tuple [256, 0, 0, 0, 0, 0, 0, 0], bytes 0])] do
    unless (prepared.run ("Wide::" ++ entry) args (hints := hints)).toOption.isNone do
      throw (IO.userError s!"u64 invalid input accepted: {entry}")
  let dishonest := prepared.environment.source.checkedHints fun _ _ =>
    .ok (.tuple (List.replicate 8 (.field 0)))
  for (entry, args) in [("from_field", [.field 1]), ("mul", [bytes 1, bytes 1])] do
    unless (prepared.run ("Wide::" ++ entry) args (hints := dishonest)).toOption.isNone do
      throw (IO.userError s!"u64 dishonest hint accepted: {entry}")
  IO.println "Passed shared U64 arithmetic, carries, conversion limits and dishonest-hint checks over Rat."

end AiurU64Tests
