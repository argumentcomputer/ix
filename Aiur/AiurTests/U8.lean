import Aiur.Library.U8
import Aiur.Library.Frontend
import Mathlib.Algebra.Field.Rat

namespace AiurU8Tests
open Aiur

set_option maxRecDepth 10000

def client : Modules.Program Nat := aiur_library% Library.U8.templates "
module Bytes {
    fn checked(value: Field) -> Field { UInt8::to_field(UInt8::from_field(value)) }
    fn less_than(a: Field, b: Field) -> Field { UInt8::raw_lt(a, b) }
    fn split(sum: Field) -> (Field, Field) {
        let (lo, carry) = UInt8::split_sum(sum);
        (UInt8::to_field(lo), UInt8::to_field(carry))
    }
    fn add(a: Field, b: Field) -> (Field, Field) {
        let (lo, carry) = UInt8::raw_add(a, b);
        (UInt8::to_field(lo), UInt8::to_field(carry))
    }
    fn sub(a: Field, b: Field) -> (Field, Field) {
        let (lo, borrow) = UInt8::raw_sub(a, b);
        (UInt8::to_field(lo), UInt8::to_field(borrow))
    }
    fn mul(a: Field, b: Field) -> (Field, Field) {
        let (lo, hi) = UInt8::raw_mul(a, b);
        (UInt8::to_field(lo), UInt8::to_field(hi))
    }
    fn join4(a: Field, b: Field) -> Field {
        UInt8::to_field(UInt8::join4(UInt8::raw_xor_split4(a, 0), UInt8::raw_xor_split4(b, 0)))
    }
    fn join7(a: Field, b: Field) -> Field {
        UInt8::to_field(UInt8::join7(UInt8::raw_xor_split7(a, 0), UInt8::raw_xor_split7(b, 0)))
    }
}"

def entries := ["Bytes::checked", "Bytes::less_than", "Bytes::split", "Bytes::add",
  "Bytes::sub", "Bytes::mul", "Bytes::join4", "Bytes::join7"]

run_cmd do
  for (type, raw) in [("UInt8::U8", "0"), ("UInt8::Parts4", "(0, 0)"), ("UInt8::Parts7", "(0, 0)")] do
    for body in [raw, s!"hint::<{type}>(0)"] do
      let .ok bad := Modules.Frontend.parse (← Lean.getEnv)
        s!"module Bad \{ fn run() -> {type} \{ {body} } }" |
        throwError "invalid opacity test"
      unless (Modules.checkTemplates (Library.U8.templates.append bad)).toOption.isNone do
        throwError "fabricated opaque value {type}: {body}"

private def ensure (message : String) (condition : Bool) : Except String Unit :=
  if condition then .ok () else .error message

private def tableRows (name : String) : Except String (Array (Generic.Expr Nat)) := do
  let some table := Library.U8.tables.find? (·.name == name) | throw s!"missing generated table {name}"
  return table.rows.toArray

private def scalar : Generic.Expr Nat → Except String Nat
  | .literal n => .ok n
  | _ => .error "expected a generated scalar"

private def pair : Generic.Expr Nat → Except String (Nat × Nat)
  | .tuple [.literal a, .literal b] => .ok (a, b)
  | _ => .error "expected a generated pair"

/-- Check the actual generated rows, including alignment of every output trace,
for all 65,536 byte pairs. This is host-side validation, not Aiur execution. -/
def checkTables : Except String Unit := do
  let byteInputs ← tableRows "byte_inputs"
  let values ← (← tableRows "byte_values").mapM scalar
  let inputs ← (← tableRows "pair_inputs").mapM pair
  let xors ← (← tableRows "pair_xors").mapM scalar
  let adds ← (← tableRows "pair_adds").mapM pair
  let subs ← (← tableRows "pair_subs").mapM pair
  let muls ← (← tableRows "pair_muls").mapM pair
  let parts4 ← (← tableRows "pair_xor_parts4").mapM pair
  let parts7 ← (← tableRows "pair_xor_parts7").mapM pair
  let units ← tableRows "pair_units"
  let sumInputs ← tableRows "sum_inputs"
  let sums ← (← tableRows "sum_bytes").mapM scalar
  ensure "incomplete byte tables" (byteInputs.size == 256 && values.size == 256)
  ensure "incomplete byte-pair tables" ([inputs.size, xors.size, adds.size, subs.size,
    muls.size, parts4.size, parts7.size, units.size].all (· == 65536))
  ensure "incomplete carry table" (sumInputs.size == 768 && sums.size == 768)
  for n in List.range 256 do
    ensure "byte table alignment" (byteInputs[n]! == .tuple [.literal n] && values[n]! == n)
  for n in List.range 768 do
    let byte := sums[n]!
    ensure "carry table alignment" (sumInputs[n]! == .tuple [.literal n])
    ensure "carry decomposition" (byte < 256 && n / 256 < 3 && byte + 256 * (n / 256) == n)
    ensure "field carry reconstruction" (((n : Rat) - byte) / 256 == (n / 256 : Nat))
  for a in List.range 256 do
    for b in List.range 256 do
      let index := 256 * a + b
      ensure "byte-pair table alignment" (inputs[index]! == (a, b))
      let x := xors[index]!
      ensure "byte XOR" (x == Nat.xor a b)
      let (sum, carry) := adds[index]!
      ensure "byte addition" (sum < 256 && carry < 2 && sum + 256 * carry == a + b)
      let (diff, borrow) := subs[index]!
      ensure "byte subtraction" (diff < 256 && borrow < 2 && diff + b == a + 256 * borrow)
      let (lo, hi) := muls[index]!
      ensure "byte multiplication" (lo < 256 && hi < 256 && lo + 256 * hi == a * b)
      let (hi, shifted) := parts4[index]!
      ensure "XOR four-bit split" (hi < 16 && shifted < 256 && shifted % 16 == 0 &&
        16 * hi + shifted / 16 == x)
      let (hi, shifted) := parts7[index]!
      ensure "XOR seven-bit split" (hi < 2 && shifted < 256 && shifted % 2 == 0 &&
        128 * hi + shifted / 2 == x)
      ensure "byte-pair range check" (units[index]! == .tuple [])


def run : IO Unit := do
  IO.ofExcept checkTables
  let prepared ← IO.ofExcept <| Modules.prepare ((Library.U8.source.append client).toField Rat) entries
  for n in ([0, 1, 254, 255] : List Nat) do
    let (actual, _) ← IO.ofExcept <| prepared.run "Bytes::checked" [.field n]
    unless actual == .field n do
      throw (IO.userError s!"wrong checked byte at {n}")
  for (a, b) in ([(0, 255), (255, 0), (255, 255)] : List (Nat × Nat)) do
    let (actual, _) ← IO.ofExcept <| prepared.run "Bytes::less_than" [.field a, .field b]
    unless actual == .field (if a < b then 1 else 0) do
      throw (IO.userError s!"wrong raw byte comparison at {a}, {b}")
  for n in ([0, 255, 256, 510, 511, 512, 767] : List Nat) do
    let (actual, _) ← IO.ofExcept <| prepared.run "Bytes::split" [.field n]
    unless actual == .tuple [.field ((n % 256 : Nat) : Rat), .field ((n / 256 : Nat) : Rat)] do
      throw (IO.userError s!"wrong split_sum at {n}")
  for (entry, args) in [("checked", [256]), ("checked", [-1]),
      ("less_than", [256, 0]), ("less_than", [0, 256]), ("less_than", [-1, 0]),
      ("less_than", [0, -1]), ("split", [768]), ("split", [-1]), ("add", [256, 0]),
      ("sub", [0, -1]), ("mul", [1, 256]), ("join4", [256, 0]), ("join7", [0, 256])] do
    unless (prepared.run ("Bytes::" ++ entry) (args.map fun x => .field x)).toOption.isNone do
      throw (IO.userError s!"out-of-domain byte operation accepted: {entry}")
  IO.println "Passed shared U8 tables (65,536 pairs, 768 sums), opacity and raw-domain checks."

end AiurU8Tests
