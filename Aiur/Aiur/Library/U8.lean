import Aiur.Modules
import Aiur.Library.Carry

/-! Checked byte operations shared by word arithmetic and Blake3.
Raw operations accept fields and check their domain through the same tables
that establish their opaque results. They never reinterpret unchecked fields.
-/
namespace Aiur.Library.U8
open Aiur

def declarations : Modules.Program Nat := aiur% r#"
module UInt8 {
    opaque type U8 = Field;
    // Only the split tables construct these parts. Joining parts from different
    // bytes is safe: their bit positions are disjoint. Keeping them opaque lets
    // other modules recombine them without another range lookup.
    opaque type Parts4 = (Field, Field);
    opaque type Parts7 = (Field, Field);

    table byte_inputs: (Field,) {}
    table byte_values: U8 {}
    table byte_bits: [Field; 8] {}
    table pair_inputs: (Field, Field) {}
    table pair_units: () {}
    table pair_xors: U8 {}
    table pair_adds: (U8, U8) {}
    table pair_subs: (U8, U8) {}
    table pair_muls: (U8, U8) {}
    table pair_xor_parts4: Parts4 {}
    table pair_xor_parts7: Parts7 {}
    table sum_inputs: (Field,) {}
    table sum_bytes: U8 {}

    map from_field(x: Field) -> U8 = byte_inputs => byte_values;
    map raw_bit_decomposition(x: Field) -> [Field; 8] = byte_inputs => byte_bits;
    map range_pair(a: Field, b: Field) -> () = pair_inputs => pair_units;
    map raw_xor(a: Field, b: Field) -> U8 = pair_inputs => pair_xors;
    map raw_add(a: Field, b: Field) -> (U8, U8) = pair_inputs => pair_adds;
    map raw_sub(a: Field, b: Field) -> (U8, U8) = pair_inputs => pair_subs;
    map raw_mul(a: Field, b: Field) -> (U8, U8) = pair_inputs => pair_muls;
    map raw_xor_split4(a: Field, b: Field) -> Parts4 = pair_inputs => pair_xor_parts4;
    map raw_xor_split7(a: Field, b: Field) -> Parts7 = pair_inputs => pair_xor_parts7;
    map raw_sum_byte(sum: Field) -> U8 = sum_inputs => sum_bytes;

    // XOR/subtraction check both raw inputs. These identities reuse their
    // fixed-table multiplicities, as in legacy's byte primitives. Division
    // by two requires odd characteristic (as does a faithful byte embedding).
    inline fn raw_and(a: Field, b: Field) -> U8 {
        let x = raw_xor(a, b);
        (a + b - x) / 2
    }
    inline fn raw_or(a: Field, b: Field) -> U8 {
        let x = raw_xor(a, b);
        (a + b + x) / 2
    }
    inline fn raw_lt(a: Field, b: Field) -> Field {
        let (_, borrow) = raw_sub(a, b);
        borrow
    }

    inline fn to_field(byte: U8) -> Field { byte }
    inline fn from_fields(a: Field, b: Field) -> (U8, U8) { range_pair(a, b); (a, b) }
    inline fn bit_decomposition(x: U8) -> [Field; 8] { raw_bit_decomposition(x) }
    inline fn xor(a: U8, b: U8) -> U8 { raw_xor(a, b) }
    inline fn and(a: U8, b: U8) -> U8 { raw_and(a, b) }
    inline fn or(a: U8, b: U8) -> U8 { raw_or(a, b) }
    inline fn less_than(a: U8, b: U8) -> Field { raw_lt(a, b) }
    inline fn add(a: U8, b: U8) -> (U8, U8) { raw_add(a, b) }
    inline fn sub(a: U8, b: U8) -> (U8, U8) { raw_sub(a, b) }
    inline fn mul(a: U8, b: U8) -> (U8, U8) { raw_mul(a, b) }
    inline fn xor_split4(a: U8, b: U8) -> Parts4 { raw_xor_split4(a, b) }
    inline fn xor_split7(a: U8, b: U8) -> Parts7 { raw_xor_split7(a, b) }
    inline fn join4(high: Parts4, low: Parts4) -> U8 { high.0 + low.1 }
    inline fn join7(high: Parts7, low: Parts7) -> U8 { high.0 + low.1 }

    // Domain 0..767 covers adding three bytes and an incoming carry. The table
    // supplies the low byte; carry recovery is the ordinary proved field identity.
    inline fn split_sum(sum: Field) -> (U8, U8) {
        let byte = raw_sum_byte(sum);
        (byte, (sum - byte) / 256)
    }
}
"#

private def byteTy : Generic.Ty := .named "U8" []
private def literal (n : Nat) : Generic.Expr Nat := .literal n
private def pair (a b : Nat) : Generic.Expr Nat := .tuple [literal a, literal b]

/-- Complete tables, independent of the workload and accelerator implementation. -/
def tables : List (Generic.Table Nat) := Id.run do
  let byte := byteTy
  let two := Generic.Ty.tuple [byte, byte]
  let inputs := (List.range 256).flatMap fun a => (List.range 256).map fun b => (a,b)
  let sums := Carry.rows 256 768
  return [
    ⟨"byte_inputs", .tuple [.field], (List.range 256).map fun x => .tuple [literal x]⟩,
    ⟨"byte_values", byte, (List.range 256).map literal⟩,
    ⟨"byte_bits", .array .field 8, (List.range 256).map fun x =>
      .array ((List.range 8).map fun i => literal ((x / 2^i) % 2))⟩,
    ⟨"pair_inputs", .tuple [.field, .field], inputs.map fun (a,b) => pair a b⟩,
    ⟨"pair_units", .tuple [], inputs.map fun _ => .tuple []⟩,
    ⟨"pair_xors", byte, inputs.map fun (a,b) => literal (Nat.xor a b)⟩,
    ⟨"pair_adds", two, inputs.map fun (a,b) => pair ((a+b)%256) ((a+b)/256)⟩,
    ⟨"pair_subs", two, inputs.map fun (a,b) => pair ((a+256-b)%256) (if a < b then 1 else 0)⟩,
    ⟨"pair_muls", two, inputs.map fun (a,b) => pair ((a*b)%256) ((a*b)/256)⟩,
    ⟨"pair_xor_parts4", .named "Parts4" [], inputs.map fun (a,b) =>
      let x := Nat.xor a b; pair (x/16) ((x%16)*16)⟩,
    ⟨"pair_xor_parts7", .named "Parts7" [], inputs.map fun (a,b) =>
      let x := Nat.xor a b; pair (x/128) ((x%128)*2)⟩,
    ⟨"sum_inputs", .tuple [.field], sums.map fun (n, _) => .tuple [literal n]⟩,
    ⟨"sum_bytes", byte, sums.map fun (_, byte) => literal byte⟩]

def templates : Modules.Program Nat :=
  { declarations with modules := declarations.modules.map fun m =>
    { m with body := match m.body with
      | .definitions d => .definitions { d with
          program.consts := d.program.consts ++ (List.range 256).map fun n =>
            ⟨s!"BYTE_{n}", .literal n⟩
          constTypes := d.constTypes ++ (List.range 256).map fun n =>
            (s!"BYTE_{n}", byteTy) }
      | body => body } }

def source : Modules.Program Nat :=
  { templates with modules := templates.modules.map fun m =>
    {m with body := match m.body with
      | .definitions d => .definitions {d with program.tables := tables}
      | body => body} }

end Aiur.Library.U8
