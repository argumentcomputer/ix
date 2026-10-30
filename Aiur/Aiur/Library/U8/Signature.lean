import Aiur.Modules

/-! The checked byte interface. Callers cannot manufacture bytes or split
parts from fields, including through hints. Maps and ordinary functions have
the same interface; table storage and host accelerators are implementation
details. The 256 typed literals are added below without exposing a cast. -/
namespace Aiur.Library.U8
open Aiur

private def interface : Modules.Program Nat := aiur% "
signature U8Signature {
    opaque type U8;
    opaque type Parts4;
    opaque type Parts7;
    fn from_field(x: Field) -> U8;
    fn from_fields(a: Field, b: Field) -> (U8, U8);
    fn to_field(byte: U8) -> Field;
    fn raw_bit_decomposition(x: Field) -> [Field; 8];
    fn range_pair(a: Field, b: Field) -> ();
    fn raw_xor(a: Field, b: Field) -> U8;
    fn raw_and(a: Field, b: Field) -> U8;
    fn raw_or(a: Field, b: Field) -> U8;
    fn raw_lt(a: Field, b: Field) -> Field;
    fn raw_add(a: Field, b: Field) -> (U8, U8);
    fn raw_sub(a: Field, b: Field) -> (U8, U8);
    fn raw_mul(a: Field, b: Field) -> (U8, U8);
    fn raw_xor_split4(a: Field, b: Field) -> Parts4;
    fn raw_xor_split7(a: Field, b: Field) -> Parts7;
    fn raw_sum_byte(sum: Field) -> U8;
    fn bit_decomposition(x: U8) -> [Field; 8];
    fn xor(a: U8, b: U8) -> U8;
    fn and(a: U8, b: U8) -> U8;
    fn or(a: U8, b: U8) -> U8;
    fn less_than(a: U8, b: U8) -> Field;
    fn add(a: U8, b: U8) -> (U8, U8);
    fn sub(a: U8, b: U8) -> (U8, U8);
    fn mul(a: U8, b: U8) -> (U8, U8);
    fn xor_split4(a: U8, b: U8) -> Parts4;
    fn xor_split7(a: U8, b: U8) -> Parts7;
    fn join4(high: Parts4, low: Parts4) -> U8;
    fn join7(high: Parts7, low: Parts7) -> U8;
    fn split_sum(sum: Field) -> (U8, U8);
}"

def signature : Modules.Program Nat :=
  { interface with signatures := interface.signatures.map fun s =>
      { s with consts := (List.range 256).map fun n =>
          (s!"BYTE_{n}", .named "U8" []) } }

end Aiur.Library.U8
