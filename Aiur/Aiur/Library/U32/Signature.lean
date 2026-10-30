import Aiur.Library.U8
import Aiur.Library.Frontend

/-! Checked words and their compact representation. The byte boundary uses
the selected UInt8 implementation; arithmetic clients only need U32Signature.
Field-specific implementations must establish their own arithmetic bounds. -/
namespace Aiur.Library.U32
open Aiur

def signature : Modules.Program Nat := aiur_library% U8.templates "
signature U32Signature {
    opaque type U32;
    opaque type Compact;
    const ZERO: U32;
    const ONE: U32;
    const MAX: U32;
    const COMPACT_ZERO: Compact;
    fn from_bytes(bytes: [UInt8::U8; 4]) -> U32;
    fn to_bytes(word: U32) -> [UInt8::U8; 4];
    fn from_fields(raw: [Field; 4]) -> U32;
    fn from_field(value: Field) -> U32;
    fn compact_field(word: Compact) -> Field;
    fn compact(word: U32) -> Compact;
    fn compact_from_field(value: Field) -> Compact;
    fn expand(word: Compact) -> U32;
    fn add(a: U32, b: U32) -> U32;
    fn add3(a: U32, b: U32, c: U32) -> U32;
    fn sub_borrow(a: Compact, b: Compact) -> (U32, Field);
    fn sub(a: U32, b: U32) -> U32;
    fn less_than(a: U32, b: U32) -> Field;
    fn compact_less_than(a: Compact, b: Compact) -> Field;
    fn less_than_fields(a: Field, b: Field) -> Field;
    fn xor(a: U32, b: U32) -> U32;
    fn and(a: U32, b: U32) -> U32;
    fn or(a: U32, b: U32) -> U32;
    fn rotr8(a: U32) -> U32;
    fn rotr16(a: U32) -> U32;
    fn xor_rotr7(a: U32, b: U32) -> U32;
    fn xor_rotr12(a: U32, b: U32) -> U32;
}"

end Aiur.Library.U32
