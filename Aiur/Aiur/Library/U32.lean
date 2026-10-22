import Aiur.Library.U8
import Aiur.Library.Frontend
import Mathlib.Algebra.CharP.Basic

/-! Opaque byte and word arithmetic. The source has no privileged operations:
host advice supplies raw fields, and ordinary assertions/lookups check it.

The compact representation and packed carry checks require an injective natural
cast below `3 * 2^32`. This includes characteristic zero and every prime field
of characteristic at least that bound; it does not assume Goldilocks.
-/
namespace Aiur.Library.U32
open Aiur

def base : Nat := 4294967296

def Compatible (F : Type) [NatCast F] : Prop :=
  Set.InjOn (Nat.cast : Nat → F) (Set.Iio (3 * base))

theorem compatible_of_charP (F : Type) [AddGroupWithOne F] (p : Nat) [CharP F p]
    (large : 3 * base ≤ p) : Compatible F := by
  intro a ha b hb equal
  exact CharP.natCast_injOn_Iio F p (lt_of_lt_of_le ha large) (lt_of_lt_of_le hb large) equal

theorem compatible_of_charZero (F : Type) [AddMonoidWithOne F] [CharZero F] :
    Compatible F := by
  intro a _ b _ equal
  exact Nat.cast_injective equal

/-- The byte and word nominal types cannot be obtained through hints or entry arguments,
including through aliases and aggregates. Only checked constructors and typed
operations below create them. Typed conversions and word operations inline;
raw field comparison shares a memoized query across callers. -/
def declarations : Modules.Program Nat := aiur_library% U8.templates r#"
module UInt32 {
    type U8 = UInt8::U8;
    opaque type U32 = [U8; 4];
    opaque type Compact = Field;

    const ZERO: U32 = [UInt8::BYTE_0; 4];
    const ONE: U32 = [UInt8::BYTE_1, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0];
    const MAX: U32 = [UInt8::BYTE_255; 4];
    const COMPACT_ZERO: Compact = 0;

    inline fn from_bytes(bytes: [U8; 4]) -> U32 { bytes }
    inline fn to_bytes(word: U32) -> [U8; 4] { word }
    inline fn compact_field(word: Compact) -> Field { word }
    inline fn compact(word: U32) -> Compact {
        UInt8::to_field(word[0]) + 256*UInt8::to_field(word[1])
            + 65536*UInt8::to_field(word[2]) + 16777216*UInt8::to_field(word[3])
    }
    inline fn from_fields(raw: [Field; 4]) -> U32 {
        let (b0, b1) = UInt8::from_fields(raw[0], raw[1]);
        let (b2, b3) = UInt8::from_fields(raw[2], raw[3]);
        [b0, b1, b2, b3]
    }
    inline fn from_field(value: Field) -> U32 {
        let raw = hint::<[Field; 4]>("u32.bytes", value);
        let word = from_fields(raw);
        constrain_eq!(compact(word), value, "u32 decomposition");
        word
    }
    inline fn compact_from_field(value: Field) -> Compact { from_field(value); value }
    inline fn expand(word: Compact) -> U32 { from_field(word) }

    // Advice consumes bytes directly. Packing and the carry relation only
    // feed constraints, so the Rust backend can discard that arithmetic.
    inline fn add(a: U32, b: U32) -> U32 {
        let raw = hint::<[Field; 4]>("u32.add",
            ([UInt8::to_field(a[0]), UInt8::to_field(a[1]), UInt8::to_field(a[2]), UInt8::to_field(a[3])],
             [UInt8::to_field(b[0]), UInt8::to_field(b[1]), UInt8::to_field(b[2]), UInt8::to_field(b[3])]));
        let result = from_fields(raw);
        let carry = (compact(a) + compact(b) - compact(result)) / 4294967296;
        constrain_eq!(carry * (carry - 1), 0, "u32 add carry");
        result
    }
    inline fn add3(a: U32, b: U32, c: U32) -> U32 {
        let raw = hint::<[Field; 4]>("u32.add3",
            ([UInt8::to_field(a[0]), UInt8::to_field(a[1]), UInt8::to_field(a[2]), UInt8::to_field(a[3])],
             [UInt8::to_field(b[0]), UInt8::to_field(b[1]), UInt8::to_field(b[2]), UInt8::to_field(b[3])],
             [UInt8::to_field(c[0]), UInt8::to_field(c[1]), UInt8::to_field(c[2]), UInt8::to_field(c[3])]));
        let result = from_fields(raw);
        let carry = (compact(a) + compact(b) + compact(c) - compact(result)) / 4294967296;
        constrain_eq!(carry * (carry - 1) * (carry - 2), 0, "u32 add3 carry");
        result
    }
    inline fn sub_borrow(a: Compact, b: Compact) -> (U32, Field) {
        let raw = hint::<[Field; 4]>("u32.sub", (compact_field(a), compact_field(b)));
        let result = from_fields(raw);
        let borrow = (compact(result) + b - a) / 4294967296;
        constrain_eq!(borrow * (borrow - 1), 0, "u32 subtraction borrow");
        (result, borrow)
    }
    inline fn sub(a: U32, b: U32) -> U32 { sub_borrow(compact(a), compact(b)).0 }
    inline fn less_than(a: U32, b: U32) -> Field { compact_less_than(compact(a), compact(b)) }
    inline fn compact_less_than(a: Compact, b: Compact) -> Field {
        sub_borrow(a, b).1
    }
    // Raw scalar compatibility boundary: both operands must be checked here.
    // One hint supplies all three byte decompositions, including the wrapped
    // difference. Reuse the byte-pair range table rather than adding a table.
    fn less_than_fields(a: Field, b: Field) -> Field {
        let raw = hint::<([Field; 4], [Field; 4], [Field; 4])>("u32.lt", (a, b));
        let left = from_fields(raw.0);
        let difference = from_fields(raw.1);
        let right = from_fields(raw.2);
        constrain_eq!(a, compact(left), "u32 comparison left");
        constrain_eq!(b, compact(right), "u32 comparison right");
        let borrow = (compact(difference) + b - a) / 4294967296;
        constrain_eq!(borrow * (borrow - 1), 0, "u32 comparison borrow");
        borrow
    }

    inline fn xor(a: U32, b: U32) -> U32 {
        [UInt8::xor(a[0], b[0]), UInt8::xor(a[1], b[1]),
         UInt8::xor(a[2], b[2]), UInt8::xor(a[3], b[3])]
    }
    inline fn and(a: U32, b: U32) -> U32 {
        [UInt8::and(a[0], b[0]), UInt8::and(a[1], b[1]),
         UInt8::and(a[2], b[2]), UInt8::and(a[3], b[3])]
    }
    inline fn or(a: U32, b: U32) -> U32 {
        [UInt8::or(a[0], b[0]), UInt8::or(a[1], b[1]),
         UInt8::or(a[2], b[2]), UInt8::or(a[3], b[3])]
    }
    inline fn rotr8(a: U32) -> U32 { [a[1], a[2], a[3], a[0]] }
    inline fn rotr16(a: U32) -> U32 { [a[2], a[3], a[0], a[1]] }
    inline fn xor_rotr7(a: U32, b: U32) -> U32 {
        let p0 = UInt8::xor_split7(a[0], b[0]);
        let p1 = UInt8::xor_split7(a[1], b[1]);
        let p2 = UInt8::xor_split7(a[2], b[2]);
        let p3 = UInt8::xor_split7(a[3], b[3]);
        [UInt8::join7(p0, p1), UInt8::join7(p1, p2), UInt8::join7(p2, p3), UInt8::join7(p3, p0)]
    }
    inline fn xor_rotr12(a: U32, b: U32) -> U32 {
        let p0 = UInt8::xor_split4(a[0], b[0]);
        let p1 = UInt8::xor_split4(a[1], b[1]);
        let p2 = UInt8::xor_split4(a[2], b[2]);
        let p3 = UInt8::xor_split4(a[3], b[3]);
        [UInt8::join4(p1, p2), UInt8::join4(p2, p3), UInt8::join4(p3, p0), UInt8::join4(p0, p1)]
    }
}
"#

def templates : Modules.Program Nat := U8.templates.append declarations

def source : Modules.Program Nat := U8.source.append declarations

/-- Preferred field-specialization entrypoint: the caller establishes the
arithmetic precondition once, independently of the compiler's field genericity. -/
def program (F : Type) [NatCast F] (_large : Compatible F) : Modules.Program F :=
  source.toField F

end Aiur.Library.U32
