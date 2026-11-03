import Aiur.Library.U8
import Aiur.Library.Frontend
import Mathlib.Algebra.CharP.Basic

/-! Eight checked little-endian bytes. The transparent word alias still contains
opaque bytes, so fields and hints cannot fabricate a word. Arithmetic lives here;
serializers may destructure existing bytes without rechecking them.
Multiplication columns and checked scalar conversion require a field with an
injective natural cast below 2^56. -/
namespace Aiur.Library.U64
open Aiur

def Compatible (F : Type) [NatCast F] : Prop :=
  Set.InjOn (Nat.cast : Nat → F) (Set.Iio (2^56))

theorem compatible_of_charP (F : Type) [AddGroupWithOne F] (p : Nat) [CharP F p]
    (large : 2^56 ≤ p) : Compatible F := by
  intro a ha b hb equal
  exact CharP.natCast_injOn_Iio F p (lt_of_lt_of_le ha large) (lt_of_lt_of_le hb large) equal

def declarations : Modules.Program Nat := aiur_library% U8.templates r#"
module UInt64 {
  type U8 = UInt8::U8;
  type U64 = [U8; 8];
  const ZERO: U64 = [UInt8::BYTE_0; 8];
  const ONE: U64 = [UInt8::BYTE_1, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0,
                    UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0];
  const MAX: U64 = [UInt8::BYTE_255; 8];
  inline fn from_bytes(bytes: [U8; 8]) -> U64 { bytes }
  inline fn to_bytes(word: U64) -> [U8; 8] { word }
  inline fn from_fields(raw: [Field; 8]) -> U64 {
    let (b0, b1) = UInt8::from_fields(raw[0], raw[1]);
    let (b2, b3) = UInt8::from_fields(raw[2], raw[3]);
    let (b4, b5) = UInt8::from_fields(raw[4], raw[5]);
    let (b6, b7) = UInt8::from_fields(raw[6], raw[7]);
    [b0, b1, b2, b3, b4, b5, b6, b7]
  }
  fn is_zero(x: U64) -> Field {
    match x {
      [UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0] => { 1 },
      _ => { 0 },
    }
  }

  fn eq(a: U64, b: U64) -> Field {
    let [a0, a1, a2, a3, a4, a5, a6, a7] = a;
    let [b0, b1, b2, b3, b4, b5, b6, b7] = b;
    match [UInt8::to_field(a0) - UInt8::to_field(b0), UInt8::to_field(a1) - UInt8::to_field(b1),
           UInt8::to_field(a2) - UInt8::to_field(b2), UInt8::to_field(a3) - UInt8::to_field(b3),
           UInt8::to_field(a4) - UInt8::to_field(b4), UInt8::to_field(a5) - UInt8::to_field(b5),
           UInt8::to_field(a6) - UInt8::to_field(b6), UInt8::to_field(a7) - UInt8::to_field(b7)] {
      [0, 0, 0, 0, 0, 0, 0, 0] => { 1 },
      _ => { 0 },
    }
  }

  fn add(a: U64, b: U64) -> (U64, U8) {
    let (s0, c1) = UInt8::split_sum(UInt8::to_field(a[0]) + UInt8::to_field(b[0]));
    let (s1, c2) = UInt8::split_sum(UInt8::to_field(a[1]) + UInt8::to_field(b[1]) + UInt8::to_field(c1));
    let (s2, c3) = UInt8::split_sum(UInt8::to_field(a[2]) + UInt8::to_field(b[2]) + UInt8::to_field(c2));
    let (s3, c4) = UInt8::split_sum(UInt8::to_field(a[3]) + UInt8::to_field(b[3]) + UInt8::to_field(c3));
    let (s4, c5) = UInt8::split_sum(UInt8::to_field(a[4]) + UInt8::to_field(b[4]) + UInt8::to_field(c4));
    let (s5, c6) = UInt8::split_sum(UInt8::to_field(a[5]) + UInt8::to_field(b[5]) + UInt8::to_field(c5));
    let (s6, c7) = UInt8::split_sum(UInt8::to_field(a[6]) + UInt8::to_field(b[6]) + UInt8::to_field(c6));
    let (s7, c8) = UInt8::split_sum(UInt8::to_field(a[7]) + UInt8::to_field(b[7]) + UInt8::to_field(c7));
    ([s0, s1, s2, s3, s4, s5, s6, s7], c8)
  }

  fn wrapping_succ(bytes: U64) -> U64 {
    let [b0, b1, b2, b3, b4, b5, b6, b7] = bytes;

    match UInt8::to_field(b0) {
      255 => { match UInt8::to_field(b1) {
        255 => { match UInt8::to_field(b2) {
          255 => { match UInt8::to_field(b3) {
            255 => { match UInt8::to_field(b4) {
              255 => { match UInt8::to_field(b5) {
                255 => { match UInt8::to_field(b6) {
                  255 => { match UInt8::to_field(b7) {
                    255 => { [UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0] },
                    _ => { [UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::from_field(UInt8::to_field(b7) + 1)] },
                  } },
                  _ => { [UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::from_field(UInt8::to_field(b6) + 1), b7] },
                } },
                _ => { [UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::from_field(UInt8::to_field(b5) + 1), b6, b7] },
              } },
              _ => { [UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::from_field(UInt8::to_field(b4) + 1), b5, b6, b7] },
            } },
            _ => { [UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::from_field(UInt8::to_field(b3) + 1), b4, b5, b6, b7] },
          } },
          _ => { [UInt8::BYTE_0, UInt8::BYTE_0, UInt8::from_field(UInt8::to_field(b2) + 1), b3, b4, b5, b6, b7] },
        } },
        _ => { [UInt8::BYTE_0, UInt8::from_field(UInt8::to_field(b1) + 1), b2, b3, b4, b5, b6, b7] },
      } },
      _ => { [UInt8::from_field(UInt8::to_field(b0) + 1), b1, b2, b3, b4, b5, b6, b7] },
    }
  }

  fn saturating_pred(bytes: U64) -> U64 {
    let [b0, b1, b2, b3, b4, b5, b6, b7] = bytes;

    match UInt8::to_field(b0) {
      0 => { match UInt8::to_field(b1) {
        0 => { match UInt8::to_field(b2) {
          0 => { match UInt8::to_field(b3) {
            0 => { match UInt8::to_field(b4) {
              0 => { match UInt8::to_field(b5) {
                0 => { match UInt8::to_field(b6) {
                  0 => { match UInt8::to_field(b7) {
                    0 => { [UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0, UInt8::BYTE_0] },
                    _ => { [UInt8::BYTE_255, UInt8::BYTE_255, UInt8::BYTE_255, UInt8::BYTE_255, UInt8::BYTE_255, UInt8::BYTE_255, UInt8::BYTE_255, UInt8::from_field(UInt8::to_field(b7) - 1)] },
                  } },
                  _ => { [UInt8::BYTE_255, UInt8::BYTE_255, UInt8::BYTE_255, UInt8::BYTE_255, UInt8::BYTE_255, UInt8::BYTE_255, UInt8::from_field(UInt8::to_field(b6) - 1), b7] },
                } },
                _ => { [UInt8::BYTE_255, UInt8::BYTE_255, UInt8::BYTE_255, UInt8::BYTE_255, UInt8::BYTE_255, UInt8::from_field(UInt8::to_field(b5) - 1), b6, b7] },
              } },
              _ => { [UInt8::BYTE_255, UInt8::BYTE_255, UInt8::BYTE_255, UInt8::BYTE_255, UInt8::from_field(UInt8::to_field(b4) - 1), b5, b6, b7] },
            } },
            _ => { [UInt8::BYTE_255, UInt8::BYTE_255, UInt8::BYTE_255, UInt8::from_field(UInt8::to_field(b3) - 1), b4, b5, b6, b7] },
          } },
          _ => { [UInt8::BYTE_255, UInt8::BYTE_255, UInt8::from_field(UInt8::to_field(b2) - 1), b3, b4, b5, b6, b7] },
        } },
        _ => { [UInt8::BYTE_255, UInt8::from_field(UInt8::to_field(b1) - 1), b2, b3, b4, b5, b6, b7] },
      } },
      _ => { [UInt8::from_field(UInt8::to_field(b0) - 1), b1, b2, b3, b4, b5, b6, b7] },
    }
  }

  fn to_field(x: [U8; 8]) -> Field {
    let [b0, b1, b2, b3, b4, b5, b6, b7] = x;
    assert_eq!(UInt8::to_field(b7), 0,
      "u64 -> field: value exceeds 2^56 (top byte must be zero)");
    UInt8::to_field(b0) + 256 * UInt8::to_field(b1) + 65536 * UInt8::to_field(b2)
      + 16777216 * UInt8::to_field(b3) + 4294967296 * UInt8::to_field(b4)
      + 1099511627776 * UInt8::to_field(b5) + 281474976710656 * UInt8::to_field(b6)
  }

  fn sub_with_borrow(a: U64, b: U64) -> (U64, Field) {
    let (s0, c1) = UInt8::split_sum(UInt8::to_field(a[0]) + 256 - UInt8::to_field(b[0]));
    let (s1, c2) = UInt8::split_sum(UInt8::to_field(a[1]) + 255 - UInt8::to_field(b[1]) + UInt8::to_field(c1));
    let (s2, c3) = UInt8::split_sum(UInt8::to_field(a[2]) + 255 - UInt8::to_field(b[2]) + UInt8::to_field(c2));
    let (s3, c4) = UInt8::split_sum(UInt8::to_field(a[3]) + 255 - UInt8::to_field(b[3]) + UInt8::to_field(c3));
    let (s4, c5) = UInt8::split_sum(UInt8::to_field(a[4]) + 255 - UInt8::to_field(b[4]) + UInt8::to_field(c4));
    let (s5, c6) = UInt8::split_sum(UInt8::to_field(a[5]) + 255 - UInt8::to_field(b[5]) + UInt8::to_field(c5));
    let (s6, c7) = UInt8::split_sum(UInt8::to_field(a[6]) + 255 - UInt8::to_field(b[6]) + UInt8::to_field(c6));
    let (s7, c8) = UInt8::split_sum(UInt8::to_field(a[7]) + 255 - UInt8::to_field(b[7]) + UInt8::to_field(c7));
    ([s0, s1, s2, s3, s4, s5, s6, s7], 1 - UInt8::to_field(c8))
  }

  fn mul(a: U64, b: U64) -> (U64, U64) {
    let a0 = UInt8::to_field(a[0]) + 256 * UInt8::to_field(a[1]);
    let b0 = UInt8::to_field(b[0]) + 256 * UInt8::to_field(b[1]);
    let a1 = UInt8::to_field(a[2]) + 256 * UInt8::to_field(a[3]);
    let b1 = UInt8::to_field(b[2]) + 256 * UInt8::to_field(b[3]);
    let a2 = UInt8::to_field(a[4]) + 256 * UInt8::to_field(a[5]);
    let b2 = UInt8::to_field(b[4]) + 256 * UInt8::to_field(b[5]);
    let a3 = UInt8::to_field(a[6]) + 256 * UInt8::to_field(a[7]);
    let b3 = UInt8::to_field(b[6]) + 256 * UInt8::to_field(b[7]);
    let (r0, c0) = mul_column((a0 * b0));
    let (r1, c1) = mul_column((a0 * b1) + (a1 * b0) + UInt8::to_field(c0[0]) + 256 * UInt8::to_field(c0[1]) + 65536 * UInt8::to_field(c0[2]));
    let (r2, c2) = mul_column((a0 * b2) + (a1 * b1) + (a2 * b0) + UInt8::to_field(c1[0]) + 256 * UInt8::to_field(c1[1]) + 65536 * UInt8::to_field(c1[2]));
    let (r3, c3) = mul_column((a0 * b3) + (a1 * b2) + (a2 * b1) + (a3 * b0) + UInt8::to_field(c2[0]) + 256 * UInt8::to_field(c2[1]) + 65536 * UInt8::to_field(c2[2]));
    let (r4, c4) = mul_column((a1 * b3) + (a2 * b2) + (a3 * b1) + UInt8::to_field(c3[0]) + 256 * UInt8::to_field(c3[1]) + 65536 * UInt8::to_field(c3[2]));
    let (r5, c5) = mul_column((a2 * b3) + (a3 * b2) + UInt8::to_field(c4[0]) + 256 * UInt8::to_field(c4[1]) + 65536 * UInt8::to_field(c4[2]));
    let (r6, c6) = mul_column((a3 * b3) + UInt8::to_field(c5[0]) + 256 * UInt8::to_field(c5[1]) + 65536 * UInt8::to_field(c5[2]));
    assert_eq!(UInt8::to_field(c6[2]), 0, "mul: final carry exceeds one radix digit");
    ([r0[0], r0[1], r1[0], r1[1], r2[0], r2[1], r3[0], r3[1]],
     [r4[0], r4[1], r5[0], r5[1], r6[0], r6[1], c6[0], c6[1]])
  }

  inline fn mul_column(x: Field) -> ([U8; 2], [U8; 3]) {
    let bytes = hint::<[Field; 8]>("bytes_le", x);
    let (r0, r1) = UInt8::from_fields(bytes[0], bytes[1]);
    let (c0, c1) = UInt8::from_fields(bytes[2], bytes[3]);
    let (c2, _) = UInt8::from_fields(bytes[4], 0);
    constrain_eq!(x, UInt8::to_field(r0) + 256 * UInt8::to_field(r1)
      + 65536 * (UInt8::to_field(c0) + 256 * UInt8::to_field(c1) + 65536 * UInt8::to_field(c2)),
      "mul: column hint does not recompose");
    ([r0, r1], [c0, c1, c2])
  }

  fn and(a: U64, b: U64) -> U64 {
    let [a0, a1, a2, a3, a4, a5, a6, a7] = a;
    let [b0, b1, b2, b3, b4, b5, b6, b7] = b;
    [UInt8::and(a0, b0), UInt8::and(a1, b1), UInt8::and(a2, b2), UInt8::and(a3, b3),
     UInt8::and(a4, b4), UInt8::and(a5, b5), UInt8::and(a6, b6), UInt8::and(a7, b7)]
  }

  fn or(a: U64, b: U64) -> U64 {
    let [a0, a1, a2, a3, a4, a5, a6, a7] = a;
    let [b0, b1, b2, b3, b4, b5, b6, b7] = b;
    [UInt8::or(a0, b0), UInt8::or(a1, b1), UInt8::or(a2, b2), UInt8::or(a3, b3),
     UInt8::or(a4, b4), UInt8::or(a5, b5), UInt8::or(a6, b6), UInt8::or(a7, b7)]
  }

  fn xor(a: U64, b: U64) -> U64 {
    let [a0, a1, a2, a3, a4, a5, a6, a7] = a;
    let [b0, b1, b2, b3, b4, b5, b6, b7] = b;
    [UInt8::xor(a0, b0), UInt8::xor(a1, b1), UInt8::xor(a2, b2), UInt8::xor(a3, b3),
     UInt8::xor(a4, b4), UInt8::xor(a5, b5), UInt8::xor(a6, b6), UInt8::xor(a7, b7)]
  }

  fn from_field(value: Field) -> U64 {
    let [h0, h1, h2, h3, h4, h5, h6, h7] = hint::<[Field; 8]>("bytes_le", value);
    let (b0, b1) = UInt8::from_fields(h0, h1);
    let (b2, b3) = UInt8::from_fields(h2, h3);
    let (b4, b5) = UInt8::from_fields(h4, h5);
    let (b6, b7) = UInt8::from_fields(h6, h7);
    let bytes = [b0, b1, b2, b3, b4, b5, b6, b7];

    constrain_eq!(to_field(bytes), value,
      "u64 bytes do not recompose to the field value");
    bytes
  }
}
"#

def templates : Modules.Program Nat := U8.templates.append declarations
def source : Modules.Program Nat := U8.source.append declarations

/-- Link this specialization with the shared UInt8 module. -/
def specialize (F : Type) [NatCast F] (_large : Compatible F) : Modules.Program F :=
  declarations.toField F

end Aiur.Library.U64
