import Aiur.Library.Field.BN254
import Aiur.Library.Field.Goldilocks.Signature
import Aiur.Library.Field
import Aiur.Library.Frontend

/-! Canonical Goldilocks residues in BN254 Fr. Multiplication checks
`a * b = q * p + r` with canonical operands and remainder and a UInt64
quotient. Both sides are below `2^128`, so the ambient field equation cannot
wrap. Byte decompositions and carries are checked by ordinary Aiur constraints.
The quadratic extension uses the same nonresidue seven as the native library. -/
namespace Aiur.Library.Field.Goldilocks.Emulated
open Aiur

abbrev modulus : Nat := 18446744069414584321
abbrev F := BN254.F

theorem product_bound : (modulus - 1) ^ 2 < BN254.modulus := by decide
theorem reduction_bound : (2^64 - 1) * modulus + (modulus - 1) < BN254.modulus := by decide

def dependencies : Modules.Program Nat :=
  U8.templates.append Library.Field.declarations |>.append Goldilocks.signature

private def implementation : Modules.Program Nat := aiur_library% dependencies ⟦
module Goldilocks: GoldilocksSignature {
  type Goldilocks = Field;
  type ExtGoldilocks = [Goldilocks; 2];
  const MODULUS: Field = 18446744069414584321;

  inline fn checked_bytes(raw: [Field; 8]) -> [UInt8::U8; 8] {
    let (b0, b1) = UInt8::from_fields(raw[0], raw[1]);
    let (b2, b3) = UInt8::from_fields(raw[2], raw[3]);
    let (b4, b5) = UInt8::from_fields(raw[4], raw[5]);
    let (b6, b7) = UInt8::from_fields(raw[6], raw[7]);
    [b0, b1, b2, b3, b4, b5, b6, b7]
  }

  inline fn pack_bytes(x: [UInt8::U8; 8]) -> Field {
    UInt8::to_field(x[0]) + 256 * UInt8::to_field(x[1]) + 65536 * UInt8::to_field(x[2])
      + 16777216 * UInt8::to_field(x[3]) + 4294967296 * UInt8::to_field(x[4])
      + 1099511627776 * UInt8::to_field(x[5]) + 281474976710656 * UInt8::to_field(x[6])
      + 72057594037927936 * UInt8::to_field(x[7])
  }

  inline fn gl_lt_p(x: [UInt8::U8; 8]) -> Field {
    let hi_max = Fields::is_zero(
      UInt8::to_field(x[4]) + UInt8::to_field(x[5]) + UInt8::to_field(x[6]) + UInt8::to_field(x[7]) - 1020);
    let lo_zero = Fields::is_zero(
      UInt8::to_field(x[0]) + UInt8::to_field(x[1]) + UInt8::to_field(x[2]) + UInt8::to_field(x[3]));
    1 - (hi_max * (1 - lo_zero))
  }

  inline fn gl_val(x: [UInt8::U8; 8]) -> Goldilocks {
    pack_bytes(x) - (1 - gl_lt_p(x)) * MODULUS
  }

  inline fn gl_from_bytes(x: [UInt8::U8; 8]) -> Goldilocks {
    assert_eq!(gl_lt_p(x), 1, "noncanonical Goldilocks encoding");
    pack_bytes(x)
  }

  fn gl_to_bytes(value: Goldilocks) -> [UInt8::U8; 8] {
    let bytes = checked_bytes(hint::<[Field; 8]>("bytes_le", value));
    assert_eq!(pack_bytes(bytes), value, "Goldilocks bytes do not recompose");
    assert_eq!(gl_lt_p(bytes), 1, "noncanonical Goldilocks value");
    bytes
  }

  fn gl_add(a: Goldilocks, b: Goldilocks) -> Goldilocks {
    gl_to_bytes(a);
    gl_to_bytes(b);
    let (result, carry) = hint::<(Field, Field)>("goldilocks.emulated.add", (a, b));
    gl_to_bytes(result);
    assert_eq!(carry * (carry - 1), 0, "Goldilocks addition carry is not boolean");
    assert_eq!(a + b, result + carry * MODULUS, "Goldilocks addition relation");
    result
  }

  fn gl_sub(a: Goldilocks, b: Goldilocks) -> Goldilocks {
    gl_to_bytes(a);
    gl_to_bytes(b);
    let (result, borrow) = hint::<(Field, Field)>("goldilocks.emulated.sub", (a, b));
    gl_to_bytes(result);
    assert_eq!(borrow * (borrow - 1), 0, "Goldilocks subtraction borrow is not boolean");
    assert_eq!(a + borrow * MODULUS, b + result, "Goldilocks subtraction relation");
    result
  }

  inline fn gl_neg(a: Goldilocks) -> Goldilocks { gl_sub(0, a) }

  fn gl_mul(a: Goldilocks, b: Goldilocks) -> Goldilocks {
    gl_to_bytes(a);
    gl_to_bytes(b);
    let (result, raw_quotient) = hint::<(Field, [Field; 8])>("goldilocks.emulated.mul", (a, b));
    let quotient = pack_bytes(checked_bytes(raw_quotient));
    gl_to_bytes(result);
    assert_eq!(a * b, quotient * MODULUS + result, "Goldilocks multiplication relation");
    result
  }

  fn gl_is_zero(a: Goldilocks) -> Field {
    gl_to_bytes(a);
    Fields::is_zero(a)
  }

  fn gl_eq(a: Goldilocks, b: Goldilocks) -> Field {
    gl_to_bytes(a);
    gl_to_bytes(b);
    Fields::is_zero(a - b)
  }

  fn gl_inverse(a: Goldilocks) -> Goldilocks {
    let inverse = hint::<Field>("goldilocks.emulated.inverse", a);
    let product = gl_mul(a, inverse);
    let zero = Fields::is_zero(a);
    assert_eq!(product, 1 - zero, "Goldilocks inverse relation");
    assert_eq!(zero * inverse, 0, "Goldilocks zero inverse");
    inverse
  }

  inline fn eg_add(a: ExtGoldilocks, b: ExtGoldilocks) -> ExtGoldilocks {
    [gl_add(a[0], b[0]), gl_add(a[1], b[1])]
  }
  inline fn eg_sub(a: ExtGoldilocks, b: ExtGoldilocks) -> ExtGoldilocks {
    [gl_sub(a[0], b[0]), gl_sub(a[1], b[1])]
  }
  inline fn eg_neg(a: ExtGoldilocks) -> ExtGoldilocks {
    [gl_neg(a[0]), gl_neg(a[1])]
  }
  inline fn eg_mul(a: ExtGoldilocks, b: ExtGoldilocks) -> ExtGoldilocks {
    [gl_add(gl_mul(a[0], b[0]), gl_mul(7, gl_mul(a[1], b[1]))),
     gl_add(gl_mul(a[0], b[1]), gl_mul(a[1], b[0]))]
  }
  inline fn eg_inverse(a: ExtGoldilocks) -> ExtGoldilocks {
    let norm = gl_sub(gl_mul(a[0], a[0]), gl_mul(7, gl_mul(a[1], a[1])));
    let inverse = gl_inverse(norm);
    [gl_mul(a[0], inverse), gl_mul(gl_neg(a[1]), inverse)]
  }
  inline fn eg_div(a: ExtGoldilocks, b: ExtGoldilocks) -> ExtGoldilocks {
    eg_mul(a, eg_inverse(b))
  }
  inline fn eg_eq(a: ExtGoldilocks, b: ExtGoldilocks) -> Field {
    gl_eq(a[0], b[0]) * gl_eq(a[1], b[1])
  }
}
⟧

def declarations : Modules.Program Nat := Goldilocks.signature.append implementation

def program : Modules.Program F := declarations.toField F

end Aiur.Library.Field.Goldilocks.Emulated
