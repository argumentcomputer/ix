import Aiur.Library.U8
import Aiur.Library.Field
import Aiur.Library.Frontend
import Aiur.Library.U32.Goldilocks
import Aiur.Library.Field.Goldilocks.Signature

/-! Canonical Goldilocks encoding, inversion, and the cubic extension
$\mathbb{F}_p[X]/(X^3 - X - 1)$, shared with the recursive verifier. Advice consists only of
raw field values; ordinary constraints check inverses and byte encodings.
Unlike the bounded U32 implementation, these formulas select Goldilocks. -/
namespace Aiur.Library.Field.Goldilocks
open Aiur

def dependencies : Modules.Program Nat := U8.templates.append Library.Field.declarations

private def implementation : Modules.Program Nat := aiur_library% (dependencies.append signature) ⟦
module Goldilocks: GoldilocksSignature {
  type Goldilocks = Field;

  type ExtGoldilocks = [Goldilocks; 3];

  inline fn gl_add(a: Goldilocks, b: Goldilocks) -> Goldilocks { a + b }

  inline fn gl_sub(a: Goldilocks, b: Goldilocks) -> Goldilocks { a - b }

  inline fn gl_neg(a: Goldilocks) -> Goldilocks { 0 - a }

  inline fn gl_mul(a: Goldilocks, b: Goldilocks) -> Goldilocks { a * b }

  inline fn gl_is_zero(a: Goldilocks) -> Field { Fields::is_zero(a) }

  inline fn gl_eq(a: Goldilocks, b: Goldilocks) -> Field {
      Fields::is_zero(a - b)
    }

  inline fn gl_val(x: [UInt8::U8; 8]) -> Field {
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

  inline fn gl_from_bytes(x: [UInt8::U8; 8]) -> Goldilocks {
      assert_eq!(gl_lt_p(x), 1);
      gl_val(x)
    }

  inline fn gl_to_bytes(v: Field) -> [UInt8::U8; 8] {
      let b = hint::<[Field; 8]>("bytes_le", v);
      let (c0, c1) = UInt8::from_fields(b[0], b[1]);
      let (c2, c3) = UInt8::from_fields(b[2], b[3]);
      let (c4, c5) = UInt8::from_fields(b[4], b[5]);
      let (c6, c7) = UInt8::from_fields(b[6], b[7]);
      let r = [c0, c1, c2, c3, c4, c5, c6, c7];
      assert_eq!(gl_val(r), v);
      assert_eq!(gl_lt_p(r), 1);
      r
    }

  inline fn gl_inverse(x: Goldilocks::Goldilocks) -> Goldilocks::Goldilocks {
      let iv = hint::<Field>("goldilocks.inverse", x);
      let t = (x * iv) - 1;
      assert_eq!(x * t, 0);
      assert_eq!(iv * t, 0);
      iv
    }

  inline fn gl_inv_nonzero(x: Goldilocks::Goldilocks) -> Goldilocks::Goldilocks {
      let iv = hint::<Field>("goldilocks.inverse", x);
      assert_eq!(x * iv, 1);
      iv
    }

  inline fn eg_add(a: ExtGoldilocks, b: ExtGoldilocks) -> ExtGoldilocks {
      [gl_add(a[0], b[0]), gl_add(a[1], b[1]), gl_add(a[2], b[2])]
    }

  inline fn eg_sub(a: ExtGoldilocks, b: ExtGoldilocks) -> ExtGoldilocks {
      [gl_sub(a[0], b[0]), gl_sub(a[1], b[1]), gl_sub(a[2], b[2])]
    }

  inline fn eg_neg(a: ExtGoldilocks) -> ExtGoldilocks {
      [gl_neg(a[0]), gl_neg(a[1]), gl_neg(a[2])]
    }

  inline fn eg_mul(a: ExtGoldilocks, b: ExtGoldilocks) -> ExtGoldilocks {
      let v0 = gl_mul(a[0], b[0]);
      let v1 = gl_mul(a[1], b[1]);
      let v2 = gl_mul(a[2], b[2]);
      let m01 = gl_sub(gl_sub(gl_mul(gl_add(a[0], a[1]), gl_add(b[0], b[1])), v0), v1);
      let m02 = gl_sub(gl_sub(gl_mul(gl_add(a[0], a[2]), gl_add(b[0], b[2])), v0), v2);
      let m12 = gl_sub(gl_sub(gl_mul(gl_add(a[1], a[2]), gl_add(b[1], b[2])), v1), v2);
      [gl_add(v0, m12), gl_add(gl_add(m01, m12), v2), gl_add(gl_add(m02, v1), v2)]
    }

  inline fn eg_inverse(a: ExtGoldilocks) -> ExtGoldilocks {
      let s = gl_add(a[0], a[2]);
      let d0 = gl_sub(gl_mul(s, s), gl_mul(a[1], gl_add(a[1], a[2])));
      let d1 = gl_sub(gl_mul(a[2], a[2]), gl_mul(a[0], a[1]));
      let d2 = gl_sub(gl_mul(a[1], a[1]), gl_mul(a[2], s));
      let norm = gl_add(gl_add(gl_mul(a[0], d0), gl_mul(a[2], d1)), gl_mul(a[1], d2));
      let ninv = gl_inverse(norm);
      [gl_mul(d0, ninv), gl_mul(d1, ninv), gl_mul(d2, ninv)]
    }

  inline fn eg_inv_nonzero(a: ExtGoldilocks) -> ExtGoldilocks {
      let s = gl_add(a[0], a[2]);
      let d0 = gl_sub(gl_mul(s, s), gl_mul(a[1], gl_add(a[1], a[2])));
      let d1 = gl_sub(gl_mul(a[2], a[2]), gl_mul(a[0], a[1]));
      let d2 = gl_sub(gl_mul(a[1], a[1]), gl_mul(a[2], s));
      let norm = gl_add(gl_add(gl_mul(a[0], d0), gl_mul(a[2], d1)), gl_mul(a[1], d2));
      let ninv = gl_inv_nonzero(norm);
      [gl_mul(d0, ninv), gl_mul(d1, ninv), gl_mul(d2, ninv)]
    }

  inline fn eg_div(a: ExtGoldilocks, b: ExtGoldilocks) -> ExtGoldilocks {
      eg_mul(a, eg_inverse(b))
    }

  inline fn eg_div_nonzero(a: ExtGoldilocks, b: ExtGoldilocks) -> ExtGoldilocks {
      eg_mul(a, eg_inv_nonzero(b))
    }

  inline fn eg_eq(a: ExtGoldilocks, b: ExtGoldilocks) -> Field {
      gl_eq(a[0], b[0]) * gl_eq(a[1], b[1]) * gl_eq(a[2], b[2])
    }
}
⟧

def declarations : Modules.Program Nat := signature.append implementation

def program : Modules.Program U32.Goldilocks.F := declarations.toField U32.Goldilocks.F

end Aiur.Library.Field.Goldilocks
