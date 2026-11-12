import Aiur.Library.U8
import Aiur.Library.Frontend

/-! Goldilocks operations with a one-field representation. The representation
is shared by native Goldilocks and canonical Goldilocks residues embedded in
a larger field. Each provider is responsible for its reduction constraints.

`gl_val` reduces any eight-byte word modulo the Goldilocks modulus;
`gl_from_bytes` instead rejects noncanonical encodings. `gl_to_bytes` emits
the canonical representative, including when its argument is a bounded native
counter. Inversion maps zero to zero. The transparent signature checks the
operation types, while the provider's constraints establish these semantics. -/
namespace Aiur.Library.Field.Goldilocks
open Aiur

def signature : Modules.Program Nat := aiur_library% U8.templates ⟦
signature GoldilocksSignature {
  type Goldilocks = Field;
  type ExtGoldilocks = [Goldilocks; 2];
  fn gl_add(a: Goldilocks, b: Goldilocks) -> Goldilocks;
  fn gl_sub(a: Goldilocks, b: Goldilocks) -> Goldilocks;
  fn gl_neg(a: Goldilocks) -> Goldilocks;
  fn gl_mul(a: Goldilocks, b: Goldilocks) -> Goldilocks;
  fn gl_is_zero(a: Goldilocks) -> Field;
  fn gl_eq(a: Goldilocks, b: Goldilocks) -> Field;
  fn gl_val(bytes: [UInt8::U8; 8]) -> Goldilocks;
  fn gl_lt_p(bytes: [UInt8::U8; 8]) -> Field;
  fn gl_from_bytes(bytes: [UInt8::U8; 8]) -> Goldilocks;
  fn gl_to_bytes(value: Goldilocks) -> [UInt8::U8; 8];
  fn gl_inverse(value: Goldilocks) -> Goldilocks;
  fn eg_add(a: ExtGoldilocks, b: ExtGoldilocks) -> ExtGoldilocks;
  fn eg_sub(a: ExtGoldilocks, b: ExtGoldilocks) -> ExtGoldilocks;
  fn eg_neg(a: ExtGoldilocks) -> ExtGoldilocks;
  fn eg_mul(a: ExtGoldilocks, b: ExtGoldilocks) -> ExtGoldilocks;
  fn eg_inverse(a: ExtGoldilocks) -> ExtGoldilocks;
  fn eg_div(a: ExtGoldilocks, b: ExtGoldilocks) -> ExtGoldilocks;
  fn eg_eq(a: ExtGoldilocks, b: ExtGoldilocks) -> Field;
}
⟧

end Aiur.Library.Field.Goldilocks
