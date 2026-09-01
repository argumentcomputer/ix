use multi_stark::p3_field::integers::QuotientMap;

pub mod protocol;
pub mod toplevel;

use aiur::G;
use lean_ffi::object::LeanRef;

#[inline]
pub(super) fn lean_unbox_nat_as_usize(obj: &impl LeanRef) -> usize {
  assert!(obj.is_scalar());
  obj.unbox_usize()
}

#[inline]
pub(super) fn lean_unbox_g(obj: &impl LeanRef) -> G {
  let u64 = obj.unbox_u64();
  unsafe { G::from_canonical_unchecked(u64) }
}

/// Specialize an exact-`Nat` constant (bytecode `Op.const` / match key)
/// into the field. Overflow is an ERROR: a constant `>= p` means the
/// field cannot represent this circuit — never wrap.
pub(super) fn lean_nat_as_field(obj: &impl LeanRef) -> G {
  use multi_stark::p3_field::{PrimeCharacteristicRing, PrimeField64};
  let n = lean_ffi::object::LeanNat::to_nat(obj);
  match n.to_u64() {
    Some(v) if v < G::ORDER_U64 => G::from_u64(v),
    _ => panic!(
      "constant {n} does not fit the field (order {}): the field cannot \
       represent this circuit",
      G::ORDER_U64
    ),
  }
}
