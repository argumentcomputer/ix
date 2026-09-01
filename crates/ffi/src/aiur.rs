use multi_stark::p3_field::integers::QuotientMap;

pub mod hypercube;
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
pub(super) fn lean_nat_as_field_in<F: multi_stark::p3_field::PrimeField64>(
  obj: &impl LeanRef,
) -> F {
  let n = lean_ffi::object::LeanNat::to_nat(obj);
  match n.to_u64() {
    Some(v) if v < F::ORDER_U64 => F::from_u64(v),
    _ => panic!(
      "constant {n} does not fit the field (order {}): the field cannot \
       represent this circuit",
      F::ORDER_U64
    ),
  }
}

/// Unbox a boxed `u64` as a field element of `F`, checked canonical.
pub(super) fn lean_unbox_field_in<F: multi_stark::p3_field::PrimeField64>(
  obj: &impl LeanRef,
) -> F {
  let v = obj.unbox_u64();
  assert!(
    v < F::ORDER_U64,
    "value {v} is not canonical in the field (order {})",
    F::ORDER_U64
  );
  F::from_u64(v)
}
