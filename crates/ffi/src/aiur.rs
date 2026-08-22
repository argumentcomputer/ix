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

/// Field-side decoding of Lean values, per outer field: the checked
/// exact-`Nat` embedding (bytecode constants / match keys) and the
/// boxed-u64 wire value (public inputs, claims). Implemented for the
/// default Goldilocks and (behind `kzg`) the BLS12-381 scalar field.
pub(super) trait LeanField: aiur::AiurField {
  fn from_lean_nat(obj: &impl LeanRef) -> Self;
  /// Used by the `kzg`-gated externs; the Goldilocks paths unbox directly.
  #[allow(dead_code)]
  fn from_lean_u64(obj: &impl LeanRef) -> Self;
}

impl LeanField for G {
  fn from_lean_nat(obj: &impl LeanRef) -> Self {
    lean_nat_as_field(obj)
  }
  fn from_lean_u64(obj: &impl LeanRef) -> Self {
    lean_unbox_g(obj)
  }
}

#[cfg(feature = "kzg")]
impl LeanField for multi_stark::ark_adapter::Scalar {
  fn from_lean_nat(obj: &impl LeanRef) -> Self {
    use multi_stark::traits::Field;
    let n = lean_ffi::object::LeanNat::to_nat(obj);
    // Every constant a toplevel ships today is < 2^64 (bytes, wire
    // words, counters), which embeds exactly in the ~2^255 scalar
    // field. Larger exact naturals would need a multi-limb embedding —
    // reject loudly instead of guessing.
    match n.to_u64() {
      Some(v) => Self::from_u64(v),
      None => panic!(
        "constant {n} exceeds 2^64: multi-limb constant embedding is not \
         implemented for the BLS12-381 scalar field"
      ),
    }
  }
  fn from_lean_u64(obj: &impl LeanRef) -> Self {
    use multi_stark::traits::Field;
    Self::from_u64(obj.unbox_u64())
  }
}
