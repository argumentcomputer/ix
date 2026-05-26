use multi_stark::p3_field::integers::QuotientMap;

pub mod protocol;
pub mod toplevel;

use crate::aiur::G;
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
