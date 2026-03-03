use multi_stark::p3_field::integers::QuotientMap;

pub mod protocol;
pub mod toplevel;

use crate::{aiur::G, lean::object::LeanObject};

#[inline]
pub(super) fn lean_unbox_nat_as_usize(obj: LeanObject) -> usize {
  assert!(obj.is_scalar());
  obj.unbox_usize()
}

#[inline]
pub(super) fn lean_unbox_g(obj: LeanObject) -> G {
  let u64 = obj.unbox_u64();
  unsafe { G::from_canonical_unchecked(u64) }
}
