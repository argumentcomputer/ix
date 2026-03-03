use multi_stark::p3_field::integers::QuotientMap;

pub mod protocol;
pub mod toplevel;

use crate::{aiur::G, lean::obj::LeanObj};

#[inline]
pub(super) fn lean_unbox_nat_as_usize(obj: LeanObj) -> usize {
  assert!(obj.is_scalar());
  obj.unbox_usize()
}

#[inline]
pub(super) fn lean_unbox_g(obj: LeanObj) -> G {
  let u64 = obj.unbox_u64();
  unsafe { G::from_canonical_unchecked(u64) }
}
