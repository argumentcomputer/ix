use multi_stark::p3_field::integers::QuotientMap;
use std::ffi::c_void;

use crate::{
    aiur2::G,
    lean::ffi::{lean_is_scalar, lean_unbox_u64},
    lean_unbox,
};

pub mod protocol;
pub mod toplevel;

#[inline]
pub(super) fn lean_unbox_nat_as_usize(ptr: *const c_void) -> usize {
    assert!(lean_is_scalar(ptr));
    lean_unbox!(usize, ptr)
}

#[inline]
pub(super) fn lean_unbox_g(ptr: *const c_void) -> G {
    let u64 = lean_unbox_u64(ptr);
    unsafe { G::from_canonical_unchecked(u64) }
}
