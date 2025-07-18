use p3_field::{PrimeField64, integers::QuotientMap};
use std::ffi::c_void;

use crate::{
    aiur2::G,
    lean::{
        array::LeanArrayObject,
        boxed::BoxedU64,
        ffi::{as_mut_unsafe, lean_is_scalar, lean_unbox_u64},
    },
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

pub(super) fn set_lean_array_data(array: &mut LeanArrayObject, gs: &[G]) {
    let array_data = array.data();
    assert_eq!(array_data.len(), gs.len());
    array_data.iter().zip(gs).for_each(|(ptr, g)| {
        let boxed_u64 = as_mut_unsafe(*ptr as *mut BoxedU64);
        boxed_u64.value = g.as_canonical_u64();
    });
}
