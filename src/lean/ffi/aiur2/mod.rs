use p3_field::PrimeCharacteristicRing;
use std::ffi::c_void;

use crate::{aiur2::G, lean::ffi::lean_is_scalar, lean_unbox};

pub mod protocol;
pub mod toplevel;

pub(super) fn lean_unbox_nat_as_usize(ptr: *const c_void) -> usize {
    assert!(lean_is_scalar(ptr));
    lean_unbox!(usize, ptr)
}

pub(super) fn lean_unbox_nat_as_g(ptr: *const c_void) -> G {
    assert!(lean_is_scalar(ptr));
    G::from_usize(lean_unbox!(usize, ptr))
}
