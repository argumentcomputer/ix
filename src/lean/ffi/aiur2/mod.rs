use p3_field::{PrimeCharacteristicRing, PrimeField64};
use std::ffi::c_void;

use crate::{
    aiur2::G,
    lean::{array::LeanArrayObject, ffi::lean_is_scalar},
    lean_unbox,
};

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

pub(super) fn set_lean_array_data(array: &mut LeanArrayObject, gs: &[G]) {
    let boxed_values = gs
        .iter()
        .map(|g| {
            let g_u64 = g.as_canonical_u64();
            let g_usize = usize::try_from(g_u64).expect("Not enough room for 64 bits");
            let g_boxed = (g_usize << 1) | 1;
            g_boxed as *const c_void
        })
        .collect::<Vec<_>>();
    array.set_data(&boxed_values);
}
