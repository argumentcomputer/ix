pub mod arith_expr;
pub mod circuit;
pub mod protocol;
pub mod transparent;
pub mod witness;

use binius_field::BinaryField128b;
use std::ffi::c_void;

use crate::{
    archon::OracleIdx,
    lean::{
        ctor::LeanCtorObject,
        ffi::{as_ref_unsafe, boxed_usize_ptr_to_usize, external_ptr_to_u128},
    },
};

#[inline]
pub(super) fn boxed_usize_ptr_to_oracle_idx(ptr: *const c_void) -> OracleIdx {
    OracleIdx(boxed_usize_ptr_to_usize(ptr))
}

pub(super) fn ctor_ptr_to_lc_factor(ptr: *const c_void) -> (OracleIdx, BinaryField128b) {
    let ctor_ptr = ptr.cast::<LeanCtorObject>();
    let ctor = as_ref_unsafe(ctor_ptr);
    let [oracle_idx_ptr, u128_external_ptr] = ctor.objs();
    let oracle_idx = boxed_usize_ptr_to_oracle_idx(oracle_idx_ptr);
    let u128 = external_ptr_to_u128(u128_external_ptr);
    (oracle_idx, BinaryField128b::new(u128))
}
