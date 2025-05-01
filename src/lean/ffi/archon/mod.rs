pub mod arith_expr;
pub mod circuit;
pub mod protocol;
pub mod witness;

use binius_core::oracle::OracleId;
use binius_field::BinaryField128b;
use std::ffi::c_void;

use crate::lean::{
    ctor::LeanCtorObject,
    ffi::{as_ref_unsafe, boxed_usize_ptr_to_usize, external_ptr_to_u128},
};

pub(super) fn ctor_ptr_to_lc_factor(ptr: *const c_void) -> (OracleId, BinaryField128b) {
    let ctor_ptr = ptr.cast::<LeanCtorObject>();
    let ctor = as_ref_unsafe(ctor_ptr);
    let [oracle_id_ptr, u128_external_ptr] = ctor.objs();
    let oracle_id = boxed_usize_ptr_to_usize(oracle_id_ptr);
    let u128 = external_ptr_to_u128(u128_external_ptr);
    (oracle_id, BinaryField128b::new(u128))
}
