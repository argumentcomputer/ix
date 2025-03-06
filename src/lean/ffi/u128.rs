use crate::lean::{
    CArray,
    external::LeanExternalObject,
    ffi::{as_ref_unsafe, drop_raw, to_raw},
    sarray::LeanSArrayObject,
};

#[unsafe(no_mangle)]
extern "C" fn rs_u128_free(ptr: *mut u128) {
    drop_raw(ptr);
}

#[unsafe(no_mangle)]
extern "C" fn rs_u128_of_hi_lo(hi: u64, lo: u64) -> *const u128 {
    to_raw((u128::from(hi) << 64) | u128::from(lo))
}

#[unsafe(no_mangle)]
extern "C" fn rs_u128_to_le_bytes(u: &LeanExternalObject) -> *const LeanSArrayObject {
    let carray_ptr = u.m_data.cast::<CArray<u8>>();
    let carray = as_ref_unsafe(carray_ptr);
    LeanSArrayObject::from_slice(carray.slice(size_of::<u128>()))
}
