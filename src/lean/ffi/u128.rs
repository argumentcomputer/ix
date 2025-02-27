use crate::lean::{
    external::LeanExternalObject,
    ffi::{drop_raw, to_raw},
    sarray::LeanSArrayObject,
    CArray,
};

#[no_mangle]
extern "C" fn rs_u128_free(ptr: *mut u128) {
    drop_raw(ptr);
}

#[no_mangle]
extern "C" fn rs_u128_of_hi_lo(hi: u64, lo: u64) -> *const u128 {
    to_raw(((hi as u128) << 64) | (lo as u128))
}

#[no_mangle]
extern "C" fn rs_u128_to_le_bytes(u: &LeanExternalObject) -> *const LeanSArrayObject {
    let carray_ptr = u.m_data as *const CArray<u8>;
    let carray = unsafe { &*carray_ptr };
    LeanSArrayObject::from_slice(carray.slice(size_of::<u128>()))
}
