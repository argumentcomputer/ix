use std::ffi::c_void;

use crate::lean::{lean::lean_alloc_sarray, lean_sarray_set_data};

#[unsafe(no_mangle)]
extern "C" fn c_u16_to_le_bytes(v: u16) -> *mut c_void {
  mk_byte_array(&v.to_le_bytes())
}

#[unsafe(no_mangle)]
extern "C" fn c_u32_to_le_bytes(v: u32) -> *mut c_void {
  mk_byte_array(&v.to_le_bytes())
}

#[unsafe(no_mangle)]
extern "C" fn c_u64_to_le_bytes(v: u64) -> *mut c_void {
  mk_byte_array(&v.to_le_bytes())
}

#[unsafe(no_mangle)]
extern "C" fn c_usize_to_le_bytes(v: usize) -> *mut c_void {
  mk_byte_array(&v.to_le_bytes())
}

#[inline]
fn mk_byte_array(bytes: &[u8]) -> *mut c_void {
  let len = bytes.len();
  let arr_ptr = unsafe { lean_alloc_sarray(1, len, len) };
  unsafe { lean_sarray_set_data(arr_ptr.cast(), bytes) };
  arr_ptr.cast()
}
