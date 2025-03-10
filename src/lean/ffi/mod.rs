pub mod binius;
pub mod binius_arith_expr;
pub mod byte_array;
pub mod u128;
pub mod u64;
pub mod usize;

use std::ffi::{CStr, c_char};

#[unsafe(no_mangle)]
extern "C" fn rs_noop() {}

#[inline]
pub fn to_raw<T>(t: T) -> *const T {
    Box::into_raw(Box::new(t))
}

#[inline]
pub(super) fn drop_raw<T>(ptr: *mut T) {
    assert!(!ptr.is_null(), "Double-free attempt");
    let t = unsafe { Box::from_raw(ptr) };
    drop(t);
}

#[inline]
pub(super) fn raw_to_str<'a>(ptr: *const c_char) -> &'a str {
    let c_str = unsafe { CStr::from_ptr(ptr) };
    c_str.to_str().expect("Invalid UTF-8 string")
}

#[inline]
pub(super) fn as_ref_unsafe<'a, T>(input: *const T) -> &'a T {
    unsafe { input.as_ref().expect("Null pointer dereference") }
}
