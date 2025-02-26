pub mod binius;
pub mod byte_array;
pub mod u128;

use std::ffi::{c_char, CStr};

#[no_mangle]
extern "C" fn rs_noop() {}

#[inline]
pub fn to_raw<T>(t: T) -> *const T {
    Box::into_raw(Box::new(t))
}

#[inline]
pub(super) fn drop_raw<T>(ptr: *mut T) {
    if ptr.is_null() {
        panic!("Double-free attempt");
    }
    let t = unsafe { Box::from_raw(ptr) };
    drop(t);
}

#[inline]
pub(super) fn raw_to_str<'a>(ptr: *const c_char) -> &'a str {
    let c_str = unsafe { CStr::from_ptr(ptr) };
    c_str.to_str().expect("Invalid UTF-8 string")
}
