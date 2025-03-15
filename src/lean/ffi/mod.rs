pub mod binius;
pub mod binius_arith_expr;
pub mod binius_boundary;
pub mod byte_array;

use std::ffi::{CStr, c_char, c_void};

use crate::lean::boxed::BoxedUSize;

/// ```c
/// typedef struct {
///     bool is_ok;
///     void *data;
/// } c_result;
/// ```
#[repr(C)]
pub struct CResult {
    pub is_ok: bool,
    pub data: *const c_void,
}

#[inline]
pub(super) fn to_raw<T>(t: T) -> *const T {
    Box::into_raw(Box::new(t))
}

#[inline]
pub(super) fn drop_raw<T>(ptr: *mut T) {
    assert!(!ptr.is_null(), "Null pointer free attempt");
    let t = unsafe { Box::from_raw(ptr) };
    drop(t);
}

#[inline]
pub(super) fn raw_to_str<'a>(ptr: *const c_char) -> &'a str {
    let c_str = unsafe { CStr::from_ptr(ptr) };
    c_str.to_str().expect("Invalid UTF-8 string")
}

#[inline]
pub(super) fn as_ref_unsafe<'a, T>(ptr: *const T) -> &'a T {
    let t_ref = unsafe { ptr.as_ref() };
    t_ref.expect("Null pointer dereference")
}

/// ```c
/// size_t lean_unbox(lean_object * o) { return (size_t)(o) >> 1; }
/// ```
#[macro_export]
macro_rules! lean_unbox {
    // For some reason it doesn't work as a type-parametric function.
    ($t:ident, $e:expr) => {
        $t::try_from($e as usize >> 1).expect("Cannot convert from usize")
    };
}

/// ```c
/// unsigned lean_unbox_uint32(b_lean_obj_arg o) {
///     if (sizeof(void*) == 4) {
///         /* 32-bit implementation */
///         return lean_ctor_get_uint32(o, 0);
///     } else {
///         /* 64-bit implementation */
///         return lean_unbox(o);
///     }
/// }
/// ```
#[inline]
pub(super) fn lean_unbox_u32(ptr: *const c_void) -> u32 {
    if size_of::<c_void>() == 4 {
        let boxed_usize: &BoxedUSize = as_ref_unsafe(ptr.cast());
        u32::try_from(boxed_usize.value).expect("Cannot convert from usize")
    } else {
        lean_unbox!(u32, ptr)
    }
}

/// ```c
/// uint64_t lean_unbox_uint64(b_lean_obj_arg o) {
///     return lean_ctor_get_uint64(o, 0);
/// }
/// ```
#[inline]
pub(super) fn lean_unbox_u64(ptr: *const c_void) -> u64 {
    let boxed_usize: &BoxedUSize = as_ref_unsafe(ptr.cast());
    boxed_usize.value as u64
}
