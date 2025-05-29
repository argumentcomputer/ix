pub mod archon;
pub mod binius;
pub mod byte_array;
pub mod iroh;
pub mod keccak;
pub mod u128;

use std::ffi::{CStr, CString, c_char, c_void};

use crate::lean::{boxed::BoxedUSize, external::LeanExternalObject};

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

// Free a `CResult` object that corresponds to the Rust type `Result<(), String>`
#[unsafe(no_mangle)]
extern "C" fn rs__c_result_unit_string_free(ptr: *mut CResult) {
    let c_result = as_ref_unsafe(ptr);
    // Free the string error message
    if !c_result.is_ok {
        let char_ptr = c_result.data as *mut c_char;
        let c_string = unsafe { CString::from_raw(char_ptr) };
        drop(c_string);
    }
    drop_raw(ptr);
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
/// bool lean_is_scalar(lean_object * o) { return ((size_t)(o) & 1) == 1; }
/// ```
#[inline]
pub(super) fn lean_is_scalar<T>(ptr: *const T) -> bool {
    ptr as usize & 1 == 1
}

/// ```c
/// size_t lean_unbox(lean_object * o) { return (size_t)(o) >> 1; }
/// ```
#[macro_export]
macro_rules! lean_unbox {
    ($t:ident, $e:expr) => {
        $e as $t >> 1
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
#[allow(dead_code)]
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

pub(super) fn boxed_usize_ptr_to_usize(ptr: *const c_void) -> usize {
    let boxed_usize_ptr = ptr.cast::<BoxedUSize>();
    let boxed_usize = as_ref_unsafe(boxed_usize_ptr);
    boxed_usize.value
}

pub(super) fn external_ptr_to_u128(ptr: *const c_void) -> u128 {
    let u128_external = as_ref_unsafe(ptr.cast::<LeanExternalObject>());
    *as_ref_unsafe(u128_external.cast_data())
}
