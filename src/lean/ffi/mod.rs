pub mod aiur;
pub mod byte_array;
pub mod iroh;
pub mod keccak;
pub mod lean_env;

use std::ffi::{CStr, CString, c_char, c_void};

use crate::lean::{
    array::LeanArrayObject, as_ref_unsafe, lean_unbox_u32, sarray::LeanSArrayObject,
};

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
pub(crate) fn to_raw<T>(t: T) -> *const T {
    Box::into_raw(Box::new(t))
}

#[inline]
pub(super) fn drop_raw<T>(ptr: *mut T) {
    assert!(!ptr.is_null(), "Null pointer free attempt");
    let t = unsafe { Box::from_raw(ptr) };
    drop(t);
}

// Only used in the Iroh client for the moment
#[inline]
#[cfg_attr(
    any(
        not(feature = "net"),
        all(target_os = "macos", target_arch = "aarch64")
    ),
    allow(dead_code)
)]
pub(crate) fn raw_to_str<'a>(ptr: *const c_char) -> &'a str {
    let c_str = unsafe { CStr::from_ptr(ptr) };
    c_str.to_str().expect("Invalid UTF-8 string")
}

#[unsafe(no_mangle)]
extern "C" fn rs_boxed_u32s_are_equivalent_to_bytes(
    u32s: &LeanArrayObject,
    bytes: &LeanSArrayObject,
) -> bool {
    let u32s = u32s
        .to_vec(lean_unbox_u32)
        .into_iter()
        .flat_map(u32::to_le_bytes)
        .collect::<Vec<_>>();
    u32s == bytes.data()
}

#[repr(C)]
pub struct BytesData {
    size: usize,
    bytes_vec: *const Vec<u8>,
}

impl BytesData {
    #[inline]
    pub(super) fn from_vec(vec: Vec<u8>) -> Self {
        Self {
            size: vec.len(),
            bytes_vec: to_raw(vec),
        }
    }
}

#[unsafe(no_mangle)]
extern "C" fn rs_move_bytes(bytes_data: *mut BytesData, byte_array: &mut LeanSArrayObject) {
    let bytes_data = unsafe { Box::from_raw(bytes_data) };
    let bytes_vec = unsafe { Box::from_raw(bytes_data.bytes_vec as *mut Vec<_>) };
    byte_array.set_data(&bytes_vec);
    drop(bytes_vec);
    drop(bytes_data);
}
