use crate::lean::ffi::{BytesData, CResult, to_raw};
use crate::lean::{as_ref_unsafe, ffi::drop_raw};

use std::ffi::{CString, c_char};

#[repr(C)]
pub struct PutResponseFFI {
    pub message: *mut c_char,
    pub hash: *mut c_char,
}

impl PutResponseFFI {
    pub fn new(message: &str, hash: &str) -> Self {
        let message = CString::new(message).unwrap().into_raw();
        let hash = CString::new(hash).unwrap().into_raw();
        PutResponseFFI { message, hash }
    }
}

#[repr(C)]
pub struct GetResponseFFI {
    pub message: *mut c_char,
    pub hash: *mut c_char,
    pub bytes: *const BytesData,
}

impl GetResponseFFI {
    pub fn new(message: &str, hash: &str, bytes: &[u8]) -> Self {
        let message = CString::new(message).unwrap().into_raw();
        let hash = CString::new(hash).unwrap().into_raw();
        let bytes = to_raw(BytesData::from_vec(bytes.to_vec()));
        GetResponseFFI {
            message,
            hash,
            bytes,
        }
    }
}

// Frees a `CResult` object that corresponds to the Rust type `Result<PutResponseFFI, String>`
#[unsafe(no_mangle)]
extern "C" fn rs__c_result_iroh_put_response_string_free(ptr: *mut CResult) {
    let c_result = as_ref_unsafe(ptr);
    // Frees the `PutResponseFFI` struct and inner fields
    if c_result.is_ok {
        let put_response_ptr = c_result.data as *mut PutResponseFFI;
        let put_response = as_ref_unsafe(put_response_ptr);
        let message = unsafe { CString::from_raw(put_response.message) };
        let hash = unsafe { CString::from_raw(put_response.hash) };
        drop(message);
        drop(hash);
        drop_raw(put_response_ptr);
    }
    // Or free the String error message
    else {
        let char_ptr = c_result.data as *mut c_char;
        let c_string = unsafe { CString::from_raw(char_ptr) };
        drop(c_string);
    }
    drop_raw(ptr);
}

// Frees a `CResult` object that corresponds to the Rust type `Result<GetResponseFFI, String>`
#[unsafe(no_mangle)]
extern "C" fn rs__c_result_iroh_get_response_string_free(ptr: *mut CResult) {
    let c_result = as_ref_unsafe(ptr);
    // Frees the `GetResponseFFI` struct and inner fields
    // `Bytes` is already freed by `rs_move_bytes`
    if c_result.is_ok {
        let get_response_ptr = c_result.data as *mut GetResponseFFI;
        let get_response = as_ref_unsafe(get_response_ptr);
        let message = unsafe { CString::from_raw(get_response.message) };
        let hash = unsafe { CString::from_raw(get_response.hash) };
        drop(message);
        drop(hash);
        drop_raw(get_response_ptr);
    }
    // Or free the String error message
    else {
        let char_ptr = c_result.data as *mut c_char;
        let c_string = unsafe { CString::from_raw(char_ptr) };
        drop(c_string);
    }
    drop_raw(ptr);
}
