use std::ffi::CString;

use crate::lean::{
    ffi::{CResult, c_char, to_raw},
    sarray::LeanSArrayObject,
};

#[unsafe(no_mangle)]
extern "C" fn rs_iroh_send(_bytes: &LeanSArrayObject) -> *const CResult {
    let msg_str = "Iroh functions not supported MacOS aarch64-darwin or when the Rust `net` feature is disabled";
    // TODO: Print `CResult` from Lean instead
    println!("{msg_str}");
    let msg = CString::new(msg_str).expect("CString::new failure");
    let c_result = CResult {
        is_ok: true,
        data: msg.into_raw().cast(),
    };
    to_raw(c_result)
}

#[unsafe(no_mangle)]
extern "C" fn rs_iroh_recv(
    _ticket: *const c_char,
    _buffer: &mut LeanSArrayObject,
    _buffer_capacity: usize,
) -> *const CResult {
    let msg_str = "Iroh functions not supported MacOS aarch64-darwin or when the Rust `net` feature is disabled";
    // TODO: Print `CResult` from Lean instead
    println!("{msg_str}");
    let msg = CString::new(msg_str).expect("CString::new failure");
    let c_result = CResult {
        is_ok: false,
        data: msg.into_raw().cast(),
    };
    to_raw(c_result)
}
