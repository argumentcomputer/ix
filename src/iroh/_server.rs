use std::ffi::CString;

use crate::lean::ffi::{CResult, to_raw};

#[unsafe(no_mangle)]
extern "C" fn rs_iroh_serve() -> *const CResult {
    let msg = CString::new("Iroh functions not supported when the Rust `net` feature is disabled or on MacOS aarch64-darwin").expect("CString::new failure");
    let c_result = CResult {
        is_ok: false,
        data: msg.into_raw().cast(),
    };
    to_raw(c_result)
}
