use std::ffi::c_void;

use crate::lean::lean_except_error_string;

/// `Iroh.Serve.serve' : Unit → Except String Unit`
#[unsafe(no_mangle)]
extern "C" fn rs_iroh_serve() -> *mut c_void {
  lean_except_error_string(
    "Iroh functions not supported when the Rust `net` feature is disabled \
     or on MacOS aarch64-darwin",
  )
}
