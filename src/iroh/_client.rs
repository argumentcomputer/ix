use std::ffi::c_void;

use crate::lean::{array::LeanArrayObject, lean_except_error_string};

const ERR_MSG: &str =
  "Iroh functions not supported when the Rust `net` feature is disabled \
   or on MacOS aarch64-darwin";

/// `Iroh.Connect.putBytes' : @& String → @& Array String → @& String → @& String → Except String PutResponse`
#[unsafe(no_mangle)]
extern "C" fn c_rs_iroh_put(
  _node_id: *const c_void,
  _addrs: &LeanArrayObject,
  _relay_url: *const c_void,
  _input: *const c_void,
) -> *mut c_void {
  lean_except_error_string(ERR_MSG)
}

/// `Iroh.Connect.getBytes' : @& String → @& Array String → @& String → @& String → Except String GetResponse`
#[unsafe(no_mangle)]
extern "C" fn c_rs_iroh_get(
  _node_id: *const c_void,
  _addrs: &LeanArrayObject,
  _relay_url: *const c_void,
  _hash: *const c_void,
) -> *mut c_void {
  lean_except_error_string(ERR_MSG)
}
