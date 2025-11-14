use std::ffi::{CString, c_char};

use crate::lean::{
  array::LeanArrayObject,
  ffi::{CResult, to_raw},
};

#[unsafe(no_mangle)]
extern "C" fn rs_iroh_put(
  _node_id: *const c_char,
  _addrs: &LeanArrayObject,
  _relay_url: *const c_char,
  _file_path: *const c_char,
) -> *const CResult {
  let msg = CString::new("Iroh functions not supported when the Rust `net` feature is disabled or on MacOS aarch64-darwin").expect("CString::new failure");
  let c_result = CResult { is_ok: false, data: msg.into_raw().cast() };
  to_raw(c_result)
}

#[unsafe(no_mangle)]
extern "C" fn rs_iroh_get(
  _node_id: *const c_char,
  _addrs: &LeanArrayObject,
  _relay_url: *const c_char,
  _hash: *const c_char,
) -> *const CResult {
  let msg = CString::new("Iroh functions not supported when the Rust `net` feature is disabled or on MacOS aarch64-darwin").expect("CString::new failure");
  let c_result = CResult { is_ok: false, data: msg.into_raw().cast() };
  to_raw(c_result)
}
