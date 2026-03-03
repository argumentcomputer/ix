//! Rust bindings for Lean, implemented by mimicking the memory layout of Lean's
//! low-level C objects.
//!
//! The `lean` submodule contains auto-generated bindings from `lean.h` via
//! bindgen. Higher-level helpers and custom `#[repr(C)]` types are defined
//! alongside it in sibling modules.

#[allow(
  non_upper_case_globals,
  non_camel_case_types,
  non_snake_case,
  dead_code,
  unsafe_op_in_unsafe_fn,
  unused_qualifications,
  clippy::all,
  clippy::ptr_as_ptr,
  clippy::cast_possible_wrap,
  clippy::cast_possible_truncation,
  clippy::derive_partial_eq_without_eq
)]
pub mod lean_sys {
  include!(concat!(env!("OUT_DIR"), "/lean.rs"));
}

pub mod ffi;
pub mod nat;
pub mod object;

use std::ffi::{CString, c_void};

/// Create a CString from a str, stripping any interior null bytes.
/// Lean strings are length-prefixed and can contain null bytes, but the
/// `lean_mk_string` FFI requires a null-terminated C string. This function
/// ensures conversion always succeeds by filtering out interior nulls.
pub fn safe_cstring(s: &str) -> CString {
  CString::new(s).unwrap_or_else(|_| {
    let bytes: Vec<u8> = s.bytes().filter(|&b| b != 0).collect();
    CString::new(bytes).expect("filtered string should have no nulls")
  })
}

/// No-op foreach callback for external classes that hold no Lean references.
///
/// # Safety
/// Must only be used as a `lean_external_foreach_fn` callback.
pub unsafe extern "C" fn noop_foreach(
  _: *mut c_void,
  _: *mut lean_sys::lean_object,
) {
}
