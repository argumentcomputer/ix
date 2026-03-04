//! Low-level Lean FFI bindings and type-safe wrappers.
//!
//! The `include` submodule contains auto-generated bindings from `lean.h` via
//! bindgen. Higher-level helpers are in `object` and `nat`.

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
pub mod include {
  include!(concat!(env!("OUT_DIR"), "/lean.rs"));
}

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
  _: *mut include::lean_object,
) {
}

/// Generate a `#[repr(transparent)]` newtype over `LeanObject` for a specific
/// Lean type, with `Deref`, `From`, and a `new` constructor.
#[macro_export]
macro_rules! lean_domain_type {
  ($($(#[$meta:meta])* $name:ident;)*) => {$(
    $(#[$meta])*
    #[derive(Clone, Copy)]
    #[repr(transparent)]
    pub struct $name($crate::object::LeanObject);

    impl std::ops::Deref for $name {
      type Target = $crate::object::LeanObject;
      #[inline]
      fn deref(&self) -> &$crate::object::LeanObject { &self.0 }
    }

    impl From<$name> for $crate::object::LeanObject {
      #[inline]
      fn from(x: $name) -> Self { x.0 }
    }

    impl $name {
      #[inline]
      pub fn new(obj: $crate::object::LeanObject) -> Self { Self(obj) }
    }
  )*};
}
