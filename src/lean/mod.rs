//! Rust bindings for Lean, implemented by mimicking the memory layout of Lean's
//! low-level C objects.
//!
//! This crate must be kept in sync with `lean/lean.h`. Pay close attention to
//! definitions containing C code in their docstrings.

pub mod array;
pub mod boxed;
pub mod ctor;
pub mod external;
pub mod ffi;
pub mod object;
pub mod sarray;
pub mod string;

use std::ffi::c_void;

use crate::lean::boxed::{BoxedU64, BoxedUSize};

#[inline]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub fn as_ref_unsafe<'a, T>(ptr: *const T) -> &'a T {
    let t_ref = unsafe { ptr.as_ref() };
    t_ref.expect("Null pointer dereference")
}

#[inline]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub fn as_mut_unsafe<'a, T>(ptr: *mut T) -> &'a mut T {
    let t_ref = unsafe { ptr.as_mut() };
    t_ref.expect("Null pointer dereference")
}

/// ```c
/// bool lean_is_scalar(lean_object * o) { return ((size_t)(o) & 1) == 1; }
/// ```
#[inline]
pub fn lean_is_scalar<T>(ptr: *const T) -> bool {
    ptr as usize & 1 == 1
}

#[macro_export]
/// ```c
/// lean_object * lean_box(size_t n) { return (lean_object*)(((size_t)(n) << 1) | 1); }
/// ```
macro_rules! lean_box {
    ($e:expr) => {
        (($e << 1) | 1) as *const std::ffi::c_void
    };
}

/// ```c
/// size_t lean_unbox(lean_object * o) { return (size_t)(o) >> 1; }
/// ```
#[macro_export]
macro_rules! lean_unbox {
    ($t:ident, $e:expr) => {
        $t::try_from(($e as usize) >> 1).expect("Unintended truncation")
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
pub fn lean_unbox_u32(ptr: *const c_void) -> u32 {
    if cfg!(target_pointer_width = "32") {
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
pub fn lean_unbox_u64(ptr: *const c_void) -> u64 {
    let boxed_usize: &BoxedU64 = as_ref_unsafe(ptr.cast());
    boxed_usize.value
}

pub fn boxed_usize_ptr_to_usize(ptr: *const c_void) -> usize {
    let boxed_usize_ptr = ptr.cast::<BoxedUSize>();
    let boxed_usize = as_ref_unsafe(boxed_usize_ptr);
    boxed_usize.value
}

/// Emulates arrays of flexible size from C.
#[repr(C)]
pub struct CArray<T>([T; 0]);

impl<T> CArray<T> {
    #[inline]
    pub fn slice(&self, len: usize) -> &[T] {
        unsafe { std::slice::from_raw_parts(self.0.as_ptr(), len) }
    }

    #[inline]
    pub fn copy_from_slice(&mut self, src: &[T]) {
        unsafe {
            std::ptr::copy_nonoverlapping(src.as_ptr(), self.0.as_ptr() as *mut _, src.len());
        }
    }
}
