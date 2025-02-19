//! Rust bindings for Lean, implemented by mimicking the memory layout of Lean's
//! low-level C objects.
//!
//! This crate must be kept in sync with `lean/lean.h`. Pay close attention to
//! definitions containing C code in their docstrings.

pub mod ffi;
pub mod object;
pub mod sarray;

use std::{
    alloc::{alloc, handle_alloc_error, Layout},
    ptr, slice,
};

/// Emulates arrays of flexible size from C.
#[repr(C)]
pub struct CArray<T>([T; 0]);

impl<T> CArray<T> {
    #[inline]
    pub fn slice(&self, len: usize) -> &[T] {
        unsafe { slice::from_raw_parts(self.0.as_ptr(), len) }
    }

    #[inline]
    pub fn copy_from_slice(&self, slice: &[T]) {
        unsafe {
            ptr::copy_nonoverlapping(slice.as_ptr(), self.0.as_ptr() as *mut _, slice.len());
        }
    }
}

#[inline]
pub fn alloc_layout<T>(layout: Layout) -> *mut T {
    let ptr = unsafe { alloc(layout) } as *mut T;
    if ptr.is_null() {
        handle_alloc_error(layout);
    }
    ptr
}
