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

/// Emulates arrays of flexible size from C.
#[repr(C)]
pub struct CArray<T>([T; 0]);

impl<T> CArray<T> {
    #[inline]
    pub fn slice(&self, len: usize) -> &[T] {
        unsafe { std::slice::from_raw_parts(self.0.as_ptr(), len) }
    }

    #[inline]
    pub fn copy_from_slice(&self, src: &[T]) {
        unsafe {
            std::ptr::copy_nonoverlapping(src.as_ptr(), self.0.as_ptr() as *mut _, src.len());
        }
    }
}
