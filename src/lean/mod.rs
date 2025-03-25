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

impl<T: Copy> CArray<T> {
    #[inline]
    pub fn copy_from_slice(&mut self, src: &[T]) {
        assert_eq!(self.0.len(), src.len());
        self.0.copy_from_slice(src);
    }
}

impl<T> CArray<T> {
    #[inline]
    pub fn slice(&self, len: usize) -> &[T] {
        assert!(len <= self.0.len());
        &self.0[..len]
    }

    #[inline]
    pub fn copy_from_slice_unsafe(&mut self, src: &[T]) {
        assert_eq!(self.0.len(), src.len());
        unsafe {
            std::ptr::copy_nonoverlapping(src.as_ptr(), self.0.as_mut_ptr(), src.len());
        }
    }
}
