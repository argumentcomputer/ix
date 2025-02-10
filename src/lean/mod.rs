pub mod ffi;
pub mod sarray;

use std::ptr;

/// ```c
/// typedef struct {
/// int      m_rc;
/// unsigned m_cs_sz:16;
/// unsigned m_other:8;
/// unsigned m_tag:8;
/// } lean_object;
/// ```
#[repr(C)]
pub struct LeanObject {
    pub m_rc: i32,
    packed_bits: u32,
}

impl LeanObject {
    #[inline]
    pub fn new(m_rc: i32, m_cs_sz: u16, m_other: u8, m_tag: u8) -> Self {
        let packed_bits = ((m_cs_sz as u32) & 0xFFFF)
            | (((m_other as u32) & 0xFF) << 16)
            | (((m_tag as u32) & 0xFF) << 24);
        Self { m_rc, packed_bits }
    }

    #[inline]
    pub fn m_cs_sz(&self) -> u16 {
        (self.packed_bits & 0xFFFF) as u16
    }

    #[inline]
    pub fn m_other(&self) -> u8 {
        ((self.packed_bits >> 16) & 0xFF) as u8
    }

    #[inline]
    pub fn m_tag(&self) -> u8 {
        ((self.packed_bits >> 24) & 0xFF) as u8
    }
}

/// Emulates arrays of flexible size from C.
#[repr(C)]
pub struct Array<T>([T; 0]);

impl<T> Array<T> {
    #[inline]
    pub fn slice(&self, len: usize) -> &[T] {
        unsafe { std::slice::from_raw_parts(self.0.as_ptr(), len) }
    }

    #[inline]
    pub fn copy_from_slice(&self, slice: &[T]) {
        unsafe {
            ptr::copy_nonoverlapping(slice.as_ptr(), self.0.as_ptr() as *mut _, slice.len());
        }
    }
}
