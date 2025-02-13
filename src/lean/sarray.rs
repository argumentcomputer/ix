use std::{
    alloc::{alloc, handle_alloc_error, Layout},
    ptr,
};

use super::{Array, LeanObject};

const LEAN_SCALAR_ARRAY: u8 = 248;

/// ```c
/// typedef struct {
/// lean_object   m_header;
/// size_t        m_size;
/// size_t        m_capacity;
/// uint8_t       m_data[];
/// } lean_sarray_object;
/// ```
#[repr(C)]
pub struct LeanSArrayObject {
    pub m_header: LeanObject,
    pub m_size: usize,
    pub m_capacity: usize,
    pub m_data: Array<u8>,
}

impl LeanSArrayObject {
    #[inline]
    pub fn data(&self) -> &[u8] {
        self.m_data.slice(self.m_size)
    }

    pub fn from_slice(slice: &[u8]) -> *const Self {
        let len = slice.len();
        let layout = Layout::from_size_align(
            size_of::<LeanSArrayObject>() + len,
            align_of::<LeanSArrayObject>(),
        )
        .expect("Couldn't compute the memory layout");

        let ptr = unsafe { alloc(layout) as *mut LeanSArrayObject };
        if ptr.is_null() {
            handle_alloc_error(layout);
        }

        let obj = LeanObject::new(1, 0, 1, LEAN_SCALAR_ARRAY);

        unsafe {
            ptr::write(&mut (*ptr).m_header, obj);
            ptr::write(&mut (*ptr).m_size, len);
            ptr::write(&mut (*ptr).m_capacity, len);
            (*ptr).m_data.copy_from_slice(slice);
        }

        ptr
    }
}
