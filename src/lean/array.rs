use std::ffi::c_void;

use super::{object::LeanObject, CArray};

/// ```c
/// typedef struct {
///     lean_object   m_header;
///     size_t        m_size;
///     size_t        m_capacity;
///     lean_object * m_data[];
/// } lean_array_object;
/// ```
#[repr(C)]
pub struct LeanArrayObject {
    m_header: LeanObject,
    m_size: usize,
    m_capacity: usize,
    m_data: CArray<*const c_void>,
}

impl LeanArrayObject {
    #[inline]
    pub fn data(&self) -> &[*const c_void] {
        self.m_data.slice(self.m_size)
    }

    #[inline]
    pub fn to_vec<T>(&self, map_fn: fn(*const c_void) -> T) -> Vec<T> {
        self.data().iter().map(|ptr| map_fn(*ptr)).collect()
    }
}
