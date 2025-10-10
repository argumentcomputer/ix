use std::ffi::c_void;

use super::{CArray, object::LeanObject};

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

    #[inline]
    pub fn to_vec_with<T, C>(&self, map_fn: fn(*const c_void, &mut C) -> T, c: &mut C) -> Vec<T> {
        self.data().iter().map(|ptr| map_fn(*ptr, c)).collect()
    }

    pub fn set_data(&mut self, data: &[*const c_void]) {
        assert!(self.m_capacity >= data.len());
        self.m_data.copy_from_slice(data);
        self.m_size = data.len();
    }
}
