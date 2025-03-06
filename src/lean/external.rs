use std::ffi::c_void;

use super::object::LeanObject;

/// ```c
/// typedef struct {
///     lean_object           m_header;
///     lean_external_class * m_class;
///     void *                m_data;
/// } lean_external_object;
/// ```
#[repr(C)]
pub struct LeanExternalObject {
    m_header: LeanObject,
    m_class: *const c_void,
    m_data: *const c_void,
}

impl LeanExternalObject {
    #[inline]
    pub fn cast_data<T>(&self) -> *const T {
        self.m_data.cast()
    }
}
