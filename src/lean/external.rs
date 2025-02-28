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
    _header: LeanObject,
    _class: *const c_void,
    pub m_data: *const c_void,
}
