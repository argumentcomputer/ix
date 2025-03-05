use std::ffi::c_void;

use super::{object::LeanObject, CArray};

/// ```c
/// typedef struct {
///     lean_object   m_header;
///     lean_object * m_objs[];
/// } lean_ctor_object;
/// ```
#[repr(C)]
pub struct LeanCtorObject {
    pub m_header: LeanObject,
    pub m_objs: CArray<*const c_void>,
}
