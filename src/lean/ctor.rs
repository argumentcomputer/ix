use super::{object::LeanObject, CArray};

/// ```c
/// typedef struct {
///     lean_object   m_header;
///     lean_object * m_objs[];
/// } lean_ctor_object;
/// ```
#[repr(C)]
pub struct LeanCtorObject<T> {
    pub m_header: LeanObject,
    pub m_objs: CArray<*const T>,
}
