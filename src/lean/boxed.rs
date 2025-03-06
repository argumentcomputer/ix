use super::object::LeanObject;

/// This is equivalent to `lean_ctor_object` with `*m_objs` cast to `size_t`.
#[repr(C)]
pub struct BoxedUSize {
    m_header: LeanObject,
    pub value: usize,
}
