use super::object::LeanObject;

/// This is equivalent to a `lean_ctor_object` with `m_objs` of size 1.
#[repr(C)]
pub struct BoxedUSize {
    m_header: LeanObject,
    pub value: usize,
}

/// This is equivalent to a `lean_ctor_object` with `m_objs` of size 1 on x64
/// and 2 on x32.
#[repr(C)]
pub struct BoxedU64 {
    m_header: LeanObject,
    pub value: u64,
}
