use super::{CArray, object::LeanObject};

/// ```c
/// typedef struct {
///     lean_object m_header;
///     size_t      m_size;
///     size_t      m_capacity;
///     uint8_t     m_data[];
/// } lean_sarray_object;
/// ```
#[repr(C)]
pub struct LeanSArrayObject {
    m_header: LeanObject,
    m_size: usize,
    m_capacity: usize,
    m_data: CArray<u8>,
}

impl LeanSArrayObject {
    #[inline]
    pub fn data(&self) -> &[u8] {
        self.m_data.slice(self.m_size)
    }
}
