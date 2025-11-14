use crate::lean::{CArray, object::LeanObject};

/// ```c
/// typedef struct {
///     lean_object m_header;
///     size_t      m_size;     /* byte length including '\0' terminator */
///     size_t      m_capacity;
///     size_t      m_length;   /* UTF8 length */
///     char        m_data[];
/// } lean_string_object;
/// ```
#[repr(C)]
pub struct LeanStringObject {
  m_header: LeanObject,
  m_size: usize,
  m_capacity: usize,
  m_length: usize,
  m_data: CArray<u8>,
}

impl LeanStringObject {
  #[inline]
  pub fn as_string(&self) -> String {
    let bytes = self.m_data.slice(self.m_size - 1); // Ignore the last '\0'
    unsafe { String::from_utf8_unchecked(bytes.to_vec()) }
  }
}
