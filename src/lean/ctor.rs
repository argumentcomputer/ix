use std::{ffi::c_void, ptr};

use super::{CArray, object::LeanObject};

/// ```c
/// typedef struct {
///     lean_object   m_header;
///     lean_object * m_objs[];
/// } lean_ctor_object;
/// ```
#[repr(C)]
pub struct LeanCtorObject {
  m_header: LeanObject,
  m_objs: CArray<*const c_void>,
}

impl LeanCtorObject {
  #[inline]
  pub fn tag(&self) -> u8 {
    self.m_header.m_tag()
  }

  /// The number of objects must be known at compile time, given the context
  /// in which the data is being read.
  #[inline]
  pub fn objs<const N: usize>(&self) -> [*const c_void; N] {
    let mut ptrs = [ptr::null(); N];
    ptrs.copy_from_slice(self.m_objs.slice(N));
    ptrs
  }

  #[inline]
  pub fn set_objs(&mut self, data: &[*const c_void]) {
    self.m_objs.copy_from_slice(data);
  }
}
