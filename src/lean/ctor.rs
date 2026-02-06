//! Lean constructor object layout and field access.

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

  /// Read a u64 scalar field from the constructor.
  /// `num_objs` is the number of object fields (pointers) in this constructor.
  /// `scalar_offset` is the byte offset within the scalar area.
  /// Scalar fields are stored after the object fields in memory.
  #[inline]
  pub fn get_scalar_u64(&self, num_objs: usize, scalar_offset: usize) -> u64 {
    // Scalar area starts after: header (8 bytes) + object pointers (8 bytes each)
    let base_ptr = (self as *const Self).cast::<u8>();
    let scalar_area = unsafe { base_ptr.add(8 + num_objs * 8 + scalar_offset) };
    unsafe { ptr::read_unaligned(scalar_area.cast::<u64>()) }
  }

  /// Read a u8 scalar field from the constructor.
  #[inline]
  pub fn get_scalar_u8(&self, num_objs: usize, scalar_offset: usize) -> u8 {
    let base_ptr = (self as *const Self).cast::<u8>();
    let scalar_area = unsafe { base_ptr.add(8 + num_objs * 8 + scalar_offset) };
    unsafe { *scalar_area }
  }

  /// Read a bool scalar field from the constructor.
  #[inline]
  pub fn get_scalar_bool(&self, num_objs: usize, scalar_offset: usize) -> bool {
    self.get_scalar_u8(num_objs, scalar_offset) != 0
  }
}
