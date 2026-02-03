//! Rust bindings for Lean, implemented by mimicking the memory layout of Lean's
//! low-level C objects.
//!
//! This crate must be kept in sync with `lean/lean.h`. Pay close attention to
//! definitions containing C code in their docstrings.

pub mod array;
pub mod boxed;
pub mod ctor;
pub mod external;
pub mod ffi;
pub mod nat;
pub mod object;
pub mod sarray;
pub mod string;

use std::ffi::c_void;

use crate::lean::{
  boxed::{BoxedU64, BoxedUSize},
  ctor::LeanCtorObject,
};

#[inline]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub fn as_ref_unsafe<'a, T>(ptr: *const T) -> &'a T {
  let t_ref = unsafe { ptr.as_ref() };
  t_ref.expect("Null pointer dereference")
}

#[inline]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub fn as_mut_unsafe<'a, T>(ptr: *mut T) -> &'a mut T {
  let t_ref = unsafe { ptr.as_mut() };
  t_ref.expect("Null pointer dereference")
}

/// ```c
/// bool lean_is_scalar(lean_object * o) { return ((size_t)(o) & 1) == 1; }
/// ```
#[inline]
pub fn lean_is_scalar<T>(ptr: *const T) -> bool {
  ptr as usize & 1 == 1
}

#[macro_export]
/// ```c
/// lean_object * lean_box(size_t n) { return (lean_object*)(((size_t)(n) << 1) | 1); }
/// ```
macro_rules! lean_box {
  ($e:expr) => {
    (($e << 1) | 1) as *const std::ffi::c_void
  };
}

/// ```c
/// size_t lean_unbox(lean_object * o) { return (size_t)(o) >> 1; }
/// ```
#[macro_export]
macro_rules! lean_unbox {
    ($t:ident, $e:expr) => {
        $t::try_from(($e as usize) >> 1).expect("Unintended truncation")
    };
}

/// ```c
/// unsigned lean_unbox_uint32(b_lean_obj_arg o) {
///     if (sizeof(void*) == 4) {
///         /* 32-bit implementation */
///         return lean_ctor_get_uint32(o, 0);
///     } else {
///         /* 64-bit implementation */
///         return lean_unbox(o);
///     }
/// }
/// ```
#[inline]
pub fn lean_unbox_u32(ptr: *const c_void) -> u32 {
  if cfg!(target_pointer_width = "32") {
    let boxed_usize: &BoxedUSize = as_ref_unsafe(ptr.cast());
    u32::try_from(boxed_usize.value).expect("Cannot convert from usize")
  } else {
    lean_unbox!(u32, ptr)
  }
}

/// ```c
/// uint64_t lean_unbox_uint64(b_lean_obj_arg o) {
///     return lean_ctor_get_uint64(o, 0);
/// }
/// ```
#[inline]
pub fn lean_unbox_u64(ptr: *const c_void) -> u64 {
  let boxed_usize: &BoxedU64 = as_ref_unsafe(ptr.cast());
  boxed_usize.value
}

/// ```c
/// lean_object * lean_box_uint64(uint64_t v) {
///     lean_object * r = lean_alloc_ctor(0, 0, sizeof(uint64_t));
///     lean_ctor_set_uint64(r, 0, v);
///     return r;
/// }
/// ```
#[inline]
pub fn lean_box_u64(v: u64) -> *mut c_void {
  unsafe {
    let obj = lean_alloc_ctor(0, 0, 8);
    lean_ctor_set_uint64(obj, 0, v);
    obj
  }
}

pub fn boxed_usize_ptr_to_usize(ptr: *const c_void) -> usize {
  let boxed_usize_ptr = ptr.cast::<BoxedUSize>();
  let boxed_usize = as_ref_unsafe(boxed_usize_ptr);
  boxed_usize.value
}

/// Emulates arrays of flexible size from C.
#[repr(C)]
pub struct CArray<T>([T; 0]);

impl<T> CArray<T> {
  #[inline]
  pub fn slice(&self, len: usize) -> &[T] {
    unsafe { std::slice::from_raw_parts(self.0.as_ptr(), len) }
  }

  #[inline]
  pub fn slice_mut(&mut self, len: usize) -> &mut [T] {
    unsafe { std::slice::from_raw_parts_mut(self.0.as_mut_ptr(), len) }
  }

  #[inline]
  pub fn copy_from_slice(&mut self, src: &[T]) {
    unsafe {
      std::ptr::copy_nonoverlapping(
        src.as_ptr(),
        self.0.as_ptr() as *mut _,
        src.len(),
      );
    }
  }
}

pub struct ListIterator(*const c_void);

impl Iterator for ListIterator {
  type Item = *const c_void;
  fn next(&mut self) -> Option<Self::Item> {
    let ptr = self.0;
    if lean_is_scalar(ptr) {
      return None;
    }
    let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
    let [head_ptr, tail_ptr] = ctor.objs();
    self.0 = tail_ptr;
    Some(head_ptr)
  }
}

pub fn collect_list<T>(
  mut ptr: *const c_void,
  map_fn: fn(*const c_void) -> T,
) -> Vec<T> {
  let mut vec = Vec::new();
  while !lean_is_scalar(ptr) {
    let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
    let [head_ptr, tail_ptr] = ctor.objs();
    vec.push(map_fn(head_ptr));
    ptr = tail_ptr;
  }
  vec
}

pub fn collect_list_with<T, C>(
  mut ptr: *const c_void,
  map_fn: fn(*const c_void, &mut C) -> T,
  c: &mut C,
) -> Vec<T> {
  let mut vec = Vec::new();
  while !lean_is_scalar(ptr) {
    let ctor: &LeanCtorObject = as_ref_unsafe(ptr.cast());
    let [head_ptr, tail_ptr] = ctor.objs();
    vec.push(map_fn(head_ptr, c));
    ptr = tail_ptr;
  }
  vec
}

// =============================================================================
// Lean C API extern declarations for object construction
// =============================================================================

use std::ffi::c_uint;

// Lean C API wrappers (defined in c/ixon_ffi.c)
// These wrap Lean's allocation functions so they can be linked from Rust
unsafe extern "C" {
  // Object allocation
  /// Allocate a constructor object with the given tag, number of object fields,
  /// and scalar size in bytes.
  #[link_name = "c_lean_alloc_ctor"]
  pub fn lean_alloc_ctor(tag: c_uint, num_objs: c_uint, scalar_sz: c_uint) -> *mut c_void;

  /// Set the i-th object field of a constructor.
  #[link_name = "c_lean_ctor_set"]
  pub fn lean_ctor_set(o: *mut c_void, i: c_uint, v: *mut c_void);

  /// Get the i-th object field of a constructor.
  #[link_name = "c_lean_ctor_get"]
  pub fn lean_ctor_get(o: *mut c_void, i: c_uint) -> *const c_void;

  /// Get the tag of a Lean object.
  #[link_name = "c_lean_obj_tag"]
  pub fn lean_obj_tag(o: *mut c_void) -> c_uint;

  /// Set a uint8 scalar field at the given byte offset (after object fields).
  #[link_name = "c_lean_ctor_set_uint8"]
  pub fn lean_ctor_set_uint8(o: *mut c_void, offset: usize, v: u8);

  /// Set a uint64 scalar field at the given byte offset (after object fields).
  #[link_name = "c_lean_ctor_set_uint64"]
  pub fn lean_ctor_set_uint64(o: *mut c_void, offset: usize, v: u64);

  // String allocation
  /// Create a Lean string from a null-terminated C string.
  #[link_name = "c_lean_mk_string"]
  pub fn lean_mk_string(s: *const std::ffi::c_char) -> *mut c_void;

  // Scalar array (ByteArray) allocation
  /// Allocate a scalar array with the given element size, initial size, and capacity.
  #[link_name = "c_lean_alloc_sarray"]
  pub fn lean_alloc_sarray(elem_size: c_uint, size: usize, capacity: usize) -> *mut c_void;

  /// Get a pointer to the data area of a scalar array.
  #[link_name = "c_lean_sarray_cptr"]
  pub fn lean_sarray_cptr(o: *mut c_void) -> *mut u8;

  // Array allocation
  /// Allocate an array with the given initial size and capacity.
  #[link_name = "c_lean_alloc_array"]
  pub fn lean_alloc_array(size: usize, capacity: usize) -> *mut c_void;

  /// Set the i-th element of an array (does not update size).
  #[link_name = "c_lean_array_set_core"]
  pub fn lean_array_set_core(o: *mut c_void, i: usize, v: *mut c_void);

  /// Get the i-th element of an array.
  #[link_name = "c_lean_array_get_core"]
  pub fn lean_array_get_core(o: *mut c_void, i: usize) -> *const c_void;

  // Reference counting
  /// Increment the reference count of a Lean object.
  #[link_name = "c_lean_inc"]
  pub fn lean_inc(o: *mut c_void);

  /// Increment the reference count by n.
  #[link_name = "c_lean_inc_n"]
  pub fn lean_inc_n(o: *mut c_void, n: usize);

  // IO result construction
  /// Wrap a value in a successful IO result.
  #[link_name = "c_lean_io_result_mk_ok"]
  pub fn lean_io_result_mk_ok(v: *mut c_void) -> *mut c_void;

  /// Wrap an error in an IO error result.
  #[link_name = "c_lean_io_result_mk_error"]
  pub fn lean_io_result_mk_error(err: *mut c_void) -> *mut c_void;

  /// Create an IO.Error.userError from a String.
  #[link_name = "c_lean_mk_io_user_error"]
  pub fn lean_mk_io_user_error(msg: *mut c_void) -> *mut c_void;

  // Nat allocation for large values
  /// Create a Nat from a uint64. For values > max boxed, allocates on heap.
  #[link_name = "c_lean_uint64_to_nat"]
  pub fn lean_uint64_to_nat(n: u64) -> *mut c_void;

  /// Create a Nat from limbs (little-endian u64 array). Uses GMP internally.
  #[link_name = "c_lean_nat_from_limbs"]
  pub fn lean_nat_from_limbs(num_limbs: usize, limbs: *const u64) -> *mut c_void;
}

/// Box a scalar value into a Lean object pointer.
/// ```c
/// lean_object * lean_box(size_t n) { return (lean_object*)(((size_t)(n) << 1) | 1); }
/// ```
#[inline]
pub fn lean_box_fn(n: usize) -> *mut c_void {
  ((n << 1) | 1) as *mut c_void
}
