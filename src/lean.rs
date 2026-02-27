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

use std::ffi::{CString, c_void};

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

/// Create a CString from a str, stripping any interior null bytes.
/// Lean strings are length-prefixed and can contain null bytes, but the
/// `lean_mk_string` FFI requires a null-terminated C string. This function
/// ensures conversion always succeeds by filtering out interior nulls.
pub fn safe_cstring(s: &str) -> CString {
  CString::new(s).unwrap_or_else(|_| {
    let bytes: Vec<u8> = s.bytes().filter(|&b| b != 0).collect();
    CString::new(bytes).expect("filtered string should have no nulls")
  })
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

// Lean C API bindings. Static inline functions use bindgen-generated
// wrappers (suffix __extern). LEAN_EXPORT functions link directly.
unsafe extern "C" {
  // Object allocation
  /// Allocate a constructor object with the given tag, number of object fields,
  /// and scalar size in bytes.
  #[link_name = "lean_alloc_ctor__extern"]
  pub fn lean_alloc_ctor(
    tag: c_uint,
    num_objs: c_uint,
    scalar_sz: c_uint,
  ) -> *mut c_void;

  /// Set the i-th object field of a constructor.
  #[link_name = "lean_ctor_set__extern"]
  pub fn lean_ctor_set(o: *mut c_void, i: c_uint, v: *mut c_void);

  /// Get the i-th object field of a constructor.
  #[link_name = "lean_ctor_get__extern"]
  pub fn lean_ctor_get(o: *mut c_void, i: c_uint) -> *const c_void;

  /// Get the tag of a Lean object.
  #[link_name = "lean_obj_tag__extern"]
  pub fn lean_obj_tag(o: *mut c_void) -> c_uint;

  /// Set a uint8 scalar field at the given byte offset (after object fields).
  #[link_name = "lean_ctor_set_uint8__extern"]
  pub fn lean_ctor_set_uint8(o: *mut c_void, offset: usize, v: u8);

  /// Set a uint64 scalar field at the given byte offset (after object fields).
  #[link_name = "lean_ctor_set_uint64__extern"]
  pub fn lean_ctor_set_uint64(o: *mut c_void, offset: usize, v: u64);

  // String allocation (LEAN_EXPORT — links directly, no wrapper needed)
  /// Create a Lean string from a null-terminated C string.
  pub fn lean_mk_string(s: *const std::ffi::c_char) -> *mut c_void;

  // Scalar array (ByteArray) allocation
  /// Allocate a scalar array with the given element size, initial size, and capacity.
  #[link_name = "lean_alloc_sarray__extern"]
  pub fn lean_alloc_sarray(
    elem_size: c_uint,
    size: usize,
    capacity: usize,
  ) -> *mut c_void;

  /// Get a pointer to the data area of a scalar array.
  #[link_name = "lean_sarray_cptr__extern"]
  pub fn lean_sarray_cptr(o: *mut c_void) -> *mut u8;

  // Array allocation
  /// Allocate an array with the given initial size and capacity.
  #[link_name = "lean_alloc_array__extern"]
  pub fn lean_alloc_array(size: usize, capacity: usize) -> *mut c_void;

  /// Set the i-th element of an array (does not update size).
  #[link_name = "lean_array_set_core__extern"]
  pub fn lean_array_set_core(o: *mut c_void, i: usize, v: *mut c_void);

  /// Get the i-th element of an array.
  #[link_name = "lean_array_get_core__extern"]
  pub fn lean_array_get_core(o: *mut c_void, i: usize) -> *const c_void;

  // Reference counting
  /// Increment the reference count of a Lean object.
  #[link_name = "lean_inc__extern"]
  pub fn lean_inc(o: *mut c_void);

  /// Increment the reference count by n.
  #[link_name = "lean_inc_n__extern"]
  pub fn lean_inc_n(o: *mut c_void, n: usize);

  /// Decrement the reference count of a Lean object.
  #[link_name = "lean_dec__extern"]
  pub fn lean_dec(o: *mut c_void);

  // External object support
  /// Register an external class with finalizer and foreach callbacks.
  /// This is a LEAN_EXPORT function and can be linked directly.
  pub fn lean_register_external_class(
    finalize: extern "C" fn(*mut c_void),
    foreach: extern "C" fn(*mut c_void, *mut c_void),
  ) -> *mut c_void;

  /// Allocate an external object wrapping opaque data.
  #[link_name = "lean_alloc_external__extern"]
  pub fn lean_alloc_external(
    cls: *mut c_void,
    data: *mut c_void,
  ) -> *mut c_void;

  // IO result construction
  /// Wrap a value in a successful IO result.
  #[link_name = "lean_io_result_mk_ok__extern"]
  pub fn lean_io_result_mk_ok(v: *mut c_void) -> *mut c_void;

  /// Wrap an error in an IO error result.
  #[link_name = "lean_io_result_mk_error__extern"]
  pub fn lean_io_result_mk_error(err: *mut c_void) -> *mut c_void;

  /// Create an IO.Error.userError from a String (LEAN_EXPORT — links directly).
  pub fn lean_mk_io_user_error(msg: *mut c_void) -> *mut c_void;

  // Nat allocation for large values
  /// Create a Nat from a uint64. For values > max boxed, allocates on heap.
  #[link_name = "lean_uint64_to_nat__extern"]
  pub fn lean_uint64_to_nat(n: u64) -> *mut c_void;

  // lean_nat_from_limbs moved to src/lean/nat.rs (uses GMP directly)
}

/// Box a scalar value into a Lean object pointer.
/// ```c
/// lean_object * lean_box(size_t n) { return (lean_object*)(((size_t)(n) << 1) | 1); }
/// ```
#[inline]
pub fn lean_box_fn(n: usize) -> *mut c_void {
  ((n << 1) | 1) as *mut c_void
}

// =============================================================================
// Lean Except constructors
// =============================================================================

/// Build `Except.ok val` — tag 1, one object field.
#[inline]
pub fn lean_except_ok(val: *mut c_void) -> *mut c_void {
  unsafe {
    let obj = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(obj, 0, val);
    obj
  }
}

/// Build `Except.error msg` — tag 0, one object field.
#[inline]
pub fn lean_except_error(msg: *mut c_void) -> *mut c_void {
  unsafe {
    let obj = lean_alloc_ctor(0, 1, 0);
    lean_ctor_set(obj, 0, msg);
    obj
  }
}

/// Build `Except.error (lean_mk_string str)` from a Rust string.
#[inline]
pub fn lean_except_error_string(msg: &str) -> *mut c_void {
  let c_msg = safe_cstring(msg);
  unsafe { lean_except_error(lean_mk_string(c_msg.as_ptr())) }
}

/// No-op foreach callback for external classes that hold no Lean references.
pub extern "C" fn noop_foreach(_: *mut c_void, _: *mut c_void) {}
