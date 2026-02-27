//! Rust bindings for Lean, implemented by mimicking the memory layout of Lean's
//! low-level C objects.
//!
//! The `lean` submodule contains auto-generated bindings from `lean.h` via
//! bindgen. Higher-level helpers and custom `#[repr(C)]` types are defined
//! alongside it in sibling modules.

#[allow(
  non_upper_case_globals,
  non_camel_case_types,
  non_snake_case,
  dead_code,
  unsafe_op_in_unsafe_fn,
  clippy::all
)]
pub mod lean {
  include!(concat!(env!("OUT_DIR"), "/lean.rs"));
}

pub mod ffi;
pub mod nat;

use std::ffi::{CString, c_void};

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

#[inline]
pub fn lean_unbox_u32(ptr: *const c_void) -> u32 {
  unsafe { lean::lean_unbox_uint32(ptr as *mut _) as u32 }
}

#[inline]
pub fn lean_unbox_u64(ptr: *const c_void) -> u64 {
  unsafe { lean::lean_unbox_uint64(ptr as *mut _) }
}

#[inline]
pub fn lean_box_u64(v: u64) -> *mut c_void {
  unsafe { lean::lean_box_uint64(v).cast() }
}

pub fn lean_obj_to_string(ptr: *const c_void) -> String {
  unsafe {
    let obj = ptr as *mut lean::lean_object;
    let len = lean::lean_string_size(obj) - 1; // m_size includes NUL
    let data = lean::lean_string_cstr(obj);
    let bytes = std::slice::from_raw_parts(data as *const u8, len);
    String::from_utf8_unchecked(bytes.to_vec())
  }
}

#[inline]
pub fn lean_tag(ptr: *const c_void) -> u8 {
  unsafe { lean::lean_obj_tag(ptr as *mut _) as u8 }
}

#[inline]
pub fn lean_ctor_objs<const N: usize>(ptr: *const c_void) -> [*const c_void; N] {
  // Use raw pointer arithmetic instead of lean_ctor_get to avoid its
  // bounds-check assertion. Call sites legitimately read past the object
  // fields into the scalar area (e.g. Expr.Data hash, Bool/BinderInfo
  // stored as UInt8 scalars). This matches the old LeanCtorObject::objs().
  let base = unsafe { (ptr as *const *const c_void).add(1) };
  std::array::from_fn(|i| unsafe { *base.add(i) })
}

#[inline]
pub fn lean_ctor_scalar_u64(ptr: *const c_void, num_objs: usize, offset: usize) -> u64 {
  unsafe {
    std::ptr::read_unaligned(ptr.cast::<u8>().add(8 + num_objs * 8 + offset).cast())
  }
}

#[inline]
pub fn lean_ctor_scalar_u8(ptr: *const c_void, num_objs: usize, offset: usize) -> u8 {
  unsafe { *ptr.cast::<u8>().add(8 + num_objs * 8 + offset) }
}

#[inline]
pub fn lean_ctor_scalar_bool(ptr: *const c_void, num_objs: usize, offset: usize) -> bool {
  lean_ctor_scalar_u8(ptr, num_objs, offset) != 0
}

// =============================================================================
// Array helpers (replace LeanArrayObject)
// =============================================================================

/// Return a slice over the elements of a Lean `Array` object.
pub fn lean_array_data(ptr: *const c_void) -> &'static [*const c_void] {
  unsafe {
    let obj = ptr as *mut lean::lean_object;
    let size = lean::lean_array_size(obj);
    let cptr = lean::lean_array_cptr(obj);
    std::slice::from_raw_parts(cptr.cast(), size)
  }
}

/// Convert a Lean `Array` to a `Vec<T>` by mapping each element.
pub fn lean_array_to_vec<T>(ptr: *const c_void, f: fn(*const c_void) -> T) -> Vec<T> {
  lean_array_data(ptr).iter().map(|&p| f(p)).collect()
}

/// Like `lean_array_to_vec` but threads a mutable context through each call.
pub fn lean_array_to_vec_with<T, C>(
  ptr: *const c_void,
  f: fn(*const c_void, &mut C) -> T,
  c: &mut C,
) -> Vec<T> {
  lean_array_data(ptr).iter().map(|&p| f(p, c)).collect()
}

// =============================================================================
// SArray (ByteArray) helpers (replace LeanSArrayObject)
// =============================================================================

/// Return a byte slice over a Lean `ByteArray` (scalar array) object.
pub fn lean_sarray_data(ptr: *const c_void) -> &'static [u8] {
  unsafe {
    let obj = ptr as *mut lean::lean_object;
    let size = lean::lean_sarray_size(obj);
    let cptr = lean::lean_sarray_cptr(obj);
    std::slice::from_raw_parts(cptr, size)
  }
}

/// Write bytes into a Lean `ByteArray` and update its size.
///
/// # Safety
/// The caller must ensure `ptr` points to a valid `lean_sarray_object`
/// with sufficient capacity for `data`.
pub unsafe fn lean_sarray_set_data(ptr: *mut c_void, data: &[u8]) {
  unsafe {
    let obj = ptr as *mut lean::lean_object;
    let cptr = lean::lean_sarray_cptr(obj);
    std::ptr::copy_nonoverlapping(data.as_ptr(), cptr, data.len());
    // Update m_size: at offset 8 (after lean_object header)
    *(ptr.cast::<u8>().add(8) as *mut usize) = data.len();
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
    let [head_ptr, tail_ptr] = lean_ctor_objs(ptr);
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
    let [head_ptr, tail_ptr] = lean_ctor_objs(ptr);
    vec.push(map_fn(head_ptr));
    ptr = tail_ptr;
  }
  vec
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
    let obj = lean::lean_alloc_ctor(1, 1, 0);
    lean::lean_ctor_set(obj, 0, val.cast());
    obj.cast()
  }
}

/// Build `Except.error msg` — tag 0, one object field.
#[inline]
pub fn lean_except_error(msg: *mut c_void) -> *mut c_void {
  unsafe {
    let obj = lean::lean_alloc_ctor(0, 1, 0);
    lean::lean_ctor_set(obj, 0, msg.cast());
    obj.cast()
  }
}

/// Build `Except.error (lean_mk_string str)` from a Rust string.
#[inline]
pub fn lean_except_error_string(msg: &str) -> *mut c_void {
  let c_msg = safe_cstring(msg);
  unsafe { lean_except_error(lean::lean_mk_string(c_msg.as_ptr()).cast()) }
}

/// No-op foreach callback for external classes that hold no Lean references.
pub unsafe extern "C" fn noop_foreach(
  _: *mut c_void,
  _: *mut lean::lean_object,
) {
}
