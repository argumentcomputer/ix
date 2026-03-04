//! Type-safe wrappers for Lean FFI object pointers.
//!
//! Each wrapper is a `#[repr(transparent)]` `Copy` newtype over `*const c_void`
//! that asserts the correct Lean tag on construction and provides safe accessor
//! methods. Reference counting is left to Lean (no `Drop` impl).

use std::ffi::c_void;
use std::marker::PhantomData;
use std::ops::Deref;

use crate::include;
use crate::safe_cstring;

// Tag constants from lean.h
const LEAN_MAX_CTOR_TAG: u8 = 243;
const LEAN_TAG_ARRAY: u8 = 246;
const LEAN_TAG_SCALAR_ARRAY: u8 = 248;
const LEAN_TAG_STRING: u8 = 249;
const LEAN_TAG_EXTERNAL: u8 = 254;

/// Constructor tag for `IO.Error.userError`.
const IO_ERROR_USER_ERROR_TAG: u8 = 7;

// =============================================================================
// LeanObject — Untyped base wrapper
// =============================================================================

/// Untyped wrapper around a raw Lean object pointer.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct LeanObject(*const c_void);

impl LeanObject {
  /// Wrap a raw pointer without any tag check.
  ///
  /// # Safety
  /// The pointer must be a valid Lean object (or tagged scalar).
  #[inline]
  pub unsafe fn from_raw(ptr: *const c_void) -> Self {
    Self(ptr)
  }

  /// Wrap a `*mut lean_object` returned from a `lean_ffi` function.
  ///
  /// # Safety
  /// The pointer must be a valid Lean object (or tagged scalar).
  #[inline]
  pub unsafe fn from_lean_ptr(ptr: *mut include::lean_object) -> Self {
    Self(ptr.cast())
  }

  /// Create a Lean `Nat` from a `u64` value.
  ///
  /// Small values are stored as tagged scalars; larger ones are heap-allocated
  /// via the Lean runtime.
  #[inline]
  pub fn from_nat_u64(n: u64) -> Self {
    unsafe { Self::from_lean_ptr(include::lean_uint64_to_nat(n)) }
  }

  #[inline]
  pub fn as_ptr(self) -> *const c_void {
    self.0
  }

  #[inline]
  pub fn as_mut_ptr(self) -> *mut c_void {
    self.0 as *mut c_void
  }

  /// True if this is a tagged scalar (bit 0 set).
  #[inline]
  pub fn is_scalar(self) -> bool {
    self.0 as usize & 1 == 1
  }

  /// Return the object tag. Panics if the object is a scalar.
  #[inline]
  pub fn tag(self) -> u8 {
    assert!(!self.is_scalar(), "tag() called on scalar");
    #[allow(clippy::cast_possible_truncation)]
    unsafe {
      include::lean_obj_tag(self.0 as *mut _) as u8
    }
  }

  #[inline]
  pub fn inc_ref(self) {
    if !self.is_scalar() {
      unsafe { include::lean_inc_ref(self.0 as *mut _) }
    }
  }

  #[inline]
  pub fn dec_ref(self) {
    if !self.is_scalar() {
      unsafe { include::lean_dec_ref(self.0 as *mut _) }
    }
  }

  /// Create a `LeanObject` from a raw tag value for zero-field enum constructors.
  /// Lean passes simple enums (all constructors have zero fields) as unboxed
  /// tag values (0, 1, 2, ...) across FFI, not as `lean_box(tag)`.
  #[inline]
  pub fn from_enum_tag(tag: usize) -> Self {
    Self(tag as *const c_void)
  }

  /// Extract the raw tag value from a zero-field enum constructor.
  /// Inverse of `from_enum_tag`.
  #[inline]
  pub fn as_enum_tag(self) -> usize {
    self.0 as usize
  }

  /// Box a `usize` into a tagged scalar pointer.
  #[inline]
  pub fn box_usize(n: usize) -> Self {
    Self(((n << 1) | 1) as *const c_void)
  }

  /// Unbox a tagged scalar pointer into a `usize`.
  #[inline]
  pub fn unbox_usize(self) -> usize {
    self.0 as usize >> 1
  }

  #[inline]
  pub fn box_u64(n: u64) -> Self {
    Self(unsafe { include::lean_box_uint64(n) }.cast())
  }

  #[inline]
  pub fn unbox_u64(self) -> u64 {
    unsafe { include::lean_unbox_uint64(self.0 as *mut _) }
  }

  /// Interpret as a constructor object (tag 0–`LEAN_MAX_CTOR_TAG`).
  ///
  /// Debug-asserts the tag is in range.
  #[inline]
  pub fn as_ctor(self) -> LeanCtor {
    debug_assert!(!self.is_scalar() && self.tag() <= LEAN_MAX_CTOR_TAG);
    LeanCtor(self)
  }

  /// Interpret as a `String` object (tag `LEAN_TAG_STRING`).
  ///
  /// Debug-asserts the tag is correct.
  #[inline]
  pub fn as_string(self) -> LeanString {
    debug_assert!(!self.is_scalar() && self.tag() == LEAN_TAG_STRING);
    LeanString(self)
  }

  /// Interpret as an `Array` object (tag `LEAN_TAG_ARRAY`).
  ///
  /// Debug-asserts the tag is correct.
  #[inline]
  pub fn as_array(self) -> LeanArray {
    debug_assert!(!self.is_scalar() && self.tag() == LEAN_TAG_ARRAY);
    LeanArray(self)
  }

  /// Interpret as a `List` (nil = scalar, cons = tag 1).
  ///
  /// Debug-asserts the tag is valid for a list.
  #[inline]
  pub fn as_list(self) -> LeanList {
    debug_assert!(self.is_scalar() || self.tag() == 1);
    LeanList(self)
  }

  /// Interpret as a `ByteArray` object (tag `LEAN_TAG_SCALAR_ARRAY`).
  #[inline]
  pub fn as_byte_array(self) -> LeanByteArray {
    debug_assert!(!self.is_scalar() && self.tag() == LEAN_TAG_SCALAR_ARRAY);
    LeanByteArray(self)
  }

  #[inline]
  pub fn box_u32(n: u32) -> Self {
    Self(unsafe { include::lean_box_uint32(n) }.cast())
  }

  #[inline]
  pub fn unbox_u32(self) -> u32 {
    unsafe { include::lean_unbox_uint32(self.0 as *mut _) }
  }
}

// =============================================================================
// LeanNat — Nat (scalar or heap mpz)
// =============================================================================

/// Typed wrapper for a Lean `Nat` (small = tagged scalar, big = heap `mpz_object`).
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct LeanNat(LeanObject);

impl Deref for LeanNat {
  type Target = LeanObject;
  #[inline]
  fn deref(&self) -> &LeanObject {
    &self.0
  }
}

impl From<LeanNat> for LeanObject {
  #[inline]
  fn from(x: LeanNat) -> Self {
    x.0
  }
}

// =============================================================================
// LeanBool — Bool (unboxed scalar: false = 0, true = 1)
// =============================================================================

/// Typed wrapper for a Lean `Bool` (always an unboxed scalar: false = 0, true = 1).
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct LeanBool(LeanObject);

impl Deref for LeanBool {
  type Target = LeanObject;
  #[inline]
  fn deref(&self) -> &LeanObject {
    &self.0
  }
}

impl From<LeanBool> for LeanObject {
  #[inline]
  fn from(x: LeanBool) -> Self {
    x.0
  }
}

impl LeanBool {
  /// Decode to a Rust `bool`.
  #[inline]
  pub fn to_bool(self) -> bool {
    self.0.as_enum_tag() != 0
  }
}

// =============================================================================
// LeanArray — Array α (tag LEAN_TAG_ARRAY)
// =============================================================================

/// Typed wrapper for a Lean `Array α` object (tag `LEAN_TAG_ARRAY`).
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct LeanArray(LeanObject);

impl Deref for LeanArray {
  type Target = LeanObject;
  #[inline]
  fn deref(&self) -> &LeanObject {
    &self.0
  }
}

impl LeanArray {
  /// Wrap a raw pointer, asserting it is an `Array` (tag `LEAN_TAG_ARRAY`).
  ///
  /// # Safety
  /// The pointer must be a valid Lean `Array` object.
  pub unsafe fn from_raw(ptr: *const c_void) -> Self {
    let obj = LeanObject(ptr);
    debug_assert!(!obj.is_scalar() && obj.tag() == LEAN_TAG_ARRAY);
    Self(obj)
  }

  /// Allocate a new array with `size` elements (capacity = size).
  pub fn alloc(size: usize) -> Self {
    let obj = unsafe { include::lean_alloc_array(size, size) };
    Self(LeanObject(obj.cast()))
  }

  pub fn len(&self) -> usize {
    unsafe { include::lean_array_size(self.0.as_ptr() as *mut _) }
  }

  pub fn is_empty(&self) -> bool {
    self.len() == 0
  }

  pub fn get(&self, i: usize) -> LeanObject {
    LeanObject(
      unsafe { include::lean_array_get_core(self.0.as_ptr() as *mut _, i) }
        .cast(),
    )
  }

  pub fn set(&self, i: usize, val: impl Into<LeanObject>) {
    let val: LeanObject = val.into();
    unsafe {
      include::lean_array_set_core(
        self.0.as_ptr() as *mut _,
        i,
        val.as_ptr() as *mut _,
      );
    }
  }

  /// Return a slice over the array elements.
  pub fn data(&self) -> &[LeanObject] {
    unsafe {
      let cptr = include::lean_array_cptr(self.0.as_ptr() as *mut _);
      // Safety: LeanObject is repr(transparent) over *const c_void, and
      // lean_array_cptr returns *mut *mut lean_object which has the same layout.
      std::slice::from_raw_parts(cptr.cast(), self.len())
    }
  }

  pub fn iter(&self) -> impl Iterator<Item = LeanObject> + '_ {
    self.data().iter().copied()
  }

  pub fn map<T>(&self, f: impl Fn(LeanObject) -> T) -> Vec<T> {
    self.iter().map(f).collect()
  }
}

// =============================================================================
// LeanByteArray — ByteArray (tag LEAN_TAG_SCALAR_ARRAY)
// =============================================================================

/// Typed wrapper for a Lean `ByteArray` object (tag `LEAN_TAG_SCALAR_ARRAY`).
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct LeanByteArray(LeanObject);

impl Deref for LeanByteArray {
  type Target = LeanObject;
  #[inline]
  fn deref(&self) -> &LeanObject {
    &self.0
  }
}

impl LeanByteArray {
  /// Wrap a raw pointer, asserting it is a `ByteArray` (tag `LEAN_TAG_SCALAR_ARRAY`).
  ///
  /// # Safety
  /// The pointer must be a valid Lean `ByteArray` object.
  pub unsafe fn from_raw(ptr: *const c_void) -> Self {
    let obj = LeanObject(ptr);
    debug_assert!(!obj.is_scalar() && obj.tag() == LEAN_TAG_SCALAR_ARRAY);
    Self(obj)
  }

  /// Allocate a new byte array with `size` bytes (capacity = size).
  pub fn alloc(size: usize) -> Self {
    let obj = unsafe { include::lean_alloc_sarray(1, size, size) };
    Self(LeanObject(obj.cast()))
  }

  /// Allocate a new byte array and copy `data` into it.
  pub fn from_bytes(data: &[u8]) -> Self {
    let arr = Self::alloc(data.len());
    unsafe {
      let cptr = include::lean_sarray_cptr(arr.0.as_ptr() as *mut _);
      std::ptr::copy_nonoverlapping(data.as_ptr(), cptr, data.len());
    }
    arr
  }

  pub fn len(&self) -> usize {
    unsafe { include::lean_sarray_size(self.0.as_ptr() as *mut _) }
  }

  pub fn is_empty(&self) -> bool {
    self.len() == 0
  }

  /// Return the byte contents as a slice.
  pub fn as_bytes(&self) -> &[u8] {
    unsafe {
      let cptr = include::lean_sarray_cptr(self.0.as_ptr() as *mut _);
      std::slice::from_raw_parts(cptr, self.len())
    }
  }

  /// Copy `data` into the byte array and update its size.
  ///
  /// # Safety
  /// The caller must ensure the array has sufficient capacity for `data`.
  pub unsafe fn set_data(&self, data: &[u8]) {
    unsafe {
      let obj = self.0.as_mut_ptr();
      let cptr = include::lean_sarray_cptr(obj.cast());
      std::ptr::copy_nonoverlapping(data.as_ptr(), cptr, data.len());
      // Update m_size: at offset 8 (after lean_object header)
      *obj.cast::<u8>().add(8).cast::<usize>() = data.len();
    }
  }
}

// =============================================================================
// LeanString — String (tag LEAN_TAG_STRING)
// =============================================================================

/// Typed wrapper for a Lean `String` object (tag `LEAN_TAG_STRING`).
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct LeanString(LeanObject);

impl Deref for LeanString {
  type Target = LeanObject;
  #[inline]
  fn deref(&self) -> &LeanObject {
    &self.0
  }
}

impl LeanString {
  /// Wrap a raw pointer, asserting it is a `String` (tag `LEAN_TAG_STRING`).
  ///
  /// # Safety
  /// The pointer must be a valid Lean `String` object.
  pub unsafe fn from_raw(ptr: *const c_void) -> Self {
    let obj = LeanObject(ptr);
    debug_assert!(!obj.is_scalar() && obj.tag() == LEAN_TAG_STRING);
    Self(obj)
  }

  /// Create a Lean string from a Rust `&str`.
  pub fn new(s: &str) -> Self {
    let c = safe_cstring(s);
    let obj = unsafe { include::lean_mk_string(c.as_ptr()) };
    Self(LeanObject(obj.cast()))
  }

  /// Number of data bytes (excluding the trailing NUL).
  pub fn byte_len(&self) -> usize {
    unsafe { include::lean_string_size(self.0.as_ptr() as *mut _) - 1 }
  }
}

impl std::fmt::Display for LeanString {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    unsafe {
      let obj = self.0.as_ptr() as *mut _;
      let len = include::lean_string_size(obj) - 1; // m_size includes NUL
      let data = include::lean_string_cstr(obj);
      let bytes = std::slice::from_raw_parts(data.cast::<u8>(), len);
      let s = std::str::from_utf8_unchecked(bytes);
      f.write_str(s)
    }
  }
}

// =============================================================================
// LeanCtor — Constructor objects (tag 0–LEAN_MAX_CTOR_TAG)
// =============================================================================

/// Typed wrapper for a Lean constructor object (tag 0–`LEAN_MAX_CTOR_TAG`).
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct LeanCtor(LeanObject);

impl Deref for LeanCtor {
  type Target = LeanObject;
  #[inline]
  fn deref(&self) -> &LeanObject {
    &self.0
  }
}

impl LeanCtor {
  /// Wrap a raw pointer, asserting it is a constructor (tag <= `LEAN_MAX_CTOR_TAG`).
  ///
  /// # Safety
  /// The pointer must be a valid Lean constructor object.
  pub unsafe fn from_raw(ptr: *const c_void) -> Self {
    let obj = LeanObject(ptr);
    debug_assert!(!obj.is_scalar() && obj.tag() <= LEAN_MAX_CTOR_TAG);
    Self(obj)
  }

  /// Allocate a new constructor object.
  pub fn alloc(tag: u8, num_objs: usize, scalar_size: usize) -> Self {
    #[allow(clippy::cast_possible_truncation)]
    let obj = unsafe {
      include::lean_alloc_ctor(tag as u32, num_objs as u32, scalar_size as u32)
    };
    Self(LeanObject(obj.cast()))
  }

  pub fn tag(&self) -> u8 {
    self.0.tag()
  }

  /// Get the `i`-th object field via `lean_ctor_get`.
  pub fn get(&self, i: usize) -> LeanObject {
    #[allow(clippy::cast_possible_truncation)]
    LeanObject(
      unsafe { include::lean_ctor_get(self.0.as_ptr() as *mut _, i as u32) }
        .cast(),
    )
  }

  /// Set the `i`-th object field via `lean_ctor_set`.
  pub fn set(&self, i: usize, val: impl Into<LeanObject>) {
    let val: LeanObject = val.into();
    #[allow(clippy::cast_possible_truncation)]
    unsafe {
      include::lean_ctor_set(
        self.0.as_ptr() as *mut _,
        i as u32,
        val.as_ptr() as *mut _,
      );
    }
  }

  /// Set a `u8` scalar field at the given byte offset (past all object fields).
  pub fn set_u8(&self, offset: usize, val: u8) {
    #[allow(clippy::cast_possible_truncation)]
    unsafe {
      include::lean_ctor_set_uint8(
        self.0.as_ptr() as *mut _,
        offset as u32,
        val,
      );
    }
  }

  /// Set a `u32` scalar field at the given byte offset (past all object fields).
  pub fn set_u32(&self, offset: usize, val: u32) {
    #[allow(clippy::cast_possible_truncation)]
    unsafe {
      include::lean_ctor_set_uint32(
        self.0.as_ptr() as *mut _,
        offset as u32,
        val,
      );
    }
  }

  /// Set a `u64` scalar field at the given byte offset (past all object fields).
  pub fn set_u64(&self, offset: usize, val: u64) {
    #[allow(clippy::cast_possible_truncation)]
    unsafe {
      include::lean_ctor_set_uint64(
        self.0.as_ptr() as *mut _,
        offset as u32,
        val,
      );
    }
  }

  /// Read `N` object-field pointers using raw pointer math.
  ///
  /// This bypasses `lean_ctor_get`'s bounds check, which is necessary when
  /// reading past the declared object fields into the scalar area (e.g. for
  /// `Expr.Data`).
  pub fn objs<const N: usize>(&self) -> [LeanObject; N] {
    let base = unsafe { self.0.as_ptr().cast::<*const c_void>().add(1) };
    std::array::from_fn(|i| LeanObject(unsafe { *base.add(i) }))
  }

  /// Read a `u64` scalar at `offset` bytes past `num_objs` object fields.
  pub fn scalar_u64(&self, num_objs: usize, offset: usize) -> u64 {
    unsafe {
      std::ptr::read_unaligned(
        self.0.as_ptr().cast::<u8>().add(8 + num_objs * 8 + offset).cast(),
      )
    }
  }

  /// Read a `u32` scalar at `offset` bytes past `num_objs` object fields.
  pub fn scalar_u32(&self, num_objs: usize, offset: usize) -> u32 {
    unsafe {
      std::ptr::read_unaligned(
        self.0.as_ptr().cast::<u8>().add(8 + num_objs * 8 + offset).cast(),
      )
    }
  }

  /// Read a `u8` scalar at `offset` bytes past `num_objs` object fields.
  pub fn scalar_u8(&self, num_objs: usize, offset: usize) -> u8 {
    unsafe { *self.0.as_ptr().cast::<u8>().add(8 + num_objs * 8 + offset) }
  }

  /// Read a `bool` scalar at `offset` bytes past `num_objs` object fields.
  pub fn scalar_bool(&self, num_objs: usize, offset: usize) -> bool {
    self.scalar_u8(num_objs, offset) != 0
  }
}

// =============================================================================
// LeanExternal<T> — External objects (tag LEAN_TAG_EXTERNAL)
// =============================================================================

/// Typed wrapper for a Lean external object (tag `LEAN_TAG_EXTERNAL`) holding a `T`.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct LeanExternal<T>(LeanObject, PhantomData<T>);

impl<T> Deref for LeanExternal<T> {
  type Target = LeanObject;
  #[inline]
  fn deref(&self) -> &LeanObject {
    &self.0
  }
}

impl<T> LeanExternal<T> {
  /// Wrap a raw pointer, asserting it is an external object (tag `LEAN_TAG_EXTERNAL`).
  ///
  /// # Safety
  /// The pointer must be a valid Lean external object whose data pointer
  /// points to a valid `T`.
  pub unsafe fn from_raw(ptr: *const c_void) -> Self {
    let obj = LeanObject(ptr);
    debug_assert!(!obj.is_scalar() && obj.tag() == LEAN_TAG_EXTERNAL);
    Self(obj, PhantomData)
  }

  /// Allocate a new external object holding `data`.
  pub fn alloc(class: &ExternalClass, data: T) -> Self {
    let data_ptr = Box::into_raw(Box::new(data));
    let obj =
      unsafe { include::lean_alloc_external(class.0.cast(), data_ptr.cast()) };
    Self(LeanObject(obj.cast()), PhantomData)
  }

  /// Get a reference to the wrapped data.
  pub fn get(&self) -> &T {
    unsafe {
      &*include::lean_get_external_data(self.0.as_ptr() as *mut _).cast::<T>()
    }
  }
}

// =============================================================================
// ExternalClass — Registered external class
// =============================================================================

/// A registered Lean external class (wraps `lean_external_class*`).
pub struct ExternalClass(*mut c_void);

// Safety: the class pointer is initialized once and read-only thereafter.
unsafe impl Send for ExternalClass {}
unsafe impl Sync for ExternalClass {}

impl ExternalClass {
  /// Register a new external class with explicit finalizer and foreach callbacks.
  ///
  /// # Safety
  /// The `finalizer` callback must correctly free the external data, and
  /// `foreach` must correctly visit any Lean object references held by the data.
  pub unsafe fn register(
    finalizer: include::lean_external_finalize_proc,
    foreach: include::lean_external_foreach_proc,
  ) -> Self {
    Self(
      unsafe { include::lean_register_external_class(finalizer, foreach) }
        .cast(),
    )
  }

  /// Register a new external class that uses `Drop` to finalize `T`
  /// and has no Lean object references to visit.
  pub fn register_with_drop<T>() -> Self {
    unsafe extern "C" fn drop_finalizer<T>(ptr: *mut c_void) {
      if !ptr.is_null() {
        drop(unsafe { Box::from_raw(ptr.cast::<T>()) });
      }
    }
    unsafe {
      Self::register(Some(drop_finalizer::<T>), Some(crate::noop_foreach))
    }
  }
}

// =============================================================================
// LeanList — List α
// =============================================================================

/// Typed wrapper for a Lean `List α` (nil = scalar `lean_box(0)`, cons = ctor tag 1).
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct LeanList(LeanObject);

impl Deref for LeanList {
  type Target = LeanObject;
  #[inline]
  fn deref(&self) -> &LeanObject {
    &self.0
  }
}

impl LeanList {
  /// Wrap a raw pointer, asserting it is a valid `List` (scalar nil or ctor tag 1).
  ///
  /// # Safety
  /// The pointer must be a valid Lean `List` object.
  pub unsafe fn from_raw(ptr: *const c_void) -> Self {
    let obj = LeanObject(ptr);
    debug_assert!(obj.is_scalar() || obj.tag() == 1);
    Self(obj)
  }

  /// The empty list.
  pub fn nil() -> Self {
    Self(LeanObject::box_usize(0))
  }

  /// Prepend `head` to `tail`.
  pub fn cons(head: impl Into<LeanObject>, tail: LeanList) -> Self {
    let ctor = LeanCtor::alloc(1, 2, 0);
    ctor.set(0, head);
    ctor.set(1, tail);
    Self(ctor.0)
  }

  pub fn is_nil(&self) -> bool {
    self.0.is_scalar()
  }

  pub fn iter(&self) -> LeanListIter {
    LeanListIter(self.0)
  }

  pub fn collect<T>(&self, f: impl Fn(LeanObject) -> T) -> Vec<T> {
    self.iter().map(f).collect()
  }
}

impl<T: Into<LeanObject>> FromIterator<T> for LeanList {
  fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
    let items: Vec<LeanObject> = iter.into_iter().map(Into::into).collect();
    let mut list = Self::nil();
    for item in items.into_iter().rev() {
      list = Self::cons(item, list);
    }
    list
  }
}

/// Iterator over the elements of a `LeanList`.
pub struct LeanListIter(LeanObject);

impl Iterator for LeanListIter {
  type Item = LeanObject;
  fn next(&mut self) -> Option<Self::Item> {
    if self.0.is_scalar() {
      return None;
    }
    let ctor = self.0.as_ctor();
    let [head, tail] = ctor.objs::<2>();
    self.0 = tail;
    Some(head)
  }
}

// =============================================================================
// LeanOption — Option α
// =============================================================================

/// Typed wrapper for a Lean `Option α` (none = scalar, some = ctor tag 1).
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct LeanOption(LeanObject);

impl Deref for LeanOption {
  type Target = LeanObject;
  #[inline]
  fn deref(&self) -> &LeanObject {
    &self.0
  }
}

impl LeanOption {
  /// Wrap a raw pointer, asserting it is a valid `Option`.
  ///
  /// # Safety
  /// The pointer must be a valid Lean `Option` object.
  pub unsafe fn from_raw(ptr: *const c_void) -> Self {
    let obj = LeanObject(ptr);
    debug_assert!(obj.is_scalar() || obj.tag() == 1);
    Self(obj)
  }

  pub fn none() -> Self {
    Self(LeanObject::box_usize(0))
  }

  pub fn some(val: impl Into<LeanObject>) -> Self {
    let ctor = LeanCtor::alloc(1, 1, 0);
    ctor.set(0, val);
    Self(ctor.0)
  }

  pub fn is_none(&self) -> bool {
    self.0.is_scalar()
  }

  pub fn is_some(&self) -> bool {
    !self.is_none()
  }

  pub fn to_option(&self) -> Option<LeanObject> {
    if self.is_none() {
      None
    } else {
      let ctor = self.0.as_ctor();
      Some(ctor.get(0))
    }
  }
}

// =============================================================================
// LeanExcept — Except ε α
// =============================================================================

/// Typed wrapper for a Lean `Except ε α` (error = ctor tag 0, ok = ctor tag 1).
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct LeanExcept(LeanObject);

impl Deref for LeanExcept {
  type Target = LeanObject;
  #[inline]
  fn deref(&self) -> &LeanObject {
    &self.0
  }
}

impl LeanExcept {
  /// Wrap a raw pointer, asserting it is a valid `Except`.
  ///
  /// # Safety
  /// The pointer must be a valid Lean `Except` object.
  pub unsafe fn from_raw(ptr: *const c_void) -> Self {
    let obj = LeanObject(ptr);
    debug_assert!(!obj.is_scalar() && (obj.tag() == 0 || obj.tag() == 1));
    Self(obj)
  }

  /// Build `Except.ok val`.
  pub fn ok(val: impl Into<LeanObject>) -> Self {
    let ctor = LeanCtor::alloc(1, 1, 0);
    ctor.set(0, val);
    Self(ctor.0)
  }

  /// Build `Except.error msg`.
  pub fn error(msg: impl Into<LeanObject>) -> Self {
    let ctor = LeanCtor::alloc(0, 1, 0);
    ctor.set(0, msg);
    Self(ctor.0)
  }

  /// Build `Except.error (String.mk msg)` from a Rust string.
  pub fn error_string(msg: &str) -> Self {
    Self::error(LeanString::new(msg))
  }

  pub fn is_ok(&self) -> bool {
    self.0.tag() == 1
  }

  pub fn is_error(&self) -> bool {
    self.0.tag() == 0
  }

  pub fn into_result(self) -> Result<LeanObject, LeanObject> {
    let ctor = self.0.as_ctor();
    if self.is_ok() { Ok(ctor.get(0)) } else { Err(ctor.get(0)) }
  }
}

// =============================================================================
// LeanIOResult — EStateM.Result (BaseIO.Result)
// =============================================================================

/// Typed wrapper for a Lean `BaseIO.Result α` (`EStateM.Result`).
/// ok = ctor tag 0 (value, world), error = ctor tag 1 (error, world).
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct LeanIOResult(LeanObject);

impl Deref for LeanIOResult {
  type Target = LeanObject;
  #[inline]
  fn deref(&self) -> &LeanObject {
    &self.0
  }
}

impl LeanIOResult {
  /// Build a successful IO result (tag 0, fields: [val, box(0)]).
  pub fn ok(val: impl Into<LeanObject>) -> Self {
    let ctor = LeanCtor::alloc(0, 2, 0);
    ctor.set(0, val);
    ctor.set(1, LeanObject::box_usize(0)); // world token
    Self(ctor.0)
  }

  /// Build an IO error result (tag 1, fields: [err, box(0)]).
  pub fn error(err: impl Into<LeanObject>) -> Self {
    let ctor = LeanCtor::alloc(1, 2, 0);
    ctor.set(0, err);
    ctor.set(1, LeanObject::box_usize(0)); // world token
    Self(ctor.0)
  }

  /// Build an IO error from a Rust string via `IO.Error.userError` (tag 7, 1 field).
  pub fn error_string(msg: &str) -> Self {
    let user_error = LeanCtor::alloc(IO_ERROR_USER_ERROR_TAG, 1, 0);
    user_error.set(0, LeanString::new(msg));
    Self::error(*user_error)
  }
}

// =============================================================================
// LeanProd — Prod α β (pair)
// =============================================================================

/// Typed wrapper for a Lean `Prod α β` (ctor tag 0, 2 object fields).
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct LeanProd(LeanObject);

impl Deref for LeanProd {
  type Target = LeanObject;
  #[inline]
  fn deref(&self) -> &LeanObject {
    &self.0
  }
}

impl From<LeanProd> for LeanObject {
  #[inline]
  fn from(x: LeanProd) -> Self {
    x.0
  }
}

impl LeanProd {
  /// Build a pair `(fst, snd)`.
  pub fn new(fst: impl Into<LeanObject>, snd: impl Into<LeanObject>) -> Self {
    let ctor = LeanCtor::alloc(0, 2, 0);
    ctor.set(0, fst);
    ctor.set(1, snd);
    Self(*ctor)
  }

  /// Get the first element.
  pub fn fst(&self) -> LeanObject {
    let ctor = self.0.as_ctor();
    ctor.get(0)
  }

  /// Get the second element.
  pub fn snd(&self) -> LeanObject {
    let ctor = self.0.as_ctor();
    ctor.get(1)
  }
}

// =============================================================================
// From<T> for LeanObject — allow wrapper types to be passed to set() etc.
// =============================================================================

impl From<LeanArray> for LeanObject {
  #[inline]
  fn from(x: LeanArray) -> Self {
    x.0
  }
}

impl From<LeanByteArray> for LeanObject {
  #[inline]
  fn from(x: LeanByteArray) -> Self {
    x.0
  }
}

impl From<LeanString> for LeanObject {
  #[inline]
  fn from(x: LeanString) -> Self {
    x.0
  }
}

impl From<LeanCtor> for LeanObject {
  #[inline]
  fn from(x: LeanCtor) -> Self {
    x.0
  }
}

impl<T> From<LeanExternal<T>> for LeanObject {
  #[inline]
  fn from(x: LeanExternal<T>) -> Self {
    x.0
  }
}

impl From<LeanList> for LeanObject {
  #[inline]
  fn from(x: LeanList) -> Self {
    x.0
  }
}

impl From<LeanOption> for LeanObject {
  #[inline]
  fn from(x: LeanOption) -> Self {
    x.0
  }
}

impl From<LeanExcept> for LeanObject {
  #[inline]
  fn from(x: LeanExcept) -> Self {
    x.0
  }
}

impl From<LeanIOResult> for LeanObject {
  #[inline]
  fn from(x: LeanIOResult) -> Self {
    x.0
  }
}

impl From<u32> for LeanObject {
  #[inline]
  fn from(x: u32) -> Self {
    Self::box_u32(x)
  }
}
