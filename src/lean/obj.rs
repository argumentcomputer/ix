//! Type-safe wrappers for Lean FFI object pointers.
//!
//! Each wrapper is a `#[repr(transparent)]` `Copy` newtype over `*const c_void`
//! that asserts the correct Lean tag on construction and provides safe accessor
//! methods. Reference counting is left to Lean (no `Drop` impl).

use std::ffi::c_void;
use std::marker::PhantomData;
use std::ops::Deref;

use super::lean;
use super::safe_cstring;

// =============================================================================
// LeanObj — Untyped base wrapper
// =============================================================================

/// Untyped wrapper around a raw Lean object pointer.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct LeanObj(*const c_void);

impl LeanObj {
  /// Wrap a raw pointer without any tag check.
  ///
  /// # Safety
  /// The pointer must be a valid Lean object (or tagged scalar).
  #[inline]
  pub unsafe fn from_raw(ptr: *const c_void) -> Self {
    Self(ptr)
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
      lean::lean_obj_tag(self.0 as *mut _) as u8
    }
  }

  #[inline]
  pub fn inc_ref(self) {
    if !self.is_scalar() {
      unsafe { lean::lean_inc_ref(self.0 as *mut _) }
    }
  }

  #[inline]
  pub fn dec_ref(self) {
    if !self.is_scalar() {
      unsafe { lean::lean_dec_ref(self.0 as *mut _) }
    }
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
    Self(unsafe { lean::lean_box_uint64(n) }.cast())
  }

  #[inline]
  pub fn unbox_u64(self) -> u64 {
    unsafe { lean::lean_unbox_uint64(self.0 as *mut _) }
  }

  #[inline]
  pub fn box_u32(n: u32) -> Self {
    Self(unsafe { lean::lean_box_uint32(n) }.cast())
  }

  #[inline]
  pub fn unbox_u32(self) -> u32 {
    unsafe { lean::lean_unbox_uint32(self.0 as *mut _) }
  }
}

// =============================================================================
// LeanArray — Array α (tag 246)
// =============================================================================

/// Typed wrapper for a Lean `Array α` object (tag 246).
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct LeanArray(LeanObj);

impl Deref for LeanArray {
  type Target = LeanObj;
  #[inline]
  fn deref(&self) -> &LeanObj {
    &self.0
  }
}

impl LeanArray {
  /// Wrap a raw pointer, asserting it is an `Array` (tag 246).
  ///
  /// # Safety
  /// The pointer must be a valid Lean `Array` object.
  pub unsafe fn from_raw(ptr: *const c_void) -> Self {
    let obj = LeanObj(ptr);
    debug_assert!(!obj.is_scalar() && obj.tag() == 246);
    Self(obj)
  }

  /// Allocate a new array with `size` elements (capacity = size).
  pub fn alloc(size: usize) -> Self {
    let obj = unsafe { lean::lean_alloc_array(size, size) };
    Self(LeanObj(obj.cast()))
  }

  pub fn len(&self) -> usize {
    unsafe { lean::lean_array_size(self.0.as_ptr() as *mut _) }
  }

  pub fn is_empty(&self) -> bool {
    self.len() == 0
  }

  pub fn get(&self, i: usize) -> LeanObj {
    LeanObj(unsafe { lean::lean_array_get_core(self.0.as_ptr() as *mut _, i) }.cast())
  }

  pub fn set(&self, i: usize, val: impl Into<LeanObj>) {
    let val: LeanObj = val.into();
    unsafe {
      lean::lean_array_set_core(self.0.as_ptr() as *mut _, i, val.as_ptr() as *mut _);
    }
  }

  /// Return a slice over the array elements.
  pub fn data(&self) -> &[LeanObj] {
    unsafe {
      let cptr = lean::lean_array_cptr(self.0.as_ptr() as *mut _);
      // Safety: LeanObj is repr(transparent) over *const c_void, and
      // lean_array_cptr returns *mut *mut lean_object which has the same layout.
      std::slice::from_raw_parts(cptr.cast(), self.len())
    }
  }

  pub fn iter(&self) -> impl Iterator<Item = LeanObj> + '_ {
    self.data().iter().copied()
  }

  pub fn map<T>(&self, f: impl Fn(LeanObj) -> T) -> Vec<T> {
    self.iter().map(f).collect()
  }
}

// =============================================================================
// LeanByteArray — ByteArray (tag 248, scalar array)
// =============================================================================

/// Typed wrapper for a Lean `ByteArray` object (tag 248).
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct LeanByteArray(LeanObj);

impl Deref for LeanByteArray {
  type Target = LeanObj;
  #[inline]
  fn deref(&self) -> &LeanObj {
    &self.0
  }
}

impl LeanByteArray {
  /// Wrap a raw pointer, asserting it is a `ByteArray` (tag 248).
  ///
  /// # Safety
  /// The pointer must be a valid Lean `ByteArray` object.
  pub unsafe fn from_raw(ptr: *const c_void) -> Self {
    let obj = LeanObj(ptr);
    debug_assert!(!obj.is_scalar() && obj.tag() == 248);
    Self(obj)
  }

  /// Allocate a new byte array with `size` bytes (capacity = size).
  pub fn alloc(size: usize) -> Self {
    let obj = unsafe { lean::lean_alloc_sarray(1, size, size) };
    Self(LeanObj(obj.cast()))
  }

  /// Allocate a new byte array and copy `data` into it.
  pub fn from_bytes(data: &[u8]) -> Self {
    let arr = Self::alloc(data.len());
    unsafe {
      let cptr = lean::lean_sarray_cptr(arr.0.as_ptr() as *mut _);
      std::ptr::copy_nonoverlapping(data.as_ptr(), cptr, data.len());
    }
    arr
  }

  pub fn len(&self) -> usize {
    unsafe { lean::lean_sarray_size(self.0.as_ptr() as *mut _) }
  }

  pub fn is_empty(&self) -> bool {
    self.len() == 0
  }

  /// Return the byte contents as a slice.
  pub fn as_bytes(&self) -> &[u8] {
    unsafe {
      let cptr = lean::lean_sarray_cptr(self.0.as_ptr() as *mut _);
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
      let cptr = lean::lean_sarray_cptr(obj as *mut _);
      std::ptr::copy_nonoverlapping(data.as_ptr(), cptr, data.len());
      // Update m_size: at offset 8 (after lean_object header)
      *obj.cast::<u8>().add(8).cast::<usize>() = data.len();
    }
  }
}

// =============================================================================
// LeanString — String (tag 249)
// =============================================================================

/// Typed wrapper for a Lean `String` object (tag 249).
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct LeanString(LeanObj);

impl Deref for LeanString {
  type Target = LeanObj;
  #[inline]
  fn deref(&self) -> &LeanObj {
    &self.0
  }
}

impl LeanString {
  /// Wrap a raw pointer, asserting it is a `String` (tag 249).
  ///
  /// # Safety
  /// The pointer must be a valid Lean `String` object.
  pub unsafe fn from_raw(ptr: *const c_void) -> Self {
    let obj = LeanObj(ptr);
    debug_assert!(!obj.is_scalar() && obj.tag() == 249);
    Self(obj)
  }

  /// Create a Lean string from a Rust `&str`.
  pub fn from_str(s: &str) -> Self {
    let c = safe_cstring(s);
    let obj = unsafe { lean::lean_mk_string(c.as_ptr()) };
    Self(LeanObj(obj.cast()))
  }

  /// Decode the Lean string into a Rust `String`.
  pub fn to_string(&self) -> String {
    unsafe {
      let obj = self.0.as_ptr() as *mut _;
      let len = lean::lean_string_size(obj) - 1; // m_size includes NUL
      let data = lean::lean_string_cstr(obj);
      let bytes = std::slice::from_raw_parts(data.cast::<u8>(), len);
      String::from_utf8_unchecked(bytes.to_vec())
    }
  }

  /// Number of data bytes (excluding the trailing NUL).
  pub fn byte_len(&self) -> usize {
    unsafe { lean::lean_string_size(self.0.as_ptr() as *mut _) - 1 }
  }
}

// =============================================================================
// LeanCtor — Constructor objects (tag 0–243)
// =============================================================================

/// Typed wrapper for a Lean constructor object (tag 0–243).
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct LeanCtor(LeanObj);

impl Deref for LeanCtor {
  type Target = LeanObj;
  #[inline]
  fn deref(&self) -> &LeanObj {
    &self.0
  }
}

impl LeanCtor {
  /// Wrap a raw pointer, asserting it is a constructor (tag <= 243).
  ///
  /// # Safety
  /// The pointer must be a valid Lean constructor object.
  pub unsafe fn from_raw(ptr: *const c_void) -> Self {
    let obj = LeanObj(ptr);
    debug_assert!(!obj.is_scalar() && obj.tag() <= 243);
    Self(obj)
  }

  /// Allocate a new constructor object.
  pub fn alloc(tag: u8, num_objs: usize, scalar_size: usize) -> Self {
    #[allow(clippy::cast_possible_truncation)]
    let obj = unsafe {
      lean::lean_alloc_ctor(
        tag as u32,
        num_objs as u32,
        scalar_size as u32,
      )
    };
    Self(LeanObj(obj.cast()))
  }

  pub fn tag(&self) -> u8 {
    self.0.tag()
  }

  /// Get the `i`-th object field via `lean_ctor_get`.
  pub fn get(&self, i: usize) -> LeanObj {
    #[allow(clippy::cast_possible_truncation)]
    LeanObj(
      unsafe { lean::lean_ctor_get(self.0.as_ptr() as *mut _, i as u32) }.cast(),
    )
  }

  /// Set the `i`-th object field via `lean_ctor_set`.
  pub fn set(&self, i: usize, val: impl Into<LeanObj>) {
    let val: LeanObj = val.into();
    #[allow(clippy::cast_possible_truncation)]
    unsafe {
      lean::lean_ctor_set(
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
      lean::lean_ctor_set_uint8(self.0.as_ptr() as *mut _, offset as u32, val);
    }
  }

  /// Read `N` object-field pointers using raw pointer math.
  ///
  /// This bypasses `lean_ctor_get`'s bounds check, which is necessary when
  /// reading past the declared object fields into the scalar area (e.g. for
  /// `Expr.Data`).
  pub fn objs<const N: usize>(&self) -> [LeanObj; N] {
    let base = unsafe { self.0.as_ptr().cast::<*const c_void>().add(1) };
    std::array::from_fn(|i| LeanObj(unsafe { *base.add(i) }))
  }

  /// Read a `u64` scalar at `offset` bytes past `num_objs` object fields.
  pub fn scalar_u64(&self, num_objs: usize, offset: usize) -> u64 {
    unsafe {
      std::ptr::read_unaligned(
        self.0
          .as_ptr()
          .cast::<u8>()
          .add(8 + num_objs * 8 + offset)
          .cast(),
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
// LeanExternal<T> — External objects (tag 254)
// =============================================================================

/// Typed wrapper for a Lean external object (tag 254) holding a `T`.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct LeanExternal<T>(LeanObj, PhantomData<T>);

impl<T> Deref for LeanExternal<T> {
  type Target = LeanObj;
  #[inline]
  fn deref(&self) -> &LeanObj {
    &self.0
  }
}

impl<T> LeanExternal<T> {
  /// Wrap a raw pointer, asserting it is an external object (tag 254).
  ///
  /// # Safety
  /// The pointer must be a valid Lean external object whose data pointer
  /// points to a valid `T`.
  pub unsafe fn from_raw(ptr: *const c_void) -> Self {
    let obj = LeanObj(ptr);
    debug_assert!(!obj.is_scalar() && obj.tag() == 254);
    Self(obj, PhantomData)
  }

  /// Allocate a new external object holding `data`.
  pub fn alloc(class: &ExternalClass, data: T) -> Self {
    let data_ptr = Box::into_raw(Box::new(data));
    let obj = unsafe { lean::lean_alloc_external(class.0 as *mut _, data_ptr.cast()) };
    Self(LeanObj(obj.cast()), PhantomData)
  }

  /// Get a reference to the wrapped data.
  pub fn get(&self) -> &T {
    unsafe { &*lean::lean_get_external_data(self.0.as_ptr() as *mut _).cast::<T>() }
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
    finalizer: lean::lean_external_finalize_proc,
    foreach: lean::lean_external_foreach_proc,
  ) -> Self {
    Self(unsafe { lean::lean_register_external_class(finalizer, foreach) }.cast())
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
      Self::register(
        Some(drop_finalizer::<T>),
        Some(super::noop_foreach),
      )
    }
  }
}

// =============================================================================
// LeanList — List α
// =============================================================================

/// Typed wrapper for a Lean `List α` (nil = scalar `lean_box(0)`, cons = ctor tag 1).
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct LeanList(LeanObj);

impl Deref for LeanList {
  type Target = LeanObj;
  #[inline]
  fn deref(&self) -> &LeanObj {
    &self.0
  }
}

impl LeanList {
  /// Wrap a raw pointer, asserting it is a valid `List` (scalar nil or ctor tag 1).
  ///
  /// # Safety
  /// The pointer must be a valid Lean `List` object.
  pub unsafe fn from_raw(ptr: *const c_void) -> Self {
    let obj = LeanObj(ptr);
    debug_assert!(obj.is_scalar() || obj.tag() == 1);
    Self(obj)
  }

  /// The empty list.
  pub fn nil() -> Self {
    Self(LeanObj::box_usize(0))
  }

  /// Prepend `head` to `tail`.
  pub fn cons(head: impl Into<LeanObj>, tail: LeanList) -> Self {
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

  pub fn collect<T>(&self, f: impl Fn(LeanObj) -> T) -> Vec<T> {
    self.iter().map(f).collect()
  }

  /// Build a list from an iterator of values convertible to `LeanObj`.
  pub fn from_iter(items: impl IntoIterator<Item = impl Into<LeanObj>>) -> Self {
    let items: Vec<LeanObj> = items.into_iter().map(Into::into).collect();
    let mut list = Self::nil();
    for item in items.into_iter().rev() {
      list = Self::cons(item, list);
    }
    list
  }
}

/// Iterator over the elements of a `LeanList`.
pub struct LeanListIter(LeanObj);

impl Iterator for LeanListIter {
  type Item = LeanObj;
  fn next(&mut self) -> Option<Self::Item> {
    if self.0.is_scalar() {
      return None;
    }
    let ctor = unsafe { LeanCtor::from_raw(self.0.as_ptr()) };
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
pub struct LeanOption(LeanObj);

impl Deref for LeanOption {
  type Target = LeanObj;
  #[inline]
  fn deref(&self) -> &LeanObj {
    &self.0
  }
}

impl LeanOption {
  /// Wrap a raw pointer, asserting it is a valid `Option`.
  ///
  /// # Safety
  /// The pointer must be a valid Lean `Option` object.
  pub unsafe fn from_raw(ptr: *const c_void) -> Self {
    let obj = LeanObj(ptr);
    debug_assert!(obj.is_scalar() || obj.tag() == 1);
    Self(obj)
  }

  pub fn none() -> Self {
    Self(LeanObj::box_usize(0))
  }

  pub fn some(val: impl Into<LeanObj>) -> Self {
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

  pub fn to_option(&self) -> Option<LeanObj> {
    if self.is_none() {
      None
    } else {
      let ctor = unsafe { LeanCtor::from_raw(self.0.as_ptr()) };
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
pub struct LeanExcept(LeanObj);

impl Deref for LeanExcept {
  type Target = LeanObj;
  #[inline]
  fn deref(&self) -> &LeanObj {
    &self.0
  }
}

impl LeanExcept {
  /// Wrap a raw pointer, asserting it is a valid `Except`.
  ///
  /// # Safety
  /// The pointer must be a valid Lean `Except` object.
  pub unsafe fn from_raw(ptr: *const c_void) -> Self {
    let obj = LeanObj(ptr);
    debug_assert!(!obj.is_scalar() && (obj.tag() == 0 || obj.tag() == 1));
    Self(obj)
  }

  /// Build `Except.ok val`.
  pub fn ok(val: impl Into<LeanObj>) -> Self {
    let ctor = LeanCtor::alloc(1, 1, 0);
    ctor.set(0, val);
    Self(ctor.0)
  }

  /// Build `Except.error msg`.
  pub fn error(msg: impl Into<LeanObj>) -> Self {
    let ctor = LeanCtor::alloc(0, 1, 0);
    ctor.set(0, msg);
    Self(ctor.0)
  }

  /// Build `Except.error (String.mk msg)` from a Rust string.
  pub fn error_string(msg: &str) -> Self {
    Self::error(LeanString::from_str(msg))
  }

  pub fn is_ok(&self) -> bool {
    self.0.tag() == 1
  }

  pub fn is_error(&self) -> bool {
    self.0.tag() == 0
  }

  pub fn into_result(self) -> Result<LeanObj, LeanObj> {
    let ctor = unsafe { LeanCtor::from_raw(self.0.as_ptr()) };
    if self.is_ok() {
      Ok(ctor.get(0))
    } else {
      Err(ctor.get(0))
    }
  }
}

// =============================================================================
// From<T> for LeanObj — allow wrapper types to be passed to set() etc.
// =============================================================================

impl From<LeanArray> for LeanObj {
  #[inline]
  fn from(x: LeanArray) -> Self { x.0 }
}

impl From<LeanByteArray> for LeanObj {
  #[inline]
  fn from(x: LeanByteArray) -> Self { x.0 }
}

impl From<LeanString> for LeanObj {
  #[inline]
  fn from(x: LeanString) -> Self { x.0 }
}

impl From<LeanCtor> for LeanObj {
  #[inline]
  fn from(x: LeanCtor) -> Self { x.0 }
}

impl<T> From<LeanExternal<T>> for LeanObj {
  #[inline]
  fn from(x: LeanExternal<T>) -> Self { x.0 }
}

impl From<LeanList> for LeanObj {
  #[inline]
  fn from(x: LeanList) -> Self { x.0 }
}

impl From<LeanOption> for LeanObj {
  #[inline]
  fn from(x: LeanOption) -> Self { x.0 }
}

impl From<LeanExcept> for LeanObj {
  #[inline]
  fn from(x: LeanExcept) -> Self { x.0 }
}

// =============================================================================
// Domain types — typed newtypes for specific Lean types
// =============================================================================

/// Generate a `#[repr(transparent)]` newtype over `LeanObj` for a specific
/// Lean type, with `Deref`, `From`, and a `new` constructor.
macro_rules! lean_domain_type {
  ($($(#[$meta:meta])* $name:ident;)*) => {$(
    $(#[$meta])*
    #[derive(Clone, Copy)]
    #[repr(transparent)]
    pub struct $name(LeanObj);

    impl Deref for $name {
      type Target = LeanObj;
      #[inline]
      fn deref(&self) -> &LeanObj { &self.0 }
    }

    impl From<$name> for LeanObj {
      #[inline]
      fn from(x: $name) -> Self { x.0 }
    }

    impl $name {
      #[inline]
      pub fn new(obj: LeanObj) -> Self { Self(obj) }
    }
  )*};
}

lean_domain_type! {
  // Ix core types
  /// Lean `Ix.Name` object.
  IxName;
  /// Lean `Ix.Level` object.
  IxLevel;
  /// Lean `Ix.Expr` object.
  IxExpr;
  /// Lean `Ix.ConstantInfo` object.
  IxConstantInfo;
  /// Lean `Ix.RawEnvironment` object.
  IxRawEnvironment;
  /// Lean `Ix.Environment` object.
  IxEnvironment;
  /// Lean `Ix.RustCondensedBlocks` object.
  IxCondensedBlocks;
  /// Lean `Ix.CompileM.RustCompilePhases` object.
  IxCompilePhases;

  // Ix data types
  /// Lean `Ix.Int` object.
  IxInt;
  /// Lean `Ix.Substring` object.
  IxSubstring;
  /// Lean `Ix.SourceInfo` object.
  IxSourceInfo;
  /// Lean `Ix.SyntaxPreresolved` object.
  IxSyntaxPreresolved;
  /// Lean `Ix.Syntax` object.
  IxSyntax;
  /// Lean `Ix.DataValue` object.
  IxDataValue;

  // Ixon types
  /// Lean `Ixon.DefKind` object.
  IxonDefKind;
  /// Lean `Ixon.DefinitionSafety` object.
  IxonDefinitionSafety;
  /// Lean `Ixon.QuotKind` object.
  IxonQuotKind;
  /// Lean `Ixon.Univ` object.
  IxonUniv;
  /// Lean `Ixon.Expr` object.
  IxonExpr;
  /// Lean `Ixon.Definition` object.
  IxonDefinition;
  /// Lean `Ixon.RecursorRule` object.
  IxonRecursorRule;
  /// Lean `Ixon.Recursor` object.
  IxonRecursor;
  /// Lean `Ixon.Axiom` object.
  IxonAxiom;
  /// Lean `Ixon.Quotient` object.
  IxonQuotient;
  /// Lean `Ixon.Constructor` object.
  IxonConstructor;
  /// Lean `Ixon.Inductive` object.
  IxonInductive;
  /// Lean `Ixon.InductiveProj` object.
  IxonInductiveProj;
  /// Lean `Ixon.ConstructorProj` object.
  IxonConstructorProj;
  /// Lean `Ixon.RecursorProj` object.
  IxonRecursorProj;
  /// Lean `Ixon.DefinitionProj` object.
  IxonDefinitionProj;
  /// Lean `Ixon.MutConst` object.
  IxonMutConst;
  /// Lean `Ixon.ConstantInfo` object.
  IxonConstantInfo;
  /// Lean `Ixon.Constant` object.
  IxonConstant;
  /// Lean `Ixon.DataValue` object.
  IxonDataValue;
  /// Lean `Ixon.ExprMetaData` object.
  IxonExprMetaData;
  /// Lean `Ixon.ExprMetaArena` object.
  IxonExprMetaArena;
  /// Lean `Ixon.ConstantMeta` object.
  IxonConstantMeta;
  /// Lean `Ixon.Named` object.
  IxonNamed;
  /// Lean `Ixon.Comm` object.
  IxonComm;
  /// Lean `Ixon.RawEnv` object.
  IxonRawEnv;

  // Error types
  /// Lean `Ixon.SerializeError` object.
  IxSerializeError;
  /// Lean `Ix.DecompileM.DecompileError` object.
  IxDecompileError;
  /// Lean `Ix.CompileM.CompileError` object.
  IxCompileError;
  /// Lean `BlockCompareResult` object.
  IxBlockCompareResult;
  /// Lean `BlockCompareDetail` object.
  IxBlockCompareDetail;
}

/// `Ix.Address = { hash : ByteArray }` — single-field struct, unboxed to `ByteArray`.
pub type IxAddress = LeanByteArray;
