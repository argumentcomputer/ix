//! Lean `Nat` (arbitrary-precision natural number) representation.
//!
//! Lean stores small naturals as tagged scalars and large ones as GMP
//! `mpz_object`s on the heap. This module handles both representations.

use std::ffi::c_int;
use std::fmt;
use std::mem::MaybeUninit;

use num_bigint::BigUint;

use crate::object::LeanObject;

/// Arbitrary-precision natural number, wrapping `BigUint`.
#[derive(Hash, PartialEq, Eq, Debug, Clone, PartialOrd, Ord)]
pub struct Nat(pub BigUint);

impl fmt::Display for Nat {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{}", self.0)
  }
}

impl From<u64> for Nat {
  fn from(x: u64) -> Self {
    Nat(BigUint::from(x))
  }
}

impl Nat {
  pub const ZERO: Self = Self(BigUint::ZERO);

  /// Try to convert to u64, returning None if the value is too large.
  #[inline]
  pub fn to_u64(&self) -> Option<u64> {
    u64::try_from(&self.0).ok()
  }

  /// Decode a `Nat` from a `LeanObject`. Handles both scalar (unboxed)
  /// and heap-allocated (GMP `mpz_object`) representations.
  pub fn from_obj(obj: LeanObject) -> Nat {
    if obj.is_scalar() {
      let u = obj.unbox_usize();
      Nat(BigUint::from_bytes_le(&u.to_le_bytes()))
    } else {
      // Heap-allocated big integer (mpz_object)
      let mpz: &MpzObject = unsafe { &*obj.as_ptr().cast() };
      Nat(mpz.m_value.to_biguint())
    }
  }

  #[inline]
  pub fn from_le_bytes(bytes: &[u8]) -> Nat {
    Nat(BigUint::from_bytes_le(bytes))
  }

  #[inline]
  pub fn to_le_bytes(&self) -> Vec<u8> {
    self.0.to_bytes_le()
  }
}

/// From https://github.com/leanprover/lean4/blob/master/src/runtime/object.h:
/// ```cpp
/// struct mpz_object {
///     lean_object m_header;
///     mpz         m_value;
///     mpz_object() {}
///     explicit mpz_object(mpz const & m):m_value(m) {}
/// };
/// ```
#[repr(C)]
struct MpzObject {
  _header: [u8; 8],
  m_value: Mpz,
}

#[repr(C)]
struct Mpz {
  alloc: i32,
  size: i32,
  d: *const u64,
}

impl Mpz {
  fn to_biguint(&self) -> BigUint {
    let nlimbs = self.size.unsigned_abs() as usize;
    let limbs = unsafe { std::slice::from_raw_parts(self.d, nlimbs) };

    // Convert limbs (little-endian by limb)
    let bytes: Vec<_> =
      limbs.iter().flat_map(|&limb| limb.to_le_bytes()).collect();

    BigUint::from_bytes_le(&bytes)
  }
}

// =============================================================================
// GMP interop for building Lean Nat objects from limbs
// =============================================================================

use crate::include::lean_uint64_to_nat;

/// LEAN_MAX_SMALL_NAT = SIZE_MAX >> 1
const LEAN_MAX_SMALL_NAT: u64 = (usize::MAX >> 1) as u64;

unsafe extern "C" {
  #[link_name = "__gmpz_init"]
  fn mpz_init(x: *mut Mpz);

  #[link_name = "__gmpz_import"]
  fn mpz_import(
    rop: *mut Mpz,
    count: usize,
    order: c_int,
    size: usize,
    endian: c_int,
    nails: usize,
    op: *const u64,
  );

  #[link_name = "__gmpz_clear"]
  fn mpz_clear(x: *mut Mpz);

  /// Lean's internal mpz allocation — deep-copies the mpz value.
  /// Caller must still call mpz_clear on the original.
  fn lean_alloc_mpz(v: *mut Mpz) -> *mut std::ffi::c_void;
}

/// Create a Lean `Nat` from a little-endian array of u64 limbs.
/// Replaces the C function `c_lean_nat_from_limbs` from `ixon_ffi.c`.
/// # Safety
/// `limbs` must be valid for reading `num_limbs` elements.
pub unsafe fn lean_nat_from_limbs(
  num_limbs: usize,
  limbs: *const u64,
) -> LeanObject {
  if num_limbs == 0 {
    return LeanObject::box_usize(0);
  }
  let first = unsafe { *limbs };
  if num_limbs == 1 && first <= LEAN_MAX_SMALL_NAT {
    #[allow(clippy::cast_possible_truncation)] // only targets 64-bit
    return LeanObject::box_usize(first as usize);
  }
  if num_limbs == 1 {
    return unsafe { LeanObject::from_lean_ptr(lean_uint64_to_nat(first)) };
  }
  // Multi-limb: use GMP
  unsafe {
    let mut value = MaybeUninit::<Mpz>::uninit();
    mpz_init(value.as_mut_ptr());
    // order = -1 (least significant limb first)
    // size = 8 bytes per limb, endian = 0 (native), nails = 0
    mpz_import(value.as_mut_ptr(), num_limbs, -1, 8, 0, 0, limbs);
    // lean_alloc_mpz deep-copies; we must free the original
    let result = lean_alloc_mpz(value.as_mut_ptr());
    mpz_clear(value.as_mut_ptr());
    LeanObject::from_raw(result)
  }
}
