use std::ffi::c_void;
use std::fmt;

use num_bigint::BigUint;

use crate::{
  lean::{as_ref_unsafe, lean_is_scalar, object::LeanObject},
  lean_unbox,
};

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

  pub fn from_ptr(ptr: *const c_void) -> Nat {
    if lean_is_scalar(ptr) {
      let u = lean_unbox!(usize, ptr);
      Nat(BigUint::from_bytes_le(&u.to_le_bytes()))
    } else {
      // Heap-allocated big integer (mpz_object)
      let obj: &MpzObject = as_ref_unsafe(ptr.cast());
      Nat(obj.m_value.to_biguint())
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
  m_header: LeanObject,
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
