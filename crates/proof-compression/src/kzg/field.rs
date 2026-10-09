//! Crate field traits for the BLS12-381 scalar field.
//!
//! [`Scalar`] is a `repr(transparent)` newtype over `ark_bls12_381::Fr`.
//! A newtype (unlike the p3 fields, which implement the crate traits
//! directly) because the traits require serde and arkworks types only
//! speak `CanonicalSerialize`; the wrapper carries a canonical 32-byte
//! little-endian serde encoding and every crate trait.
//!
//! The field is its own challenge field: `ExtensionOf<Scalar>` with
//! `D = 1` (|Fr| ~ 2^255 dwarfs every Schwartz-Zippel term), and its own
//! packing with `WIDTH = 1` (the sweep runs scalar; MSM dominates the
//! prover here, not constraint evaluation).

use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use ark_bls12_381::Fr;
use ark_ff::{AdditiveGroup, FftField, Field as ArkField};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use p3_matrix::Matrix;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use multi_stark::traits::Algebra;
use multi_stark::traits::ExtensionOf;
use multi_stark::traits::Field;
use multi_stark::traits::Packed;
use multi_stark::traits::PackedExtension;
use multi_stark::traits::TwoAdicField;

/// The BLS12-381 scalar field as a crate [`Field`].
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Default)]
#[repr(transparent)]
pub struct Scalar(pub Fr);

impl Serialize for Scalar {
  fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
    let mut bytes = [0u8; 32];
    self
      .0
      .serialize_compressed(&mut bytes[..])
      .map_err(serde::ser::Error::custom)?;
    bytes.serialize(serializer)
  }
}

impl<'de> Deserialize<'de> for Scalar {
  fn deserialize<D: Deserializer<'de>>(
    deserializer: D,
  ) -> Result<Self, D::Error> {
    let bytes = <[u8; 32]>::deserialize(deserializer)?;
    Fr::deserialize_compressed(&bytes[..])
      .map(Self)
      .map_err(serde::de::Error::custom)
  }
}

impl Add for Scalar {
  type Output = Self;
  #[inline]
  fn add(self, rhs: Self) -> Self {
    Self(self.0 + rhs.0)
  }
}
impl Sub for Scalar {
  type Output = Self;
  #[inline]
  fn sub(self, rhs: Self) -> Self {
    Self(self.0 - rhs.0)
  }
}
impl Mul for Scalar {
  type Output = Self;
  #[inline]
  fn mul(self, rhs: Self) -> Self {
    Self(self.0 * rhs.0)
  }
}
impl Neg for Scalar {
  type Output = Self;
  #[inline]
  fn neg(self) -> Self {
    Self(-self.0)
  }
}
impl AddAssign for Scalar {
  #[inline]
  fn add_assign(&mut self, rhs: Self) {
    self.0 += rhs.0;
  }
}
impl SubAssign for Scalar {
  #[inline]
  fn sub_assign(&mut self, rhs: Self) {
    self.0 -= rhs.0;
  }
}
impl MulAssign for Scalar {
  #[inline]
  fn mul_assign(&mut self, rhs: Self) {
    self.0 *= rhs.0;
  }
}

impl core::fmt::Display for Scalar {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    write!(f, "{}", self.0)
  }
}

impl Scalar {
  /// Low 64 bits of the canonical value — exact for values < 2^64.
  /// For Aiur-style consumers that only extract bytes/pointers/counters
  /// (values small by construction).
  pub fn canonical_low_u64(&self) -> u64 {
    use ark_ff::PrimeField;
    self.0.into_bigint().0[0]
  }

  /// The canonical value as four little-endian 64-bit limbs.
  pub fn canonical_limbs_le(&self) -> [u64; 4] {
    use ark_ff::PrimeField;
    self.0.into_bigint().0
  }

  /// The element with the given canonical little-endian limbs.
  ///
  /// # Panics
  /// Panics if the limbs are not below the modulus.
  pub fn from_limbs_le(limbs: [u64; 4]) -> Self {
    use ark_ff::{BigInt, PrimeField};
    Self(
      Fr::from_bigint(BigInt(limbs))
        .expect("limbs must be below the scalar modulus"),
    )
  }
}

impl Algebra<Self> for Scalar {
  const ZERO: Self = Self(<Fr as AdditiveGroup>::ZERO);
  const ONE: Self = Self(<Fr as ArkField>::ONE);
}

impl Field for Scalar {
  const TWO: Self = Self(ark_ff::MontFp!("2"));
  const NEG_ONE: Self = Self(ark_ff::MontFp!("-1"));
  fn prime_order_exceeds(_: usize) -> bool {
    true
  }

  type Packing = Self;

  #[inline]
  fn inverse(&self) -> Self {
    // `inverse(0)` is free per the trait contract; zero keeps it total.
    self.0.inverse().map_or(<Self as Algebra<Self>>::ZERO, Self)
  }

  #[inline]
  fn exp_u64(&self, exp: u64) -> Self {
    Self(self.0.pow([exp]))
  }

  #[inline]
  fn from_bool(b: bool) -> Self {
    Self(Fr::from(b))
  }

  #[inline]
  fn from_u8(x: u8) -> Self {
    Self(Fr::from(x))
  }

  #[inline]
  fn from_u32(x: u32) -> Self {
    Self(Fr::from(x))
  }

  #[inline]
  fn from_u64(x: u64) -> Self {
    Self(Fr::from(x))
  }

  #[inline]
  fn from_usize(x: usize) -> Self {
    Self(Fr::from(u64::try_from(x).expect("usize fits u64")))
  }
}

impl TwoAdicField for Scalar {
  // Fr has a 2^32 root of unity; pinned by a test below.
  const TWO_ADICITY: usize = 32;

  #[inline]
  fn two_adic_generator(bits: usize) -> Self {
    assert!(bits <= Self::TWO_ADICITY);
    Self(Fr::get_root_of_unity(1u64 << bits).expect("two-adic subgroup exists"))
  }
}

impl Packed<Self> for Scalar {
  const WIDTH: usize = 1;

  #[inline]
  fn from_slice(slice: &[Self]) -> &Self {
    &slice[0]
  }

  #[inline]
  fn as_slice(&self) -> &[Self] {
    core::slice::from_ref(self)
  }

  #[inline]
  fn packed_row_pair<M: Matrix<Self>>(
    matrix: &M,
    i: usize,
    step: usize,
  ) -> Vec<Self> {
    let height = matrix.height();
    let width = matrix.width();
    let mut out = Vec::with_capacity(2 * width);
    for r in [i % height, (i + step) % height] {
      out.extend_from_slice(&matrix.row_slice(r).expect("row in range"));
    }
    out
  }
}

impl ExtensionOf<Self> for Scalar {
  const D: usize = 1;
  // Unused at D = 1 (the basis is the identity).
  const W: Self = <Self as Algebra<Self>>::ZERO;
  type ExtPacking = Self;

  #[inline]
  fn as_basis_coefficients_slice(&self) -> &[Self] {
    core::slice::from_ref(self)
  }

  #[inline]
  fn from_basis_coefficients_fn(mut f: impl FnMut(usize) -> Self) -> Self {
    f(0)
  }
}

impl PackedExtension<Self, Self> for Scalar {
  #[inline]
  fn from_basis_coefficients_fn(mut f: impl FnMut(usize) -> Self) -> Self {
    f(0)
  }

  #[inline]
  fn as_basis_coefficients_slice(&self) -> &[Self] {
    core::slice::from_ref(self)
  }
}

impl multi_stark::traits::PrimeField for Scalar {
  fn canonical_u64(self) -> Option<u64> {
    let [lo, a, b, c] = self.canonical_limbs_le();
    (a == 0 && b == 0 && c == 0).then_some(lo)
  }
  fn modulus_u64() -> Option<u64> {
    None
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn two_adicity_matches_ark() {
    assert_eq!(
      u32::try_from(Scalar::TWO_ADICITY).unwrap(),
      <Fr as FftField>::TWO_ADICITY
    );
    // The order-2^k generators nest: g_k^2 == g_{k-1}.
    for bits in 1..=Scalar::TWO_ADICITY {
      let g = Scalar::two_adic_generator(bits);
      assert_eq!(g * g, Scalar::two_adic_generator(bits - 1));
    }
    assert_eq!(Scalar::two_adic_generator(0), <Scalar as Algebra<Scalar>>::ONE);
  }

  #[test]
  fn serde_round_trip() {
    let x = Scalar::from_u64(0xdead_beef_cafe_f00d);
    let bytes =
      bincode::serde::encode_to_vec(x, bincode::config::standard()).unwrap();
    let (y, _): (Scalar, usize) =
      bincode::serde::decode_from_slice(&bytes, bincode::config::standard())
        .unwrap();
    assert_eq!(x, y);
  }

  #[test]
  fn inverse_and_powers() {
    let x = Scalar::from_u32(12345);
    assert_eq!(x * x.inverse(), <Scalar as Algebra<Scalar>>::ONE);
    let cube: Vec<Scalar> = x.powers().take(4).collect();
    assert_eq!(cube[3], x * x * x);
    assert_eq!(x.exp_u64(3), cube[3]);
    assert_eq!(x.exp_power_of_2(3), x.exp_u64(8));
  }
}
