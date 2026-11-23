//! Crate field traits for KZG curve scalar fields (`Bn254` and `Bls12381`).
//!
//! [`CurveScalar`] is a `repr(transparent)` newtype over `C::Fr`.
//! A newtype (unlike the p3 fields, which implement the crate traits
//! directly) because the traits require serde and arkworks types only
//! speak `CanonicalSerialize`; the wrapper carries a canonical 32-byte
//! little-endian serde encoding and every crate trait.
//!
//! The field is its own challenge field: `ExtensionOf<CurveScalar<C>>` with
//! `D = 1`, and its own packing with `WIDTH = 1` (the sweep runs scalar; MSM
//! dominates the prover here, not constraint evaluation).

use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use super::curve::{Bls12381, Bn254, KzgCurve};
use ark_ff::{FftField, Field as ArkField};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use p3_matrix::Matrix;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use multi_stark::traits::Algebra;
use multi_stark::traits::ExtensionModulus;
use multi_stark::traits::ExtensionOf;
use multi_stark::traits::Field;
use multi_stark::traits::Packed;
use multi_stark::traits::PackedExtension;
use multi_stark::traits::TwoAdicField;

/// A KZG curve's scalar field as a crate [`Field`].
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Default)]
#[repr(transparent)]
pub struct CurveScalar<C: KzgCurve = Bn254>(pub C::Fr);

/// The default (BN254) KZG scalar field.
pub type Scalar = CurveScalar<Bn254>;

/// The BLS12-381 KZG scalar field.
pub type Bls12381Scalar = CurveScalar<Bls12381>;

impl<C: KzgCurve> Serialize for CurveScalar<C> {
  fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
    let mut bytes = [0u8; 32];
    self
      .0
      .serialize_compressed(&mut bytes[..])
      .map_err(serde::ser::Error::custom)?;
    bytes.serialize(serializer)
  }
}

impl<'de, C: KzgCurve> Deserialize<'de> for CurveScalar<C> {
  fn deserialize<D: Deserializer<'de>>(
    deserializer: D,
  ) -> Result<Self, D::Error> {
    let bytes = <[u8; 32]>::deserialize(deserializer)?;
    C::Fr::deserialize_compressed(&bytes[..])
      .map(Self)
      .map_err(serde::de::Error::custom)
  }
}

impl<C: KzgCurve> Add for CurveScalar<C> {
  type Output = Self;
  #[inline]
  fn add(self, rhs: Self) -> Self {
    Self(self.0 + rhs.0)
  }
}
impl<C: KzgCurve> Sub for CurveScalar<C> {
  type Output = Self;
  #[inline]
  fn sub(self, rhs: Self) -> Self {
    Self(self.0 - rhs.0)
  }
}
impl<C: KzgCurve> Mul for CurveScalar<C> {
  type Output = Self;
  #[inline]
  fn mul(self, rhs: Self) -> Self {
    Self(self.0 * rhs.0)
  }
}
impl<C: KzgCurve> Neg for CurveScalar<C> {
  type Output = Self;
  #[inline]
  fn neg(self) -> Self {
    Self(-self.0)
  }
}
impl<C: KzgCurve> AddAssign for CurveScalar<C> {
  #[inline]
  fn add_assign(&mut self, rhs: Self) {
    self.0 += rhs.0;
  }
}
impl<C: KzgCurve> SubAssign for CurveScalar<C> {
  #[inline]
  fn sub_assign(&mut self, rhs: Self) {
    self.0 -= rhs.0;
  }
}
impl<C: KzgCurve> MulAssign for CurveScalar<C> {
  #[inline]
  fn mul_assign(&mut self, rhs: Self) {
    self.0 *= rhs.0;
  }
}

impl<C: KzgCurve> core::fmt::Display for CurveScalar<C> {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    write!(f, "{}", self.0)
  }
}

impl<C: KzgCurve> CurveScalar<C> {
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
      C::Fr::from_bigint(BigInt(limbs))
        .expect("limbs must be below the scalar modulus"),
    )
  }
}

impl<C: KzgCurve> Algebra<Self> for CurveScalar<C> {
  const ZERO: Self = Self(C::FR_ZERO);
  const ONE: Self = Self(C::FR_ONE);
}

impl<C: KzgCurve> Field for CurveScalar<C> {
  const TWO: Self = Self(C::FR_TWO);
  const NEG_ONE: Self = Self(C::FR_NEG_ONE);
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
    Self(C::Fr::from(b))
  }

  #[inline]
  fn from_u8(x: u8) -> Self {
    Self(C::Fr::from(x))
  }

  #[inline]
  fn from_u32(x: u32) -> Self {
    Self(C::Fr::from(x))
  }

  #[inline]
  fn from_u64(x: u64) -> Self {
    Self(C::Fr::from(x))
  }

  #[inline]
  fn from_usize(x: usize) -> Self {
    Self(C::Fr::from(u64::try_from(x).expect("usize fits u64")))
  }
}

impl<C: KzgCurve> TwoAdicField for CurveScalar<C> {
  const TWO_ADICITY: usize = C::FR_TWO_ADICITY;

  #[inline]
  fn two_adic_generator(bits: usize) -> Self {
    assert!(bits <= Self::TWO_ADICITY, "domain exceeds scalar two-adicity");
    Self(
      C::Fr::get_root_of_unity(1u64 << bits).expect("two-adic subgroup exists"),
    )
  }
}

impl<C: KzgCurve> Packed<Self> for CurveScalar<C> {
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

impl<C: KzgCurve> ExtensionOf<Self> for CurveScalar<C> {
  const D: usize = 1;
  // Unused at D = 1 (the basis is the identity).
  const MODULUS: ExtensionModulus<Self> = ExtensionModulus::Base;
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

impl<C: KzgCurve> PackedExtension<Self, Self> for CurveScalar<C> {
  #[inline]
  fn from_basis_coefficients_fn(mut f: impl FnMut(usize) -> Self) -> Self {
    f(0)
  }

  #[inline]
  fn as_basis_coefficients_slice(&self) -> &[Self] {
    core::slice::from_ref(self)
  }
}

impl<C: KzgCurve> multi_stark::traits::PrimeField for CurveScalar<C> {
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
  use ark_ff::{BigInteger, PrimeField};

  fn check_two_adicity<C: KzgCurve>(expected_two_adicity: usize) {
    assert_eq!(
      u32::try_from(CurveScalar::<C>::TWO_ADICITY).unwrap(),
      <C::Fr as FftField>::TWO_ADICITY
    );
    // The order-2^k generators nest: g_k^2 == g_{k-1}.
    for bits in 1..=CurveScalar::<C>::TWO_ADICITY {
      let g = CurveScalar::<C>::two_adic_generator(bits);
      assert_eq!(g * g, CurveScalar::<C>::two_adic_generator(bits - 1));
    }
    assert_eq!(
      CurveScalar::<C>::two_adic_generator(0),
      <CurveScalar<C> as Algebra<CurveScalar<C>>>::ONE
    );
    assert_eq!(
      CurveScalar::<C>::two_adic_generator(CurveScalar::<C>::TWO_ADICITY)
        .exp_power_of_2(CurveScalar::<C>::TWO_ADICITY - 1),
      CurveScalar::<C>::NEG_ONE
    );
    assert_eq!(CurveScalar::<C>::TWO_ADICITY, expected_two_adicity);
  }

  fn check_serde<C: KzgCurve>() {
    for x in [
      CurveScalar::<C>::ZERO,
      CurveScalar::<C>::from_u64(0xdead_beef_cafe_f00d),
      CurveScalar::<C>::NEG_ONE,
    ] {
      let bytes =
        bincode::serde::encode_to_vec(x, bincode::config::standard()).unwrap();
      assert_eq!(bytes, x.0.into_bigint().to_bytes_le());
      let (y, consumed): (CurveScalar<C>, usize) =
        bincode::serde::decode_from_slice(&bytes, bincode::config::standard())
          .unwrap();
      assert_eq!(consumed, 32);
      assert_eq!(x, y);
    }
    for bytes in [C::Fr::MODULUS.to_bytes_le(), vec![255; 32], vec![0; 31]] {
      let decoded: Result<(CurveScalar<C>, usize), _> =
        bincode::serde::decode_from_slice(&bytes, bincode::config::standard());
      assert!(decoded.is_err());
    }
  }

  #[test]
  fn two_adicity_matches_ark_for_both_curves() {
    check_two_adicity::<Bn254>(28);
    check_two_adicity::<Bls12381>(32);
  }

  #[test]
  #[should_panic(expected = "domain exceeds scalar two-adicity")]
  fn rejects_oversized_generator_bn254() {
    Scalar::two_adic_generator(Scalar::TWO_ADICITY + 1);
  }

  #[test]
  #[should_panic(expected = "domain exceeds scalar two-adicity")]
  fn rejects_oversized_generator_bls12_381() {
    Bls12381Scalar::two_adic_generator(Bls12381Scalar::TWO_ADICITY + 1);
  }

  #[test]
  fn serde_round_trip_and_noncanonical_rejection_for_both_curves() {
    check_serde::<Bn254>();
    check_serde::<Bls12381>();
  }
}
