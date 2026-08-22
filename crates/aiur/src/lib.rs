pub mod bytecode;
pub mod constraints;
pub mod execute;
pub mod gadgets;
pub mod memory;
pub mod querymap;
pub mod synthesis;
pub mod trace;
pub mod vk_codec;

use indexmap::IndexMap;
use multi_stark::p3_field::PrimeField64;
use multi_stark::traits::{Algebra, Field, TwoAdicField};
use rustc_hash::FxBuildHasher;

/// The default (and currently only proving-ready) Aiur field.
pub type G = multi_stark::p3_goldilocks::Goldilocks;
pub type FxIndexMap<K, V> = IndexMap<K, V, FxBuildHasher>;

/// The field surface Aiur needs beyond multi-stark's crate traits:
/// canonical integer extraction. The executor and witness builders only
/// ever call it on values that are small by construction (bytes,
/// pointers, counters, u32 words) or on the deliberate 8-byte hint
/// decomposition (`UnconstrainedGToBytes`), so implementations for
/// fields larger than 64 bits may take the canonical value's low 64
/// bits — with the caveat that such a field's toplevels must not use
/// the 8-byte hint (the foreign Goldilocks interface doesn't).
pub trait AiurField: Field + TwoAdicField + Ord + std::fmt::Display {
  /// The canonical value as a `u64`; exact for values < 2^64.
  fn as_canonical_u64(&self) -> u64;
  /// The `UnconstrainedGlDivMod` hint: the canonical integer value split
  /// as `q · p_goldilocks + r` with `r < p_goldilocks`, both returned as
  /// field values. Over Goldilocks itself every value is `< p`, so this
  /// is `(0, v)`; over a large field it is exact big-integer division.
  fn gl_divmod(&self) -> (Self, Self);
  /// The `UnconstrainedGlInverse` hint: the inverse MODULO p_goldilocks of
  /// a canonical value `< p_goldilocks` (`0 ↦ 0`), as a field value.
  fn gl_inverse(&self) -> Self;
}

/// The Goldilocks modulus, the inner field of the recursive verifier.
pub const GOLDILOCKS_P: u64 = 0xFFFF_FFFF_0000_0001;

impl AiurField for G {
  #[inline]
  fn as_canonical_u64(&self) -> u64 {
    <Self as PrimeField64>::as_canonical_u64(self)
  }
  #[inline]
  fn gl_divmod(&self) -> (Self, Self) {
    (<Self as Algebra<Self>>::ZERO, *self)
  }
  #[inline]
  fn gl_inverse(&self) -> Self {
    if self.is_zero() { <Self as Algebra<Self>>::ZERO } else { self.inverse() }
  }
}

/// The BLS12-381 scalar field as an Aiur field (the KZG terminal
/// stage). `as_canonical_u64` takes the canonical value's low 64 bits —
/// exact for the bytes/pointers/counters Aiur extracts; toplevels for
/// this field must not use the 8-byte hint (see the trait docs).
#[cfg(feature = "kzg")]
impl AiurField for multi_stark::ark_adapter::Scalar {
  #[inline]
  fn as_canonical_u64(&self) -> u64 {
    self.canonical_low_u64()
  }
  fn gl_divmod(&self) -> (Self, Self) {
    use multi_stark::ark_adapter::Scalar;
    // Long division of the canonical 256-bit value by the 64-bit modulus,
    // most significant limb first; the quotient is < the scalar modulus
    // (it is < v), so it embeds exactly.
    let limbs = self.canonical_limbs_le();
    let mut q = [0u64; 4];
    let mut rem: u128 = 0;
    for i in (0..4).rev() {
      let cur = (rem << 64) | u128::from(limbs[i]);
      q[i] = u64::try_from(cur / u128::from(GOLDILOCKS_P))
        .expect("limb quotient fits");
      rem = cur % u128::from(GOLDILOCKS_P);
    }
    (
      Scalar::from_limbs_le(q),
      Self::from_u64(u64::try_from(rem).expect("remainder < p")),
    )
  }
  fn gl_inverse(&self) -> Self {
    let v = <G as Field>::from_u64(self.canonical_low_u64());
    <Self as Field>::from_u64(AiurField::as_canonical_u64(
      &AiurField::gl_inverse(&v),
    ))
  }
}

#[inline]
pub fn function_channel<F: AiurField>() -> F {
  <F as Algebra<F>>::ZERO
}

#[inline]
pub fn memory_channel<F: AiurField>() -> F {
  <F as Algebra<F>>::ONE
}

#[inline]
pub fn u8_bit_decomposition_channel<F: AiurField>() -> F {
  F::from_u8(2)
}

#[inline]
pub fn u8_shift_left_channel<F: AiurField>() -> F {
  F::from_u8(3)
}

#[inline]
pub fn u8_shift_right_channel<F: AiurField>() -> F {
  F::from_u8(4)
}

#[inline]
pub fn u8_xor_channel<F: AiurField>() -> F {
  F::from_u8(5)
}

#[inline]
pub fn u8_add_channel<F: AiurField>() -> F {
  F::from_u8(6)
}

#[inline]
pub fn u8_sub_channel<F: AiurField>() -> F {
  F::from_u8(7)
}

#[inline]
pub fn u8_and_channel<F: AiurField>() -> F {
  F::from_u8(8)
}

#[inline]
pub fn u8_or_channel<F: AiurField>() -> F {
  F::from_u8(9)
}

#[inline]
pub fn u8_less_than_channel<F: AiurField>() -> F {
  F::from_u8(10)
}

#[inline]
pub fn u8_range_check_channel<F: AiurField>() -> F {
  F::from_u8(11)
}

#[inline]
pub fn u8_mul_channel<F: AiurField>() -> F {
  F::from_u8(12)
}

#[inline]
pub fn u8_xor_split7_channel<F: AiurField>() -> F {
  F::from_u8(13)
}

#[inline]
pub fn u8_xor_split4_channel<F: AiurField>() -> F {
  F::from_u8(14)
}
