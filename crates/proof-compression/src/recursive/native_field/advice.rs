use std::sync::OnceLock;

use super::{
  BigInt, BigUint, CARRY_BIAS_BITS, CARRY_BITS, CurveScalar, KzgCurve, W,
  digits, integer, limb_count, modulus, quotient_bias_bits, quotient_bits,
  relation_advice_len, scalar,
};
use crate::kzg::curve::Curve;
use multi_stark::traits::{Algebra, Field};

pub(super) struct Constants {
  pub(super) modulus_digits: Vec<BigUint>,
  modulus_signed_digits: Vec<BigInt>,
  prime: BigInt,
  quotient_bias: BigInt,
  bias_digits: Vec<BigInt>,
  carry_bias: BigInt,
}

fn build_constants<C: KzgCurve>() -> Constants {
  let prime = modulus::<C>();
  let modulus_digits = digits::<C>(&prime);
  let quotient_bias = BigUint::from(1u8) << quotient_bias_bits::<C>();
  Constants {
    modulus_signed_digits: modulus_digits
      .iter()
      .cloned()
      .map(BigInt::from)
      .collect(),
    modulus_digits,
    prime: BigInt::from(prime),
    bias_digits: digits::<C>(&quotient_bias)
      .into_iter()
      .map(BigInt::from)
      .collect(),
    quotient_bias: BigInt::from(quotient_bias),
    carry_bias: BigInt::from(1u8) << CARRY_BIAS_BITS,
  }
}

pub(super) fn constants<C: KzgCurve>() -> &'static Constants {
  static BN254_CONSTANTS: OnceLock<Constants> = OnceLock::new();
  static BLS12381_CONSTANTS: OnceLock<Constants> = OnceLock::new();
  match C::CURVE {
    Curve::Bn254 => BN254_CONSTANTS.get_or_init(build_constants::<C>),
    Curve::Bls12381 => BLS12381_CONSTANTS.get_or_init(build_constants::<C>),
  }
}

pub(super) fn range_limbs<C: KzgCurve, const N: usize>(
  value: CurveScalar<C>,
) -> [CurveScalar<C>; N] {
  let words = value.canonical_limbs_le();
  let bit = |index: usize| (words[index / 64] >> (index % 64)) & 1;
  std::array::from_fn(|i| {
    let limb = (0..super::RANGE_BITS).fold(0u64, |acc, j| {
      let index = super::RANGE_BITS * i + j;
      acc | if index < 256 { bit(index) << j } else { 0 }
    });
    CurveScalar::<C>::from_u64(limb)
  })
}

pub(super) fn relation<C: KzgCurve>(
  values: &[CurveScalar<C>],
  products: &[i8],
  linear: &[i8],
  constant: i8,
) -> Result<Vec<CurveScalar<C>>, String> {
  let l = limb_count::<C>();
  let advice_len = relation_advice_len::<C>();
  let constants = constants::<C>();
  let values: Vec<_> =
    values.iter().map(|&v| BigInt::from(integer(v))).collect();
  let mut terms: Vec<BigInt> = vec![BigInt::from(0u8); 2 * l];
  let mut at = 0;
  for &coefficient in products {
    let scaled: Vec<BigInt> =
      (0..l).map(|i| coefficient * &values[at + i]).collect();
    for i in 0..l {
      for j in 0..l {
        terms[i + j] += &scaled[i] * &values[at + l + j];
      }
    }
    at += 2 * l;
  }
  for &coefficient in linear {
    for i in 0..l {
      terms[i] += coefficient * &values[at + i];
    }
    at += l;
  }
  terms[0] += constant;
  let total = terms.iter().rev().fold(BigInt::from(0u8), |a, c| (a << W) + c);
  let quotient = &total / &constants.prime;
  let remainder = &total % &constants.prime;
  if remainder != BigInt::from(0u8) {
    return Err("nonzero Fq relation".into());
  }
  let quotient = quotient + &constants.quotient_bias;
  let quotient = quotient.to_biguint().ok_or("negative biased quotient")?;
  if quotient.bits() > quotient_bits::<C>() as u64 {
    return Err("Fq quotient overflow".into());
  }
  let quotient = digits::<C>(&quotient);
  let unbiased: Vec<BigInt> = (0..l)
    .map(|i| BigInt::from(quotient[i].clone()) - &constants.bias_digits[i])
    .collect();
  for i in 0..l {
    for j in 0..l {
      terms[i + j] -= &constants.modulus_signed_digits[i] * &unbiased[j];
    }
  }
  let mut out = vec![CurveScalar::<C>::ZERO; advice_len];
  for i in 0..l {
    out[i] = scalar::<C>(&quotient[i]);
  }
  let mut carry = BigInt::from(0u8);
  for j in 0..l {
    carry += &terms[2 * j] + (&terms[2 * j + 1] << W);
    divide_carry(&mut carry)?;
    if j < l - 1 {
      let biased = &carry + &constants.carry_bias;
      let value = biased.to_biguint().ok_or("negative biased carry")?;
      if value.bits() > CARRY_BITS as u64 {
        return Err("Fq carry overflow".into());
      }
      out[l + j] = scalar::<C>(&value);
    }
  }
  if carry != BigInt::from(0u8) {
    return Err("nonzero final Fq carry".into());
  }
  Ok(out)
}

pub(super) fn relation_array<C: KzgCurve, const N: usize>(
  values: &[CurveScalar<C>],
  products: &[i8],
  linear: &[i8],
  constant: i8,
) -> Result<[CurveScalar<C>; N], String> {
  debug_assert_eq!(N, relation_advice_len::<C>());
  let out = relation::<C>(values, products, linear, constant)?;
  Ok(std::array::from_fn(|i| out[i]))
}

fn divide_carry(carry: &mut BigInt) -> Result<(), String> {
  // Exactness makes arithmetic right shift agree with division for negative
  // carries too. Zero has no trailing-zero count and is exactly divisible.
  if carry.trailing_zeros().is_some_and(|bits| bits < (2 * W) as u64) {
    return Err("nonintegral Fq carry".into());
  }
  *carry >>= 2 * W;
  Ok(())
}

#[cfg(test)]
mod tests;
