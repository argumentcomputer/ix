use std::sync::OnceLock;

use super::{
  BigInt, BigUint, CARRY_BITS, L, Scalar, W, digits, integer, modulus, scalar,
};
use multi_stark::traits::{Algebra, Field};

pub(super) struct Constants {
  pub(super) modulus_digits: [BigUint; L],
  modulus_signed_digits: [BigInt; L],
  prime: BigInt,
  quotient_bias: BigInt,
  bias_digits: [BigInt; L],
  carry_bias: BigInt,
}

pub(super) fn constants() -> &'static Constants {
  static CONSTANTS: OnceLock<Constants> = OnceLock::new();
  CONSTANTS.get_or_init(|| {
    let prime = modulus();
    let modulus_digits = digits(&prime);
    let quotient_bias = BigUint::from(1u8) << 383;
    Constants {
      modulus_signed_digits: modulus_digits.clone().map(BigInt::from),
      modulus_digits,
      prime: BigInt::from(prime),
      bias_digits: digits(&quotient_bias).map(BigInt::from),
      quotient_bias: BigInt::from(quotient_bias),
      carry_bias: BigInt::from(1u8) << 88usize,
    }
  })
}

pub(super) fn range_limbs<const N: usize>(value: Scalar) -> [Scalar; N] {
  let words = value.canonical_limbs_le();
  std::array::from_fn(|i| {
    Scalar::from_u64((words[i / 4] >> (16 * (i % 4))) & 0xffff)
  })
}

pub(super) fn relation(
  values: &[Scalar],
  products: &[i8],
  linear: &[i8],
  constant: i8,
) -> Result<[Scalar; 9], String> {
  let constants = constants();
  let values: Vec<_> =
    values.iter().map(|&v| BigInt::from(integer(v))).collect();
  let mut terms: [BigInt; 10] = std::array::from_fn(|_| BigInt::from(0u8));
  let mut at = 0;
  for &coefficient in products {
    let scaled: [BigInt; L] =
      std::array::from_fn(|i| coefficient * &values[at + i]);
    for i in 0..L {
      for j in 0..L {
        terms[i + j] += &scaled[i] * &values[at + L + j];
      }
    }
    at += 2 * L;
  }
  for &coefficient in linear {
    for i in 0..L {
      terms[i] += coefficient * &values[at + i];
    }
    at += L;
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
  if quotient.bits() > 384 {
    return Err("Fq quotient overflow".into());
  }
  let quotient = digits(&quotient);
  let unbiased: [BigInt; L] = std::array::from_fn(|i| {
    BigInt::from(quotient[i].clone()) - &constants.bias_digits[i]
  });
  for i in 0..L {
    for j in 0..L {
      terms[i + j] -= &constants.modulus_signed_digits[i] * &unbiased[j];
    }
  }
  let mut out = [Scalar::ZERO; 9];
  for i in 0..L {
    out[i] = scalar(&quotient[i]);
  }
  let mut carry = BigInt::from(0u8);
  for j in 0..5 {
    carry += &terms[2 * j] + (&terms[2 * j + 1] << W);
    divide_carry(&mut carry)?;
    if j < 4 {
      let biased = &carry + &constants.carry_bias;
      let value = biased.to_biguint().ok_or("negative biased carry")?;
      if value.bits() > CARRY_BITS as u64 {
        return Err("Fq carry overflow".into());
      }
      out[L + j] = scalar(&value);
    }
  }
  if carry != BigInt::from(0u8) {
    return Err("nonzero final Fq carry".into());
  }
  Ok(out)
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

#[cfg(test)]
pub(super) use tests::{range_reference, relation_reference};
