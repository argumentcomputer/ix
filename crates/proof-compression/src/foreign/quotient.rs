use ark_ff::{
  BigInt as Limbs, BigInteger, biginteger::arithmetic::mac_with_carry,
};
use num_bigint::BigInt;
#[cfg(test)]
use num_bigint::Sign;

use super::{P, Scalar, integer, scalar};

pub(super) struct QuotientHint {
  coefficients: [i64; 5],
  offset: Limbs<4>,
}

impl QuotientHint {
  #[cfg(test)]
  pub(super) fn new(coefficients: [i128; 5], offset: &BigInt) -> Self {
    let (sign, words) = offset.to_u64_digits();
    assert_ne!(sign, Sign::Minus);
    assert!(offset.bits() <= 193, "Goldilocks quotient offset bound");
    let mut offset = Limbs::zero();
    offset.0[..words.len()].copy_from_slice(&words);
    Self::from_limbs(coefficients, offset)
  }

  pub(super) fn from_limbs(coefficients: [i128; 5], offset: Limbs<4>) -> Self {
    assert!(offset.num_bits() <= 193, "Goldilocks quotient offset bound");
    Self {
      coefficients: coefficients.map(|c| {
        assert!(c.unsigned_abs() <= u128::from(P / 2));
        i64::try_from(c).expect("signed Goldilocks coefficient")
      }),
      offset,
    }
  }

  pub(super) fn evaluate(&self, values: &[Scalar]) -> Result<Scalar, String> {
    let words =
      [values[0], values[1], values[2]].map(|v| v.canonical_limbs_le());
    if words.iter().any(|v| v[1..] != [0; 3]) {
      return self.evaluate_large(values);
    }
    let [a, b, c] = words.map(|v| u128::from(v[0]));
    let mut positive = self.offset;
    let mut negative = Limbs::zero();
    // |coefficient| < 2^63, a,b,c < 2^64, and offset < 2^193.
    // Each signed accumulator is below 2^194, including all five terms.
    for (coefficient, value) in
      self.coefficients.into_iter().zip([a * b, a, b, c, 1])
    {
      if coefficient == 0 {
        continue;
      }
      let term = product(value, coefficient.unsigned_abs());
      let accumulator =
        if coefficient < 0 { &mut negative } else { &mut positive };
      assert!(!accumulator.add_with_carry(&term));
    }
    let (mut magnitude, smaller, is_negative) = if positive < negative {
      (negative, positive, true)
    } else {
      (positive, negative, false)
    };
    assert!(!magnitude.sub_with_borrow(&smaller));
    let (quotient, remainder) = divide(magnitude);
    if remainder != 0 {
      return Err("invalid Goldilocks gate".into());
    }
    let quotient = Scalar::from_limbs_le(quotient.0);
    Ok(if is_negative { -quotient } else { quotient })
  }

  fn evaluate_large(&self, values: &[Scalar]) -> Result<Scalar, String> {
    let [a, b, c] =
      [integer(values[0]), integer(values[1]), integer(values[2])];
    let [qm, qa, qb, qc, k] = self.coefficients;
    let sum =
      qm * &a * &b + qa * a + qb * b + qc * c + k + BigInt::from(self.offset);
    if &sum % P != BigInt::from(0) {
      return Err("invalid Goldilocks gate".into());
    }
    Ok(scalar(&(sum / P)))
  }
}

#[allow(clippy::cast_possible_truncation)]
pub(super) fn product(value: u128, coefficient: u64) -> Limbs<4> {
  let mut carry = 0;
  let low = mac_with_carry(0, value as u64, coefficient, &mut carry);
  let high = mac_with_carry(0, (value >> 64) as u64, coefficient, &mut carry);
  Limbs([low, high, carry, 0])
}

pub(super) fn divide(value: Limbs<4>) -> (Limbs<4>, u64) {
  let mut quotient = Limbs::zero();
  let mut remainder = 0u128;
  for (word, output) in value.0.into_iter().zip(&mut quotient.0).rev() {
    let dividend = (remainder << 64) | u128::from(word);
    *output =
      u64::try_from(dividend / u128::from(P)).expect("single-limb quotient");
    remainder = dividend % u128::from(P);
  }
  (quotient, u64::try_from(remainder).unwrap())
}
