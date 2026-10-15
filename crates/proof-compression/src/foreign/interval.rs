use ark_ff::{BigInt as Limbs, BigInteger};

use super::{P, quotient};

#[derive(Debug, PartialEq, Eq)]
pub(super) enum GatePlan {
  Direct,
  Quotient { offset: Limbs<4>, bits: usize },
}

impl GatePlan {
  pub(super) fn new(coefficients: [i128; 5], bounds: [u64; 3]) -> Self {
    assert!(coefficients.iter().all(|c| c.unsigned_abs() <= u128::from(P / 2)));
    let [a, b, c] = bounds.map(u128::from);
    let k = coefficients[4];
    let constant = Limbs::from(u64::try_from(k.unsigned_abs()).unwrap());
    let low_positive = if k < 0 { Limbs::zero() } else { constant };
    let mut low_negative = if k < 0 { constant } else { Limbs::zero() };
    let mut high_positive = low_positive;
    let high_negative = low_negative;
    // Each coefficient has magnitude below 2^63 and each bound below
    // 2^64. All interval magnitudes and their width fit below 2^192.
    for (coefficient, maximum) in coefficients.into_iter().zip([a * b, a, b, c])
    {
      let term = quotient::product(
        maximum,
        u64::try_from(coefficient.unsigned_abs()).unwrap(),
      );
      let accumulator =
        if coefficient < 0 { &mut low_negative } else { &mut high_positive };
      assert!(!accumulator.add_with_carry(&term));
    }
    let (low_negative, low) = difference(low_positive, low_negative);
    let (high_negative, high) = difference(high_positive, high_negative);
    let modulus = Limbs::from(P);
    if (!low_negative || low < modulus) && (high_negative || high < modulus) {
      return Self::Direct;
    }
    let mut offset = if low_negative { low } else { Limbs::zero() };
    if low_negative {
      let (_, remainder) = quotient::divide(offset);
      if remainder != 0 {
        assert!(!offset.add_with_carry(&Limbs::from(P - remainder)));
      }
    }
    // offset >= -low and high >= low, even if both endpoints are negative.
    let mut numerator = offset;
    if high_negative {
      assert!(!numerator.sub_with_borrow(&high));
    } else {
      assert!(!numerator.add_with_carry(&high));
    }
    let (max_q, _) = quotient::divide(numerator);
    let bits = usize::try_from(max_q.num_bits()).unwrap();
    assert!(bits <= 130, "Goldilocks gate quotient bound");
    Self::Quotient { offset, bits }
  }
}

fn difference(positive: Limbs<4>, negative: Limbs<4>) -> (bool, Limbs<4>) {
  let (is_negative, mut magnitude, smaller) = if positive < negative {
    (true, negative, positive)
  } else {
    (false, positive, negative)
  };
  assert!(!magnitude.sub_with_borrow(&smaller));
  (is_negative, magnitude)
}
