use super::*;
use crate::{kzg::curve::Fq, recursive::native_field::FqGadget};
use ark_ff::PrimeField;

fn integer_reference(value: Scalar) -> BigUint {
  BigUint::from_bytes_le(
    &value
      .canonical_limbs_le()
      .into_iter()
      .flat_map(u64::to_le_bytes)
      .collect::<Vec<_>>(),
  )
}

fn range_reference<const N: usize>(value: Scalar) -> [Scalar; N] {
  let n = integer_reference(value);
  let bits = crate::recursive::native_field::RANGE_BITS;
  let mask = (BigUint::from(1u8) << bits) - BigUint::from(1u8);
  std::array::from_fn(|i| scalar(&((&n >> (bits * i)) & &mask)))
}

fn relation_reference(
  values: &[Scalar],
  pc: &[i8],
  lc: &[i8],
  constant: i8,
  p_hint: &[BigUint; L],
) -> Result<[Scalar; RELATION_ADVICE_LEN], String> {
  let mut t = vec![BigInt::from(0u8); 2 * L];
  let mut at = 0;
  for &c in pc {
    for i in 0..L {
      for j in 0..L {
        t[i + j] += BigInt::from(c)
          * BigInt::from(integer_reference(values[at + i]))
          * BigInt::from(integer_reference(values[at + L + j]));
      }
    }
    at += 2 * L;
  }
  for &c in lc {
    for i in 0..L {
      t[i] += BigInt::from(c) * BigInt::from(integer_reference(values[at + i]));
    }
    at += L;
  }
  t[0] += constant;
  let total = t.iter().rev().fold(BigInt::from(0u8), |a, c| (a << W) + c);
  let prime = BigInt::from(modulus());
  if &total % &prime != BigInt::from(0u8) {
    return Err("nonzero Fq relation".into());
  }
  let q: BigInt = total / prime + (BigInt::from(1u8) << QUOTIENT_BIAS_BITS);
  let q = q.to_biguint().ok_or("negative biased quotient")?;
  if q.bits() > QUOTIENT_BITS as u64 {
    return Err("Fq quotient overflow".into());
  }
  let q = digits(&q);
  let bias = digits(&(BigUint::from(1u8) << QUOTIENT_BIAS_BITS));
  for i in 0..L {
    for j in 0..L {
      t[i + j] -= BigInt::from(p_hint[i].clone())
        * (BigInt::from(q[j].clone()) - BigInt::from(bias[j].clone()));
    }
  }
  let mut out = [Scalar::ZERO; RELATION_ADVICE_LEN];
  for i in 0..L {
    out[i] = scalar(&q[i]);
  }
  let radix = BigInt::from(1u8) << W;
  let block_radix = &radix * &radix;
  let mut carry = BigInt::from(0u8);
  for j in 0..L {
    carry += &t[2 * j] + &radix * &t[2 * j + 1];
    if &carry % &block_radix != BigInt::from(0u8) {
      return Err("nonintegral Fq carry".into());
    }
    carry /= &block_radix;
    if j < L - 1 {
      let biased: BigInt = &carry + (BigInt::from(1u8) << CARRY_BIAS_BITS);
      let v = biased.to_biguint().ok_or("negative biased carry")?;
      if v.bits() > CARRY_BITS as u64 {
        return Err("Fq carry overflow".into());
      }
      out[L + j] = scalar(&v);
    }
  }
  if carry != BigInt::from(0u8) {
    return Err("nonzero final Fq carry".into());
  }
  Ok(out)
}

struct Case {
  products: Vec<i8>,
  linear: Vec<i8>,
  constant: i8,
  values: Vec<Scalar>,
}

fn cases(count: usize) -> Vec<Case> {
  let mut state = 0x918e_6af2_a79d_c043u64;
  let mut next = || {
    let mut bytes = [0; 48];
    for word in bytes.as_chunks_mut::<8>().0 {
      state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
      *word = state.to_le_bytes();
    }
    Fq::from_le_bytes_mod_order(&bytes)
  };
  (0..count)
    .map(|index| {
      let products: Vec<i8> = [
        vec![1],
        vec![-1],
        vec![3],
        vec![-3],
        vec![1, 1, 1],
        vec![-1, -1, -1],
        vec![2, -1],
        vec![],
      ][index % 8]
        .clone();
      let constant: i8 = [-4, 0, 4][index % 3];
      let mut total = Fq::from(constant.unsigned_abs());
      if constant < 0 {
        total = -total;
      }
      let mut values = Vec::new();
      for &coefficient in &products {
        let a = if index < 8 { -Fq::from(1u8) } else { next() };
        let b = next();
        let term = Fq::from(coefficient.unsigned_abs()) * a * b;
        total += if coefficient < 0 { -term } else { term };
        values.extend(FqGadget::witness_values(a));
        values.extend(FqGadget::witness_values(b));
      }
      let addend = next();
      total += addend;
      values.extend(FqGadget::witness_values(addend));
      values.extend(FqGadget::witness_values(total));
      Case { products, linear: vec![1, -1], constant, values }
    })
    .collect()
}

#[test]
fn range_extraction_and_integer_encoding_match_full_width_reference() {
  for value in [
    Scalar::ZERO,
    Scalar::ONE,
    Scalar::NEG_ONE,
    Scalar::from_limbs_le([u64::MAX, u64::MAX, u64::MAX, 1]),
  ] {
    assert_eq!(integer(value), integer_reference(value));
    assert_eq!(range_limbs::<1>(value), range_reference::<1>(value));
    assert_eq!(range_limbs::<4>(value), range_reference::<4>(value));
    assert_eq!(range_limbs::<5>(value), range_reference::<5>(value));
    assert_eq!(range_limbs::<6>(value), range_reference::<6>(value));
  }
}

#[test]
fn carry_division_preserves_signed_exactness_at_radix_boundaries() {
  let radix = BigInt::from(1u8) << (2 * W);
  for multiplier in [
    BigInt::from(0u8),
    BigInt::from(1i8),
    BigInt::from(-1i8),
    BigInt::from(127i8),
    BigInt::from(-127i8),
    BigInt::from(1u8) << 383,
    -(BigInt::from(1u8) << 383usize),
  ] {
    let exact = &multiplier * &radix;
    for delta in [-1i8, 0, 1] {
      let value = &exact + delta;
      let (quotient, remainder) = (&value / &radix, &value % &radix);
      let mut actual = value.clone();
      let result = divide_carry(&mut actual);
      if remainder == BigInt::from(0u8) {
        assert_eq!(result, Ok(()));
        assert_eq!(actual, quotient);
      } else {
        assert_eq!(result, Err("nonintegral Fq carry".into()));
        assert_eq!(actual, value);
      }
    }
  }
}

#[test]
fn zero_and_quotient_limit_errors_match_reference() {
  let modulus_digits = digits(&modulus());
  assert_eq!(
    relation(&[], &[], &[], 0),
    relation_reference(&[], &[], &[], 0, &modulus_digits)
  );
  let mut values = vec![Scalar::ZERO; 2 * L];
  values[L - 1] = Scalar::NEG_ONE;
  for (value, limb) in values[L..].iter_mut().zip(&modulus_digits) {
    *value = scalar(limb);
  }
  for (coefficient, error) in
    [(1, "Fq quotient overflow"), (-1, "negative biased quotient")]
  {
    let expected = Err(error.into());
    assert_eq!(relation(&values, &[coefficient], &[], 0), expected);
    assert_eq!(
      relation_reference(&values, &[coefficient], &[], 0, &modulus_digits),
      expected
    );
  }
}

#[test]
fn maximal_representatives_have_exact_signed_integer_quotients() {
  let field_bits = Fq::MODULUS_BIT_SIZE as usize;
  let max = (BigUint::from(1u8) << field_bits) - 1u8;
  let total = 3u8 * &max * &max + 3u8 * &max + 4u8;
  let residue = &total % modulus();
  let quotient = &total / modulus();
  let mut values = Vec::new();
  for n in [&max, &max, &max, &residue] {
    values.extend(digits(n).map(|limb| scalar(&limb)));
  }
  for sign in [-1i8, 1] {
    let advice =
      relation(&values, &[3 * sign], &[3 * sign, -sign], 4 * sign).unwrap();
    let encoded_quotient = advice[..L]
      .iter()
      .rev()
      .fold(BigUint::from(0u8), |acc, &limb| (acc << W) + integer(limb));
    let expected = (BigInt::from(1u8) << QUOTIENT_BIAS_BITS)
      + sign * BigInt::from(quotient.clone());
    assert_eq!(BigInt::from(encoded_quotient), expected);
    let top = integer(advice[L - 1]);
    assert!(top.bits() <= (QUOTIENT_BITS - W * (L - 1)) as u64);
    for &carry in &advice[L..] {
      assert!(integer(carry).bits() <= CARRY_BITS as u64);
    }
  }
}

#[test]
fn quotient_carries_and_rejections_match_reference() {
  let modulus_digits = digits(&modulus());
  for mut case in cases(256) {
    let expected = relation_reference(
      &case.values,
      &case.products,
      &case.linear,
      case.constant,
      &modulus_digits,
    )
    .unwrap();
    assert_eq!(
      relation(&case.values, &case.products, &case.linear, case.constant),
      Ok(expected)
    );
    let last_input = case.values.len() - L;
    case.values[last_input] += Scalar::ONE;
    let expected = relation_reference(
      &case.values,
      &case.products,
      &case.linear,
      case.constant,
      &modulus_digits,
    );
    assert!(expected.is_err());
    assert_eq!(
      relation(&case.values, &case.products, &case.linear, case.constant),
      expected
    );
    case.values[0] = Scalar::NEG_ONE;
    assert_eq!(
      relation(&case.values, &case.products, &case.linear, case.constant),
      relation_reference(
        &case.values,
        &case.products,
        &case.linear,
        case.constant,
        &modulus_digits
      )
    );
  }
  let prime = FqGadget::witness_values(Fq::from(0u8));
  let redundant = digits(&modulus()).map(|v| scalar(&v));
  for representative in [prime, redundant] {
    let values: Vec<_> =
      representative.into_iter().cycle().take(3 * L).collect();
    assert_eq!(
      relation(&values, &[-3], &[3], 0),
      relation_reference(&values, &[-3], &[3], 0, &modulus_digits)
    );
  }
}
