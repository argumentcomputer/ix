use super::*;
use crate::{
  kzg::curve::{Bls12381, Bn254},
  recursive::native_field::FqGadget,
};
use ark_ff::PrimeField;

fn integer_reference<C: KzgCurve>(value: CurveScalar<C>) -> BigUint {
  BigUint::from_bytes_le(
    &value
      .canonical_limbs_le()
      .into_iter()
      .flat_map(u64::to_le_bytes)
      .collect::<Vec<_>>(),
  )
}

fn range_reference<C: KzgCurve, const N: usize>(
  value: CurveScalar<C>,
) -> [CurveScalar<C>; N] {
  let n = integer_reference(value);
  let bits = crate::recursive::native_field::RANGE_BITS;
  let mask = (BigUint::from(1u8) << bits) - BigUint::from(1u8);
  std::array::from_fn(|i| scalar::<C>(&((&n >> (bits * i)) & &mask)))
}

fn relation_reference<C: KzgCurve>(
  values: &[CurveScalar<C>],
  pc: &[i8],
  lc: &[i8],
  constant: i8,
  p_hint: &[BigUint],
) -> Result<Vec<CurveScalar<C>>, String> {
  let l = limb_count::<C>();
  let advice_len = relation_advice_len::<C>();
  let mut t = vec![BigInt::from(0u8); 2 * l];
  let mut at = 0;
  for &c in pc {
    for i in 0..l {
      for j in 0..l {
        t[i + j] += BigInt::from(c)
          * BigInt::from(integer_reference(values[at + i]))
          * BigInt::from(integer_reference(values[at + l + j]));
      }
    }
    at += 2 * l;
  }
  for &c in lc {
    for i in 0..l {
      t[i] += BigInt::from(c) * BigInt::from(integer_reference(values[at + i]));
    }
    at += l;
  }
  t[0] += constant;
  let total = t.iter().rev().fold(BigInt::from(0u8), |a, c| (a << W) + c);
  let prime = BigInt::from(modulus::<C>());
  if &total % &prime != BigInt::from(0u8) {
    return Err("nonzero Fq relation".into());
  }
  let q: BigInt =
    total / prime + (BigInt::from(1u8) << quotient_bias_bits::<C>());
  let q = q.to_biguint().ok_or("negative biased quotient")?;
  if q.bits() > quotient_bits::<C>() as u64 {
    return Err("Fq quotient overflow".into());
  }
  let q = digits::<C>(&q);
  let bias = digits::<C>(&(BigUint::from(1u8) << quotient_bias_bits::<C>()));
  for i in 0..l {
    for j in 0..l {
      t[i + j] -= BigInt::from(p_hint[i].clone())
        * (BigInt::from(q[j].clone()) - BigInt::from(bias[j].clone()));
    }
  }
  let mut out = vec![CurveScalar::<C>::ZERO; advice_len];
  for i in 0..l {
    out[i] = scalar::<C>(&q[i]);
  }
  let radix = BigInt::from(1u8) << W;
  let block_radix = &radix * &radix;
  let mut carry = BigInt::from(0u8);
  for j in 0..l {
    carry += &t[2 * j] + &radix * &t[2 * j + 1];
    if &carry % &block_radix != BigInt::from(0u8) {
      return Err("nonintegral Fq carry".into());
    }
    carry /= &block_radix;
    if j < l - 1 {
      let biased: BigInt = &carry + (BigInt::from(1u8) << CARRY_BIAS_BITS);
      let v = biased.to_biguint().ok_or("negative biased carry")?;
      if v.bits() > CARRY_BITS as u64 {
        return Err("Fq carry overflow".into());
      }
      out[l + j] = scalar::<C>(&v);
    }
  }
  if carry != BigInt::from(0u8) {
    return Err("nonzero final Fq carry".into());
  }
  Ok(out)
}

struct Case<C: KzgCurve> {
  products: Vec<i8>,
  linear: Vec<i8>,
  constant: i8,
  values: Vec<CurveScalar<C>>,
}

fn cases<C: KzgCurve>(count: usize) -> Vec<Case<C>> {
  let mut state = 0x918e_6af2_a79d_c043u64;
  let mut next = || {
    let mut bytes = [0; 48];
    for word in bytes.as_chunks_mut::<8>().0 {
      state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
      *word = state.to_le_bytes();
    }
    C::Fq::from_le_bytes_mod_order(&bytes)
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
      let mut total = C::Fq::from(constant.unsigned_abs());
      if constant < 0 {
        total = -total;
      }
      let mut values = Vec::new();
      for &coefficient in &products {
        let a = if index < 8 { -C::Fq::from(1u8) } else { next() };
        let b = next();
        let term = C::Fq::from(coefficient.unsigned_abs()) * a * b;
        total += if coefficient < 0 { -term } else { term };
        values.extend(FqGadget::<C>::witness_values(a));
        values.extend(FqGadget::<C>::witness_values(b));
      }
      let addend = next();
      total += addend;
      values.extend(FqGadget::<C>::witness_values(addend));
      values.extend(FqGadget::<C>::witness_values(total));
      Case { products, linear: vec![1, -1], constant, values }
    })
    .collect()
}

fn check_range_extraction<C: KzgCurve>() {
  for value in [
    CurveScalar::<C>::ZERO,
    CurveScalar::<C>::ONE,
    CurveScalar::<C>::NEG_ONE,
    CurveScalar::<C>::from_limbs_le([u64::MAX, u64::MAX, u64::MAX, 1]),
  ] {
    assert_eq!(integer(value), integer_reference(value));
    assert_eq!(range_limbs::<C, 1>(value), range_reference::<C, 1>(value));
    assert_eq!(range_limbs::<C, 4>(value), range_reference::<C, 4>(value));
    assert_eq!(range_limbs::<C, 5>(value), range_reference::<C, 5>(value));
    assert_eq!(range_limbs::<C, 6>(value), range_reference::<C, 6>(value));
  }
}

#[test]
fn range_extraction_and_integer_encoding_match_full_width_reference() {
  check_range_extraction::<Bn254>();
  check_range_extraction::<Bls12381>();
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

fn check_zero_and_quotient_limits<C: KzgCurve>() {
  let l = limb_count::<C>();
  let modulus_digits = digits::<C>(&modulus::<C>());
  assert_eq!(
    relation::<C>(&[], &[], &[], 0),
    relation_reference::<C>(&[], &[], &[], 0, &modulus_digits)
  );
  let mut values = vec![CurveScalar::<C>::ZERO; 2 * l];
  values[l - 1] = CurveScalar::<C>::NEG_ONE;
  for (value, limb) in values[l..].iter_mut().zip(&modulus_digits) {
    *value = scalar::<C>(limb);
  }
  for (coefficient, error) in
    [(1, "Fq quotient overflow"), (-1, "negative biased quotient")]
  {
    let expected = Err(error.into());
    assert_eq!(relation::<C>(&values, &[coefficient], &[], 0), expected);
    assert_eq!(
      relation_reference::<C>(&values, &[coefficient], &[], 0, &modulus_digits),
      expected
    );
  }
}

#[test]
fn zero_and_quotient_limit_errors_match_reference() {
  check_zero_and_quotient_limits::<Bn254>();
  check_zero_and_quotient_limits::<Bls12381>();
}

fn check_maximal_representatives<C: KzgCurve>() {
  let l = limb_count::<C>();
  let field_bits = C::Fq::MODULUS_BIT_SIZE as usize;
  let max = (BigUint::from(1u8) << field_bits) - 1u8;
  let total = 3u8 * &max * &max + 3u8 * &max + 4u8;
  let residue = &total % modulus::<C>();
  let quotient = &total / modulus::<C>();
  let mut values = Vec::new();
  for n in [&max, &max, &max, &residue] {
    values.extend(digits::<C>(n).into_iter().map(|limb| scalar::<C>(&limb)));
  }
  for sign in [-1i8, 1] {
    let advice =
      relation::<C>(&values, &[3 * sign], &[3 * sign, -sign], 4 * sign)
        .unwrap();
    let encoded_quotient = advice[..l]
      .iter()
      .rev()
      .fold(BigUint::from(0u8), |acc, &limb| (acc << W) + integer(limb));
    let expected = (BigInt::from(1u8) << quotient_bias_bits::<C>())
      + sign * BigInt::from(quotient.clone());
    assert_eq!(BigInt::from(encoded_quotient), expected);
    let top = integer(advice[l - 1]);
    assert!(top.bits() <= (quotient_bits::<C>() - W * (l - 1)) as u64);
    for &carry in &advice[l..] {
      assert!(integer(carry).bits() <= CARRY_BITS as u64);
    }
  }
}

#[test]
fn maximal_representatives_have_exact_signed_integer_quotients() {
  check_maximal_representatives::<Bn254>();
  check_maximal_representatives::<Bls12381>();
}

fn check_quotient_carries_and_rejections<C: KzgCurve>() {
  let l = limb_count::<C>();
  let modulus_digits = digits::<C>(&modulus::<C>());
  for mut case in cases::<C>(256) {
    let expected = relation_reference::<C>(
      &case.values,
      &case.products,
      &case.linear,
      case.constant,
      &modulus_digits,
    )
    .unwrap();
    assert_eq!(
      relation::<C>(&case.values, &case.products, &case.linear, case.constant),
      Ok(expected)
    );
    let last_input = case.values.len() - l;
    case.values[last_input] += CurveScalar::<C>::ONE;
    let expected = relation_reference::<C>(
      &case.values,
      &case.products,
      &case.linear,
      case.constant,
      &modulus_digits,
    );
    assert!(expected.is_err());
    assert_eq!(
      relation::<C>(&case.values, &case.products, &case.linear, case.constant),
      expected
    );
    case.values[0] = CurveScalar::<C>::NEG_ONE;
    assert_eq!(
      relation::<C>(&case.values, &case.products, &case.linear, case.constant),
      relation_reference::<C>(
        &case.values,
        &case.products,
        &case.linear,
        case.constant,
        &modulus_digits
      )
    );
  }
  let prime = FqGadget::<C>::witness_values(C::Fq::from(0u8));
  let redundant: Vec<_> =
    digits::<C>(&modulus::<C>()).into_iter().map(|v| scalar::<C>(&v)).collect();
  for representative in [prime, redundant] {
    let values: Vec<_> =
      representative.into_iter().cycle().take(3 * l).collect();
    assert_eq!(
      relation::<C>(&values, &[-3], &[3], 0),
      relation_reference::<C>(&values, &[-3], &[3], 0, &modulus_digits)
    );
  }
}

#[test]
fn quotient_carries_and_rejections_match_reference() {
  check_quotient_carries_and_rejections::<Bn254>();
  check_quotient_carries_and_rejections::<Bls12381>();
}
