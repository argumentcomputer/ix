use super::*;
use crate::recursive::native_field::{Builder, FqGadget};
use ark_bls12_381::Fq;
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

pub(in crate::recursive::native_field) fn range_reference<const N: usize>(
  value: Scalar,
) -> [Scalar; N] {
  let n = integer_reference(value);
  std::array::from_fn(|i| scalar(&((&n >> (16 * i)) & BigUint::from(65535u32))))
}

pub(in crate::recursive::native_field) fn relation_reference(
  values: &[Scalar],
  pc: &[i8],
  lc: &[i8],
  constant: i8,
  p_hint: &[BigUint; L],
) -> Result<[Scalar; 9], String> {
  let mut t = vec![BigInt::from(0u8); 10];
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
  let q: BigInt = total / prime + (BigInt::from(1u8) << 383usize);
  let q = q.to_biguint().ok_or("negative biased quotient")?;
  if q.bits() > 384 {
    return Err("Fq quotient overflow".into());
  }
  let q = digits(&q);
  let bias = digits(&(BigUint::from(1u8) << 383));
  for i in 0..L {
    for j in 0..L {
      t[i + j] -= BigInt::from(p_hint[i].clone())
        * (BigInt::from(q[j].clone()) - BigInt::from(bias[j].clone()));
    }
  }
  let mut out = [Scalar::ZERO; 9];
  for i in 0..L {
    out[i] = scalar(&q[i]);
  }
  let radix = BigInt::from(1u8) << W;
  let block_radix = &radix * &radix;
  let mut carry = BigInt::from(0u8);
  for j in 0..5 {
    carry += &t[2 * j] + &radix * &t[2 * j + 1];
    if &carry % &block_radix != BigInt::from(0u8) {
      return Err("nonintegral Fq carry".into());
    }
    carry /= &block_radix;
    if j < 4 {
      let biased: BigInt = &carry + (BigInt::from(1u8) << 88usize);
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
  let modulus_digits = constants().modulus_digits.clone();
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
fn quotient_carries_and_rejections_match_reference() {
  let modulus_digits = constants().modulus_digits.clone();
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

fn fixture(
  reference: bool,
) -> (
  multi_stark::plonkish::Circuit<Scalar>,
  multi_stark::plonkish::Assignment<Scalar>,
) {
  let mut builder = Builder::new();
  let mut field = FqGadget::new(&mut builder);
  field.reference_advice = reference;
  let x = field.input(&mut builder, "x");
  let y = field.input(&mut builder, "y");
  let product = field.mul(&mut builder, x, y);
  let expected = field.constant(&mut builder, Fq::from(0u8));
  field.equal(&mut builder, product, expected);
  for value in product.0 {
    builder.expose_public(value);
  }
  let circuit = builder.finish();
  let mut witness = circuit.witness();
  for (value, assigned) in x
    .0
    .into_iter()
    .zip(FqGadget::witness_values(-Fq::from(1u8)))
    .chain(y.0.into_iter().zip(FqGadget::witness_values(Fq::from(0u8))))
  {
    witness.set(value, assigned).unwrap();
  }
  let assignment = witness.generate().unwrap();
  (circuit, assignment)
}

#[test]
fn advice_preserves_complete_frontend_assignment_and_constraints() {
  let (reference, old) = fixture(true);
  let (optimized, new) = fixture(false);
  assert_eq!(reference.stats(), optimized.stats());
  assert_eq!(old.public_values(), new.public_values());
  for (left, right) in reference.gates().iter().zip(optimized.gates()) {
    assert_eq!(left.wires.map(|v| v.index()), right.wires.map(|v| v.index()));
    assert_eq!(left.coefficients, right.coefficients);
    assert_eq!(
      left.wires.map(|v| old.value(v).unwrap()),
      right.wires.map(|v| new.value(v).unwrap())
    );
  }
  for (left, right) in reference.lookups().iter().zip(optimized.lookups()) {
    assert_eq!(left.table.index(), right.table.index());
    assert_eq!(
      left.values.iter().map(|&v| old.value(v).unwrap()).collect::<Vec<_>>(),
      right.values.iter().map(|&v| new.value(v).unwrap()).collect::<Vec<_>>()
    );
  }
}

#[test]
#[ignore = "two CPU KZG proofs of a native Fq primitive with its full range table"]
fn recursive_advice_kzg_byte_parity() {
  use crate::{
    foreign::KzgCircuitExt,
    kzg::{KzgConfig, Srs, compact::FixedProofCodec},
  };
  use multi_stark::system::{System, SystemWitness};
  use std::sync::Arc;
  let config = KzgConfig::new(
    Arc::new(Srs::unsafe_dev_setup(1 << 16, b"recursive-advice-parity")),
    4,
  );
  let mut bytes = Vec::new();
  for reference in [true, false] {
    let (circuit, assignment) = fixture(reference);
    let compiled = circuit.lower_to_multi_stark(Scalar::from_u8(79)).unwrap();
    let traces = compiled.traces(&assignment).unwrap();
    let claims = compiled.claims(assignment.public_values()).unwrap();
    let (system, key) = System::new(
      config.clone(),
      compiled.kzg_circuit_inputs(1 << 16, 4).unwrap(),
    );
    let refs = claims.iter().map(Vec::as_slice).collect::<Vec<_>>();
    let proof = system.prove_multiple_claims(
      &key,
      &refs,
      SystemWitness::from_stage_1(traces, &system),
    );
    system.verify_multiple_claims(&refs, &proof).unwrap();
    bytes.push(
      FixedProofCodec::new(&system, &proof.log_degrees)
        .unwrap()
        .encode(&proof)
        .unwrap(),
    );
  }
  assert_eq!(bytes[0], bytes[1]);
  println!(
    "RECURSIVE_ADVICE_PROOF bytes={} blake3={}",
    bytes[0].len(),
    blake3::hash(&bytes[0])
  );
}

#[test]
#[ignore = "isolated recursive-field advice comparison"]
fn recursive_advice_benchmark() {
  use std::{hint::black_box, time::Instant};
  let cases = cases(1 << 12);
  let modulus_digits = constants().modulus_digits.clone();
  for case in &cases {
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
  for iteration in 0..5 {
    let mut seconds = [0.0; 2];
    let mut outputs = [Vec::new(), Vec::new()];
    for optimized in
      if iteration % 2 == 0 { [false, true] } else { [true, false] }
    {
      let started = Instant::now();
      outputs[usize::from(optimized)] = cases
        .iter()
        .map(|case| {
          let case = black_box(case);
          if optimized {
            relation(&case.values, &case.products, &case.linear, case.constant)
              .unwrap()
          } else {
            relation_reference(
              &case.values,
              &case.products,
              &case.linear,
              case.constant,
              &modulus_digits,
            )
            .unwrap()
          }
        })
        .collect::<Vec<_>>();
      seconds[usize::from(optimized)] = started.elapsed().as_secs_f64();
    }
    assert_eq!(outputs[0], outputs[1]);
    println!(
      "RECURSIVE_ADVICE_BENCH iteration={iteration} relations={} reference_seconds={:.9} optimized_seconds={:.9}",
      cases.len(),
      seconds[0],
      seconds[1]
    );
  }
}
