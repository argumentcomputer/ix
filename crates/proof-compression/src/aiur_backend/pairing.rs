//! Canonical tower transport and preparation of trusted fixed G2 operands.
//! Runtime pairing arithmetic belongs to the constrained Aiur source library.

pub mod final_program;

use super::{AiurCurve, Bn254, fq};
use crate::kzg::{
  CurveScalar, KzgCurve, Scalar, VerifierParams,
  curve::{Bls12381, Bn254 as Bn254Curve, G1AffineOf, G2AffineOf},
};
use aiur::field::FieldBackend;
use ark_bn254::{Config, Fq2, Fq6, Fq12, G2Affine};
use ark_ec::{
  AffineRepr,
  bls12::{Bls12Config, G2Prepared as Bls12G2Prepared},
  bn::{BnConfig, G2Prepared},
};

pub fn encode_fp2(value: Fq2) -> [Scalar; 8] {
  let a = fq::encode(value.c0);
  let b = fq::encode(value.c1);
  std::array::from_fn(|i| if i < 4 { a[i] } else { b[i - 4] })
}

pub fn decode_fp2(value: &[Scalar]) -> Result<Fq2, String> {
  if value.len() != 8 {
    return Err("Fp2 needs eight scalar limbs".into());
  }
  Ok(Fq2::new(fq::decode(&value[..4])?, fq::decode(&value[4..])?))
}

pub fn encode_fp6(value: Fq6) -> [Scalar; 24] {
  let values =
    [encode_fp2(value.c0), encode_fp2(value.c1), encode_fp2(value.c2)];
  std::array::from_fn(|i| values[i / 8][i % 8])
}

pub fn decode_fp6(value: &[Scalar]) -> Result<Fq6, String> {
  if value.len() != 24 {
    return Err("Fp6 needs 24 scalar limbs".into());
  }
  Ok(Fq6::new(
    decode_fp2(&value[..8])?,
    decode_fp2(&value[8..16])?,
    decode_fp2(&value[16..])?,
  ))
}

pub fn encode_fp12(value: Fq12) -> [Scalar; 48] {
  let values = [encode_fp6(value.c0), encode_fp6(value.c1)];
  std::array::from_fn(|i| values[i / 24][i % 24])
}

pub fn decode_fp12(value: &[Scalar]) -> Result<Fq12, String> {
  if value.len() != 48 {
    return Err("Fp12 needs 48 scalar limbs".into());
  }
  Ok(Fq12::new(decode_fp6(&value[..24])?, decode_fp6(&value[24..])?))
}

/// Each row is `[square, active0, active1, line0(24 limbs), line1(24 limbs)]`.
/// These rows are compiler constants, never prover-supplied advice. Callers
/// authenticate both anchors independently before constructing a circuit key.
pub fn fixed_lines(
  anchors: [G2Affine; 2],
) -> Result<Vec<[Scalar; 51]>, String> {
  for point in &anchors {
    if point.is_zero()
      || !point.is_on_curve()
      || !point.is_in_correct_subgroup_assuming_on_curve()
    {
      return Err(
        "fixed pairing anchor must be a nonzero BN254 G2 subgroup point".into(),
      );
    }
  }
  let prepared = anchors.map(G2Prepared::<Config>::from);
  let mut squares = vec![];
  for (index, bit) in Config::ATE_LOOP_COUNT.iter().rev().skip(1).enumerate() {
    squares.push(index != 0);
    if *bit == 1 || *bit == -1 {
      squares.push(false);
    }
  }
  squares.extend([false, false]);
  for point in &prepared {
    if !point.infinity && point.ell_coeffs.len() != squares.len() {
      return Err("prepared G2 line schedule differs".into());
    }
  }
  Ok(
    squares
      .into_iter()
      .enumerate()
      .map(|(index, square)| {
        let mut row = [Bn254.zero(); 51];
        row[0] = Bn254.from_u64(u64::from(square));
        for (operand, point) in prepared.iter().enumerate() {
          row[1 + operand] = Bn254.from_u64(u64::from(!point.infinity));
          if !point.infinity {
            let line = &point.ell_coeffs[index];
            for (component, value) in
              [line.0, line.1, line.2].into_iter().enumerate()
            {
              let start = 3 + operand * 24 + component * 8;
              row[start..start + 8].copy_from_slice(&encode_fp2(value));
            }
          }
        }
        row
      })
      .collect(),
  )
}

/// Evaluate the prepared constant table natively for fixture validation.
/// This is not registered as an execution hint and supplies no proof witness.
pub fn evaluate_fixed_lines(
  rows: &[[Scalar; 51]],
  points: [ark_bn254::G1Affine; 2],
) -> Result<Fq12, String> {
  use ark_ff::{Field, One};
  let mut accumulator = Fq12::one();
  for row in rows {
    match Bn254.try_to_u64(row[0])? {
      0 => {},
      1 => {
        accumulator.square_in_place();
      },
      _ => return Err("nonboolean Miller square flag".into()),
    }
    for (operand, point) in points.iter().enumerate() {
      match Bn254.try_to_u64(row[1 + operand])? {
        0 => continue,
        1 => {},
        _ => return Err("nonboolean G2 activation flag".into()),
      }
      if point.is_zero() {
        continue;
      }
      let start = 3 + operand * 24;
      let mut c0 = decode_fp2(&row[start..start + 8])?;
      let mut c1 = decode_fp2(&row[start + 8..start + 16])?;
      let c2 = decode_fp2(&row[start + 16..start + 24])?;
      c0.mul_assign_by_fp(&point.y);
      c1.mul_assign_by_fp(&point.x);
      accumulator.mul_by_034(&c0, &c1, &c2);
    }
  }
  Ok(accumulator)
}

/// Copy the anchors from independently authenticated KZG verifier parameters.
pub fn verifier_anchors_for<C: KzgCurve>(
  parameters: &VerifierParams<C>,
) -> ([G1AffineOf<C>; 2], [G2AffineOf<C>; 2]) {
  (parameters.g1, [parameters.g2, parameters.tau_g2])
}

/// Copy the anchors from independently authenticated BN254 KZG verifier parameters.
pub fn verifier_anchors(
  parameters: &VerifierParams,
) -> ([ark_bn254::G1Affine; 2], [G2Affine; 2]) {
  verifier_anchors_for::<Bn254Curve>(parameters)
}

pub fn encode_fp2_bls(
  value: ark_bls12_381::Fq2,
) -> [CurveScalar<Bls12381>; 10] {
  let a = fq::encode_for::<Bls12381>(value.c0);
  let b = fq::encode_for::<Bls12381>(value.c1);
  std::array::from_fn(|i| if i < 5 { a[i] } else { b[i - 5] })
}

pub fn decode_fp2_bls(
  value: &[CurveScalar<Bls12381>],
) -> Result<ark_bls12_381::Fq2, String> {
  if value.len() != 10 {
    return Err("BLS12-381 Fp2 needs ten scalar limbs".into());
  }
  Ok(ark_bls12_381::Fq2::new(
    fq::decode_for::<Bls12381>(&value[..5])?,
    fq::decode_for::<Bls12381>(&value[5..])?,
  ))
}

pub fn encode_fp6_bls(
  value: ark_bls12_381::Fq6,
) -> [CurveScalar<Bls12381>; 30] {
  let values = [
    encode_fp2_bls(value.c0),
    encode_fp2_bls(value.c1),
    encode_fp2_bls(value.c2),
  ];
  std::array::from_fn(|i| values[i / 10][i % 10])
}

pub fn decode_fp6_bls(
  value: &[CurveScalar<Bls12381>],
) -> Result<ark_bls12_381::Fq6, String> {
  if value.len() != 30 {
    return Err("BLS12-381 Fp6 needs 30 scalar limbs".into());
  }
  Ok(ark_bls12_381::Fq6::new(
    decode_fp2_bls(&value[..10])?,
    decode_fp2_bls(&value[10..20])?,
    decode_fp2_bls(&value[20..])?,
  ))
}

pub fn encode_fp12_bls(
  value: ark_bls12_381::Fq12,
) -> [CurveScalar<Bls12381>; 60] {
  let values = [encode_fp6_bls(value.c0), encode_fp6_bls(value.c1)];
  std::array::from_fn(|i| values[i / 30][i % 30])
}

pub fn decode_fp12_bls(
  value: &[CurveScalar<Bls12381>],
) -> Result<ark_bls12_381::Fq12, String> {
  if value.len() != 60 {
    return Err("BLS12-381 Fp12 needs 60 scalar limbs".into());
  }
  Ok(ark_bls12_381::Fq12::new(
    decode_fp6_bls(&value[..30])?,
    decode_fp6_bls(&value[30..])?,
  ))
}

/// Prepared BLS12-381 G2 Miller-loop lines for two trusted anchors:
/// `[square, active0, active1, line0(30 limbs), line1(30 limbs)]`.
pub fn fixed_lines_bls12_381(
  anchors: [ark_bls12_381::G2Affine; 2],
) -> Result<Vec<[CurveScalar<Bls12381>; 63]>, String> {
  use ark_ff::BitIteratorBE;
  for point in &anchors {
    if point.is_zero()
      || !point.is_on_curve()
      || !point.is_in_correct_subgroup_assuming_on_curve()
    {
      return Err(
        "fixed pairing anchor must be a nonzero BLS12-381 G2 subgroup point"
          .into(),
      );
    }
  }
  let prepared = anchors.map(Bls12G2Prepared::<ark_bls12_381::Config>::from);
  let mut squares = vec![];
  for (index, bit) in
    BitIteratorBE::without_leading_zeros(ark_bls12_381::Config::X)
      .skip(1)
      .enumerate()
  {
    squares.push(index != 0);
    if bit {
      squares.push(false);
    }
  }
  for point in &prepared {
    if !point.infinity && point.ell_coeffs.len() != squares.len() {
      return Err("prepared BLS12-381 G2 line schedule differs".into());
    }
  }
  Ok(
    squares
      .into_iter()
      .enumerate()
      .map(|(index, square)| {
        let mut row = [Bls12381::FIELD.zero(); 63];
        row[0] = Bls12381::FIELD.from_u64(u64::from(square));
        for (operand, point) in prepared.iter().enumerate() {
          row[1 + operand] =
            Bls12381::FIELD.from_u64(u64::from(!point.infinity));
          if !point.infinity {
            let line = &point.ell_coeffs[index];
            for (component, value) in
              [line.0, line.1, line.2].into_iter().enumerate()
            {
              let start = 3 + operand * 30 + component * 10;
              row[start..start + 10].copy_from_slice(&encode_fp2_bls(value));
            }
          }
        }
        row
      })
      .collect(),
  )
}

/// Evaluate prepared BLS12-381 Miller lines natively for fixture validation.
pub fn evaluate_fixed_lines_bls12_381(
  rows: &[[CurveScalar<Bls12381>; 63]],
  points: [ark_bls12_381::G1Affine; 2],
) -> Result<ark_bls12_381::Fq12, String> {
  use ark_ff::{CyclotomicMultSubgroup, Field, One};
  let mut accumulator = ark_bls12_381::Fq12::one();
  for row in rows {
    match Bls12381::FIELD.try_to_u64(row[0])? {
      0 => {},
      1 => {
        accumulator.square_in_place();
      },
      _ => return Err("nonboolean Miller square flag".into()),
    }
    for (operand, point) in points.iter().enumerate() {
      match Bls12381::FIELD.try_to_u64(row[1 + operand])? {
        0 => continue,
        1 => {},
        _ => return Err("nonboolean G2 activation flag".into()),
      }
      if point.is_zero() {
        continue;
      }
      let start = 3 + operand * 30;
      let c0 = decode_fp2_bls(&row[start..start + 10])?;
      let mut c1 = decode_fp2_bls(&row[start + 10..start + 20])?;
      let mut c2 = decode_fp2_bls(&row[start + 20..start + 30])?;
      // BLS12-381 uses TwistType::M: c2 * y, c1 * x, mul_by_014(c0, c1, c2).
      c2.mul_assign_by_fp(&point.y);
      c1.mul_assign_by_fp(&point.x);
      accumulator.mul_by_014(&c0, &c1, &c2);
    }
  }
  if ark_bls12_381::Config::X_IS_NEGATIVE {
    accumulator.cyclotomic_inverse_in_place();
  }
  Ok(accumulator)
}

fn scalar_integer_for<C: AiurCurve>(
  value: &num_bigint::BigUint,
) -> Result<CurveScalar<C>, String> {
  let words = value.to_u64_digits();
  if words.len() > 4 {
    return Err("pairing arithmetic advice exceeds scalar width".into());
  }
  let mut limbs = [0; 4];
  limbs[..words.len()].copy_from_slice(&words);
  let word = aiur::FieldWord::from_limbs_le(limbs);
  if !C::FIELD.contains(word) {
    return Err("pairing arithmetic advice exceeds Fr".into());
  }
  Ok(C::FIELD.from_word(word))
}

fn radix_limbs_n(
  value: &num_bigint::BigUint,
  n: usize,
) -> Vec<num_bigint::BigUint> {
  let mask = (num_bigint::BigUint::from(1u8) << fq::LIMB_BITS) - 1u8;
  (0..n).map(|index| (value >> (fq::LIMB_BITS * index)) & &mask).collect()
}

fn pairing_channel_prefix<C: AiurCurve>() -> &'static str {
  if C::FQ_U80_LIMBS == 4 { "bn254.pairing" } else { "bls12_381.pairing" }
}

/// Candidate arithmetic advice for curve `C`; every quotient and biased carry
/// is checked by the constrained Fq product library.
pub fn advice_for<C: AiurCurve>(
  channel: &str,
  input: &[CurveScalar<C>],
) -> Result<Vec<CurveScalar<C>>, String> {
  use crate::recursive::native_field::{integer, modulus};
  use ark_ff::{BigInteger, PrimeField};
  use num_bigint::{BigInt, BigUint};
  let prefix = pairing_channel_prefix::<C>();
  let bytes86 = format!("{prefix}.bytes86");
  let u16_86 = format!("{prefix}.u16_86");
  if channel == bytes86 || channel == u16_86 {
    let [value] = input else {
      return Err("86-bit advice requires one field".into());
    };
    let value = integer::<C>(*value);
    if value.bits() > 86 {
      return Err("pairing carry exceeds 86 bits".into());
    }
    let mut bytes = value.to_bytes_le();
    if channel == u16_86 {
      bytes.resize(12, 0);
      return Ok(
        bytes
          .as_chunks::<2>()
          .0
          .iter()
          .map(|pair| {
            C::FIELD.from_u64(u64::from(u16::from_le_bytes([pair[0], pair[1]])))
          })
          .collect(),
      );
    }
    bytes.resize(11, 0);
    return Ok(
      bytes
        .into_iter()
        .map(|byte| C::FIELD.from_u64(u64::from(byte)))
        .collect(),
    );
  }
  let n = C::FQ_U80_LIMBS;
  let full_name = format!("{prefix}.fq_products");
  let pairs_name = format!("{prefix}.fq_products_pairs");
  let paired = channel == pairs_name;
  if (channel != full_name && !paired) || input.len() != 4 * n + 1 {
    return Err("unknown pairing advice or invalid input width".into());
  }
  let mut operands = Vec::with_capacity(4);
  for values in input[..4 * n].chunks_exact(n) {
    operands.push(BigUint::from_bytes_le(
      &fq::decode_for::<C>(values)?.into_bigint().to_bytes_le(),
    ));
  }
  let subtract = match C::FIELD.try_to_u64(input[4 * n])? {
    0 => false,
    1 => true,
    _ => return Err("nonboolean product sign".into()),
  };
  let p = modulus::<C>();
  let first = &operands[0] * &operands[1] + &p * &p;
  let second = &operands[2] * &operands[3];
  let numerator = if subtract { first - second } else { first + second };
  let remainder = &numerator % &p;
  let quotient = &numerator / &p;
  if quotient >= 3u8 * &p {
    return Err("two-product quotient exceeds honest bound".into());
  }
  let raw = radix_limbs_n(&remainder, n);
  let q = radix_limbs_n(&quotient, n);
  let mut output = raw
    .iter()
    .chain(&q)
    .map(scalar_integer_for::<C>)
    .collect::<Result<Vec<_>, _>>()?;
  let operands: Vec<_> =
    operands.iter().map(|op| radix_limbs_n(op, n)).collect();
  let p = radix_limbs_n(&p, n);
  let sign = if subtract { BigInt::from(-1) } else { BigInt::from(1) };
  let coeff_count = 2 * n;
  let mut coefficients = vec![BigInt::from(0); coeff_count];
  for i in 0..n {
    for j in 0..n {
      coefficients[i + j] += BigInt::from(&operands[0][i] * &operands[1][j])
        + &sign * BigInt::from(&operands[2][i] * &operands[3][j])
        + BigInt::from(&p[i] * &p[j])
        - BigInt::from(&q[i] * &p[j]);
    }
    coefficients[i] -= BigInt::from(raw[i].clone());
  }
  let radix = BigInt::from(1u8) << fq::LIMB_BITS;
  let bias = 32u8 * &radix;
  let limit = BigUint::from(1u8) << 86;
  let mut carry = BigInt::from(0);
  for (index, coefficient) in coefficients.into_iter().enumerate() {
    let sum = coefficient + carry;
    if &sum % &radix != BigInt::from(0) {
      return Err("nonintegral product carry".into());
    }
    carry = sum / &radix;
    if index + 1 == coeff_count {
      if carry != BigInt::from(0) {
        return Err("nonzero product carry endpoint".into());
      }
    } else {
      let encoded =
        (&carry + &bias).to_biguint().ok_or("negative biased product carry")?;
      if encoded >= limit {
        return Err("product carry exceeds 86 bits".into());
      }
      output.push(scalar_integer_for::<C>(&encoded)?);
    }
  }
  if paired {
    let retained: Vec<_> =
      (0..n - 1).map(|k| output[2 * n + 1 + 2 * k]).collect();
    output.truncate(2 * n);
    output.extend(retained);
  }
  Ok(output)
}

/// Candidate arithmetic advice; every quotient and biased carry is checked
/// by BN254FqProducts. No extension-field or pairing result is trusted.
pub fn advice(channel: &str, input: &[Scalar]) -> Result<Vec<Scalar>, String> {
  advice_for::<Bn254Curve>(channel, input)
}

/// Register the two-product arithmetic channels for curve `C` in addition to
/// `fq::register_for::<C>`.
pub fn register_for<C: AiurCurve>(
  channels: &mut aiur::hints::HintChannels<CurveScalar<C>>,
) -> Result<(), String> {
  use aiur::bytecode::Type;
  let n = C::FQ_U80_LIMBS;
  let prefix = pairing_channel_prefix::<C>();
  let fields = |length| Type::Tuple { items: vec![Type::Field; length] };
  let defs: [(String, Type, Type); 4] = [
    (format!("{prefix}.bytes86"), Type::Field, fields(11)),
    (format!("{prefix}.u16_86"), Type::Field, fields(6)),
    (
      format!("{prefix}.fq_products"),
      Type::Tuple {
        items: vec![fields(n), fields(n), fields(n), fields(n), Type::Field],
      },
      Type::Tuple { items: vec![fields(n), fields(n), fields(2 * n - 1)] },
    ),
    (
      format!("{prefix}.fq_products_pairs"),
      Type::Tuple {
        items: vec![fields(n), fields(n), fields(n), fields(n), Type::Field],
      },
      Type::Tuple { items: vec![fields(n), fields(n), fields(n - 1)] },
    ),
  ];
  for (name, input, output) in defs {
    let channel_name = name.clone();
    channels.insert(&name, input, output, move |input, output| {
      let values = advice_for::<C>(&channel_name, input)?;
      if values.len() != output.len() {
        return Err("pairing advice output width mismatch".into());
      }
      output.copy_from_slice(&values);
      Ok(())
    })?;
  }
  Ok(())
}

/// Register the two-product arithmetic channels in addition to `fq::register`.
pub fn register(
  channels: &mut aiur::hints::HintChannels<Scalar>,
) -> Result<(), String> {
  register_for::<Bn254Curve>(channels)
}
