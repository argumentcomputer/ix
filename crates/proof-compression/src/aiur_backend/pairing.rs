//! Canonical tower transport and preparation of trusted fixed G2 operands.
//! Runtime pairing arithmetic belongs to the constrained Aiur source library.

pub mod final_program;

use super::{Bn254, fq};
use crate::kzg::Scalar;
use aiur::field::FieldBackend;
use ark_bn254::{Config, Fq2, Fq6, Fq12, G2Affine};
use ark_ec::{
  AffineRepr,
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
pub fn verifier_anchors(
  parameters: &crate::kzg::VerifierParams,
) -> ([ark_bn254::G1Affine; 2], [G2Affine; 2]) {
  (parameters.g1, [parameters.g2, parameters.tau_g2])
}

fn scalar_integer(value: &num_bigint::BigUint) -> Result<Scalar, String> {
  let words = value.to_u64_digits();
  if words.len() > 4 {
    return Err("pairing arithmetic advice exceeds scalar width".into());
  }
  let mut limbs = [0; 4];
  limbs[..words.len()].copy_from_slice(&words);
  let word = aiur::FieldWord::from_limbs_le(limbs);
  if !Bn254.contains(word) {
    return Err("pairing arithmetic advice exceeds Fr".into());
  }
  Ok(Bn254.from_word(word))
}

fn radix_limbs(value: &num_bigint::BigUint) -> [num_bigint::BigUint; 4] {
  let mask = (num_bigint::BigUint::from(1u8) << fq::LIMB_BITS) - 1u8;
  std::array::from_fn(|index| (value >> (fq::LIMB_BITS * index)) & &mask)
}

/// Candidate arithmetic advice; every quotient and biased carry is checked
/// by BN254FqProducts. No extension-field or pairing result is trusted.
pub fn advice(channel: &str, input: &[Scalar]) -> Result<Vec<Scalar>, String> {
  use crate::recursive::native_field::{integer, modulus};
  use ark_ff::{BigInteger, PrimeField};
  use num_bigint::{BigInt, BigUint};
  if channel == "bn254.pairing.bytes86" || channel == "bn254.pairing.u16_86" {
    let [value] = input else {
      return Err("86-bit advice requires one field".into());
    };
    let value = integer(*value);
    if value.bits() > 86 {
      return Err("pairing carry exceeds 86 bits".into());
    }
    let mut bytes = value.to_bytes_le();
    if channel == "bn254.pairing.u16_86" {
      bytes.resize(12, 0);
      return Ok(
        bytes
          .as_chunks::<2>()
          .0
          .iter()
          .map(|pair| {
            Bn254.from_u64(u64::from(u16::from_le_bytes([pair[0], pair[1]])))
          })
          .collect(),
      );
    }
    bytes.resize(11, 0);
    return Ok(
      bytes.into_iter().map(|byte| Bn254.from_u64(u64::from(byte))).collect(),
    );
  }
  let paired = channel == "bn254.pairing.fq_products_pairs";
  if (channel != "bn254.pairing.fq_products" && !paired) || input.len() != 17 {
    return Err("unknown pairing advice or invalid input width".into());
  }
  let mut operands = vec![];
  for values in input[..16].as_chunks::<4>().0 {
    operands.push(BigUint::from_bytes_le(
      &fq::decode(values)?.into_bigint().to_bytes_le(),
    ));
  }
  let subtract = match Bn254.try_to_u64(input[16])? {
    0 => false,
    1 => true,
    _ => return Err("nonboolean product sign".into()),
  };
  let p = modulus();
  let first = &operands[0] * &operands[1] + &p * &p;
  let second = &operands[2] * &operands[3];
  let numerator = if subtract { first - second } else { first + second };
  let remainder = &numerator % &p;
  let quotient = &numerator / &p;
  if quotient >= 3u8 * &p {
    return Err("two-product quotient exceeds honest bound".into());
  }
  let raw = radix_limbs(&remainder);
  let q = radix_limbs(&quotient);
  let mut output =
    raw.iter().chain(&q).map(scalar_integer).collect::<Result<Vec<_>, _>>()?;
  let operands: Vec<_> = operands.iter().map(radix_limbs).collect();
  let p = radix_limbs(&p);
  let sign = if subtract { BigInt::from(-1) } else { BigInt::from(1) };
  let mut coefficients = vec![BigInt::from(0); 8];
  for i in 0..4 {
    for j in 0..4 {
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
    if index == 7 {
      if carry != BigInt::from(0) {
        return Err("nonzero product carry endpoint".into());
      }
    } else {
      let encoded =
        (&carry + &bias).to_biguint().ok_or("negative biased product carry")?;
      if encoded >= limit {
        return Err("product carry exceeds 86 bits".into());
      }
      output.push(scalar_integer(&encoded)?);
    }
  }
  if paired {
    let retained = [output[9], output[11], output[13]];
    output.truncate(8);
    output.extend(retained);
  }
  Ok(output)
}

/// Register the two-product arithmetic channels in addition to `fq::register`.
pub fn register(
  channels: &mut aiur::hints::HintChannels<Scalar>,
) -> Result<(), String> {
  use aiur::bytecode::Type;
  let fields = |length| Type::Tuple { items: vec![Type::Field; length] };
  for (name, input, output) in [
    ("bn254.pairing.bytes86", Type::Field, fields(11)),
    ("bn254.pairing.u16_86", Type::Field, fields(6)),
    (
      "bn254.pairing.fq_products",
      Type::Tuple {
        items: vec![fields(4), fields(4), fields(4), fields(4), Type::Field],
      },
      Type::Tuple { items: vec![fields(4), fields(4), fields(7)] },
    ),
    (
      "bn254.pairing.fq_products_pairs",
      Type::Tuple {
        items: vec![fields(4), fields(4), fields(4), fields(4), Type::Field],
      },
      Type::Tuple { items: vec![fields(4), fields(4), fields(3)] },
    ),
  ] {
    channels.insert(name, input, output, move |input, output| {
      let values = advice(name, input)?;
      if values.len() != output.len() {
        return Err("pairing advice output width mismatch".into());
      }
      output.copy_from_slice(&values);
      Ok(())
    })?;
  }
  Ok(())
}
