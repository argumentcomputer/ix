//! Candidate advice for the Aiur BN254 (4 × 80-bit) and BLS12-381 (5 × 80-bit)
//! base-field libraries. The source program checks byte ranges, canonical
//! subtraction and every radix coefficient; these callbacks provide no trusted
//! arithmetic constraints.

use super::AiurCurve;
use crate::{
  kzg::{CurveScalar, Scalar},
  recursive::native_field::{integer, modulus},
};
use aiur::{
  FieldWord, bytecode::Type, field::FieldBackend, hints::HintChannels,
};
use ark_bn254::Fq;
use ark_ff::{BigInteger, Field, PrimeField};
use num_bigint::{BigInt, BigUint, Sign};

pub const LIMB_BITS: usize = 80;
pub const CARRY_BITS: usize = 84;

fn scalar_for<C: AiurCurve>(value: &BigUint) -> Result<CurveScalar<C>, String> {
  let words = value.to_u64_digits();
  if words.len() > 4 {
    return Err("Fq advice exceeds scalar representation".into());
  }
  let mut limbs = [0; 4];
  limbs[..words.len()].copy_from_slice(&words);
  let word = FieldWord::from_limbs_le(limbs);
  if !C::FIELD.contains(word) {
    return Err("Fq advice reaches scalar modulus".into());
  }
  Ok(C::FIELD.from_word(word))
}

fn digits_n(value: &BigUint, n: usize) -> Vec<BigUint> {
  let mask = (BigUint::from(1u8) << LIMB_BITS) - 1u8;
  (0..n).map(|i| (value >> (LIMB_BITS * i)) & &mask).collect()
}

/// Canonical `C::FQ_U80_LIMBS`-limb encoding (`4 × 80`-bit for BN254,
/// `5 × 80`-bit for BLS12-381); every limb retains all of its 80 bits.
pub fn encode_for<C: AiurCurve>(value: C::Fq) -> Vec<CurveScalar<C>> {
  digits_n(
    &BigUint::from_bytes_le(&value.into_bigint().to_bytes_le()),
    C::FQ_U80_LIMBS,
  )
  .into_iter()
  .map(|limb| scalar_for::<C>(&limb).expect("80-bit limb is below Fr"))
  .collect()
}

/// Canonical four-limb BN254 encoding; every limb retains all of its 80 bits.
pub fn encode(value: Fq) -> [Scalar; 4] {
  encode_for::<crate::kzg::Bn254>(value)
    .try_into()
    .expect("BN254 Fq has 4 limbs")
}

fn bounded_for<C: AiurCurve>(
  values: &[CurveScalar<C>],
) -> Result<Vec<BigUint>, String> {
  if values.len() != C::FQ_U80_LIMBS {
    return Err(format!("Fq advice needs {} limbs", C::FQ_U80_LIMBS));
  }
  let limbs: Vec<_> = values.iter().map(|&v| integer::<C>(v)).collect();
  if limbs.iter().any(|limb| limb.bits() > LIMB_BITS as u64) {
    return Err("Fq operand limb exceeds 80 bits".into());
  }
  Ok(limbs)
}

fn number_for<C: AiurCurve>(
  values: &[CurveScalar<C>],
) -> Result<BigUint, String> {
  let limbs = bounded_for::<C>(values)?;
  let value = limbs
    .iter()
    .rev()
    .fold(BigUint::from(0u8), |n, limb| (n << LIMB_BITS) + limb);
  if value >= modulus::<C>() {
    return Err("noncanonical Fq operand".into());
  }
  Ok(value)
}

/// Decode without reduction for `C`. Invalid limb widths and noncanonical
/// integers are rejected, including values that share the same residue modulo
/// `C::Fq`.
pub fn decode_for<C: AiurCurve>(
  values: &[CurveScalar<C>],
) -> Result<C::Fq, String> {
  Ok(C::Fq::from_le_bytes_mod_order(&number_for::<C>(values)?.to_bytes_le()))
}

/// Decode without reduction for BN254.
pub fn decode(values: &[Scalar]) -> Result<Fq, String> {
  decode_for::<crate::kzg::Bn254>(values)
}

fn canonical_for<C: AiurCurve>(
  values: &[CurveScalar<C>],
) -> Result<Vec<CurveScalar<C>>, String> {
  let limbs = bounded_for::<C>(values)?;
  let top = digits_n(&(modulus::<C>() - 1u8), C::FQ_U80_LIMBS);
  let radix = BigInt::from(1u8) << LIMB_BITS;
  let mut borrow = BigInt::from(0u8);
  let mut differences = vec![];
  let mut borrows = vec![];
  for (limb, limit) in limbs.into_iter().zip(top) {
    let mut difference = BigInt::from(limit) - BigInt::from(limb) - &borrow;
    borrow = BigInt::from(u8::from(difference.sign() == Sign::Minus));
    if difference.sign() == Sign::Minus {
      difference += &radix;
    }
    differences.push(scalar_for::<C>(
      &difference.to_biguint().ok_or("negative canonical limb")?,
    )?);
    borrows
      .push(scalar_for::<C>(&borrow.to_biguint().ok_or("negative borrow")?)?);
  }
  differences.extend(borrows);
  Ok(differences)
}

fn carries_for<C: AiurCurve>(
  coefficients: &[BigInt],
) -> Result<Vec<CurveScalar<C>>, String> {
  let radix = BigInt::from(1u8) << LIMB_BITS;
  let bias: BigInt = &radix * 8u8;
  let limit = BigUint::from(1u8) << CARRY_BITS;
  let mut carry = BigInt::from(0u8);
  let mut result = vec![];
  for (i, coefficient) in coefficients.iter().enumerate() {
    let sum = coefficient + &carry;
    if &sum % &radix != BigInt::from(0u8) {
      return Err("nonintegral Fq carry".into());
    }
    carry = sum / &radix;
    if i + 1 == coefficients.len() {
      if carry != BigInt::from(0u8) {
        return Err("nonzero final Fq carry".into());
      }
    } else {
      let value = (&carry + &bias).to_biguint().ok_or("Fq carry below bias")?;
      if value >= limit {
        return Err("Fq carry exceeds 84 bits".into());
      }
      result.push(scalar_for::<C>(&value)?);
    }
  }
  Ok(result)
}

fn arithmetic_for<C: AiurCurve>(
  kind: &str,
  values: &[CurveScalar<C>],
) -> Result<Vec<CurveScalar<C>>, String> {
  let n = C::FQ_U80_LIMBS;
  if values.len() != 2 * n {
    return Err("Fq arithmetic advice needs two operands".into());
  }
  let a = number_for::<C>(&values[..n])?;
  let b = number_for::<C>(&values[n..])?;
  let p = modulus::<C>();
  let (result, quotient) = match kind {
    "add" => {
      let sum = &a + &b;
      (&sum % &p, &sum / &p)
    },
    "sub" => {
      let borrow = BigUint::from(u8::from(a < b));
      (&a + &borrow * &p - &b, borrow)
    },
    "mul" => {
      let product = &a * &b;
      (&product % &p, &product / &p)
    },
    _ => return Err("unknown Fq arithmetic operation".into()),
  };
  let x: Vec<BigInt> = digits_n(&a, n).into_iter().map(BigInt::from).collect();
  let y: Vec<BigInt> = digits_n(&b, n).into_iter().map(BigInt::from).collect();
  let z = digits_n(&result, n);
  let p: Vec<BigInt> = digits_n(&p, n).into_iter().map(BigInt::from).collect();
  let mut output =
    z.iter().map(scalar_for::<C>).collect::<Result<Vec<_>, _>>()?;
  let coefficients = if kind == "mul" {
    let quotient = digits_n(&quotient, n);
    output.extend(
      quotient.iter().map(scalar_for::<C>).collect::<Result<Vec<_>, _>>()?,
    );
    let quotient: Vec<BigInt> =
      quotient.into_iter().map(BigInt::from).collect();
    let mut coefficients = vec![BigInt::from(0u8); 2 * n];
    for i in 0..n {
      for j in 0..n {
        coefficients[i + j] += &x[i] * &y[j] - &quotient[i] * &p[j];
      }
      coefficients[i] -= BigInt::from(z[i].clone());
    }
    coefficients
  } else {
    output.push(scalar_for::<C>(&quotient)?);
    let quotient = BigInt::from(quotient);
    (0..n)
      .map(|i| {
        (if kind == "add" {
          &x[i] + &y[i] - &quotient * &p[i]
        } else {
          &x[i] + &quotient * &p[i] - &y[i]
        }) - BigInt::from(z[i].clone())
      })
      .collect()
  };
  output.extend(carries_for::<C>(&coefficients)?);
  Ok(output)
}

/// Evaluate a named advice channel for curve `C` using canonical, full-width
/// scalar inputs. The result is a candidate and must be checked by the Aiur
/// source program.
pub fn advice_for<C: AiurCurve>(
  channel: &str,
  input: &[CurveScalar<C>],
) -> Result<Vec<CurveScalar<C>>, String> {
  let suffix = channel
    .strip_prefix(C::HINT_PREFIX)
    .and_then(|rest| rest.strip_prefix(".fq."))
    .ok_or_else(|| format!("unknown Fq advice channel {channel}"))?;
  let n = C::FQ_U80_LIMBS;
  match suffix {
    "bytes80" | "bytes84" | "u16_80" | "u16_84" => {
      let [value] = input else {
        return Err("Fq byte advice needs one value".into());
      };
      let bits = if suffix.ends_with("80") { LIMB_BITS } else { CARRY_BITS };
      let value = integer::<C>(*value);
      if value.bits() > bits as u64 {
        return Err("Fq byte advice value exceeds range".into());
      }
      let mut bytes = value.to_bytes_le();
      if suffix.starts_with("u16_") {
        bytes.resize(2 * bits.div_ceil(16), 0);
        return Ok(
          bytes
            .as_chunks::<2>()
            .0
            .iter()
            .map(|pair| {
              C::FIELD
                .from_u64(u64::from(u16::from_le_bytes([pair[0], pair[1]])))
            })
            .collect(),
        );
      }
      bytes.resize(bits.div_ceil(8), 0);
      Ok(
        bytes
          .into_iter()
          .map(|byte| C::FIELD.from_u64(u64::from(byte)))
          .collect(),
      )
    },
    "canonical" => canonical_for::<C>(input),
    "add" => arithmetic_for::<C>("add", input),
    "sub" => arithmetic_for::<C>("sub", input),
    "mul" => arithmetic_for::<C>("mul", input),
    "mul_pairs" => {
      let mut values = arithmetic_for::<C>("mul", input)?;
      let pair_carries: Vec<_> =
        (0..n - 1).map(|i| values[2 * n + 2 * i + 1]).collect();
      values.truncate(2 * n);
      values.extend(pair_carries);
      Ok(values)
    },
    "inverse" => {
      let inverse =
        decode_for::<C>(input)?.inverse().ok_or("Fq inverse of zero")?;
      Ok(encode_for::<C>(inverse))
    },
    _ => Err(format!("unknown Fq advice channel {channel}")),
  }
}

/// Evaluate a named BN254 advice channel.
pub fn advice(channel: &str, input: &[Scalar]) -> Result<Vec<Scalar>, String> {
  advice_for::<crate::kzg::Bn254>(channel, input)
}

fn fields(length: usize) -> Type {
  Type::Tuple { items: vec![Type::Field; length] }
}

pub fn register_for<C: AiurCurve>(
  channels: &mut HintChannels<CurveScalar<C>>,
) -> Result<(), String> {
  let n = C::FQ_U80_LIMBS;
  let pair = Type::Tuple { items: vec![fields(n); 2] };
  let p = C::HINT_PREFIX;
  for (suffix, input, output) in [
    ("bytes80", Type::Field, fields(10)),
    ("bytes84", Type::Field, fields(11)),
    ("u16_80", Type::Field, fields(5)),
    ("u16_84", Type::Field, fields(6)),
    ("canonical", fields(n), Type::Tuple { items: vec![fields(n); 2] }),
    (
      "add",
      pair.clone(),
      Type::Tuple { items: vec![fields(n), Type::Field, fields(n - 1)] },
    ),
    (
      "sub",
      pair.clone(),
      Type::Tuple { items: vec![fields(n), Type::Field, fields(n - 1)] },
    ),
    (
      "mul",
      pair.clone(),
      Type::Tuple { items: vec![fields(n), fields(n), fields(2 * n - 1)] },
    ),
    (
      "mul_pairs",
      pair,
      Type::Tuple { items: vec![fields(n), fields(n), fields(n - 1)] },
    ),
    ("inverse", fields(n), fields(n)),
  ] {
    let name = format!("{p}.fq.{suffix}");
    let channel_name = name.clone();
    channels.insert(&name, input, output, move |input, output| {
      let values = advice_for::<C>(&channel_name, input)?;
      if output.len() != values.len() {
        return Err("Fq advice output width mismatch".into());
      }
      output.copy_from_slice(&values);
      Ok(())
    })?;
  }
  Ok(())
}

pub fn register(channels: &mut HintChannels<Scalar>) -> Result<(), String> {
  register_for::<crate::kzg::Bn254>(channels)
}
