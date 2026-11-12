//! Candidate advice for the Aiur BN254 base-field library. The source program
//! checks byte ranges, canonical subtraction and every radix coefficient;
//! these callbacks provide no trusted arithmetic constraints.

use super::Bn254;
use crate::{
  kzg::Scalar,
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

fn scalar(value: &BigUint) -> Result<Scalar, String> {
  let words = value.to_u64_digits();
  if words.len() > 4 {
    return Err("Fq advice exceeds scalar representation".into());
  }
  let mut limbs = [0; 4];
  limbs[..words.len()].copy_from_slice(&words);
  let word = FieldWord::from_limbs_le(limbs);
  if !Bn254.contains(word) {
    return Err("Fq advice reaches scalar modulus".into());
  }
  Ok(Bn254.from_word(word))
}

fn digits(value: &BigUint) -> [BigUint; 4] {
  let mask = (BigUint::from(1u8) << LIMB_BITS) - 1u8;
  std::array::from_fn(|i| (value >> (LIMB_BITS * i)) & &mask)
}

/// Canonical four-limb encoding; every limb retains all of its 80 bits.
pub fn encode(value: Fq) -> [Scalar; 4] {
  digits(&BigUint::from_bytes_le(&value.into_bigint().to_bytes_le()))
    .map(|limb| scalar(&limb).expect("80-bit limb is below Fr"))
}

fn bounded(values: &[Scalar]) -> Result<[BigUint; 4], String> {
  if values.len() != 4 {
    return Err("Fq advice needs four limbs".into());
  }
  let limbs = std::array::from_fn(|i| integer(values[i]));
  if limbs.iter().any(|limb| limb.bits() > LIMB_BITS as u64) {
    return Err("Fq operand limb exceeds 80 bits".into());
  }
  Ok(limbs)
}

fn number(values: &[Scalar]) -> Result<BigUint, String> {
  let limbs = bounded(values)?;
  let value = limbs
    .iter()
    .rev()
    .fold(BigUint::from(0u8), |n, limb| (n << LIMB_BITS) + limb);
  if value >= modulus() {
    return Err("noncanonical Fq operand".into());
  }
  Ok(value)
}

/// Decode without reduction. Invalid limb widths and noncanonical integers
/// are rejected, including values that share the same residue modulo Fq.
pub fn decode(values: &[Scalar]) -> Result<Fq, String> {
  Ok(Fq::from_le_bytes_mod_order(&number(values)?.to_bytes_le()))
}

fn canonical(values: &[Scalar]) -> Result<Vec<Scalar>, String> {
  let limbs = bounded(values)?;
  let top = digits(&(modulus() - 1u8));
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
    differences.push(scalar(
      &difference.to_biguint().ok_or("negative canonical limb")?,
    )?);
    borrows.push(scalar(&borrow.to_biguint().ok_or("negative borrow")?)?);
  }
  differences.extend(borrows);
  Ok(differences)
}

fn carries(coefficients: &[BigInt]) -> Result<Vec<Scalar>, String> {
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
      result.push(scalar(&value)?);
    }
  }
  Ok(result)
}

fn arithmetic(kind: &str, values: &[Scalar]) -> Result<Vec<Scalar>, String> {
  if values.len() != 8 {
    return Err("Fq arithmetic advice needs two operands".into());
  }
  let a = number(&values[..4])?;
  let b = number(&values[4..])?;
  let p = modulus();
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
  let x = digits(&a).map(BigInt::from);
  let y = digits(&b).map(BigInt::from);
  let z = digits(&result);
  let p = digits(&p).map(BigInt::from);
  let mut output = z.iter().map(scalar).collect::<Result<Vec<_>, _>>()?;
  let coefficients = if kind == "mul" {
    let quotient = digits(&quotient);
    output.extend(quotient.iter().map(scalar).collect::<Result<Vec<_>, _>>()?);
    let quotient = quotient.map(BigInt::from);
    let mut coefficients = vec![BigInt::from(0u8); 8];
    for i in 0..4 {
      for j in 0..4 {
        coefficients[i + j] += &x[i] * &y[j] - &quotient[i] * &p[j];
      }
      coefficients[i] -= BigInt::from(z[i].clone());
    }
    coefficients
  } else {
    output.push(scalar(&quotient)?);
    let quotient = BigInt::from(quotient);
    (0..4)
      .map(|i| {
        (if kind == "add" {
          &x[i] + &y[i] - &quotient * &p[i]
        } else {
          &x[i] + &quotient * &p[i] - &y[i]
        }) - BigInt::from(z[i].clone())
      })
      .collect()
  };
  output.extend(carries(&coefficients)?);
  Ok(output)
}

/// Evaluate a named advice channel using canonical, full-width scalar inputs.
/// The result is a candidate and must be checked by the Aiur source program.
pub fn advice(channel: &str, input: &[Scalar]) -> Result<Vec<Scalar>, String> {
  match channel {
    "bn254.fq.bytes80" | "bn254.fq.bytes84" | "bn254.fq.u16_80"
    | "bn254.fq.u16_84" => {
      let [value] = input else {
        return Err("Fq byte advice needs one value".into());
      };
      let bits = if channel.ends_with("80") { LIMB_BITS } else { CARRY_BITS };
      let value = integer(*value);
      if value.bits() > bits as u64 {
        return Err("Fq byte advice value exceeds range".into());
      }
      let mut bytes = value.to_bytes_le();
      if channel.contains(".u16_") {
        bytes.resize(2 * bits.div_ceil(16), 0);
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
      bytes.resize(bits.div_ceil(8), 0);
      Ok(
        bytes.into_iter().map(|byte| Bn254.from_u64(u64::from(byte))).collect(),
      )
    },
    "bn254.fq.canonical" => canonical(input),
    "bn254.fq.add" => arithmetic("add", input),
    "bn254.fq.sub" => arithmetic("sub", input),
    "bn254.fq.mul" => arithmetic("mul", input),
    "bn254.fq.inverse" => {
      let inverse = decode(input)?.inverse().ok_or("Fq inverse of zero")?;
      Ok(encode(inverse).to_vec())
    },
    _ => Err(format!("unknown Fq advice channel {channel}")),
  }
}

fn fields(length: usize) -> Type {
  Type::Tuple { items: vec![Type::Field; length] }
}

pub fn register(channels: &mut HintChannels<Scalar>) -> Result<(), String> {
  let pair = Type::Tuple { items: vec![fields(4); 2] };
  for (name, input, output) in [
    ("bn254.fq.bytes80", Type::Field, fields(10)),
    ("bn254.fq.bytes84", Type::Field, fields(11)),
    ("bn254.fq.u16_80", Type::Field, fields(5)),
    ("bn254.fq.u16_84", Type::Field, fields(6)),
    (
      "bn254.fq.canonical",
      fields(4),
      Type::Tuple { items: vec![fields(4); 2] },
    ),
    (
      "bn254.fq.add",
      pair.clone(),
      Type::Tuple { items: vec![fields(4), Type::Field, fields(3)] },
    ),
    (
      "bn254.fq.sub",
      pair.clone(),
      Type::Tuple { items: vec![fields(4), Type::Field, fields(3)] },
    ),
    (
      "bn254.fq.mul",
      pair,
      Type::Tuple { items: vec![fields(4), fields(4), fields(7)] },
    ),
    ("bn254.fq.inverse", fields(4), fields(4)),
  ] {
    channels.insert(name, input, output, move |input, output| {
      let values = advice(name, input)?;
      if output.len() != values.len() {
        return Err("Fq advice output width mismatch".into());
      }
      output.copy_from_slice(&values);
      Ok(())
    })?;
  }
  Ok(())
}
