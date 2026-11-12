//! Untrusted quotient and carry candidates for bounded signed Fq relations.
//! Aiur constructs the coefficients, checks their expression weights, and
//! constrains every advice limb with range lookups and four integer equations.

use crate::{
  kzg::Scalar,
  recursive::native_field::{integer, modulus, scalar},
};
use aiur::{bytecode::Type, hints::HintChannels};
use ark_ff::{BigInteger, PrimeField};
use num_bigint::{BigInt, BigUint};
use std::sync::OnceLock;

pub const LIMB_BITS: usize = 80;
pub const QUOTIENT_BITS: usize = 257;
pub const CARRY_BITS: usize = 89;
pub const ADVICE_LEN: usize = 7;

struct Constants {
  scalar_modulus: BigInt,
  scalar_midpoint: BigUint,
  coefficient_bound: BigInt,
  modulus: BigInt,
  modulus_digits: [BigInt; 4],
  quotient_bias: BigInt,
  carry_bias: BigInt,
  pair_radix: BigInt,
}

fn digits(value: &BigUint) -> [BigUint; 4] {
  let mask = (BigUint::from(1u8) << LIMB_BITS) - 1u8;
  std::array::from_fn(|i| (value >> (LIMB_BITS * i)) & &mask)
}

fn constants() -> &'static Constants {
  static CONSTANTS: OnceLock<Constants> = OnceLock::new();
  CONSTANTS.get_or_init(|| {
    let radix = BigUint::from(1u8) << LIMB_BITS;
    let scalar_modulus =
      BigUint::from_bytes_le(&ark_bn254::Fr::MODULUS.to_bytes_le());
    let prime = modulus();
    Constants {
      scalar_midpoint: &scalar_modulus / 2u8,
      scalar_modulus: scalar_modulus.into(),
      coefficient_bound: (12u8 * &radix * &radix + 3u8 * &radix + 4u8).into(),
      modulus_digits: digits(&prime).map(BigInt::from),
      modulus: prime.into(),
      quotient_bias: BigInt::from(1u8) << (QUOTIENT_BITS - 1),
      carry_bias: BigInt::from(1u8) << (CARRY_BITS - 1),
      pair_radix: BigInt::from(1u8) << (2 * LIMB_BITS),
    }
  })
}

fn relation(input: &[Scalar]) -> Result<Vec<Scalar>, String> {
  if input.len() != 8 {
    return Err("Fq relation requires eight coefficients".into());
  }
  let constants = constants();
  let mut terms = input
    .iter()
    .map(|&value| {
      let value = integer(value);
      // The expression-weight bound is below half Fr, making this signed
      // representative unique for every coefficient produced by Aiur.
      let centered = if value > constants.scalar_midpoint {
        BigInt::from(value) - &constants.scalar_modulus
      } else {
        BigInt::from(value)
      };
      if centered <= -&constants.coefficient_bound
        || centered >= constants.coefficient_bound
      {
        return Err("Fq relation coefficient exceeds expression bound".into());
      }
      Ok(centered)
    })
    .collect::<Result<Vec<_>, String>>()?;
  let total = terms
    .iter()
    .rev()
    .fold(BigInt::from(0u8), |value, c| (value << LIMB_BITS) + c);
  if &total % &constants.modulus != BigInt::from(0u8) {
    return Err("nonzero Fq relation".into());
  }
  let quotient = total / &constants.modulus + &constants.quotient_bias;
  let quotient = quotient.to_biguint().ok_or("negative biased quotient")?;
  if quotient.bits() > QUOTIENT_BITS as u64 {
    return Err("Fq relation quotient exceeds 257 bits".into());
  }
  let quotient = digits(&quotient);
  let mut output = quotient.iter().map(scalar).collect::<Vec<_>>();
  let mut unbiased = quotient.map(BigInt::from);
  unbiased[3] -= BigInt::from(1u8) << (QUOTIENT_BITS - 1 - 3 * LIMB_BITS);
  for i in 0..4 {
    for j in 0..4 {
      terms[i + j] -= &unbiased[i] * &constants.modulus_digits[j];
    }
  }
  let mut carry = BigInt::from(0u8);
  for pair in 0..4 {
    carry += &terms[2 * pair] + (&terms[2 * pair + 1] << LIMB_BITS);
    if &carry % &constants.pair_radix != BigInt::from(0u8) {
      return Err("nonintegral Fq relation carry".into());
    }
    carry /= &constants.pair_radix;
    if pair < 3 {
      let biased = (&carry + &constants.carry_bias)
        .to_biguint()
        .ok_or("negative biased carry")?;
      if biased.bits() > CARRY_BITS as u64 {
        return Err("Fq relation carry exceeds 89 bits".into());
      }
      output.push(scalar(&biased));
    }
  }
  if carry != BigInt::from(0u8) {
    return Err("nonzero final Fq relation carry".into());
  }
  Ok(output)
}

/// Candidate advice only; acceptance requires the compiled Aiur constraints.
pub fn advice(channel: &str, input: &[Scalar]) -> Result<Vec<Scalar>, String> {
  match channel {
    "bn254.fq_relation.zero" => relation(input),
    "bn254.fq_relation.u16_17" | "bn254.fq_relation.u16_89" => {
      let [value] = input else {
        return Err("Fq relation range advice requires one value".into());
      };
      let bits = if channel.ends_with("17") { 17 } else { CARRY_BITS };
      let value = integer(*value);
      if value.bits() > bits as u64 {
        return Err("Fq relation range advice exceeds width".into());
      }
      let mask = BigUint::from(65535u32);
      Ok(
        (0..bits.div_ceil(16))
          .map(|i| scalar(&((&value >> (16 * i)) & &mask)))
          .collect(),
      )
    },
    _ => Err(format!("unknown Fq relation advice channel {channel}")),
  }
}

fn fields(length: usize) -> Type {
  Type::Tuple { items: vec![Type::Field; length] }
}

pub fn register(channels: &mut HintChannels<Scalar>) -> Result<(), String> {
  for (name, input, output) in [
    (
      "bn254.fq_relation.zero",
      fields(8),
      Type::Tuple { items: vec![fields(4), fields(3)] },
    ),
    ("bn254.fq_relation.u16_17", Type::Field, fields(2)),
    ("bn254.fq_relation.u16_89", Type::Field, fields(6)),
  ] {
    channels.insert(name, input, output, move |input, output| {
      let candidate = advice(name, input)?;
      if output.len() != candidate.len() {
        return Err("Fq relation advice output width mismatch".into());
      }
      output.copy_from_slice(&candidate);
      Ok(())
    })?;
  }
  Ok(())
}
