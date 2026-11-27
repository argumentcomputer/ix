//! Untrusted quotient and carry candidates for bounded signed Fq relations
//! (4 × 80-bit for BN254, 5 × 80-bit for BLS12-381). Aiur constructs the
//! coefficients, checks their expression weights, and constrains every advice
//! limb with range lookups and integer equations.

use super::AiurCurve;
use crate::{
  kzg::{CurveScalar, Scalar},
  recursive::native_field::{integer, modulus, scalar},
};
use aiur::{bytecode::Type, hints::HintChannels};
use ark_ff::{BigInteger, PrimeField};
use num_bigint::{BigInt, BigUint};
use std::sync::OnceLock;

pub const LIMB_BITS: usize = 80;
pub const QUOTIENT_BITS: usize = 257;
pub const BLS12_381_QUOTIENT_BITS: usize = 385;
pub const CARRY_BITS: usize = 89;
pub const ADVICE_LEN: usize = 7;
pub const BLS12_381_ADVICE_LEN: usize = 9;

struct Constants {
  limbs: usize,
  quotient_bits: usize,
  scalar_modulus: BigInt,
  scalar_midpoint: BigUint,
  coefficient_bound: BigInt,
  modulus: BigInt,
  modulus_digits: Vec<BigInt>,
  quotient_bias: BigInt,
  carry_bias: BigInt,
  pair_radix: BigInt,
}

fn digits_n(value: &BigUint, n: usize) -> Vec<BigUint> {
  let mask = (BigUint::from(1u8) << LIMB_BITS) - 1u8;
  (0..n).map(|i| (value >> (LIMB_BITS * i)) & &mask).collect()
}

fn build_constants<C: AiurCurve>(quotient_bits: usize) -> Constants {
  let radix = BigUint::from(1u8) << LIMB_BITS;
  let scalar_modulus = BigUint::from_bytes_le(&C::Fr::MODULUS.to_bytes_le());
  let prime = modulus::<C>();
  Constants {
    limbs: C::FQ_U80_LIMBS,
    quotient_bits,
    scalar_midpoint: &scalar_modulus / 2u8,
    scalar_modulus: scalar_modulus.into(),
    coefficient_bound: (12u8 * &radix * &radix + 3u8 * &radix + 4u8).into(),
    modulus_digits: digits_n(&prime, C::FQ_U80_LIMBS)
      .into_iter()
      .map(BigInt::from)
      .collect(),
    modulus: prime.into(),
    quotient_bias: BigInt::from(1u8) << (quotient_bits - 1),
    carry_bias: BigInt::from(1u8) << (CARRY_BITS - 1),
    pair_radix: BigInt::from(1u8) << (2 * LIMB_BITS),
  }
}

fn constants_for<C: AiurCurve>() -> &'static Constants {
  static BN254_CONSTANTS: OnceLock<Constants> = OnceLock::new();
  static BLS12_381_CONSTANTS: OnceLock<Constants> = OnceLock::new();
  match C::CURVE {
    crate::kzg::Curve::Bn254 => BN254_CONSTANTS
      .get_or_init(|| build_constants::<crate::kzg::Bn254>(QUOTIENT_BITS)),
    crate::kzg::Curve::Bls12381 => BLS12_381_CONSTANTS.get_or_init(|| {
      build_constants::<crate::kzg::Bls12381>(BLS12_381_QUOTIENT_BITS)
    }),
  }
}

fn relation_for<C: AiurCurve>(
  input: &[CurveScalar<C>],
) -> Result<Vec<CurveScalar<C>>, String> {
  let constants = constants_for::<C>();
  let n = constants.limbs;
  if input.len() != 2 * n {
    return Err(format!("Fq relation requires {} coefficients", 2 * n));
  }
  let mut terms = input
    .iter()
    .map(|&value| {
      let value = integer::<C>(value);
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
  if quotient.bits() > constants.quotient_bits as u64 {
    return Err(format!(
      "Fq relation quotient exceeds {} bits",
      constants.quotient_bits
    ));
  }
  let quotient = digits_n(&quotient, n);
  let mut output = quotient.iter().map(scalar::<C>).collect::<Vec<_>>();
  let mut unbiased: Vec<BigInt> =
    quotient.into_iter().map(BigInt::from).collect();
  unbiased[n - 1] -=
    BigInt::from(1u8) << (constants.quotient_bits - 1 - (n - 1) * LIMB_BITS);
  for i in 0..n {
    for j in 0..n {
      terms[i + j] -= &unbiased[i] * &constants.modulus_digits[j];
    }
  }
  let mut carry = BigInt::from(0u8);
  for pair in 0..n {
    carry += &terms[2 * pair] + (&terms[2 * pair + 1] << LIMB_BITS);
    if &carry % &constants.pair_radix != BigInt::from(0u8) {
      return Err("nonintegral Fq relation carry".into());
    }
    carry /= &constants.pair_radix;
    if pair + 1 < n {
      let biased = (&carry + &constants.carry_bias)
        .to_biguint()
        .ok_or("negative biased carry")?;
      if biased.bits() > CARRY_BITS as u64 {
        return Err("Fq relation carry exceeds 89 bits".into());
      }
      output.push(scalar::<C>(&biased));
    }
  }
  if carry != BigInt::from(0u8) {
    return Err("nonzero final Fq relation carry".into());
  }
  Ok(output)
}

/// Candidate advice only; acceptance requires the compiled Aiur constraints.
pub fn advice_for<C: AiurCurve>(
  channel: &str,
  input: &[CurveScalar<C>],
) -> Result<Vec<CurveScalar<C>>, String> {
  let suffix = channel
    .strip_prefix(C::HINT_PREFIX)
    .and_then(|rest| rest.strip_prefix(".fq_relation."))
    .ok_or_else(|| format!("unknown Fq relation advice channel {channel}"))?;
  match suffix {
    "zero" => relation_for::<C>(input),
    "u16_17" | "u16_65" | "u16_89" => {
      let [value] = input else {
        return Err("Fq relation range advice requires one value".into());
      };
      let bits = match suffix {
        "u16_17" => 17,
        "u16_65" => 65,
        _ => CARRY_BITS,
      };
      let value = integer::<C>(*value);
      if value.bits() > bits as u64 {
        return Err("Fq relation range advice exceeds width".into());
      }
      let mask = BigUint::from(65535u32);
      Ok(
        (0..bits.div_ceil(16))
          .map(|i| scalar::<C>(&((&value >> (16 * i)) & &mask)))
          .collect(),
      )
    },
    _ => Err(format!("unknown Fq relation advice channel {channel}")),
  }
}

/// BN254 specialization of [`advice_for`].
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
  let p = C::HINT_PREFIX;
  let (top_suffix, top_chunks) = match C::CURVE {
    crate::kzg::Curve::Bn254 => ("u16_17", 2),
    crate::kzg::Curve::Bls12381 => ("u16_65", 5),
  };
  for (suffix, input, output) in [
    (
      "zero",
      fields(2 * n),
      Type::Tuple { items: vec![fields(n), fields(n - 1)] },
    ),
    (top_suffix, Type::Field, fields(top_chunks)),
    ("u16_89", Type::Field, fields(6)),
  ] {
    let name = format!("{p}.fq_relation.{suffix}");
    let channel_name = name.clone();
    channels.insert(&name, input, output, move |input, output| {
      let candidate = advice_for::<C>(&channel_name, input)?;
      if output.len() != candidate.len() {
        return Err("Fq relation advice output width mismatch".into());
      }
      output.copy_from_slice(&candidate);
      Ok(())
    })?;
  }
  Ok(())
}

pub fn register(channels: &mut HintChannels<Scalar>) -> Result<(), String> {
  register_for::<crate::kzg::Bn254>(channels)
}
