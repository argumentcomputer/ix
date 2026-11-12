//! Candidate transport and affine arithmetic advice for the Aiur G1 program.
//! Canonical coordinates and bounded Fq relations constrain every candidate.

use super::{Bn254, fq, fq_relation};
use crate::{
  kzg::{
    Scalar,
    curve::{Fq, Fr, G1Affine, read_g1_compressed},
  },
  recursive::native_field::{integer, modulus},
};
use aiur::{
  FieldWord, bytecode::Type, field::FieldBackend, hints::HintChannels,
};
use ark_ff::{BigInteger, Field, PrimeField};
use ark_serialize::CanonicalSerialize;
use num_bigint::{BigInt, BigUint, Sign};

fn scalar(value: &BigUint) -> Result<Scalar, String> {
  let digits = value.to_u64_digits();
  if digits.len() > 4 {
    return Err("G1 advice exceeds scalar representation".into());
  }
  let mut limbs = [0; 4];
  limbs[..digits.len()].copy_from_slice(&digits);
  let word = FieldWord::from_limbs_le(limbs);
  if !Bn254.contains(word) {
    return Err("G1 advice reaches scalar modulus".into());
  }
  Ok(Bn254.from_word(word))
}

fn digits(value: &BigUint) -> [BigUint; 4] {
  let mask = (BigUint::from(1u8) << fq::LIMB_BITS) - 1u8;
  std::array::from_fn(|i| (value >> (fq::LIMB_BITS * i)) & &mask)
}

fn subtraction(
  value: &BigUint,
  bound: &BigUint,
) -> Result<Vec<Scalar>, String> {
  let radix = BigInt::from(1u8) << fq::LIMB_BITS;
  let mut borrow = BigInt::from(0u8);
  let mut difference = vec![];
  let mut borrows = vec![];
  for (value, bound) in digits(value).into_iter().zip(digits(bound)) {
    let mut limb = BigInt::from(bound) - BigInt::from(value) - &borrow;
    borrow = BigInt::from(u8::from(limb.sign() == Sign::Minus));
    if limb.sign() == Sign::Minus {
      limb += &radix;
    }
    difference
      .push(scalar(&limb.to_biguint().ok_or("negative G1 subtraction limb")?)?);
    borrows.push(scalar(&borrow.to_biguint().ok_or("negative G1 borrow")?)?);
  }
  difference.extend(borrows);
  Ok(difference)
}

/// Internal affine representation: four x limbs, four y limbs, infinity flag.
/// Infinity always has zero coordinates, independently of arkworks' in-memory
/// identity coordinates.
pub fn encode(point: G1Affine) -> [Scalar; 9] {
  let (x, y) = if point.infinity {
    (Fq::from(0u8), Fq::from(0u8))
  } else {
    (point.x, point.y)
  };
  let x = fq::encode(x);
  let y = fq::encode(y);
  std::array::from_fn(|i| match i {
    0..=3 => x[i],
    4..=7 => y[i - 4],
    _ => Bn254.from_u64(u64::from(point.infinity)),
  })
}

pub fn decode(values: &[Scalar]) -> Result<G1Affine, String> {
  if values.len() != 9 {
    return Err("G1 point needs nine fields".into());
  }
  let x = fq::decode(&values[..4])?;
  let y = fq::decode(&values[4..8])?;
  match Bn254.try_to_u64(values[8])? {
    1 if x == Fq::from(0u8) && y == Fq::from(0u8) => Ok(G1Affine::identity()),
    0 => {
      let point = G1Affine::new_unchecked(x, y);
      if point.is_on_curve() && point.is_in_correct_subgroup_assuming_on_curve()
      {
        Ok(point)
      } else {
        Err("G1 point is not on the curve".into())
      }
    },
    _ => Err("noncanonical G1 infinity encoding".into()),
  }
}

fn affine(input: &[Scalar], doubling: bool) -> Result<Vec<Scalar>, String> {
  let expected = if doubling { 8 } else { 16 };
  if input.len() != expected {
    return Err(format!("G1 affine advice needs {expected} coordinate limbs"));
  }
  let xa = fq::decode(&input[..4])?;
  let ya = fq::decode(&input[4..8])?;
  let (xb, numerator, denominator) = if doubling {
    (xa, Fq::from(3u8) * xa.square(), ya + ya)
  } else {
    let xb = fq::decode(&input[8..12])?;
    let yb = fq::decode(&input[12..16])?;
    (xb, yb - ya, xb - xa)
  };
  let slope =
    numerator * denominator.inverse().ok_or("zero G1 affine denominator")?;
  let x = slope.square() - xa - xb;
  let y = slope * (xa - x) - ya;
  Ok([slope, x, y].into_iter().flat_map(fq::encode).collect())
}

/// Evaluate the source library's candidate hint protocol without truncating
/// native scalar inputs. Fq channels retain their own constrained protocol.
pub fn advice(channel: &str, input: &[Scalar]) -> Result<Vec<Scalar>, String> {
  match channel {
    "bn254.g1.affine_double" => affine(input, true),
    "bn254.g1.affine_add" => affine(input, false),
    "bn254.g1.scalar" => {
      let [value] = input else {
        return Err("G1 scalar advice needs one field".into());
      };
      let value = integer(*value);
      let r = BigUint::from_bytes_le(&Fr::MODULUS.to_bytes_le());
      let mut output =
        digits(&value).iter().map(scalar).collect::<Result<Vec<_>, _>>()?;
      output.extend(subtraction(&value, &(r - 1u8))?);
      Ok(output)
    },
    "bn254.g1.halve" => {
      let [value] = input else {
        return Err("G1 bit advice needs one field".into());
      };
      let value = integer(*value);
      if value.bits() > fq::LIMB_BITS as u64 {
        return Err("G1 bit advice exceeds limb width".into());
      }
      Ok(vec![
        scalar(&(&value >> 1usize))?,
        scalar(&(&value & BigUint::from(1u8)))?,
      ])
    },
    "bn254.g1.sign" => {
      let value = fq::decode(input)?;
      subtraction(
        &BigUint::from_bytes_le(&value.into_bigint().to_bytes_le()),
        &((modulus() - 1u8) / 2u8),
      )
    },
    "bn254.g1.decode" => {
      if input.len() != 32 {
        return Err("compressed G1 point needs 32 bytes".into());
      }
      let bytes = input
        .iter()
        .map(|&value| {
          u8::try_from(Bn254.try_to_u64(value)?)
            .map_err(|error| format!("G1 byte: {error}"))
        })
        .collect::<Result<Vec<_>, String>>()?;
      let point = read_g1_compressed(&mut bytes.as_slice())
        .map_err(|error| format!("invalid compressed G1 point: {error}"))?;
      Ok(encode(point).to_vec())
    },
    "bn254.g1.u128_bytes" => {
      let [value] = input else {
        return Err("G1 chunk advice needs one field".into());
      };
      Ok(
        chunk_bytes(*value)?
          .into_iter()
          .map(|byte| Bn254.from_u64(u64::from(byte)))
          .collect(),
      )
    },
    "bn254.g1.bytes64" => {
      let [value] = input else {
        return Err("G1 length advice needs one field".into());
      };
      Ok(
        Bn254
          .try_to_u64(*value)?
          .to_le_bytes()
          .into_iter()
          .map(|byte| Bn254.from_u64(u64::from(byte)))
          .collect(),
      )
    },
    name if name.starts_with("bn254.fq.") => fq::advice(channel, input),
    name if name.starts_with("bn254.fq_relation.") => {
      fq_relation::advice(channel, input)
    },
    _ => Err(format!("unknown G1 advice channel {channel}")),
  }
}

fn fields(length: usize) -> Type {
  Type::Tuple { items: vec![Type::Field; length] }
}

/// Register G1 and Fq-relation channels. Register `fq::register` as well for
/// the canonical base-field constructors and arithmetic operations.
pub fn register(channels: &mut HintChannels<Scalar>) -> Result<(), String> {
  fq_relation::register(channels)?;
  for (name, input, output) in [
    (
      "bn254.g1.affine_double",
      Type::Tuple { items: vec![fields(4); 2] },
      Type::Tuple { items: vec![fields(4); 3] },
    ),
    (
      "bn254.g1.affine_add",
      Type::Tuple { items: vec![fields(4); 4] },
      Type::Tuple { items: vec![fields(4); 3] },
    ),
    ("bn254.g1.scalar", Type::Field, Type::Tuple { items: vec![fields(4); 3] }),
    ("bn254.g1.halve", Type::Field, fields(2)),
    ("bn254.g1.sign", fields(4), Type::Tuple { items: vec![fields(4); 2] }),
    ("bn254.g1.decode", fields(32), fields(9)),
    ("bn254.g1.bytes64", Type::Field, fields(8)),
    ("bn254.g1.u128_bytes", Type::Field, fields(16)),
  ] {
    channels.insert(name, input, output, move |input, output| {
      let values = advice(name, input)?;
      if values.len() != output.len() {
        return Err("G1 advice output width mismatch".into());
      }
      output.copy_from_slice(&values);
      Ok(())
    })?;
  }
  Ok(())
}

fn chunk_bytes(value: Scalar) -> Result<[u8; 16], String> {
  let value = integer(value);
  if value.bits() > 128 {
    return Err("G1 chunk exceeds 128 bits".into());
  }
  let bytes = value.to_bytes_le();
  let mut output = [0; 16];
  output[..bytes.len()].copy_from_slice(&bytes);
  Ok(output)
}

/// Two canonical compressed G1 points as four little-endian u128 scalars.
pub fn encode_chunks(points: [G1Affine; 2]) -> Result<[Scalar; 4], String> {
  let mut chunks = [Bn254.zero(); 4];
  for (index, point) in points.into_iter().enumerate() {
    if !point.is_on_curve() {
      return Err("G1 point is not on the curve".into());
    }
    let mut bytes = [0u8; 32];
    point
      .serialize_compressed(bytes.as_mut_slice())
      .map_err(|error| error.to_string())?;
    for (half, block) in bytes.as_chunks::<16>().0.iter().enumerate() {
      chunks[2 * index + half] = Scalar(Fr::from(u128::from_le_bytes(*block)));
    }
  }
  Ok(chunks)
}

pub fn decode_chunks(chunks: &[Scalar]) -> Result<[G1Affine; 2], String> {
  if chunks.len() != 4 {
    return Err("G1 pair needs four u128 chunks".into());
  }
  let mut points = [G1Affine::identity(); 2];
  for (index, words) in chunks.as_chunks::<2>().0.iter().enumerate() {
    let mut bytes = [0; 32];
    bytes[..16].copy_from_slice(&chunk_bytes(words[0])?);
    bytes[16..].copy_from_slice(&chunk_bytes(words[1])?);
    points[index] = read_g1_compressed(&mut bytes.as_slice())
      .map_err(|error| format!("invalid compressed G1 point: {error}"))?;
  }
  Ok(points)
}
