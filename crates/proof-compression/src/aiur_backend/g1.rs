//! Candidate transport, affine arithmetic, and endomorphism subgroup-check
//! advice for the Aiur G1 programs (BN254 4 × 80-bit and BLS12-381 5 × 80-bit).
//! Canonical coordinates and bounded Fq relations constrain every candidate.
//! For BLS12-381 (`HAS_COFACTOR = true`), `bls12_381.g1.subgroup_inv` supplies
//! the denominator-inverse witness `(([|x|]P).x - P.x)^-1` for the Bowe
//! endomorphism subgroup criterion `[x^2]P = -phi(P)` (matching the mandatory
//! in-circuit constraint in `recursive::native_curve::Affine::subgroup`). No
//! BLS12-381 Aiur library exists under `Aiur/Aiur/Library/Field/` yet (the
//! narrow stage rejects BLS12-381 manifests until that library is ported;
//! BN254 G1 has cofactor one, so its curve equation suffices).

use super::{AiurCurve, fq, fq_relation};
use crate::{
  kzg::{
    CurveScalar, Scalar,
    curve::{G1Affine, G1AffineOf, G1ProjectiveOf, read_g1_compressed_for},
  },
  recursive::native_field::{integer, modulus},
};
use aiur::{
  FieldWord, bytecode::Type, field::FieldBackend, hints::HintChannels,
};
use ark_ec::{AdditiveGroup, CurveGroup};
use ark_ff::{BigInteger, Field, PrimeField};
use ark_serialize::CanonicalSerialize;
use num_bigint::{BigInt, BigUint, Sign};

fn scalar_for<C: AiurCurve>(value: &BigUint) -> Result<CurveScalar<C>, String> {
  let digits = value.to_u64_digits();
  if digits.len() > 4 {
    return Err("G1 advice exceeds scalar representation".into());
  }
  let mut limbs = [0; 4];
  limbs[..digits.len()].copy_from_slice(&digits);
  let word = FieldWord::from_limbs_le(limbs);
  if !C::FIELD.contains(word) {
    return Err("G1 advice reaches scalar modulus".into());
  }
  Ok(C::FIELD.from_word(word))
}

fn digits_n(value: &BigUint, n: usize) -> Vec<BigUint> {
  let mask = (BigUint::from(1u8) << fq::LIMB_BITS) - 1u8;
  (0..n).map(|i| (value >> (fq::LIMB_BITS * i)) & &mask).collect()
}

fn subtraction_for<C: AiurCurve>(
  value: &BigUint,
  bound: &BigUint,
  n: usize,
) -> Result<Vec<CurveScalar<C>>, String> {
  let radix = BigInt::from(1u8) << fq::LIMB_BITS;
  let mut borrow = BigInt::from(0u8);
  let mut difference = vec![];
  let mut borrows = vec![];
  for (value, bound) in digits_n(value, n).into_iter().zip(digits_n(bound, n)) {
    let mut limb = BigInt::from(bound) - BigInt::from(value) - &borrow;
    borrow = BigInt::from(u8::from(limb.sign() == Sign::Minus));
    if limb.sign() == Sign::Minus {
      limb += &radix;
    }
    difference.push(scalar_for::<C>(
      &limb.to_biguint().ok_or("negative G1 subtraction limb")?,
    )?);
    borrows.push(scalar_for::<C>(
      &borrow.to_biguint().ok_or("negative G1 borrow")?,
    )?);
  }
  difference.extend(borrows);
  Ok(difference)
}

/// Internal affine representation for curve `C`: `FQ_U80_LIMBS` x limbs,
/// `FQ_U80_LIMBS` y limbs, and an infinity flag (`9` words for BN254, `11` for
/// BLS12-381). Infinity always has zero coordinates, independently of
/// arkworks' in-memory identity coordinates.
pub fn encode_for<C: AiurCurve>(point: G1AffineOf<C>) -> Vec<CurveScalar<C>> {
  let (x, y) = if point.infinity {
    (C::Fq::from(0u8), C::Fq::from(0u8))
  } else {
    (point.x, point.y)
  };
  let mut out = fq::encode_for::<C>(x);
  out.extend(fq::encode_for::<C>(y));
  out.push(C::FIELD.from_u64(u64::from(point.infinity)));
  out
}

/// Internal BN254 affine representation: four x limbs, four y limbs, infinity.
pub fn encode(point: G1Affine) -> [Scalar; 9] {
  encode_for::<crate::kzg::Bn254>(point)
    .try_into()
    .expect("BN254 G1 has 9 words")
}

/// Explicit binary double-and-add on `E(Fq)` without assuming prime-order
/// subgroup membership (safe for arbitrary on-curve points, including torsion).
fn mul_u64_for<C: AiurCurve>(point: G1AffineOf<C>, n: u64) -> G1AffineOf<C> {
  assert!(n > 0);
  let base = G1ProjectiveOf::<C>::from(point);
  let mut acc = base;
  for i in (0..63 - n.leading_zeros()).rev() {
    acc.double_in_place();
    if n & (1u64 << i) != 0 {
      acc += base;
    }
  }
  acc.into_affine()
}

/// Compute the Bowe endomorphism subgroup-check denominator inverse
/// `(([|x|]P).x - P.x)^-1` for a non-identity point on a cofactor curve
/// (BLS12-381), verifying all three endomorphism equations:
/// 1. `P` is on `y^2 = x^3 + b`,
/// 2. `xp = [|x|]P` is non-identity with `xp.x != P.x`, and
/// 3. `x2p = [|x|]xp` satisfies `x2p.x == beta * P.x` and `x2p.y + P.y == 0`.
pub fn subgroup_inv_for<C: AiurCurve>(
  point: G1AffineOf<C>,
) -> Result<C::Fq, String> {
  if !C::HAS_COFACTOR {
    return Err(format!("{} G1 has cofactor one", C::NAME));
  }
  if point.infinity || !point.is_on_curve() {
    return Err(
      "G1 subgroup check requires a non-identity on-curve point".into(),
    );
  }
  let beta =
    C::endo_beta().ok_or("cofactor curve missing endomorphism beta")?;
  let xp = mul_u64_for::<C>(point, C::SUBGROUP_CHECK_SEED);
  if xp.infinity {
    return Err(
      "G1 point failed endomorphism subgroup check (xp is infinity)".into(),
    );
  }
  let inv = (xp.x - point.x)
    .inverse()
    .ok_or("G1 point failed endomorphism subgroup check (xp.x == P.x)")?;
  let x2p = mul_u64_for::<C>(xp, C::SUBGROUP_CHECK_SEED);
  if x2p.infinity
    || x2p.x != beta * point.x
    || x2p.y + point.y != C::Fq::from(0u8)
  {
    return Err("G1 point is not in the prime-order subgroup".into());
  }
  Ok(inv)
}

/// Verify curve and prime-order G1 subgroup membership using the Bowe
/// endomorphism criterion for cofactor curves (`HAS_COFACTOR`), matching
/// `recursive::native_curve::Affine::subgroup`.
pub fn verify_subgroup_endomorphism<C: AiurCurve>(
  point: G1AffineOf<C>,
) -> Result<(), String> {
  if point.infinity {
    return Ok(());
  }
  if !point.is_on_curve() {
    return Err("G1 point is not on the curve".into());
  }
  if C::HAS_COFACTOR {
    let _inv = subgroup_inv_for::<C>(point)?;
  }
  Ok(())
}

/// Decode affine words for curve `C`, enforcing curve and prime-order G1
/// subgroup membership via both the endomorphism criterion and arkworks' check.
pub fn decode_for<C: AiurCurve>(
  values: &[CurveScalar<C>],
) -> Result<G1AffineOf<C>, String> {
  let n = C::FQ_U80_LIMBS;
  if values.len() != C::G1_WORDS {
    return Err(format!("G1 point needs {} fields", C::G1_WORDS));
  }
  let x = fq::decode_for::<C>(&values[..n])?;
  let y = fq::decode_for::<C>(&values[n..2 * n])?;
  match C::FIELD.try_to_u64(values[2 * n])? {
    1 if x == C::Fq::from(0u8) && y == C::Fq::from(0u8) => {
      Ok(G1AffineOf::<C>::identity())
    },
    0 => {
      let point = G1AffineOf::<C>::new_unchecked(x, y);
      verify_subgroup_endomorphism::<C>(point)?;
      if point.is_in_correct_subgroup_assuming_on_curve() {
        Ok(point)
      } else {
        Err("G1 point is not on the curve or subgroup".into())
      }
    },
    _ => Err("noncanonical G1 infinity encoding".into()),
  }
}

pub fn decode(values: &[Scalar]) -> Result<G1Affine, String> {
  decode_for::<crate::kzg::Bn254>(values)
}

fn affine_for<C: AiurCurve>(
  input: &[CurveScalar<C>],
  doubling: bool,
) -> Result<Vec<CurveScalar<C>>, String> {
  let n = C::FQ_U80_LIMBS;
  let expected = if doubling { 2 * n } else { 4 * n };
  if input.len() != expected {
    return Err(format!("G1 affine advice needs {expected} coordinate limbs"));
  }
  let xa = fq::decode_for::<C>(&input[..n])?;
  let ya = fq::decode_for::<C>(&input[n..2 * n])?;
  let (xb, numerator, denominator) = if doubling {
    // Both BN254 (y^2 = x^3 + 3) and BLS12-381 (y^2 = x^3 + 4) have a = 0.
    (xa, C::Fq::from(3u8) * xa.square(), ya + ya)
  } else {
    let xb = fq::decode_for::<C>(&input[2 * n..3 * n])?;
    let yb = fq::decode_for::<C>(&input[3 * n..4 * n])?;
    (xb, yb - ya, xb - xa)
  };
  let slope =
    numerator * denominator.inverse().ok_or("zero G1 affine denominator")?;
  let x = slope.square() - xa - xb;
  let y = slope * (xa - x) - ya;
  Ok([slope, x, y].into_iter().flat_map(fq::encode_for::<C>).collect())
}

/// Evaluate the source library's candidate hint protocol for curve `C` without
/// truncating native scalar inputs. Fq channels retain their own constrained
/// protocol.
pub fn advice_for<C: AiurCurve>(
  channel: &str,
  input: &[CurveScalar<C>],
) -> Result<Vec<CurveScalar<C>>, String> {
  let n = C::FQ_U80_LIMBS;
  let Some(rest) = channel.strip_prefix(C::HINT_PREFIX) else {
    return Err(format!("unknown G1 advice channel {channel}"));
  };
  if rest.starts_with(".fq.") {
    return fq::advice_for::<C>(channel, input);
  }
  if rest.starts_with(".fq_relation.") {
    return fq_relation::advice_for::<C>(channel, input);
  }
  let suffix = rest
    .strip_prefix(".g1.")
    .ok_or_else(|| format!("unknown G1 advice channel {channel}"))?;
  match suffix {
    "affine_double" => affine_for::<C>(input, true),
    "affine_add" => affine_for::<C>(input, false),
    "scalar" => {
      let [value] = input else {
        return Err("G1 scalar advice needs one field".into());
      };
      let value = integer::<C>(*value);
      let r = BigUint::from_bytes_le(&C::Fr::MODULUS.to_bytes_le());
      // Fr is 254 bits (BN254) or 255 bits (BLS12-381): 4 × 80-bit limbs.
      let mut output = digits_n(&value, 4)
        .iter()
        .map(scalar_for::<C>)
        .collect::<Result<Vec<_>, _>>()?;
      output.extend(subtraction_for::<C>(&value, &(r - 1u8), 4)?);
      Ok(output)
    },
    "halve" => {
      let [value] = input else {
        return Err("G1 bit advice needs one field".into());
      };
      let value = integer::<C>(*value);
      if value.bits() > fq::LIMB_BITS as u64 {
        return Err("G1 bit advice exceeds limb width".into());
      }
      Ok(vec![
        scalar_for::<C>(&(&value >> 1usize))?,
        scalar_for::<C>(&(&value & BigUint::from(1u8)))?,
      ])
    },
    "sign" => {
      let value = fq::decode_for::<C>(input)?;
      subtraction_for::<C>(
        &BigUint::from_bytes_le(&value.into_bigint().to_bytes_le()),
        &((modulus::<C>() - 1u8) / 2u8),
        n,
      )
    },
    "decode" => {
      if input.len() != C::G1_COMPRESSED_BYTES {
        return Err(format!(
          "compressed G1 point needs {} bytes",
          C::G1_COMPRESSED_BYTES
        ));
      }
      let bytes = input
        .iter()
        .map(|&value| {
          u8::try_from(C::FIELD.try_to_u64(value)?)
            .map_err(|error| format!("G1 byte: {error}"))
        })
        .collect::<Result<Vec<_>, String>>()?;
      // read_g1_compressed_for enforces curve AND G1 prime-order subgroup check.
      let point = read_g1_compressed_for::<C>(&mut bytes.as_slice())
        .map_err(|error| format!("invalid compressed G1 point: {error}"))?;
      Ok(encode_for::<C>(point))
    },
    "u128_bytes" => {
      let [value] = input else {
        return Err("G1 chunk advice needs one field".into());
      };
      Ok(
        chunk_bytes_for::<C>(*value)?
          .into_iter()
          .map(|byte| C::FIELD.from_u64(u64::from(byte)))
          .collect(),
      )
    },
    "subgroup_inv" => {
      if !C::HAS_COFACTOR {
        return Err(format!("unknown G1 advice channel {channel}"));
      }
      if input.len() != 2 * n {
        return Err(format!(
          "G1 subgroup_inv advice needs {} coordinate limbs",
          2 * n
        ));
      }
      let x = fq::decode_for::<C>(&input[..n])?;
      let y = fq::decode_for::<C>(&input[n..2 * n])?;
      let point = G1AffineOf::<C>::new_unchecked(x, y);
      let inv = subgroup_inv_for::<C>(point)?;
      Ok(fq::encode_for::<C>(inv))
    },
    "bytes64" => {
      let [value] = input else {
        return Err("G1 length advice needs one field".into());
      };
      Ok(
        C::FIELD
          .try_to_u64(*value)?
          .to_le_bytes()
          .into_iter()
          .map(|byte| C::FIELD.from_u64(u64::from(byte)))
          .collect(),
      )
    },
    _ => Err(format!("unknown G1 advice channel {channel}")),
  }
}

/// Evaluate BN254 G1 advice.
pub fn advice(channel: &str, input: &[Scalar]) -> Result<Vec<Scalar>, String> {
  advice_for::<crate::kzg::Bn254>(channel, input)
}

fn fields(length: usize) -> Type {
  Type::Tuple { items: vec![Type::Field; length] }
}

/// Register G1 and Fq-relation channels for curve `C`. Register
/// `fq::register_for::<C>` as well for the canonical base-field constructors
/// and arithmetic operations.
pub fn register_for<C: AiurCurve>(
  channels: &mut HintChannels<CurveScalar<C>>,
) -> Result<(), String> {
  fq_relation::register_for::<C>(channels)?;
  let n = C::FQ_U80_LIMBS;
  let p = C::HINT_PREFIX;
  for (suffix, input, output) in [
    (
      "affine_double",
      Type::Tuple { items: vec![fields(n); 2] },
      Type::Tuple { items: vec![fields(n); 3] },
    ),
    (
      "affine_add",
      Type::Tuple { items: vec![fields(n); 4] },
      Type::Tuple { items: vec![fields(n); 3] },
    ),
    ("scalar", Type::Field, Type::Tuple { items: vec![fields(4); 3] }),
    ("halve", Type::Field, fields(2)),
    ("sign", fields(n), Type::Tuple { items: vec![fields(n); 2] }),
    ("decode", fields(C::G1_COMPRESSED_BYTES), fields(C::G1_WORDS)),
    ("bytes64", Type::Field, fields(8)),
    ("u128_bytes", Type::Field, fields(16)),
  ] {
    let name = format!("{p}.g1.{suffix}");
    let channel_name = name.clone();
    channels.insert(&name, input, output, move |input, output| {
      let values = advice_for::<C>(&channel_name, input)?;
      if values.len() != output.len() {
        return Err("G1 advice output width mismatch".into());
      }
      output.copy_from_slice(&values);
      Ok(())
    })?;
  }
  if C::HAS_COFACTOR {
    let name = format!("{p}.g1.subgroup_inv");
    let channel_name = name.clone();
    channels.insert(
      &name,
      Type::Tuple { items: vec![fields(n); 2] },
      fields(n),
      move |input, output| {
        let values = advice_for::<C>(&channel_name, input)?;
        if values.len() != output.len() {
          return Err("G1 subgroup_inv output width mismatch".into());
        }
        output.copy_from_slice(&values);
        Ok(())
      },
    )?;
  }
  Ok(())
}

/// Register BN254 G1 and Fq-relation channels.
pub fn register(channels: &mut HintChannels<Scalar>) -> Result<(), String> {
  register_for::<crate::kzg::Bn254>(channels)
}

fn chunk_bytes_for<C: AiurCurve>(
  value: CurveScalar<C>,
) -> Result<[u8; 16], String> {
  let value = integer::<C>(value);
  if value.bits() > 128 {
    return Err("G1 chunk exceeds 128 bits".into());
  }
  let bytes = value.to_bytes_le();
  let mut output = [0; 16];
  output[..bytes.len()].copy_from_slice(&bytes);
  Ok(output)
}

/// Two canonical compressed G1 points packed into little-endian `u128` scalars
/// (`4` chunks for BN254 32-byte points, `6` chunks for BLS12-381 48-byte
/// points). Enforces curve and prime-order subgroup membership.
pub fn encode_chunks_for<C: AiurCurve>(
  points: [G1AffineOf<C>; 2],
) -> Result<Vec<CurveScalar<C>>, String> {
  let chunks_per_point = C::G1_COMPRESSED_BYTES / 16;
  let mut chunks = vec![C::FIELD.zero(); 2 * chunks_per_point];
  for (index, point) in points.into_iter().enumerate() {
    verify_subgroup_endomorphism::<C>(point)?;
    if !point.is_in_correct_subgroup_assuming_on_curve() {
      return Err("G1 point is not on the curve or subgroup".into());
    }
    let mut bytes = vec![0u8; C::G1_COMPRESSED_BYTES];
    point
      .serialize_compressed(bytes.as_mut_slice())
      .map_err(|error| error.to_string())?;
    for (part, block) in bytes.as_chunks::<16>().0.iter().enumerate() {
      chunks[chunks_per_point * index + part] =
        CurveScalar::new(C::Fr::from(u128::from_le_bytes(*block)));
    }
  }
  Ok(chunks)
}

/// Two canonical compressed BN254 G1 points as four little-endian u128 scalars.
pub fn encode_chunks(points: [G1Affine; 2]) -> Result<[Scalar; 4], String> {
  encode_chunks_for::<crate::kzg::Bn254>(points)?
    .try_into()
    .map_err(|_chunks| "BN254 G1 pair needs four u128 chunks".into())
}

pub fn decode_chunks_for<C: AiurCurve>(
  chunks: &[CurveScalar<C>],
) -> Result<[G1AffineOf<C>; 2], String> {
  if chunks.len() != C::ACCUMULATOR_CHUNKS {
    return Err(format!("G1 pair needs {} u128 chunks", C::ACCUMULATOR_CHUNKS));
  }
  let chunks_per_point = C::G1_COMPRESSED_BYTES / 16;
  let mut points = [G1AffineOf::<C>::identity(); 2];
  for (index, words) in chunks.chunks_exact(chunks_per_point).enumerate() {
    let mut bytes = vec![0u8; C::G1_COMPRESSED_BYTES];
    for (part, &word) in words.iter().enumerate() {
      bytes[16 * part..16 * (part + 1)]
        .copy_from_slice(&chunk_bytes_for::<C>(word)?);
    }
    points[index] = read_g1_compressed_for::<C>(&mut bytes.as_slice())
      .map_err(|error| format!("invalid compressed G1 point: {error}"))?;
  }
  Ok(points)
}

pub fn decode_chunks(chunks: &[Scalar]) -> Result<[G1Affine; 2], String> {
  decode_chunks_for::<crate::kzg::Bn254>(chunks)
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::kzg::curve::{Bls12381, KzgCurve};
  use crate::recursive::{
    native_curve::PointInput,
    native_field::{Builder, FqGadget},
  };
  use ark_ec::AffineRepr;

  fn collect_bls12_381_off_subgroup_points(
    count: usize,
  ) -> Vec<ark_bls12_381::G1Affine> {
    let mut out = vec![ark_bls12_381::G1Affine::new_unchecked(
      ark_bls12_381::Fq::from(0u8),
      ark_bls12_381::Fq::from(2u8),
    )];
    assert!(out[0].is_on_curve());
    assert!(!out[0].is_in_correct_subgroup_assuming_on_curve());
    for x_u64 in 1u64..1000 {
      if out.len() >= count {
        break;
      }
      if let Some(p) = ark_bls12_381::G1Affine::get_point_from_x_unchecked(
        ark_bls12_381::Fq::from(x_u64),
        false,
      ) && p.is_on_curve()
        && !p.is_in_correct_subgroup_assuming_on_curve()
      {
        out.push(p);
      }
    }
    assert_eq!(out.len(), count);
    out
  }

  #[test]
  fn bls12_381_endomorphism_subgroup_check_accepts_valid_and_rejects_torsion() {
    let g = ark_bls12_381::G1Affine::generator();
    let beta = Bls12381::endo_beta().unwrap();

    // Positive: valid prime-order subgroup points and infinity.
    verify_subgroup_endomorphism::<Bls12381>(
      ark_bls12_381::G1Affine::identity(),
    )
    .unwrap();
    for k in [1u64, 2, 7, 13, 123_456_789, u64::MAX] {
      for point in [
        (g * ark_bls12_381::Fr::from(k)).into_affine(),
        -(g * ark_bls12_381::Fr::from(k)).into_affine(),
      ] {
        verify_subgroup_endomorphism::<Bls12381>(point).unwrap();
        let inv = subgroup_inv_for::<Bls12381>(point).unwrap();
        let xp = mul_u64_for::<Bls12381>(point, Bls12381::SUBGROUP_CHECK_SEED);
        let x2p = mul_u64_for::<Bls12381>(xp, Bls12381::SUBGROUP_CHECK_SEED);
        assert_eq!((xp.x - point.x) * inv, ark_bls12_381::Fq::from(1u8));
        assert_eq!(x2p.x, beta * point.x);
        assert_eq!(x2p.y + point.y, ark_bls12_381::Fq::from(0u8));

        let coords = encode_for::<Bls12381>(point)[..10].to_vec();
        let advice_inv =
          advice_for::<Bls12381>("bls12_381.g1.subgroup_inv", &coords).unwrap();
        assert_eq!(fq::decode_for::<Bls12381>(&advice_inv).unwrap(), inv);
      }
    }

    // Build the in-circuit Plonkish BLS12-381 G1 subgroup checker.
    let mut b = Builder::<Bls12381>::new();
    let f = FqGadget::<Bls12381>::new(&mut b);
    let p_in = PointInput::<Bls12381>::new(&mut b, &f, "p");
    let circuit = b.finish();
    let run_circuit = |pt: ark_bls12_381::G1Affine| {
      let mut w = circuit.witness();
      for (v, val) in p_in.inputs(pt) {
        w.set(v, val).unwrap();
      }
      w.generate()
    };
    run_circuit(g).unwrap();
    run_circuit(ark_bls12_381::G1Affine::identity()).unwrap();

    // Negative: on-curve off-subgroup points (including (0, 2)) must be
    // rejected by every advice helper, decoder, chunk codec, and in-circuit
    // endomorphism constraint.
    for bad in collect_bls12_381_off_subgroup_points(9) {
      assert!(bad.is_on_curve());
      assert!(!bad.is_in_correct_subgroup_assuming_on_curve());

      assert!(verify_subgroup_endomorphism::<Bls12381>(bad).is_err());
      assert!(subgroup_inv_for::<Bls12381>(bad).is_err());

      let words = encode_for::<Bls12381>(bad);
      assert!(decode_for::<Bls12381>(&words).is_err());
      assert!(
        advice_for::<Bls12381>("bls12_381.g1.subgroup_inv", &words[..10])
          .is_err()
      );
      assert!(encode_chunks_for::<Bls12381>([bad, g]).is_err());

      let mut compressed = Vec::new();
      bad.serialize_compressed(&mut compressed).unwrap();
      let compressed_fields: Vec<_> = compressed
        .iter()
        .map(|&byte| Bls12381::FIELD.from_u64(u64::from(byte)))
        .collect();
      assert!(
        advice_for::<Bls12381>("bls12_381.g1.decode", &compressed_fields)
          .is_err()
      );

      assert!(
        run_circuit(bad).is_err(),
        "in-circuit BLS12-381 G1 constraints must reject off-subgroup point"
      );
    }

    // Off-curve point must also fail.
    let off_curve = ark_bls12_381::G1Affine::new_unchecked(
      ark_bls12_381::Fq::from(7u8),
      ark_bls12_381::Fq::from(9u8),
    );
    assert!(!off_curve.is_on_curve());
    assert!(verify_subgroup_endomorphism::<Bls12381>(off_curve).is_err());
    assert!(run_circuit(off_curve).is_err());
  }
}
