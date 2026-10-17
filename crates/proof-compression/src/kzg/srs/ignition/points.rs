use std::io;

use ark_bn254::Fq2;
use ark_ec::AffineRepr;
use ark_ff::{BigInt, PrimeField};

use crate::kzg::curve::{Fq, G1Affine, G2Affine};

fn invalid(message: &'static str) -> io::Error {
  io::Error::new(io::ErrorKind::InvalidData, message)
}

fn decode_field(bytes: &[u8], source_encoding: bool) -> io::Result<Fq> {
  if bytes.len() != 32 {
    return Err(invalid("invalid BN254 coordinate length"));
  }
  let mut limbs = [0; 4];
  for (limb, bytes) in limbs.iter_mut().zip(bytes.as_chunks::<8>().0) {
    let word = *bytes;
    *limb = if source_encoding {
      u64::from_be_bytes(word)
    } else {
      u64::from_le_bytes(word)
    };
  }
  Fq::from_bigint(BigInt(limbs))
    .ok_or_else(|| invalid("noncanonical BN254 coordinate"))
}

fn read_g1(bytes: &[u8], source_encoding: bool) -> io::Result<G1Affine> {
  if bytes.len() != 64 {
    return Err(invalid("invalid BN254 G1 length"));
  }
  let point = G1Affine::new_unchecked(
    decode_field(&bytes[..32], source_encoding)?,
    decode_field(&bytes[32..], source_encoding)?,
  );
  // BN254 G1 has cofactor one, so curve membership implies subgroup membership.
  if point.is_zero() || !point.is_on_curve() {
    return Err(invalid("invalid or identity BN254 G1 point"));
  }
  Ok(point)
}

fn read_g2(bytes: &[u8], source_encoding: bool) -> io::Result<G2Affine> {
  if bytes.len() != 128 {
    return Err(invalid("invalid BN254 G2 length"));
  }
  let point = G2Affine::new_unchecked(
    Fq2::new(
      decode_field(&bytes[..32], source_encoding)?,
      decode_field(&bytes[32..64], source_encoding)?,
    ),
    Fq2::new(
      decode_field(&bytes[64..96], source_encoding)?,
      decode_field(&bytes[96..], source_encoding)?,
    ),
  );
  if point.is_zero()
    || !point.is_on_curve()
    || !point.is_in_correct_subgroup_assuming_on_curve()
  {
    return Err(invalid("invalid or identity BN254 G2 point"));
  }
  Ok(point)
}

pub(super) fn decode_source_g1(bytes: &[u8]) -> io::Result<G1Affine> {
  read_g1(bytes, true)
}

pub(super) fn decode_source_g2(bytes: &[u8]) -> io::Result<G2Affine> {
  read_g2(bytes, true)
}

fn encode_field(value: &Fq, bytes: &mut [u8]) {
  for (limb, bytes) in
    value.into_bigint().0.iter().zip(bytes.as_chunks_mut::<8>().0)
  {
    bytes.copy_from_slice(&limb.to_le_bytes());
  }
}

pub(super) fn encode_g1(point: &G1Affine) -> [u8; 64] {
  let mut bytes = [0; 64];
  encode_field(&point.x, &mut bytes[..32]);
  encode_field(&point.y, &mut bytes[32..]);
  bytes
}

pub(super) fn decode_g1(bytes: &[u8]) -> io::Result<G1Affine> {
  read_g1(bytes, false)
}

pub(super) fn encode_g2(point: &G2Affine) -> [u8; 128] {
  let mut bytes = [0; 128];
  encode_field(&point.x.c0, &mut bytes[..32]);
  encode_field(&point.x.c1, &mut bytes[32..64]);
  encode_field(&point.y.c0, &mut bytes[64..96]);
  encode_field(&point.y.c1, &mut bytes[96..]);
  bytes
}

pub(super) fn decode_g2(bytes: &[u8]) -> io::Result<G2Affine> {
  read_g2(bytes, false)
}
