//! Prefix loading for BN254 `kzg.SRS.WriteRawTo` files from gnark-crypto.
//! Ceremony verification and selection happen during release preparation.
use super::{PublicSetup, Srs};
use crate::kzg::curve::{Fq, G1Affine, G2Affine};
use ark_bn254::Fq2;
use ark_ec::AffineRepr;
use ark_serialize::CanonicalDeserialize;
use p3_maybe_rayon::prelude::*;
use std::{
  fs::File,
  io::{self, Read, Seek, SeekFrom},
  path::Path,
};

const MAX_POINTS: usize = 100_800_000;
const BLOCK_POINTS: usize = 1 << 16;
// Two G2 points, one G1 point, and 2×2×66 pairs of Fq2 line coefficients.
const VK_BYTES: u64 = 2 * 128 + 64 + 2 * 2 * 66 * 2 * 64;

fn invalid(message: &'static str) -> io::Error {
  io::Error::new(io::ErrorKind::InvalidData, message)
}

fn field(bytes: &[u8]) -> io::Result<Fq> {
  let mut encoded: [u8; 32] = bytes.try_into().expect("coordinate length");
  encoded.reverse();
  Fq::deserialize_uncompressed(encoded.as_slice())
    .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))
}

fn g1(bytes: &[u8]) -> io::Result<G1Affine> {
  let point =
    G1Affine::new_unchecked(field(&bytes[..32])?, field(&bytes[32..])?);
  // BN254 G1 has cofactor one.
  if point.is_zero() || !point.is_on_curve() {
    return Err(invalid("invalid BN254 G1 point"));
  }
  Ok(point)
}

fn g2(bytes: &[u8]) -> io::Result<G2Affine> {
  // gnark writes the imaginary component before the real component.
  let point = G2Affine::new_unchecked(
    Fq2::new(field(&bytes[32..64])?, field(&bytes[..32])?),
    Fq2::new(field(&bytes[96..128])?, field(&bytes[64..96])?),
  );
  if point.is_zero()
    || !point.is_on_curve()
    || !point.is_in_correct_subgroup_assuming_on_curve()
  {
    return Err(invalid("invalid BN254 G2 point"));
  }
  Ok(point)
}

/// Load a prefix of an approved, uncompressed gnark SRS. The public setup
/// identity comes from the verifier release, not metadata in this file.
pub fn load(
  path: &Path,
  prefix_len: usize,
  public_setup: PublicSetup,
) -> io::Result<Srs> {
  if prefix_len < 2
    || !prefix_len.is_power_of_two()
    || prefix_len > MAX_POINTS
    || prefix_len - 1 > public_setup.max_degree
  {
    return Err(invalid("invalid SRS prefix length"));
  }
  let mut file = File::open(path)?;
  let mut count = [0; 4];
  file.read_exact(&mut count)?;
  let count = u32::from_be_bytes(count) as usize;
  if count < prefix_len
    || count > MAX_POINTS
    || file.metadata()?.len() != 4 + count as u64 * 64 + VK_BYTES
  {
    return Err(invalid(
      "invalid gnark SRS length; expected WriteRawTo encoding",
    ));
  }
  let mut powers = Vec::with_capacity(prefix_len);
  let mut buffer = vec![0; prefix_len.min(BLOCK_POINTS) * 64];
  while powers.len() < prefix_len {
    let count = (prefix_len - powers.len()).min(BLOCK_POINTS);
    let bytes = &mut buffer[..count * 64];
    file.read_exact(bytes)?;
    let chunk =
      bytes.par_chunks_exact(64).map(g1).collect::<io::Result<Vec<_>>>()?;
    powers.extend(chunk);
  }
  file.seek(SeekFrom::Start(4 + count as u64 * 64))?;
  let mut anchors = [0; 320];
  file.read_exact(&mut anchors)?;
  if g1(&anchors[256..])? != powers[0] {
    return Err(invalid("gnark SRS G1 anchor differs from its powers"));
  }
  Ok(Srs {
    g1: powers,
    g2: g2(&anchors[..128])?,
    tau_g2: g2(&anchors[128..256])?,
    public_setup,
  })
}

#[cfg(test)]
mod tests {
  use super::*;
  use ark_ff::{BigInteger, PrimeField};
  use std::io::Write;

  // Only the G1/G2 portion is consumed by Rust; pairing lines are a gnark optimization.
  fn fixture(srs: &Srs) -> Vec<u8> {
    let mut bytes = (srs.g1.len() as u32).to_be_bytes().to_vec();
    let encode_g1 = |p: G1Affine| {
      [p.x, p.y]
        .into_iter()
        .flat_map(|v| v.into_bigint().to_bytes_be())
        .collect::<Vec<_>>()
    };
    for p in &srs.g1 {
      bytes.extend(encode_g1(*p));
    }
    for p in [srs.g2, srs.tau_g2] {
      for v in [p.x.c1, p.x.c0, p.y.c1, p.y.c0] {
        bytes.extend(v.into_bigint().to_bytes_be());
      }
    }
    bytes.extend(encode_g1(srs.g1[0]));
    bytes.resize(4 + srs.g1.len() * 64 + VK_BYTES as usize, 0);
    bytes
  }

  #[test]
  fn prefix_loading_checks_framing_coordinates_and_anchors() -> io::Result<()> {
    let srs = Srs::unsafe_dev_setup(8, b"gnark-reader");
    let path =
      std::env::temp_dir().join(format!("ix-gnark-srs-{}", std::process::id()));
    let mut file =
      std::fs::OpenOptions::new().write(true).create_new(true).open(&path)?;
    let bytes = fixture(&srs);
    file.write_all(&bytes)?;
    drop(file);
    let prefix = load(&path, 4, srs.public_setup)?;
    assert_eq!(prefix.g1, srs.g1[..4]);
    assert_eq!(prefix.g2, srs.g2);
    assert_eq!(prefix.tau_g2, srs.tau_g2);
    assert!(load(&path, 16, srs.public_setup).is_err());
    for offset in [0, 4, 4 + 8 * 64, 4 + 8 * 64 + 256] {
      let mut damaged = bytes.clone();
      damaged[offset] ^= 0xff;
      std::fs::write(&path, damaged)?;
      assert!(load(&path, 4, srs.public_setup).is_err());
    }
    std::fs::write(&path, &bytes[..bytes.len() - 1])?;
    assert!(load(&path, 4, srs.public_setup).is_err());
    std::fs::remove_file(path)
  }
}
