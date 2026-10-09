//! KZG parameters: G1 powers, G2 anchors and G2 powers for degree checks.
//! Imported parameters need validated point decoding, [`Srs::validate`] and
//! trusted provenance. Consistency does not establish an unknown trapdoor.
//! The full available G1 degree range and every required G2 degree key must
//! be represented; truncating public parameters does not reduce that range.
//! [`Srs::unsafe_dev_setup`] reveals its trapdoor and is only for tests.

use ark_bls12_381::{
  Bls12_381, Fr, G1Affine, G1Projective, G2Affine, G2Projective,
};
use ark_ec::{
  AffineRepr, CurveGroup, PrimeGroup, VariableBaseMSM, pairing::Pairing,
};
use ark_ff::{Field, PrimeField, Zero};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use p3_maybe_rayon::prelude::*;
use std::io::{self, Read, Write};

/// `[G, τG, τ²G, …]` in G1 and `[H, τH]` in G2.
pub struct Srs {
  pub g1: Vec<G1Affine>,
  pub g2: G2Affine,
  pub tau_g2: G2Affine,
  /// Entry k is τ^(max_len - 2^k) H, for degree-bound checks.
  pub degree_keys: Vec<G2Affine>,
}

impl Srs {
  /// Read IXKZGS01: magic, little-endian u32 log-length, G1 powers,
  /// G2, tau-G2, and log-length + 1 degree keys (compressed Ark points).
  /// Validates point encodings, subgroups and the complete powers relation.
  /// The caller must independently authenticate the source of these parameters.
  pub fn from_reader(mut reader: impl Read) -> io::Result<Self> {
    let invalid = |e| io::Error::new(io::ErrorKind::InvalidData, e);
    let mut magic = [0; 8];
    reader.read_exact(&mut magic)?;
    if &magic != b"IXKZGS01" {
      return Err(invalid("unsupported KZG SRS format"));
    }
    let mut log = [0; 4];
    reader.read_exact(&mut log)?;
    let log = u32::from_le_bytes(log);
    // BLS12-381's scalar field has two-adicity 32. Leave room for the
    // quotient domain and reject oversized headers before allocating.
    if !(1..=30).contains(&log) {
      return Err(invalid("unsupported KZG SRS log-length"));
    }
    let decode_error = |e| io::Error::new(io::ErrorKind::InvalidData, e);
    // Grow only as points are read, so a truncated header cannot force a
    // large allocation. Deserialization performs subgroup checks.
    let mut g1 = Vec::new();
    for _ in 0..1usize << log {
      g1.push(
        G1Affine::deserialize_compressed(&mut reader).map_err(decode_error)?,
      );
    }
    let g2 =
      G2Affine::deserialize_compressed(&mut reader).map_err(decode_error)?;
    let tau_g2 =
      G2Affine::deserialize_compressed(&mut reader).map_err(decode_error)?;
    let mut degree_keys = Vec::new();
    for _ in 0..=log {
      degree_keys.push(
        G2Affine::deserialize_compressed(&mut reader).map_err(decode_error)?,
      );
    }
    if reader.read(&mut [0])? != 0 {
      return Err(invalid("trailing KZG SRS data"));
    }
    let srs = Self { g1, g2, tau_g2, degree_keys };
    srs.validate().map_err(invalid)?;
    Ok(srs)
  }

  /// Export parameters in the format consumed by [`Self::from_reader`].
  pub fn write(&self, mut writer: impl Write) -> io::Result<()> {
    if self.max_len() < 2
      || !self.max_len().is_power_of_two()
      || self.max_len().ilog2() > 30
      || self.degree_keys.len() != self.max_len().ilog2() as usize + 1
    {
      return Err(io::Error::new(
        io::ErrorKind::InvalidInput,
        "invalid SRS dimensions",
      ));
    }
    writer.write_all(b"IXKZGS01")?;
    writer.write_all(&self.max_len().ilog2().to_le_bytes())?;
    let encode_error = |e| io::Error::new(io::ErrorKind::InvalidData, e);
    for point in &self.g1 {
      point.serialize_compressed(&mut writer).map_err(encode_error)?;
    }
    self.g2.serialize_compressed(&mut writer).map_err(encode_error)?;
    self.tau_g2.serialize_compressed(&mut writer).map_err(encode_error)?;
    for point in &self.degree_keys {
      point.serialize_compressed(&mut writer).map_err(encode_error)?;
    }
    Ok(())
  }

  /// The largest polynomial length (degree + 1) this SRS can commit.
  #[inline]
  pub fn max_len(&self) -> usize {
    self.g1.len()
  }

  /// Check nonzero anchors, degree keys and the powers relation
  /// `e(g1[i+1], H) = e(g1[i], τH)`, batched with a challenge derived
  /// from the SRS bytes. Points must already have passed validated
  /// deserialization, including subgroup checks. This does not establish
  /// trusted provenance or an unknown trapdoor.
  pub fn validate(&self) -> Result<(), &'static str> {
    if self.g1.len() < 2 || !self.g1.len().is_power_of_two() {
      return Err("SRS length must be a power of two >= 2");
    }
    if self.g1[0].is_zero()
      || self.g1[1].is_zero()
      || self.g2.is_zero()
      || self.tau_g2.is_zero()
    {
      return Err("SRS anchor is the identity");
    }
    let logs = p3_util::log2_strict_usize(self.max_len());
    if self.degree_keys.len() != logs + 1 {
      return Err("missing degree keys");
    }
    for (k, key) in self.degree_keys.iter().enumerate() {
      let shift = self.max_len() - (1 << k);
      if !Bls12_381::multi_pairing(
        [self.g1[shift], (-G1Projective::from(self.g1[0])).into_affine()],
        [self.g2, *key],
      )
      .is_zero()
      {
        return Err("inconsistent degree key");
      }
    }

    let mut bytes = Vec::new();
    self
      .g1
      .serialize_compressed(&mut bytes)
      .expect("serialization into a Vec cannot fail");
    self
      .g2
      .serialize_compressed(&mut bytes)
      .expect("serialization into a Vec cannot fail");
    self
      .tau_g2
      .serialize_compressed(&mut bytes)
      .expect("serialization into a Vec cannot fail");
    let mut wide = [0u8; 64];
    blake3::Hasher::new()
      .update(b"multi-stark/kzg/srs-validate")
      .update(&bytes)
      .finalize_xof()
      .fill(&mut wide);
    let r = Fr::from_le_bytes_mod_order(&wide);

    let mut r_powers = Vec::with_capacity(self.g1.len() - 1);
    let mut acc = Fr::ONE;
    for _ in 0..self.g1.len() - 1 {
      r_powers.push(acc);
      acc *= r;
    }
    let low = G1Projective::msm(&self.g1[..self.g1.len() - 1], &r_powers)
      .expect("equal lengths");
    let high =
      G1Projective::msm(&self.g1[1..], &r_powers).expect("equal lengths");
    // e(high, H) = e(low, τH)  ⇔  e(high, H)·e(−low, τH) = 1.
    let check = Bls12_381::multi_pairing(
      [high.into_affine(), (-low).into_affine()],
      [self.g2, self.tau_g2],
    );
    if check.is_zero() {
      Ok(())
    } else {
      Err("G1 powers are not one τ-progression against the G2 pair")
    }
  }

  /// A deterministic SRS with τ derived from `seed`. TESTS AND
  /// DEVELOPMENT ONLY: τ is recoverable, so commitments under this
  /// SRS are not binding against anyone who knows the seed.
  pub fn unsafe_dev_setup(max_len: usize, seed: &[u8]) -> Self {
    assert!(max_len >= 2 && max_len.is_power_of_two());
    let mut wide = [0u8; 64];
    blake3::Hasher::new()
      .update(b"multi-stark/kzg/dev-srs")
      .update(seed)
      .finalize_xof()
      .fill(&mut wide);
    let tau = Fr::from_le_bytes_mod_order(&wide);

    let g1_gen = G1Projective::generator();
    // τ-powers in independent chunks (each chunk seeds itself with
    // τ^start), so the scalar multiplications parallelize under the
    // `parallel` feature; serial otherwise.
    let chunk = 1usize << 14;
    let mut g1 = vec![G1Affine::identity(); max_len];
    g1.par_chunks_mut(chunk).enumerate().for_each(|(i, dst)| {
      let mut acc = tau.pow([(i * chunk) as u64]);
      let powers: Vec<_> = (0..dst.len())
        .map(|_| {
          let point = g1_gen * acc;
          acc *= tau;
          point
        })
        .collect();
      dst.copy_from_slice(&G1Projective::normalize_batch(&powers));
    });
    let g2_gen = G2Projective::generator();
    Self {
      g1,
      g2: g2_gen.into_affine(),
      tau_g2: (g2_gen * tau).into_affine(),
      degree_keys: (0..=p3_util::log2_strict_usize(max_len))
        .map(|k| {
          (g2_gen * tau.pow([(max_len - (1 << k)) as u64])).into_affine()
        })
        .collect(),
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn srs_transport_rejects_malformed_and_inconsistent_parameters() {
    let mut srs = Srs::unsafe_dev_setup(32, b"srs-transport");
    let mut bytes = Vec::new();
    srs.write(&mut bytes).unwrap();
    let decoded = Srs::from_reader(bytes.as_slice()).unwrap();
    assert_eq!(decoded.g1, srs.g1);
    assert_eq!(decoded.degree_keys, srs.degree_keys);
    assert!(Srs::from_reader(&bytes[..bytes.len() - 1]).is_err());
    let mut trailing = bytes.clone();
    trailing.push(0);
    assert!(Srs::from_reader(trailing.as_slice()).is_err());
    bytes[8..12].copy_from_slice(&u32::MAX.to_le_bytes());
    assert!(Srs::from_reader(bytes.as_slice()).is_err());
    bytes[8..12].copy_from_slice(&30u32.to_le_bytes());
    assert!(Srs::from_reader(&bytes[..12]).is_err());
    srs.g1[7] = srs.g1[8];
    bytes.clear();
    srs.write(&mut bytes).unwrap();
    assert!(Srs::from_reader(bytes.as_slice()).is_err());
  }

  #[test]
  fn development_powers_match_naive_at_chunk_boundaries() {
    let seed = b"chunk-powers";
    let srs = Srs::unsafe_dev_setup(1 << 16, seed);
    let mut wide = [0u8; 64];
    blake3::Hasher::new()
      .update(b"multi-stark/kzg/dev-srs")
      .update(seed)
      .finalize_xof()
      .fill(&mut wide);
    let tau = Fr::from_le_bytes_mod_order(&wide);
    for i in [0, 1, (1 << 14) - 1, 1 << 14, (1 << 15) - 1, (1 << 16) - 1] {
      assert_eq!(
        srs.g1[i],
        (G1Projective::generator() * tau.pow([i as u64])).into_affine()
      );
    }
  }

  #[test]
  fn dev_setup_validates() {
    Srs::unsafe_dev_setup(1 << 5, b"validate-test").validate().unwrap();
  }

  #[test]
  fn corrupted_power_rejected() {
    let mut srs = Srs::unsafe_dev_setup(1 << 5, b"validate-test");
    srs.g1[7] =
      (G1Projective::from(srs.g1[7]) + G1Projective::generator()).into_affine();
    assert!(srs.validate().is_err());
  }

  #[test]
  fn mismatched_tau_g2_rejected() {
    let mut srs = Srs::unsafe_dev_setup(1 << 5, b"validate-test");
    srs.tau_g2 = (G2Projective::from(srs.tau_g2) + G2Projective::generator())
      .into_affine();
    assert!(srs.validate().is_err());
  }
}
