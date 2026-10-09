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
use ark_serialize::CanonicalSerialize;
use p3_maybe_rayon::prelude::*;

/// `[G, τG, τ²G, …]` in G1 and `[H, τH]` in G2.
pub struct Srs {
  pub g1: Vec<G1Affine>,
  pub g2: G2Affine,
  pub tau_g2: G2Affine,
  /// Entry k is τ^(max_len - 2^k) H, for degree-bound checks.
  pub degree_keys: Vec<G2Affine>,
}

impl Srs {
  /// Reuse a trusted-local cache of `unsafe_dev_setup` parameters. The
  /// checksum detects corruption, not malicious replacement. This never
  /// supplies a production SRS; its trapdoor remains public.
  pub fn unsafe_dev_setup_cached(
    max_len: usize,
    seed: &[u8],
    path: impl AsRef<std::path::Path>,
  ) -> Result<Self, ark_serialize::SerializationError> {
    super::srs_cache::cached(max_len, seed, path.as_ref())
  }

  /// The largest polynomial length (degree + 1) this SRS can commit.
  #[inline]
  pub fn max_len(&self) -> usize {
    self.g1.len()
  }

  /// Consistency check for user-supplied parameters: the G1 powers
  /// must form one geometric progression in the secret the G2 pair
  /// encodes — `e(g1[i+1], H) = e(g1[i], τH)` for every `i` — and the
  /// anchors must not be the identity. Batched into two MSMs and one
  /// 2-pairing product with a random combiner derived from the SRS
  /// bytes themselves (whoever fixed the SRS could not predict it).
  ///
  /// Subgroup membership is NOT checked here: obtain the points
  /// through validated deserialization (the arkworks default), which
  /// already enforces it.
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
  fn development_cache_matches_and_rejects_corruption_or_wrong_profile() {
    use std::io::{Seek, SeekFrom, Write};
    let path = std::env::temp_dir().join(format!(
      "kzg-dev-cache-{}-{}.bin",
      std::process::id(),
      std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos()
    ));
    let original = Srs::unsafe_dev_setup_cached(64, b"cache", &path).unwrap();
    let loaded = Srs::unsafe_dev_setup_cached(64, b"cache", &path).unwrap();
    assert_eq!(original.g1, loaded.g1);
    assert_eq!(original.g2, loaded.g2);
    assert_eq!(original.tau_g2, loaded.tau_g2);
    assert_eq!(original.degree_keys, loaded.degree_keys);
    loaded.validate().unwrap();
    assert!(Srs::unsafe_dev_setup_cached(32, b"cache", &path).is_err());
    assert!(Srs::unsafe_dev_setup_cached(64, b"other", &path).is_err());
    let mut file = std::fs::OpenOptions::new().write(true).open(&path).unwrap();
    file.seek(SeekFrom::End(-32)).unwrap();
    file.write_all(&[0; 32]).unwrap();
    assert!(Srs::unsafe_dev_setup_cached(64, b"cache", &path).is_err());
    file.set_len(0).unwrap();
    assert!(Srs::unsafe_dev_setup_cached(64, b"cache", &path).is_err());
    drop(file);
    std::fs::remove_file(path).unwrap();
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
