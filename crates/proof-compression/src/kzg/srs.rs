//! KZG public parameters: a G1 prefix, G2 anchors and authenticated degree metadata.
//! Imported parameters need validated point decoding, [`Srs::validate`] and
//! trusted provenance. Consistency does not establish an unknown trapdoor.
//! The declared public degree is independent of the locally loaded prefix.
//! [`Srs::unsafe_dev_setup`] reveals its trapdoor and is only for tests.

use super::curve::{
  Fr, G1Affine, G1Projective, G2Affine, G2Projective, PairingCurve,
};
use ark_ec::{
  AffineRepr, CurveGroup, PrimeGroup, VariableBaseMSM, pairing::Pairing,
};
use ark_ff::{Field, PrimeField, Zero};
use ark_serialize::CanonicalSerialize;
use p3_maybe_rayon::prelude::*;
use std::io::{self, Write};

pub mod ignition;

const PUBLIC_SETUP_DOMAIN: &[u8] =
  b"multi-stark/kzg/bn254/known-trapdoor-public-degree/v1";
const DEV_TAU_DOMAIN: &[u8] = b"multi-stark/kzg/bn254/dev-srs";
const VALIDATION_DOMAIN: &[u8] = b"multi-stark/kzg/bn254/srs-validate/v4";

/// Identity and maximum polynomial degree of the complete public parameter set.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PublicSetup {
  pub max_degree: usize,
  pub id: [u8; 32],
}

impl PublicSetup {
  pub fn known_trapdoor(max_degree: usize, seed: &[u8]) -> Self {
    assert!(max_degree >= 1 && max_degree.checked_add(1).is_some());
    let mut hash = blake3::Hasher::new();
    hash.update(PUBLIC_SETUP_DOMAIN);
    hash.update(&(max_degree as u64).to_le_bytes());
    hash.update(blake3::hash(seed).as_bytes());
    Self { max_degree, id: *hash.finalize().as_bytes() }
  }
}

/// The development trapdoor of `seed`.
pub(super) fn dev_tau(seed: &[u8]) -> Fr {
  let mut wide = [0u8; 64];
  blake3::Hasher::new()
    .update(DEV_TAU_DOMAIN)
    .update(seed)
    .finalize_xof()
    .fill(&mut wide);
  Fr::from_le_bytes_mod_order(&wide)
}

/// `[G, τG, τ²G, …]` in G1 and `[H, τH]` in G2.
pub struct Srs {
  pub g1: Vec<G1Affine>,
  pub g2: G2Affine,
  pub tau_g2: G2Affine,
  pub public_setup: PublicSetup,
}

impl Srs {
  /// Reuse or populate a shared cache directory holding one file per
  /// prefix length and seed, so stages of different heights share one
  /// trusted-local location.
  pub fn unsafe_dev_setup_prefix_in_cache_directory(
    max_len: usize,
    public_max_degree: usize,
    seed: &[u8],
    directory: impl AsRef<std::path::Path>,
  ) -> io::Result<Self> {
    super::srs_cache::cached_in_directory(
      max_len,
      public_max_degree,
      seed,
      directory.as_ref(),
    )
  }

  /// Authenticate setup metadata independently before importing public powers.
  pub fn from_public_powers(
    g1: Vec<G1Affine>,
    g2: G2Affine,
    tau_g2: G2Affine,
    public_setup: PublicSetup,
  ) -> Result<Self, &'static str> {
    if g1.par_iter().any(|p| {
      !p.is_on_curve() || !p.is_in_correct_subgroup_assuming_on_curve()
    }) || [&g2, &tau_g2].into_iter().any(|p| {
      !p.is_on_curve() || !p.is_in_correct_subgroup_assuming_on_curve()
    }) {
      return Err("invalid public parameter point");
    }
    let srs = Self { g1, g2, tau_g2, public_setup };
    srs.validate()?;
    Ok(srs)
  }

  /// Number of locally loaded powers, independent of the full public degree.
  #[inline]
  pub fn max_len(&self) -> usize {
    self.g1.len()
  }

  /// Check nonzero anchors, public degree metadata and the powers relation
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
    if self.public_setup.max_degree < self.max_len() - 1
      || self.public_setup.max_degree.checked_add(1).is_none()
    {
      return Err("invalid public degree allowance");
    }

    // Preserve the validation challenge's exact encoding without retaining a
    // second, serialized copy of all powers (12 GiB for a 2^28 BLS12-381 SRS).
    struct HashWriter(blake3::Hasher);
    impl Write for HashWriter {
      fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        self.0.update(bytes);
        Ok(bytes.len())
      }
      fn flush(&mut self) -> io::Result<()> {
        Ok(())
      }
    }
    let mut writer = HashWriter(blake3::Hasher::new());
    writer.0.update(VALIDATION_DOMAIN);
    writer.0.update(&self.public_setup.id);
    writer.0.update(&(self.public_setup.max_degree as u64).to_le_bytes());
    self.g1.serialize_compressed(&mut writer).expect("infallible hash writer");
    self.g2.serialize_compressed(&mut writer).expect("infallible hash writer");
    self
      .tau_g2
      .serialize_compressed(&mut writer)
      .expect("infallible hash writer");
    let mut wide = [0u8; 64];
    writer.0.finalize_xof().fill(&mut wide);
    let r = Fr::from_le_bytes_mod_order(&wide);
    if r.is_zero() {
      return Err("zero parameter-validation challenge");
    }

    // Bound both powers and MSM digit/bucket scratch independently of SRS
    // length. All adjacent pairs still participate with their original weight.
    const CHUNK: usize = 1 << 16;
    let concurrency = current_num_threads().div_ceil(8).min(4);
    let mut low = G1Projective::zero();
    let mut high = G1Projective::zero();
    for start in (0..self.g1.len() - 1).step_by(CHUNK * concurrency) {
      let end = (start + CHUNK * concurrency).min(self.g1.len() - 1);
      let parts: Vec<_> = self.g1[start..end]
        .par_chunks(CHUNK)
        .enumerate()
        .map(|(index, points)| {
          let offset = start + index * CHUNK;
          let mut acc = r.pow([offset as u64]);
          let powers: Vec<_> = (0..points.len())
            .map(|_| {
              let value = acc;
              acc *= r;
              value
            })
            .collect();
          (
            G1Projective::msm(points, &powers).expect("equal lengths"),
            G1Projective::msm(
              &self.g1[offset + 1..offset + 1 + points.len()],
              &powers,
            )
            .expect("equal lengths"),
          )
        })
        .collect();
      for (a, b) in parts {
        low += a;
        high += b;
      }
    }
    // e(high, H) = e(low, τH)  ⇔  e(high, H)·e(−low, τH) = 1.
    let check = PairingCurve::multi_pairing(
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
    Self::unsafe_dev_setup_prefix(max_len, max_len - 1, seed)
  }

  /// Known-trapdoor powers with an identity independent of the loaded prefix.
  pub fn unsafe_dev_setup_prefix(
    max_len: usize,
    public_max_degree: usize,
    seed: &[u8],
  ) -> Self {
    assert!(max_len >= 2 && max_len.is_power_of_two());
    assert!(public_max_degree >= max_len - 1);
    let public_setup = PublicSetup::known_trapdoor(public_max_degree, seed);
    let tau = dev_tau(seed);

    let g1_gen = G1Projective::generator();
    // τ-powers in independent chunks (each chunk seeds itself with
    // τ^start), so the scalar multiplications parallelize under the
    // `parallel` feature; serial otherwise. A bounded fixed-base table
    // amortizes the generator multiplication across powers without a table
    // whose size grows with the SRS degree.
    let chunk = 1usize << 14;
    let table = ark_ec::scalar_mul::BatchMulPreprocessing::new(
      g1_gen,
      max_len.min(1 << 12),
    );
    let mut g1 = vec![G1Affine::identity(); max_len];
    g1.par_chunks_mut(chunk).enumerate().for_each(|(i, dst)| {
      let mut acc = tau.pow([(i * chunk) as u64]);
      let scalars: Vec<_> = (0..dst.len())
        .map(|_| {
          let value = acc;
          acc *= tau;
          value
        })
        .collect();
      dst.copy_from_slice(&table.batch_mul(&scalars));
    });
    let g2_gen = G2Projective::generator();
    Self {
      g1,
      g2: g2_gen.into_affine(),
      tau_g2: (g2_gen * tau).into_affine(),
      public_setup,
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn development_identity_and_anchors_are_curve_specific() {
    let seed = b"curve-specific-setup";
    let srs = Srs::unsafe_dev_setup(4, seed);
    let mut legacy_id = blake3::Hasher::new();
    legacy_id.update(b"multi-stark/kzg/known-trapdoor-public-degree/v1");
    legacy_id.update(&3u64.to_le_bytes());
    legacy_id.update(blake3::hash(seed).as_bytes());
    assert_ne!(srs.public_setup.id, *legacy_id.finalize().as_bytes());

    let mut wide = [0; 64];
    blake3::Hasher::new()
      .update(b"multi-stark/kzg/dev-srs")
      .update(seed)
      .finalize_xof()
      .fill(&mut wide);
    let legacy_tau = Fr::from_le_bytes_mod_order(&wide);
    assert_ne!(dev_tau(seed), legacy_tau);
    assert_ne!(
      srs.g1[1],
      (G1Projective::generator() * legacy_tau).into_affine()
    );
    assert_ne!(
      srs.tau_g2,
      (G2Projective::generator() * legacy_tau).into_affine()
    );
    srs.validate().unwrap();
  }

  #[test]
  fn development_powers_match_naive_at_chunk_boundaries() {
    let seed = b"chunk-powers";
    let srs = Srs::unsafe_dev_setup(1 << 16, seed);
    let mut wide = [0u8; 64];
    blake3::Hasher::new()
      .update(DEV_TAU_DOMAIN)
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
  fn validation_covers_chunk_boundaries() {
    let mut srs = Srs::unsafe_dev_setup(1 << 17, b"validation-chunks");
    srs.validate().unwrap();
    for index in [(1 << 16) - 1, 1 << 16, (1 << 16) + 1, (1 << 17) - 2] {
      let saved = srs.g1[index];
      srs.g1[index] = srs.g1[index + 1];
      assert!(srs.validate().is_err(), "accepted changed power {index}");
      srs.g1[index] = saved;
    }
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
