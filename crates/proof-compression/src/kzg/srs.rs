//! KZG public parameters: a G1 prefix, G2 anchors and authenticated degree metadata.
//! Imported parameters need validated point decoding, [`Srs::validate`] and
//! trusted provenance. Consistency does not establish an unknown trapdoor.
//! The declared public degree is independent of the locally loaded prefix.
//! [`Srs::unsafe_dev_setup`] reveals its trapdoor and is only for tests.

use super::curve::{
  Bn254, G1AffineOf, G1ProjectiveOf, G2AffineOf, G2ProjectiveOf, KzgCurve,
};
use ark_ec::{
  AffineRepr, CurveGroup, PrimeGroup, VariableBaseMSM, pairing::Pairing,
};
use ark_ff::{Field, PrimeField, Zero};
use ark_serialize::CanonicalSerialize;
use p3_maybe_rayon::prelude::*;
use std::io::{self, Write};

pub mod filecoin;
pub mod gnark;

/// Identity and maximum polynomial degree of the complete public parameter set.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PublicSetup {
  pub max_degree: usize,
  pub id: [u8; 32],
}

impl PublicSetup {
  /// Derive the deterministic setup identity for a known-trapdoor dev SRS on BN254.
  pub fn known_trapdoor(max_degree: usize, seed: &[u8]) -> Self {
    Self::known_trapdoor_for::<Bn254>(max_degree, seed)
  }

  /// Derive the deterministic setup identity for a known-trapdoor dev SRS on curve `C`.
  pub fn known_trapdoor_for<C: KzgCurve>(
    max_degree: usize,
    seed: &[u8],
  ) -> Self {
    assert!(max_degree >= 1 && max_degree.checked_add(1).is_some());
    let mut hash = blake3::Hasher::new();
    hash.update(C::PUBLIC_SETUP_DOMAIN);
    hash.update(&(max_degree as u64).to_le_bytes());
    hash.update(blake3::hash(seed).as_bytes());
    Self { max_degree, id: *hash.finalize().as_bytes() }
  }
}

/// The development trapdoor of `seed` on curve `C`.
pub(super) fn dev_tau<C: KzgCurve>(seed: &[u8]) -> C::Fr {
  let mut wide = [0u8; 64];
  blake3::Hasher::new()
    .update(C::DEV_TAU_DOMAIN)
    .update(seed)
    .finalize_xof()
    .fill(&mut wide);
  C::Fr::from_le_bytes_mod_order(&wide)
}

/// `[G, τG, τ²G, …]` in G1 and `[H, τH]` in G2.
pub struct Srs<C: KzgCurve = Bn254> {
  pub g1: Vec<G1AffineOf<C>>,
  pub g2: G2AffineOf<C>,
  pub tau_g2: G2AffineOf<C>,
  pub public_setup: PublicSetup,
}

impl<C: KzgCurve> Srs<C> {
  /// Reuse or populate a shared cache directory holding one file per
  /// curve, prefix length and seed, so stages of different heights share one
  /// trusted-local location.
  pub fn unsafe_dev_setup_prefix_in_cache_directory(
    max_len: usize,
    public_max_degree: usize,
    seed: &[u8],
    directory: impl AsRef<std::path::Path>,
  ) -> io::Result<Self> {
    super::dev_srs_cache::cached_in_directory::<C>(
      max_len,
      public_max_degree,
      seed,
      directory.as_ref(),
    )
  }

  /// Authenticate setup metadata independently before importing public powers.
  pub fn from_public_powers(
    g1: Vec<G1AffineOf<C>>,
    g2: G2AffineOf<C>,
    tau_g2: G2AffineOf<C>,
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
    // Bound both powers and MSM digit/bucket scratch independently of SRS
    // length. All adjacent pairs still participate with their original weight.
    const CHUNK: usize = 1 << 16;
    self.validate_with_chunk(CHUNK)
  }

  fn validate_with_chunk(&self, chunk: usize) -> Result<(), &'static str> {
    assert!(chunk > 0);
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
    // second, serialized copy of all powers (gigabytes for a 2^28 SRS).
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
    writer.0.update(C::VALIDATION_DOMAIN);
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
    let r = C::Fr::from_le_bytes_mod_order(&wide);
    if r.is_zero() {
      return Err("zero parameter-validation challenge");
    }

    let concurrency = current_num_threads().div_ceil(8).min(4);
    let mut low = G1ProjectiveOf::<C>::zero();
    let mut high = G1ProjectiveOf::<C>::zero();
    for start in (0..self.g1.len() - 1).step_by(chunk * concurrency) {
      let end = (start + chunk * concurrency).min(self.g1.len() - 1);
      let parts: Vec<_> = self.g1[start..end]
        .par_chunks(chunk)
        .enumerate()
        .map(|(index, points)| {
          let offset = start + index * chunk;
          let mut acc = r.pow([offset as u64]);
          let powers: Vec<_> = (0..points.len())
            .map(|_| {
              let value = acc;
              acc *= r;
              value
            })
            .collect();
          (
            G1ProjectiveOf::<C>::msm(points, &powers).expect("equal lengths"),
            G1ProjectiveOf::<C>::msm(
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
    let check = C::PairingCurve::multi_pairing(
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
    // τ-powers in independent chunks (each chunk seeds itself with
    // τ^start), so the scalar multiplications parallelize under the
    // `parallel` feature; serial otherwise.
    Self::unsafe_dev_setup_prefix_with_chunk(
      max_len,
      public_max_degree,
      seed,
      1usize << 14,
    )
  }

  fn unsafe_dev_setup_prefix_with_chunk(
    max_len: usize,
    public_max_degree: usize,
    seed: &[u8],
    chunk: usize,
  ) -> Self {
    assert!(chunk > 0);
    assert!(max_len >= 2 && max_len.is_power_of_two());
    assert!(public_max_degree >= max_len - 1);
    let public_setup =
      PublicSetup::known_trapdoor_for::<C>(public_max_degree, seed);
    let tau = dev_tau::<C>(seed);

    let g1_gen = G1ProjectiveOf::<C>::generator();
    // A bounded fixed-base table amortizes the generator multiplication across
    // powers without a table whose size grows with the SRS degree.
    let table = ark_ec::scalar_mul::BatchMulPreprocessing::new(
      g1_gen,
      max_len.min(1 << 12),
    );
    let mut g1 = vec![G1AffineOf::<C>::identity(); max_len];
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
    let g2_gen = G2ProjectiveOf::<C>::generator();
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
  use crate::kzg::curve::Bls12381;

  fn check_srs_suite<C: KzgCurve>() {
    let seed = b"chunk-powers";
    let chunk = 1 << 6;
    let srs = Srs::<C>::unsafe_dev_setup_prefix_with_chunk(
      1 << 9,
      (1 << 9) - 1,
      seed,
      chunk,
    );
    assert_eq!(srs.g1, Srs::<C>::unsafe_dev_setup(1 << 9, seed).g1);
    let tau = dev_tau::<C>(seed);
    for i in [
      0,
      1,
      chunk - 1,
      chunk,
      2 * chunk - 1,
      2 * chunk,
      4 * chunk - 1,
      4 * chunk,
      (1 << 9) - 1,
    ] {
      assert_eq!(
        srs.g1[i],
        (G1ProjectiveOf::<C>::generator() * tau.pow([i as u64])).into_affine()
      );
    }

    let mut srs = Srs::<C>::unsafe_dev_setup(1 << 9, b"validation-chunks");
    srs.validate().unwrap();
    srs.validate_with_chunk(chunk).unwrap();
    for index in [
      chunk - 1,
      chunk,
      chunk + 1,
      4 * chunk - 1,
      4 * chunk,
      4 * chunk + 1,
      (1 << 9) - 2,
    ] {
      let saved = srs.g1[index];
      srs.g1[index] = srs.g1[index + 1];
      assert!(
        srs.validate_with_chunk(chunk).is_err(),
        "accepted changed power {index}"
      );
      srs.g1[index] = saved;
    }

    let mut srs = Srs::<C>::unsafe_dev_setup(1 << 5, b"validate-test");
    srs.g1[7] = (G1ProjectiveOf::<C>::from(srs.g1[7])
      + G1ProjectiveOf::<C>::generator())
    .into_affine();
    assert!(srs.validate().is_err());

    let mut srs = Srs::<C>::unsafe_dev_setup(1 << 5, b"validate-test");
    srs.tau_g2 = (G2ProjectiveOf::<C>::from(srs.tau_g2)
      + G2ProjectiveOf::<C>::generator())
    .into_affine();
    assert!(srs.validate().is_err());
  }

  #[test]
  fn srs_generation_and_validation_work_for_both_curves() {
    check_srs_suite::<Bn254>();
    check_srs_suite::<Bls12381>();
  }
}
