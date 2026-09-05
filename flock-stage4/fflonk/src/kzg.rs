use ark_bls12_381::{Bls12_381, Fr, G1Affine, G1Projective, G2Affine};
use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM, pairing::Pairing};
use ark_ff::{One, PrimeField, Zero};
use ark_serialize::CanonicalSerialize;
use core::fmt;

const SRS_DIGEST_DOMAIN: &[u8] = b"ix:stage4:kzg-srs:bls12-381:v1";
const SRS_BATCH_CHALLENGE_DOMAIN: &[u8] =
  b"ix:stage4:kzg-srs-batch-challenge:bls12-381:v1";

/// Universal BLS12-381 powers-of-tau material used by the Stage 4 backend.
///
/// `powers_of_g1[i] = tau^i G1`, while `tau_g2 = tau G2`. Construction
/// checks curve and prime-order subgroup membership before verifying a
/// Fiat--Shamir batched pairing relation across every consecutive G1 power.
/// Both degree-zero generators are pinned to Arkworks' canonical generators.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KzgUniversalSrsV1 {
  powers_of_g1: Vec<G1Affine>,
  g2: G2Affine,
  tau_g2: G2Affine,
  digest: [u8; 32],
}

impl KzgUniversalSrsV1 {
  pub fn new(
    powers_of_g1: Vec<G1Affine>,
    g2: G2Affine,
    tau_g2: G2Affine,
  ) -> Result<Self, KzgError> {
    if powers_of_g1.len() < 2 {
      return Err(KzgError::InsufficientPowers {
        required: 2,
        available: powers_of_g1.len(),
      });
    }
    if powers_of_g1[0] != G1Affine::generator() || g2 != G2Affine::generator() {
      return Err(KzgError::NonCanonicalGenerator);
    }
    if powers_of_g1.iter().any(AffineRepr::is_zero) || tau_g2.is_zero() {
      return Err(KzgError::IdentityInSrs);
    }
    for (index, point) in powers_of_g1.iter().enumerate() {
      if !point.is_on_curve()
        || !point.is_in_correct_subgroup_assuming_on_curve()
      {
        return Err(KzgError::InvalidG1Power { index });
      }
    }
    if !tau_g2.is_on_curve()
      || !tau_g2.is_in_correct_subgroup_assuming_on_curve()
    {
      return Err(KzgError::InvalidTauG2);
    }
    let digest = srs_digest(&powers_of_g1, &g2, &tau_g2)?;
    let challenge = srs_batch_challenge(digest);
    let powers = challenge_powers(challenge, powers_of_g1.len() - 1);
    let left = G1Projective::msm(&powers_of_g1[..powers.len()], &powers)
      .map_err(|_| KzgError::InternalShape)?;
    let right = G1Projective::msm(&powers_of_g1[1..], &powers)
      .map_err(|_| KzgError::InternalShape)?;
    if Bls12_381::pairing(left.into_affine(), tau_g2)
      != Bls12_381::pairing(right.into_affine(), g2)
    {
      return Err(KzgError::InconsistentPowers);
    }
    Ok(Self { powers_of_g1, g2, tau_g2, digest })
  }

  #[must_use]
  pub fn max_degree(&self) -> usize {
    self.powers_of_g1.len() - 1
  }

  #[must_use]
  pub const fn digest(&self) -> [u8; 32] {
    self.digest
  }

  pub fn powers_of_g1(&self) -> &[G1Affine] {
    &self.powers_of_g1
  }

  #[must_use]
  pub fn verifier_key(&self) -> KzgVerifierKeyV1 {
    KzgVerifierKeyV1 {
      g1: self.powers_of_g1[0],
      g2: self.g2,
      tau_g2: self.tau_g2,
      srs_digest: self.digest,
    }
  }

  pub fn ensure_degree(&self, degree: usize) -> Result<(), KzgError> {
    if degree > self.max_degree() {
      return Err(KzgError::DegreeTooLarge {
        degree,
        max_degree: self.max_degree(),
      });
    }
    Ok(())
  }
}

/// Constant-size KZG verifier material derived from a validated universal SRS.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct KzgVerifierKeyV1 {
  pub g1: G1Affine,
  pub g2: G2Affine,
  pub tau_g2: G2Affine,
  pub srs_digest: [u8; 32],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct KzgCommitmentV1(pub G1Affine);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct KzgOpeningV1 {
  pub point: Fr,
  pub value: Fr,
  pub witness: G1Affine,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum KzgError {
  InsufficientPowers { required: usize, available: usize },
  DegreeTooLarge { degree: usize, max_degree: usize },
  NonCanonicalGenerator,
  IdentityInSrs,
  InvalidG1Power { index: usize },
  InvalidTauG2,
  InconsistentPowers,
  Serialization,
  InternalShape,
}

impl fmt::Display for KzgError {
  fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::InsufficientPowers { required, available } => write!(
        formatter,
        "KZG SRS has {available} powers; at least {required} are required",
      ),
      Self::DegreeTooLarge { degree, max_degree } => write!(
        formatter,
        "polynomial degree {degree} exceeds KZG SRS degree {max_degree}",
      ),
      Self::NonCanonicalGenerator => {
        formatter.write_str("KZG SRS does not use canonical curve generators")
      },
      Self::IdentityInSrs => {
        formatter.write_str("KZG SRS contains an identity power")
      },
      Self::InvalidG1Power { index } => write!(
        formatter,
        "KZG SRS power {index} is not a valid BLS12-381 G1 subgroup point",
      ),
      Self::InvalidTauG2 => formatter
        .write_str("KZG SRS tau G2 is not a valid BLS12-381 G2 subgroup point"),
      Self::InconsistentPowers => {
        formatter.write_str("KZG SRS powers fail batched pairing consistency")
      },
      Self::Serialization => {
        formatter.write_str("KZG SRS point serialization failed")
      },
      Self::InternalShape => formatter.write_str("internal KZG shape mismatch"),
    }
  }
}

impl std::error::Error for KzgError {}

/// Commit to a coefficient-form polynomial in ascending degree order.
pub fn commit_polynomial(
  srs: &KzgUniversalSrsV1,
  coefficients: &[Fr],
) -> Result<KzgCommitmentV1, KzgError> {
  let live_len = coefficients
    .iter()
    .rposition(|coefficient| !coefficient.is_zero())
    .map_or(0, |degree| degree + 1);
  if live_len == 0 {
    return Ok(KzgCommitmentV1(G1Affine::identity()));
  }
  srs.ensure_degree(live_len - 1)?;
  let commitment =
    G1Projective::msm(&srs.powers_of_g1[..live_len], &coefficients[..live_len])
      .map_err(|_| KzgError::InternalShape)?;
  Ok(KzgCommitmentV1(commitment.into_affine()))
}

#[must_use]
pub fn evaluate_polynomial(coefficients: &[Fr], point: Fr) -> Fr {
  coefficients
    .iter()
    .rev()
    .fold(Fr::zero(), |value, coefficient| value * point + coefficient)
}

/// Open a coefficient-form polynomial at one point using synthetic division.
pub fn open_polynomial(
  srs: &KzgUniversalSrsV1,
  coefficients: &[Fr],
  point: Fr,
) -> Result<KzgOpeningV1, KzgError> {
  let value = evaluate_polynomial(coefficients, point);
  let quotient = quotient_by_linear(coefficients, point, value);
  let witness = commit_polynomial(srs, &quotient)?.0;
  Ok(KzgOpeningV1 { point, value, witness })
}

#[must_use]
pub fn verify_opening(
  verifier_key: &KzgVerifierKeyV1,
  commitment: &KzgCommitmentV1,
  opening: &KzgOpeningV1,
) -> bool {
  let value_commitment =
    verifier_key.g1.mul_bigint(opening.value.into_bigint());
  let left = (commitment.0.into_group() - value_commitment).into_affine();
  let point_g2 = verifier_key.g2.mul_bigint(opening.point.into_bigint());
  let right_g2 = (verifier_key.tau_g2.into_group() - point_g2).into_affine();
  Bls12_381::pairing(left, verifier_key.g2)
    == Bls12_381::pairing(opening.witness, right_g2)
}

fn quotient_by_linear(coefficients: &[Fr], point: Fr, value: Fr) -> Vec<Fr> {
  if coefficients.len() <= 1 {
    debug_assert_eq!(evaluate_polynomial(coefficients, point), value);
    return Vec::new();
  }
  let mut quotient = vec![Fr::zero(); coefficients.len() - 1];
  let mut accumulator = *coefficients.last().expect("nonconstant polynomial");
  for degree in (1..coefficients.len()).rev() {
    quotient[degree - 1] = accumulator;
    accumulator = coefficients[degree - 1] + point * accumulator;
  }
  debug_assert_eq!(accumulator, value);
  quotient
}

fn challenge_powers(challenge: Fr, count: usize) -> Vec<Fr> {
  let mut current = Fr::one();
  (0..count)
    .map(|_| {
      let output = current;
      current *= challenge;
      output
    })
    .collect()
}

fn srs_batch_challenge(digest: [u8; 32]) -> Fr {
  let mut hasher = blake3::Hasher::new();
  hasher.update(SRS_BATCH_CHALLENGE_DOMAIN);
  hasher.update(&digest);
  let mut challenge = Fr::from_le_bytes_mod_order(hasher.finalize().as_bytes());
  if challenge.is_zero() {
    challenge = Fr::one();
  }
  challenge
}

fn srs_digest(
  powers_of_g1: &[G1Affine],
  g2: &G2Affine,
  tau_g2: &G2Affine,
) -> Result<[u8; 32], KzgError> {
  let mut hasher = blake3::Hasher::new();
  hasher.update(SRS_DIGEST_DOMAIN);
  hasher.update(
    &u64::try_from(powers_of_g1.len())
      .map_err(|_| KzgError::InternalShape)?
      .to_le_bytes(),
  );
  for power in powers_of_g1 {
    hash_point(&mut hasher, power)?;
  }
  hash_point(&mut hasher, g2)?;
  hash_point(&mut hasher, tau_g2)?;
  Ok(*hasher.finalize().as_bytes())
}

fn hash_point<P: CanonicalSerialize>(
  hasher: &mut blake3::Hasher,
  point: &P,
) -> Result<(), KzgError> {
  let mut encoded = Vec::with_capacity(point.compressed_size());
  point
    .serialize_compressed(&mut encoded)
    .map_err(|_| KzgError::Serialization)?;
  hasher.update(
    &u64::try_from(encoded.len())
      .map_err(|_| KzgError::InternalShape)?
      .to_le_bytes(),
  );
  hasher.update(&encoded);
  Ok(())
}

#[cfg(test)]
mod tests {
  use super::*;
  use ark_bls12_381::{Fq, Fq2};

  fn test_srs(max_degree: usize, tau: Fr) -> KzgUniversalSrsV1 {
    let mut scalar = Fr::one();
    let powers = (0..=max_degree)
      .map(|_| {
        let point = G1Affine::generator().mul_bigint(scalar.into_bigint());
        scalar *= tau;
        point.into_affine()
      })
      .collect();
    let tau_g2 =
      G2Affine::generator().mul_bigint(tau.into_bigint()).into_affine();
    KzgUniversalSrsV1::new(powers, G2Affine::generator(), tau_g2).unwrap()
  }

  #[test]
  fn commits_opens_and_verifies_a_nonconstant_polynomial() {
    let srs = test_srs(8, Fr::from(11u64));
    let polynomial =
      [Fr::from(3u64), Fr::from(5u64), Fr::from(8u64), Fr::from(13u64)];
    let point = Fr::from(17u64);
    let commitment = commit_polynomial(&srs, &polynomial).unwrap();
    let opening = open_polynomial(&srs, &polynomial, point).unwrap();
    assert_eq!(opening.value, evaluate_polynomial(&polynomial, point));
    assert!(verify_opening(&srs.verifier_key(), &commitment, &opening));
  }

  #[test]
  fn rejects_wrong_point_value_and_witness() {
    let srs = test_srs(6, Fr::from(7u64));
    let polynomial = [Fr::from(2u64), Fr::from(3u64), Fr::from(5u64)];
    let commitment = commit_polynomial(&srs, &polynomial).unwrap();
    let opening = open_polynomial(&srs, &polynomial, Fr::from(19u64)).unwrap();
    for bad in [
      KzgOpeningV1 { point: opening.point + Fr::one(), ..opening },
      KzgOpeningV1 { value: opening.value + Fr::one(), ..opening },
      KzgOpeningV1 { witness: G1Affine::generator(), ..opening },
    ] {
      assert!(!verify_opening(&srs.verifier_key(), &commitment, &bad));
    }
  }

  #[test]
  fn validates_all_srs_powers_in_one_batched_pairing_equation() {
    let srs = test_srs(8, Fr::from(23u64));
    let mut powers = srs.powers_of_g1.clone();
    powers[5] = G1Affine::generator();
    assert_eq!(
      KzgUniversalSrsV1::new(powers, srs.g2, srs.tau_g2),
      Err(KzgError::InconsistentPowers),
    );
  }

  #[test]
  fn rejects_torsion_in_an_otherwise_pairing_consistent_srs() {
    let srs = test_srs(1, Fr::from(13u64));
    let torsion = G1Affine::new_unchecked(Fq::from(0u64), Fq::from(2u64));
    assert!(torsion.is_on_curve());
    let mut powers = srs.powers_of_g1.clone();
    powers[1] = (powers[1].into_group() + torsion.into_group()).into_affine();
    assert!(!powers[1].is_in_correct_subgroup_assuming_on_curve());
    // A pairing consistency check alone does not detect this torsion point.
    assert_eq!(
      Bls12_381::pairing(powers[0], srs.tau_g2),
      Bls12_381::pairing(powers[1], srs.g2),
    );
    assert_eq!(
      KzgUniversalSrsV1::new(powers, srs.g2, srs.tau_g2),
      Err(KzgError::InvalidG1Power { index: 1 }),
    );
  }

  #[test]
  fn rejects_unchecked_off_curve_srs_points() {
    let srs = test_srs(2, Fr::from(13u64));
    let mut powers = srs.powers_of_g1.clone();
    powers[2] = G1Affine::new_unchecked(Fq::zero(), Fq::one());
    assert!(!powers[2].is_on_curve());
    assert_eq!(
      KzgUniversalSrsV1::new(powers, srs.g2, srs.tau_g2),
      Err(KzgError::InvalidG1Power { index: 2 }),
    );
    let tau_g2 = G2Affine::new_unchecked(Fq2::zero(), Fq2::one());
    assert!(!tau_g2.is_on_curve());
    assert_eq!(
      KzgUniversalSrsV1::new(srs.powers_of_g1, srs.g2, tau_g2),
      Err(KzgError::InvalidTauG2),
    );
  }

  #[test]
  fn rejects_tau_g2_outside_the_prime_order_subgroup() {
    let srs = test_srs(2, Fr::from(13u64));
    let tau_g2 = (0u64..)
      .find_map(|x| {
        G2Affine::get_point_from_x_unchecked(Fq2::from(x), false)
          .filter(|point| !point.is_in_correct_subgroup_assuming_on_curve())
      })
      .expect("BLS12-381 G2 has a nontrivial cofactor");
    assert_eq!(
      KzgUniversalSrsV1::new(srs.powers_of_g1, srs.g2, tau_g2),
      Err(KzgError::InvalidTauG2),
    );
  }

  #[test]
  fn rejects_a_polynomial_beyond_the_universal_degree() {
    let srs = test_srs(2, Fr::from(29u64));
    let error =
      commit_polynomial(&srs, &[Fr::one(), Fr::one(), Fr::one(), Fr::one()])
        .unwrap_err();
    assert_eq!(error, KzgError::DegreeTooLarge { degree: 3, max_degree: 2 },);
  }

  #[test]
  fn zero_and_constant_polynomials_have_identity_opening_witnesses() {
    let srs = test_srs(2, Fr::from(31u64));
    for polynomial in [vec![], vec![Fr::from(9u64)]] {
      let commitment = commit_polynomial(&srs, &polynomial).unwrap();
      let opening = open_polynomial(&srs, &polynomial, Fr::from(4u64)).unwrap();
      assert!(opening.witness.is_zero());
      assert!(verify_opening(&srs.verifier_key(), &commitment, &opening));
    }
  }
}
