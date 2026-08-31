use crate::{
  FflonkVerificationKeyError, FflonkVerificationKeyV1, KzgCommitmentV1,
  KzgError, KzgUniversalSrsV1, PlonkArithmetizationV1, PlonkCellV1,
  commit_polynomial,
};
use ark_bls12_381::Fr;
use ark_ff::{BigInteger, FftField, Field, PrimeField, Zero};
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
use std::fmt;

const PREPROCESSING_DIGEST_DOMAIN: &[u8] =
  b"ix:stage4:fflonk-preprocessing:bls12-381:v1";

/// Maximum coefficient degree required by the Stage 4 FFLONK prover profile.
/// C2 has the largest bound and needs powers through `9*n + 17` inclusive.
pub const FFLONK_SRS_DOMAIN_MULTIPLIER: u64 = 9;
pub const FFLONK_SRS_DEGREE_OVERHEAD: u64 = 17;

/// One domain-evaluation polynomial and its coefficient-form IFFT.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FflonkPreprocessedPolynomialV1 {
  evaluations: Vec<Fr>,
  coefficients: Vec<Fr>,
}

impl FflonkPreprocessedPolynomialV1 {
  pub fn evaluations(&self) -> &[Fr] {
    &self.evaluations
  }

  pub fn coefficients(&self) -> &[Fr] {
    &self.coefficients
  }
}

/// Circuit-specific selector and copy-permutation polynomials.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FflonkPreprocessedPolynomialsV1 {
  pub ql: FflonkPreprocessedPolynomialV1,
  pub qr: FflonkPreprocessedPolynomialV1,
  pub qm: FflonkPreprocessedPolynomialV1,
  pub qo: FflonkPreprocessedPolynomialV1,
  pub qc: FflonkPreprocessedPolynomialV1,
  pub sigma1: FflonkPreprocessedPolynomialV1,
  pub sigma2: FflonkPreprocessedPolynomialV1,
  pub sigma3: FflonkPreprocessedPolynomialV1,
}

/// Materialized development proving key for one canonical Stage 4 relation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FflonkPreprocessedCircuitV1 {
  arithmetization: PlonkArithmetizationV1,
  polynomials: FflonkPreprocessedPolynomialsV1,
  c0_coefficients: Vec<Fr>,
  c0_commitment: KzgCommitmentV1,
  verification_key: FflonkVerificationKeyV1,
  required_srs_degree: u64,
  digest: [u8; 32],
}

impl FflonkPreprocessedCircuitV1 {
  pub fn arithmetization(&self) -> &PlonkArithmetizationV1 {
    &self.arithmetization
  }

  pub fn polynomials(&self) -> &FflonkPreprocessedPolynomialsV1 {
    &self.polynomials
  }

  pub fn c0_coefficients(&self) -> &[Fr] {
    &self.c0_coefficients
  }

  #[must_use]
  pub const fn c0_commitment(&self) -> KzgCommitmentV1 {
    self.c0_commitment
  }

  #[must_use]
  pub const fn verification_key(&self) -> FflonkVerificationKeyV1 {
    self.verification_key
  }

  #[must_use]
  pub const fn required_srs_degree(&self) -> u64 {
    self.required_srs_degree
  }

  #[must_use]
  pub const fn digest(&self) -> [u8; 32] {
    self.digest
  }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FflonkPreprocessingError {
  UnsupportedDomain { domain_size: u64 },
  CountOverflow,
  Srs(KzgError),
  VerificationKey(FflonkVerificationKeyError),
}

impl fmt::Display for FflonkPreprocessingError {
  fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::UnsupportedDomain { domain_size } => write!(
        formatter,
        "cannot construct an FFT domain of size {domain_size} for FFLONK preprocessing",
      ),
      Self::CountOverflow => {
        formatter.write_str("FFLONK preprocessing size overflow")
      },
      Self::Srs(error) => error.fmt(formatter),
      Self::VerificationKey(error) => error.fmt(formatter),
    }
  }
}

impl std::error::Error for FflonkPreprocessingError {
  fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
    match self {
      Self::Srs(error) => Some(error),
      Self::VerificationKey(error) => Some(error),
      Self::UnsupportedDomain { .. } | Self::CountOverflow => None,
    }
  }
}

impl From<KzgError> for FflonkPreprocessingError {
  fn from(error: KzgError) -> Self {
    Self::Srs(error)
  }
}

impl From<FflonkVerificationKeyError> for FflonkPreprocessingError {
  fn from(error: FflonkVerificationKeyError) -> Self {
    Self::VerificationKey(error)
  }
}

/// Returns the universal SRS degree required for a domain of size `n`.
pub fn required_fflonk_srs_degree(
  domain_size: u64,
) -> Result<u64, FflonkPreprocessingError> {
  domain_size
    .checked_mul(FFLONK_SRS_DOMAIN_MULTIPLIER)
    .and_then(|degree| degree.checked_add(FFLONK_SRS_DEGREE_OVERHEAD))
    .ok_or(FflonkPreprocessingError::CountOverflow)
}

/// Computes selector and sigma polynomials, packs and commits C0, and returns
/// the validated circuit-specific verification key.
pub fn preprocess_fflonk(
  srs: &KzgUniversalSrsV1,
  arithmetization: PlonkArithmetizationV1,
) -> Result<FflonkPreprocessedCircuitV1, FflonkPreprocessingError> {
  let domain_size_u64 = arithmetization.census().domain_size;
  let domain_size = usize::try_from(domain_size_u64)
    .map_err(|_| FflonkPreprocessingError::CountOverflow)?;
  let domain = Radix2EvaluationDomain::<Fr>::new(domain_size).ok_or(
    FflonkPreprocessingError::UnsupportedDomain {
      domain_size: domain_size_u64,
    },
  )?;
  if domain.size() != domain_size {
    return Err(FflonkPreprocessingError::UnsupportedDomain {
      domain_size: domain_size_u64,
    });
  }
  let required_srs_degree = required_fflonk_srs_degree(domain_size_u64)?;
  srs.ensure_degree(
    usize::try_from(required_srs_degree)
      .map_err(|_| FflonkPreprocessingError::CountOverflow)?,
  )?;

  let k1 = Fr::GENERATOR;
  let k2 = k1.square();
  let sigma_evaluations = sigma_evaluations(
    arithmetization.sigma(),
    domain.elements().collect::<Vec<_>>().as_slice(),
    k1,
    k2,
  )?;
  let gates = arithmetization.gates();
  let polynomials = FflonkPreprocessedPolynomialsV1 {
    ql: polynomial(&domain, gates.iter().map(|gate| gate.ql).collect()),
    qr: polynomial(&domain, gates.iter().map(|gate| gate.qr).collect()),
    qm: polynomial(&domain, gates.iter().map(|gate| gate.qm).collect()),
    qo: polynomial(&domain, gates.iter().map(|gate| gate.qo).collect()),
    qc: polynomial(&domain, gates.iter().map(|gate| gate.qc).collect()),
    sigma1: polynomial(&domain, sigma_evaluations[0].clone()),
    sigma2: polynomial(&domain, sigma_evaluations[1].clone()),
    sigma3: polynomial(&domain, sigma_evaluations[2].clone()),
  };
  let c0_coefficients = pack_c0(&polynomials, domain_size)?;
  let c0_commitment = commit_polynomial(srs, &c0_coefficients)?;
  let verification_key = FflonkVerificationKeyV1::new(
    usize::try_from(arithmetization.census().public_input_rows)
      .map_err(|_| FflonkPreprocessingError::CountOverflow)?,
    domain_size_u64,
    k1,
    k2,
    c0_commitment.0,
    srs.verifier_key(),
  )?;
  debug_assert_eq!(verification_key.omega(), domain.group_gen());
  let digest = preprocessing_digest(
    &arithmetization,
    &polynomials,
    &c0_coefficients,
    srs.digest(),
    required_srs_degree,
  );
  Ok(FflonkPreprocessedCircuitV1 {
    arithmetization,
    polynomials,
    c0_coefficients,
    c0_commitment,
    verification_key,
    required_srs_degree,
    digest,
  })
}

fn polynomial(
  domain: &Radix2EvaluationDomain<Fr>,
  evaluations: Vec<Fr>,
) -> FflonkPreprocessedPolynomialV1 {
  debug_assert_eq!(evaluations.len(), domain.size());
  let coefficients = domain.ifft(&evaluations);
  FflonkPreprocessedPolynomialV1 { evaluations, coefficients }
}

fn sigma_evaluations(
  sigma: &[Vec<PlonkCellV1>; 3],
  omega_powers: &[Fr],
  k1: Fr,
  k2: Fr,
) -> Result<[Vec<Fr>; 3], FflonkPreprocessingError> {
  let cosets = [Fr::ONE, k1, k2];
  let mut output: [Vec<Fr>; 3] =
    core::array::from_fn(|_| Vec::with_capacity(omega_powers.len()));
  for (column, targets) in sigma.iter().enumerate() {
    if targets.len() != omega_powers.len() {
      return Err(FflonkPreprocessingError::CountOverflow);
    }
    for target in targets {
      let row = usize::try_from(target.row)
        .map_err(|_| FflonkPreprocessingError::CountOverflow)?;
      let omega =
        omega_powers.get(row).ok_or(FflonkPreprocessingError::CountOverflow)?;
      let coset = cosets
        .get(usize::from(target.column))
        .ok_or(FflonkPreprocessingError::CountOverflow)?;
      output[column].push(*coset * omega);
    }
  }
  Ok(output)
}

fn pack_c0(
  polynomials: &FflonkPreprocessedPolynomialsV1,
  domain_size: usize,
) -> Result<Vec<Fr>, FflonkPreprocessingError> {
  let packed_len = domain_size
    .checked_mul(8)
    .ok_or(FflonkPreprocessingError::CountOverflow)?;
  let mut packed = vec![Fr::zero(); packed_len];
  for (offset, coefficients) in [
    polynomials.ql.coefficients(),
    polynomials.qr.coefficients(),
    polynomials.qo.coefficients(),
    polynomials.qm.coefficients(),
    polynomials.qc.coefficients(),
    polynomials.sigma1.coefficients(),
    polynomials.sigma2.coefficients(),
    polynomials.sigma3.coefficients(),
  ]
  .into_iter()
  .enumerate()
  {
    if coefficients.len() != domain_size {
      return Err(FflonkPreprocessingError::CountOverflow);
    }
    for (degree, coefficient) in coefficients.iter().enumerate() {
      packed[8 * degree + offset] = *coefficient;
    }
  }
  Ok(packed)
}

fn preprocessing_digest(
  arithmetization: &PlonkArithmetizationV1,
  polynomials: &FflonkPreprocessedPolynomialsV1,
  c0_coefficients: &[Fr],
  srs_digest: [u8; 32],
  required_srs_degree: u64,
) -> [u8; 32] {
  let mut hasher = blake3::Hasher::new();
  hasher.update(PREPROCESSING_DIGEST_DOMAIN);
  hasher.update(&arithmetization.r1cs_digest());
  hasher.update(&arithmetization.census().domain_size.to_le_bytes());
  hasher.update(&required_srs_degree.to_le_bytes());
  hasher.update(&srs_digest);
  for polynomial in [
    &polynomials.ql,
    &polynomials.qr,
    &polynomials.qm,
    &polynomials.qo,
    &polynomials.qc,
    &polynomials.sigma1,
    &polynomials.sigma2,
    &polynomials.sigma3,
  ] {
    hash_fields(&mut hasher, polynomial.coefficients());
  }
  hash_fields(&mut hasher, c0_coefficients);
  *hasher.finalize().as_bytes()
}

fn hash_fields(hasher: &mut blake3::Hasher, values: &[Fr]) {
  hasher.update(
    &u64::try_from(values.len())
      .expect("field vector length fits u64")
      .to_le_bytes(),
  );
  for value in values {
    let mut encoded = [0_u8; 32];
    let bytes = value.into_bigint().to_bytes_le();
    encoded[..bytes.len()].copy_from_slice(&bytes);
    hasher.update(&encoded);
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::{arithmetize_r1cs, evaluate_polynomial};
  use ark_bls12_381::{G1Affine, G2Affine};
  use ark_ec::{AffineRepr, CurveGroup};
  use ix_terminal_circuit::{ConstraintPhase, LinearCombination, R1csBuilder};

  fn test_srs(max_degree: usize, tau: Fr) -> KzgUniversalSrsV1 {
    let mut scalar = Fr::ONE;
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

  fn fixture() -> PlonkArithmetizationV1 {
    let mut builder = R1csBuilder::new();
    let public = builder.alloc_public(Fr::from(3_u64)).unwrap();
    let private = builder.alloc_private(Fr::from(5_u64)).unwrap();
    let product = builder.alloc_private(Fr::from(15_u64)).unwrap();
    builder.enforce(
      ConstraintPhase::Statement,
      LinearCombination::from_variable(public),
      LinearCombination::from_variable(private),
      LinearCombination::from_variable(product),
    );
    let (r1cs, _) = builder.finish().unwrap();
    arithmetize_r1cs(&r1cs).unwrap()
  }

  #[test]
  fn preprocessing_round_trips_selector_and_sigma_evaluations() {
    let arithmetization = fixture();
    let domain_size = arithmetization.census().domain_size;
    let srs = test_srs(
      usize::try_from(required_fflonk_srs_degree(domain_size).unwrap())
        .unwrap(),
      Fr::from(13_u64),
    );
    let preprocessed = preprocess_fflonk(&srs, arithmetization).unwrap();
    let domain =
      Radix2EvaluationDomain::<Fr>::new(usize::try_from(domain_size).unwrap())
        .unwrap();
    for polynomial in [
      &preprocessed.polynomials().ql,
      &preprocessed.polynomials().qr,
      &preprocessed.polynomials().qm,
      &preprocessed.polynomials().qo,
      &preprocessed.polynomials().qc,
      &preprocessed.polynomials().sigma1,
      &preprocessed.polynomials().sigma2,
      &preprocessed.polynomials().sigma3,
    ] {
      assert_eq!(
        domain.fft(polynomial.coefficients()),
        polynomial.evaluations()
      );
    }
    assert_eq!(
      preprocessed.c0_commitment(),
      commit_polynomial(&srs, preprocessed.c0_coefficients(),).unwrap()
    );
    assert_eq!(
      preprocessed.required_srs_degree(),
      FFLONK_SRS_DOMAIN_MULTIPLIER * domain_size + FFLONK_SRS_DEGREE_OVERHEAD,
    );
    assert_ne!(preprocessed.digest(), [0_u8; 32]);
  }

  #[test]
  fn c0_interleaving_evaluates_to_the_eight_packed_polynomials() {
    let arithmetization = fixture();
    let required =
      required_fflonk_srs_degree(arithmetization.census().domain_size).unwrap();
    let srs = test_srs(usize::try_from(required).unwrap(), Fr::from(17_u64));
    let preprocessed = preprocess_fflonk(&srs, arithmetization).unwrap();
    let x = Fr::from(19_u64);
    let x8 = x.pow([8]);
    let polynomials = preprocessed.polynomials();
    let expected = evaluate_polynomial(polynomials.ql.coefficients(), x8)
      + x * evaluate_polynomial(polynomials.qr.coefficients(), x8)
      + x.pow([2]) * evaluate_polynomial(polynomials.qo.coefficients(), x8)
      + x.pow([3]) * evaluate_polynomial(polynomials.qm.coefficients(), x8)
      + x.pow([4]) * evaluate_polynomial(polynomials.qc.coefficients(), x8)
      + x.pow([5]) * evaluate_polynomial(polynomials.sigma1.coefficients(), x8)
      + x.pow([6]) * evaluate_polynomial(polynomials.sigma2.coefficients(), x8)
      + x.pow([7]) * evaluate_polynomial(polynomials.sigma3.coefficients(), x8);
    assert_eq!(
      evaluate_polynomial(preprocessed.c0_coefficients(), x),
      expected
    );
  }

  #[test]
  fn rejects_an_srs_that_only_covers_c0() {
    let arithmetization = fixture();
    let domain_size = arithmetization.census().domain_size;
    let c0_degree = usize::try_from(8 * domain_size - 1).unwrap();
    let srs = test_srs(c0_degree, Fr::from(23_u64));
    assert_eq!(
      preprocess_fflonk(&srs, arithmetization),
      Err(FflonkPreprocessingError::Srs(KzgError::DegreeTooLarge {
        degree: usize::try_from(
          required_fflonk_srs_degree(domain_size).unwrap(),
        )
        .unwrap(),
        max_degree: c0_degree,
      })),
    );
  }
}
