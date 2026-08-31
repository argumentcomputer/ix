use crate::{
  FflonkChallengesV1, FflonkEvaluationRootsV1, FflonkProofV1,
  FflonkTranscriptError, FflonkVerificationKeyV1, derive_fflonk_challenges,
};
use ark_bls12_381::{Bls12_381, Fr, G1Affine};
use ark_ec::{CurveGroup, VariableBaseMSM, pairing::Pairing};
use ark_ff::{Field, One, Zero, batch_inversion};
use core::fmt;

/// Verifies one Stage 4 BLS12-381 FFLONK proof.
///
/// `Ok(false)` means the final KZG pairing equation did not hold. Malformed
/// proof points, input-shape mismatches, and negligible-probability singular
/// Fiat--Shamir challenges are reported as explicit errors.
pub fn verify_fflonk(
  verification_key: &FflonkVerificationKeyV1,
  proof: &FflonkProofV1,
  public_inputs: &[Fr],
) -> Result<bool, FflonkVerificationError> {
  validate_proof_points(proof)?;
  let (challenges, roots) =
    derive_fflonk_challenges(verification_key, proof, public_inputs)?;
  let equation = build_verification_equation(
    verification_key,
    proof,
    public_inputs,
    &challenges,
    &roots,
  )?;
  let a1 = <ark_bls12_381::G1Projective as VariableBaseMSM>::msm(
    &equation.msm_points,
    &equation.msm_scalars,
  )
  .unwrap_or_else(|_| unreachable!("fixed FFLONK MSM shapes agree"));
  Ok(
    Bls12_381::pairing(a1.into_affine(), verification_key.kzg().g2)
      == Bls12_381::pairing(
        equation.pairing_rhs,
        verification_key.kzg().tau_g2,
      ),
  )
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FflonkVerificationError {
  Transcript(FflonkTranscriptError),
  InvalidProofCommitment { index: usize },
  SingularChallenge { relation: &'static str },
}

impl fmt::Display for FflonkVerificationError {
  fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::Transcript(error) => error.fmt(formatter),
      Self::InvalidProofCommitment { index } => write!(
        formatter,
        "FFLONK proof commitment {index} is not a valid BLS12-381 G1 point",
      ),
      Self::SingularChallenge { relation } => write!(
        formatter,
        "FFLONK Fiat-Shamir challenges make {relation} singular",
      ),
    }
  }
}

impl std::error::Error for FflonkVerificationError {
  fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
    match self {
      Self::Transcript(error) => Some(error),
      Self::InvalidProofCommitment { .. } | Self::SingularChallenge { .. } => {
        None
      },
    }
  }
}

impl From<FflonkTranscriptError> for FflonkVerificationError {
  fn from(error: FflonkTranscriptError) -> Self {
    Self::Transcript(error)
  }
}

pub(crate) struct VerificationEquation {
  pub(crate) msm_points: [G1Affine; 6],
  pub(crate) msm_scalars: [Fr; 6],
  pub(crate) pairing_rhs: G1Affine,
  #[cfg(test)]
  pub(crate) aggregated_evaluation: Fr,
}

struct VerificationScalars {
  r0: Fr,
  r1: Fr,
  r2: Fr,
  z0_at_y: Fr,
  quotient1: Fr,
  quotient2: Fr,
}

pub(crate) fn build_verification_equation(
  verification_key: &FflonkVerificationKeyV1,
  proof: &FflonkProofV1,
  public_inputs: &[Fr],
  challenges: &FflonkChallengesV1,
  roots: &FflonkEvaluationRootsV1,
) -> Result<VerificationEquation, FflonkVerificationError> {
  let scalars = verification_scalars(
    verification_key,
    proof,
    public_inputs,
    challenges,
    roots,
  )?;
  let commitments = proof.named_commitments();
  let aggregated_evaluation = scalars.r0
    + scalars.quotient1 * scalars.r1
    + scalars.quotient2 * scalars.r2;
  Ok(VerificationEquation {
    msm_points: [
      verification_key.c0(),
      commitments.c1,
      commitments.c2,
      verification_key.kzg().g1,
      commitments.w1,
      commitments.w2,
    ],
    msm_scalars: [
      Fr::one(),
      scalars.quotient1,
      scalars.quotient2,
      -aggregated_evaluation,
      -scalars.z0_at_y,
      challenges.y,
    ],
    pairing_rhs: commitments.w2,
    #[cfg(test)]
    aggregated_evaluation,
  })
}

fn verification_scalars(
  verification_key: &FflonkVerificationKeyV1,
  proof: &FflonkProofV1,
  public_inputs: &[Fr],
  challenges: &FflonkChallengesV1,
  roots: &FflonkEvaluationRootsV1,
) -> Result<VerificationScalars, FflonkVerificationError> {
  let zh = challenges.xi_to_n - Fr::one();
  let public_lagrange_parts = public_lagrange_parts(
    verification_key,
    challenges.xi,
    zh,
    public_inputs.len().max(1),
  );
  let r0_lagrange_parts = lagrange_basis_parts(&roots.h0_omega8, challenges.y);
  let r1_lagrange_parts = lagrange_basis_parts(&roots.h1_omega4, challenges.y);
  let r2_roots = [
    roots.h2_omega3[0],
    roots.h2_omega3[1],
    roots.h2_omega3[2],
    roots.h3_omega3[0],
    roots.h3_omega3[1],
    roots.h3_omega3[2],
  ];
  let r2_lagrange_parts = lagrange_basis_parts(&r2_roots, challenges.y);
  let z0_at_y = vanishing_at(&roots.h0_omega8, challenges.y);
  let z1_at_y = vanishing_at(&roots.h1_omega4, challenges.y);
  let z2_at_y = vanishing_at(&r2_roots, challenges.y);

  let mut denominators = BatchDenominators::default();
  let inv_zh_index = denominators.push(zh, "Z_H(xi)");
  let public_start = denominators.len();
  for denominator in &public_lagrange_parts.denominators {
    denominators.push(*denominator, "a public-input Lagrange denominator");
  }
  let r0_start = denominators.len();
  for denominator in r0_lagrange_parts.denominators {
    denominators.push(denominator, "the C0 interpolation set");
  }
  let r1_start = denominators.len();
  for denominator in r1_lagrange_parts.denominators {
    denominators.push(denominator, "the C1 interpolation set");
  }
  let r2_start = denominators.len();
  for denominator in r2_lagrange_parts.denominators {
    denominators.push(denominator, "the C2 interpolation set");
  }
  let z1_index = denominators.push(z1_at_y, "Z_1(y)");
  let z2_index = denominators.push(z2_at_y, "Z_2(y)");
  let inverses = denominators.invert()?;
  let inv_zh = inverses[inv_zh_index];
  let public_lagrange = public_lagrange_parts
    .numerators
    .iter()
    .enumerate()
    .map(|(index, numerator)| *numerator * inverses[public_start + index])
    .collect::<Vec<_>>();
  let r0_lagrange: [Fr; 8] = core::array::from_fn(|index| {
    r0_lagrange_parts.numerators[index] * inverses[r0_start + index]
  });
  let r1_lagrange: [Fr; 4] = core::array::from_fn(|index| {
    r1_lagrange_parts.numerators[index] * inverses[r1_start + index]
  });
  let r2_lagrange: [Fr; 6] = core::array::from_fn(|index| {
    r2_lagrange_parts.numerators[index] * inverses[r2_start + index]
  });
  let public_input_evaluation = public_inputs
    .iter()
    .zip(&public_lagrange)
    .fold(Fr::zero(), |value, (input, lagrange)| value - *input * lagrange);

  let evaluations = proof.named_evaluations();
  let r0 = roots.h0_omega8.iter().zip(r0_lagrange).fold(
    Fr::zero(),
    |value, (root, lagrange)| {
      let root2 = root.square();
      let root4 = root2.square();
      let c0_at_root = evaluations.ql
        + evaluations.qr * root
        + evaluations.qo * root2
        + evaluations.qm * (root2 * root)
        + evaluations.qc * root4
        + evaluations.s1 * (root4 * root)
        + evaluations.s2 * (root4 * root2)
        + evaluations.s3 * (root4 * root2 * root);
      value + c0_at_root * lagrange
    },
  );

  let t0 = (evaluations.ql * evaluations.a
    + evaluations.qr * evaluations.b
    + evaluations.qm * evaluations.a * evaluations.b
    + evaluations.qo * evaluations.c
    + evaluations.qc
    + public_input_evaluation)
    * inv_zh;
  let r1 = roots.h1_omega4.iter().zip(r1_lagrange).fold(
    Fr::zero(),
    |value, (root, lagrange)| {
      let root2 = root.square();
      let c1_at_root = evaluations.a
        + evaluations.b * root
        + evaluations.c * root2
        + t0 * root2 * root;
      value + c1_at_root * lagrange
    },
  );

  let t1 = (evaluations.z - Fr::one()) * public_lagrange[0] * inv_zh;
  let beta_xi = challenges.beta * challenges.xi;
  let identity_permutation = (evaluations.a + beta_xi + challenges.gamma)
    * (evaluations.b + beta_xi * verification_key.k1() + challenges.gamma)
    * (evaluations.c + beta_xi * verification_key.k2() + challenges.gamma)
    * evaluations.z;
  let copy_permutation =
    (evaluations.a + challenges.beta * evaluations.s1 + challenges.gamma)
      * (evaluations.b + challenges.beta * evaluations.s2 + challenges.gamma)
      * (evaluations.c + challenges.beta * evaluations.s3 + challenges.gamma)
      * evaluations.zw;
  let t2 = (identity_permutation - copy_permutation) * inv_zh;
  let r2 = r2_roots.iter().enumerate().zip(r2_lagrange).fold(
    Fr::zero(),
    |value, ((index, root), lagrange)| {
      let c2_at_root = if index < 3 {
        evaluations.z + t1 * root + t2 * root.square()
      } else {
        evaluations.zw
          + evaluations.t1w * root
          + evaluations.t2w * root.square()
      };
      value + c2_at_root * lagrange
    },
  );

  let quotient1 = challenges.alpha * z0_at_y * inverses[z1_index];
  let quotient2 = challenges.alpha.square() * z0_at_y * inverses[z2_index];

  Ok(VerificationScalars { r0, r1, r2, z0_at_y, quotient1, quotient2 })
}

struct PublicLagrangeParts {
  numerators: Vec<Fr>,
  denominators: Vec<Fr>,
}

fn public_lagrange_parts(
  verification_key: &FflonkVerificationKeyV1,
  xi: Fr,
  zh: Fr,
  count: usize,
) -> PublicLagrangeParts {
  let domain_size = Fr::from(verification_key.domain_size());
  let mut omega_i = Fr::one();
  let mut numerators = Vec::with_capacity(count);
  let mut denominators = Vec::with_capacity(count);
  for _ in 0..count {
    numerators.push(omega_i * zh);
    denominators.push(domain_size * (xi - omega_i));
    omega_i *= verification_key.omega();
  }
  PublicLagrangeParts { numerators, denominators }
}

struct LagrangeBasisParts<const N: usize> {
  numerators: [Fr; N],
  denominators: [Fr; N],
}

fn lagrange_basis_parts<const N: usize>(
  roots: &[Fr; N],
  point: Fr,
) -> LagrangeBasisParts<N> {
  let mut numerators = [Fr::zero(); N];
  let mut denominators = [Fr::zero(); N];
  for (index, root) in roots.iter().enumerate() {
    let mut numerator = Fr::one();
    let mut denominator = Fr::one();
    for (other_index, other_root) in roots.iter().enumerate() {
      if other_index != index {
        numerator *= point - other_root;
        denominator *= root - other_root;
      }
    }
    numerators[index] = numerator;
    denominators[index] = denominator;
  }
  LagrangeBasisParts { numerators, denominators }
}

fn vanishing_at<const N: usize>(roots: &[Fr; N], point: Fr) -> Fr {
  roots.iter().fold(Fr::one(), |value, root| value * (point - root))
}

#[derive(Default)]
struct BatchDenominators {
  values: Vec<Fr>,
  relations: Vec<&'static str>,
}

impl BatchDenominators {
  fn len(&self) -> usize {
    self.values.len()
  }

  fn push(&mut self, value: Fr, relation: &'static str) -> usize {
    let index = self.values.len();
    self.values.push(value);
    self.relations.push(relation);
    index
  }

  fn invert(mut self) -> Result<Vec<Fr>, FflonkVerificationError> {
    if let Some((index, _)) =
      self.values.iter().enumerate().find(|(_, value)| value.is_zero())
    {
      return Err(FflonkVerificationError::SingularChallenge {
        relation: self.relations[index],
      });
    }
    batch_inversion(&mut self.values);
    Ok(self.values)
  }
}

pub(crate) fn validate_proof_points(
  proof: &FflonkProofV1,
) -> Result<(), FflonkVerificationError> {
  for (index, point) in proof.commitments.iter().enumerate() {
    if !point.is_on_curve() || !point.is_in_correct_subgroup_assuming_on_curve()
    {
      return Err(FflonkVerificationError::InvalidProofCommitment { index });
    }
  }
  Ok(())
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::{FFLONK_COMMITMENTS, FFLONK_EVALUATIONS, KzgVerifierKeyV1};
  use ark_bls12_381::{G1Affine, G2Affine};
  use ark_ec::{AffineRepr, CurveGroup};
  use ark_ff::{FftField, PrimeField};

  fn point(scalar: Fr) -> G1Affine {
    G1Affine::generator().mul_bigint(scalar.into_bigint()).into_affine()
  }

  fn fixture_key(tau: Fr, c0_scalar: Fr) -> FflonkVerificationKeyV1 {
    let kzg = KzgVerifierKeyV1 {
      g1: G1Affine::generator(),
      g2: G2Affine::generator(),
      tau_g2: G2Affine::generator().mul_bigint(tau.into_bigint()).into_affine(),
      srs_digest: [11_u8; 32],
    };
    FflonkVerificationKeyV1::new(
      2,
      16,
      Fr::GENERATOR,
      Fr::GENERATOR.square(),
      point(c0_scalar),
      kzg,
    )
    .unwrap()
  }

  fn forge_equation_fixture()
  -> (FflonkVerificationKeyV1, FflonkProofV1, [Fr; 2]) {
    let tau = Fr::from(13_u64);
    let c0_scalar = Fr::from(7_u64);
    let key = fixture_key(tau, c0_scalar);
    let public_inputs = [Fr::from(3_u64), Fr::from(5_u64)];
    let mut proof = FflonkProofV1 {
      commitments: [G1Affine::identity(); FFLONK_COMMITMENTS],
      evaluations: core::array::from_fn(|index| Fr::from(index as u64 + 1)),
    };
    let (challenges, roots) =
      derive_fflonk_challenges(&key, &proof, &public_inputs).unwrap();
    let equation = build_verification_equation(
      &key,
      &proof,
      &public_inputs,
      &challenges,
      &roots,
    )
    .unwrap();
    let witness_scalar = (c0_scalar - equation.aggregated_evaluation)
      * (tau - challenges.y).inverse().unwrap();
    proof.commitments[3] = point(witness_scalar);
    (key, proof, public_inputs)
  }

  #[test]
  fn generic_lagrange_basis_reconstructs_a_cubic() {
    let roots = [Fr::from(2), Fr::from(3), Fr::from(5), Fr::from(7)];
    let point = Fr::from(11);
    let parts = lagrange_basis_parts(&roots, point);
    let mut denominator_inverses = parts.denominators;
    batch_inversion(&mut denominator_inverses);
    let basis: [Fr; 4] = core::array::from_fn(|index| {
      parts.numerators[index] * denominator_inverses[index]
    });
    let polynomial = |x: Fr| {
      Fr::from(17)
        + Fr::from(19) * x
        + Fr::from(23) * x.square()
        + Fr::from(29) * x.square() * x
    };
    let reconstructed =
      roots.iter().zip(basis).fold(Fr::zero(), |value, (root, lagrange)| {
        value + polynomial(*root) * lagrange
      });
    assert_eq!(reconstructed, polynomial(point));
  }

  #[test]
  fn complete_pairing_equation_accepts_and_rejects_mutations() {
    let (key, proof, public_inputs) = forge_equation_fixture();
    assert_eq!(verify_fflonk(&key, &proof, &public_inputs), Ok(true));

    let mut changed_w2 = proof.clone();
    changed_w2.commitments[3] = (changed_w2.commitments[3].into_group()
      + G1Affine::generator())
    .into_affine();
    assert_eq!(verify_fflonk(&key, &changed_w2, &public_inputs), Ok(false));

    let mut changed_evaluation = proof;
    changed_evaluation.evaluations[FFLONK_EVALUATIONS - 1] += Fr::one();
    assert_eq!(
      verify_fflonk(&key, &changed_evaluation, &public_inputs),
      Ok(false),
    );
  }

  #[test]
  fn malformed_unchecked_commitment_is_rejected_before_pairing() {
    let (key, mut proof, public_inputs) = forge_equation_fixture();
    proof.commitments[0] = G1Affine::new_unchecked(
      ark_bls12_381::Fq::zero(),
      ark_bls12_381::Fq::one(),
    );
    assert_eq!(
      verify_fflonk(&key, &proof, &public_inputs),
      Err(FflonkVerificationError::InvalidProofCommitment { index: 0 }),
    );
  }
}
