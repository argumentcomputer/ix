use crate::proof::{encode_g1_eip2537, encode_scalar_be};
use crate::{FflonkProofV1, FflonkVerificationKeyV1};
use ark_bls12_381::{Fr, G1Affine};
use ark_ff::{Field, One, PrimeField};
use core::fmt;
use tiny_keccak::{Hasher, Keccak};

/// Fiat--Shamir challenges for the Stage 4 BLS12-381 FFLONK profile.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FflonkChallengesV1 {
  pub beta: Fr,
  pub gamma: Fr,
  pub xi_seed: Fr,
  pub xi: Fr,
  pub xi_omega: Fr,
  pub xi_to_n: Fr,
  pub alpha: Fr,
  pub y: Fr,
}

/// Evaluation cosets derived from `xi_seed` for the three packed commitments.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FflonkEvaluationRootsV1 {
  pub h0_omega8: [Fr; 8],
  pub h1_omega4: [Fr; 4],
  pub h2_omega3: [Fr; 3],
  pub h3_omega3: [Fr; 3],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FflonkTranscriptError {
  WrongPublicInputCount { expected: usize, actual: usize },
}

impl fmt::Display for FflonkTranscriptError {
  fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::WrongPublicInputCount { expected, actual } => write!(
        formatter,
        "FFLONK verification key expects {expected} public inputs, got {actual}",
      ),
    }
  }
}

impl std::error::Error for FflonkTranscriptError {}

/// Derives the five FFLONK transcript rounds and their packed evaluation roots.
///
/// The transcript hashes points exactly as their 128-byte EIP-2537 calldata
/// encoding and scalars as canonical 32-byte big-endian integers. Each round
/// starts a fresh Keccak-256 preimage, following the FFLONK challenge chain:
///
/// `C0 || public || C1 -> beta`, `beta -> gamma`,
/// `gamma || C2 -> xi_seed`, `xi_seed || evaluations -> alpha`, and
/// `alpha || W1 -> y`.
pub fn derive_fflonk_challenges(
  verification_key: &FflonkVerificationKeyV1,
  proof: &FflonkProofV1,
  public_inputs: &[Fr],
) -> Result<(FflonkChallengesV1, FflonkEvaluationRootsV1), FflonkTranscriptError>
{
  if public_inputs.len() != verification_key.num_public_inputs() {
    return Err(FflonkTranscriptError::WrongPublicInputCount {
      expected: verification_key.num_public_inputs(),
      actual: public_inputs.len(),
    });
  }

  let commitments = proof.named_commitments();

  let mut transcript = KeccakTranscript::default();
  transcript.append_point(&verification_key.c0());
  for input in public_inputs {
    transcript.append_scalar(input);
  }
  transcript.append_point(&commitments.c1);
  let beta = transcript.challenge();

  transcript.clear();
  transcript.append_scalar(&beta);
  let gamma = transcript.challenge();

  transcript.clear();
  transcript.append_scalar(&gamma);
  transcript.append_point(&commitments.c2);
  let xi_seed = transcript.challenge();
  let roots = evaluation_roots(verification_key, xi_seed);
  // All three packed sets share the vanishing value xi = xi_seed^24:
  // (xi_seed^3)^8 = (xi_seed^6)^4 = (xi_seed^8)^3.
  let xi = roots.h2_omega3[0].pow([3]);
  debug_assert_eq!(roots.h0_omega8[0].pow([8]), xi);
  debug_assert_eq!(roots.h1_omega4[0].pow([4]), xi);
  let xi_omega = xi * verification_key.omega();
  let xi_to_n = xi.pow([verification_key.domain_size()]);

  transcript.clear();
  transcript.append_scalar(&xi_seed);
  for evaluation in &proof.evaluations {
    transcript.append_scalar(evaluation);
  }
  let alpha = transcript.challenge();

  transcript.clear();
  transcript.append_scalar(&alpha);
  transcript.append_point(&commitments.w1);
  let y = transcript.challenge();

  Ok((
    FflonkChallengesV1 {
      beta,
      gamma,
      xi_seed,
      xi,
      xi_omega,
      xi_to_n,
      alpha,
      y,
    },
    roots,
  ))
}

fn evaluation_roots(
  verification_key: &FflonkVerificationKeyV1,
  xi_seed: Fr,
) -> FflonkEvaluationRootsV1 {
  let xi_seed_squared = xi_seed.square();
  let h0 = xi_seed_squared * xi_seed;
  let h1 = h0.square();
  let h2 = h1 * xi_seed_squared;
  let h3 = h2 * verification_key.omega_r();
  FflonkEvaluationRootsV1 {
    h0_omega8: root_coset(h0, verification_key.omega_8()),
    h1_omega4: root_coset(h1, verification_key.omega_4()),
    h2_omega3: root_coset(h2, verification_key.omega_3()),
    h3_omega3: root_coset(h3, verification_key.omega_3()),
  }
}

fn root_coset<const N: usize>(root: Fr, omega: Fr) -> [Fr; N] {
  let mut current = Fr::one();
  core::array::from_fn(|_| {
    let value = root * current;
    current *= omega;
    value
  })
}

#[derive(Default)]
struct KeccakTranscript {
  preimage: Vec<u8>,
}

impl KeccakTranscript {
  fn clear(&mut self) {
    self.preimage.clear();
  }

  fn append_point(&mut self, point: &G1Affine) {
    self.preimage.extend_from_slice(&encode_g1_eip2537(point));
  }

  fn append_scalar(&mut self, scalar: &Fr) {
    self.preimage.extend_from_slice(&encode_scalar_be(scalar));
  }

  fn challenge(&self) -> Fr {
    debug_assert!(!self.preimage.is_empty());
    Fr::from_be_bytes_mod_order(&keccak256(&self.preimage))
  }
}

fn keccak256(input: &[u8]) -> [u8; 32] {
  let mut output = [0_u8; 32];
  let mut hasher = Keccak::v256();
  hasher.update(input);
  hasher.finalize(&mut output);
  output
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::{FFLONK_COMMITMENTS, FFLONK_EVALUATIONS, KzgVerifierKeyV1};
  use ark_bls12_381::G2Affine;
  use ark_ec::{AffineRepr, CurveGroup};
  use ark_ff::{FftField, PrimeField};

  fn point(scalar: u64) -> G1Affine {
    G1Affine::generator()
      .mul_bigint(Fr::from(scalar).into_bigint())
      .into_affine()
  }

  fn verification_key() -> FflonkVerificationKeyV1 {
    let tau = Fr::from(13_u64);
    let kzg = KzgVerifierKeyV1 {
      g1: G1Affine::generator(),
      g2: G2Affine::generator(),
      tau_g2: G2Affine::generator().mul_bigint(tau.into_bigint()).into_affine(),
      srs_digest: [9_u8; 32],
    };
    FflonkVerificationKeyV1::new(
      2,
      16,
      Fr::GENERATOR,
      Fr::GENERATOR.square(),
      point(7),
      kzg,
    )
    .unwrap()
  }

  fn proof() -> FflonkProofV1 {
    FflonkProofV1 {
      commitments: core::array::from_fn(|index| point(index as u64 + 2)),
      evaluations: core::array::from_fn(|index| Fr::from(index as u64 + 1)),
    }
  }

  #[test]
  fn keccak_uses_ethereum_not_fips_sha3_padding() {
    assert_eq!(
      keccak256(&[]),
      [
        0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c, 0x92, 0x7e, 0x7d, 0xb2,
        0xdc, 0xc7, 0x03, 0xc0, 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b,
        0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70,
      ],
    );
  }

  #[test]
  fn packed_roots_share_xi_and_the_shifted_coset_shares_xi_omega() {
    let key = verification_key();
    let (challenges, roots) =
      derive_fflonk_challenges(&key, &proof(), &[Fr::from(3), Fr::from(5)])
        .unwrap();
    for root in roots.h0_omega8 {
      assert_eq!(root.pow([8]), challenges.xi);
    }
    for root in roots.h1_omega4 {
      assert_eq!(root.pow([4]), challenges.xi);
    }
    for root in roots.h2_omega3 {
      assert_eq!(root.pow([3]), challenges.xi);
    }
    for root in roots.h3_omega3 {
      assert_eq!(root.pow([3]), challenges.xi_omega);
    }
  }

  #[test]
  fn transcript_round_dependencies_are_pinned() {
    let key = verification_key();
    let public = [Fr::from(3), Fr::from(5)];
    let base_proof = proof();
    let (base, _) =
      derive_fflonk_challenges(&key, &base_proof, &public).unwrap();

    let mut changed_evaluation = base_proof.clone();
    changed_evaluation.evaluations[FFLONK_EVALUATIONS - 1] += Fr::one();
    let (evaluation_challenges, _) =
      derive_fflonk_challenges(&key, &changed_evaluation, &public).unwrap();
    assert_eq!(evaluation_challenges.beta, base.beta);
    assert_eq!(evaluation_challenges.gamma, base.gamma);
    assert_eq!(evaluation_challenges.xi_seed, base.xi_seed);
    assert_ne!(evaluation_challenges.alpha, base.alpha);
    assert_ne!(evaluation_challenges.y, base.y);

    let mut changed_w1 = base_proof.clone();
    changed_w1.commitments[2] = point(41);
    let (w1_challenges, _) =
      derive_fflonk_challenges(&key, &changed_w1, &public).unwrap();
    assert_eq!(w1_challenges.alpha, base.alpha);
    assert_ne!(w1_challenges.y, base.y);

    let mut changed_w2 = base_proof;
    changed_w2.commitments[FFLONK_COMMITMENTS - 1] = point(43);
    let (w2_challenges, _) =
      derive_fflonk_challenges(&key, &changed_w2, &public).unwrap();
    assert_eq!(w2_challenges, base);
  }

  #[test]
  fn rejects_a_public_input_count_mismatch_before_hashing() {
    assert_eq!(
      derive_fflonk_challenges(&verification_key(), &proof(), &[Fr::one()]),
      Err(FflonkTranscriptError::WrongPublicInputCount {
        expected: 2,
        actual: 1,
      }),
    );
  }
}
