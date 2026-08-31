use crate::{
  FflonkProofV1, FflonkVerificationError, FflonkVerificationKeyV1,
  derive_fflonk_challenges,
  proof::{encode_field_be, encode_g1_eip2537, encode_scalar_be},
  verifier::{build_verification_equation, validate_proof_points},
};
use ark_bls12_381::G2Affine;

/// EIP-2537 address for BLS12-381 G1 multi-scalar multiplication.
pub const EIP2537_G1_MSM_ADDRESS: u8 = 0x0c;
/// EIP-2537 address for the BLS12-381 pairing check.
pub const EIP2537_PAIRING_ADDRESS: u8 = 0x0f;

/// The final FFLONK commitment equation is one six-term G1 MSM.
pub const FFLONK_EIP2537_G1_MSM_TERMS: usize = 6;
/// The final KZG equation is one EIP-2537 pairing check with two pairs.
pub const FFLONK_EIP2537_PAIRING_PAIRS: usize = 2;
/// EIP-2537 encodes each G1/scalar MSM term in 160 bytes.
pub const EIP2537_G1_MSM_TERM_BYTES: usize = 160;
/// EIP-2537 encodes each G1/G2 pairing pair in 384 bytes.
pub const EIP2537_PAIRING_PAIR_BYTES: usize = 384;
/// Exact input width of the FFLONK G1 MSM call.
pub const FFLONK_EIP2537_G1_MSM_INPUT_BYTES: usize =
  FFLONK_EIP2537_G1_MSM_TERMS * EIP2537_G1_MSM_TERM_BYTES;
/// Exact input width of the FFLONK pairing call.
pub const FFLONK_EIP2537_PAIRING_INPUT_BYTES: usize =
  FFLONK_EIP2537_PAIRING_PAIRS * EIP2537_PAIRING_PAIR_BYTES;

const EIP2537_G2_BYTES: usize = 256;
const EIP2537_BASE_FIELD_BYTES: usize = 64;
const PAIRING_DYNAMIC_OUTPUT_BYTES: usize = 128;
const PAIRING_SUFFIX_BYTES: usize =
  FFLONK_EIP2537_PAIRING_INPUT_BYTES - PAIRING_DYNAMIC_OUTPUT_BYTES;

/// Consensus-priced EIP-2537 gas used by the two curve calls.
///
/// This excludes EVM bytecode, memory expansion, calldata, Keccak, and scalar
/// field arithmetic. It is the exact cryptographic-precompile floor for this
/// verifier shape under the final EIP-2537 schedule.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FflonkEip2537GasV1 {
  pub g1_msm: u64,
  pub pairing: u64,
}

impl FflonkEip2537GasV1 {
  #[must_use]
  pub const fn total(self) -> u64 {
    self.g1_msm + self.pairing
  }
}

/// Six G1 multiplications receive EIP-2537's `k = 6` discount of 750/1000.
pub const FFLONK_EIP2537_GAS: FflonkEip2537GasV1 = FflonkEip2537GasV1 {
  g1_msm: 6 * 12_000 * 750 / 1_000,
  pairing: 2 * 32_600 + 37_700,
};

/// Byte-exact EIP-2537 curve-call plan for one already-parsed FFLONK proof.
///
/// A contract computes the scalar coefficients, calls G1 MSM at `0x0c`, then
/// places its 128-byte output before `pairing_suffix` and calls pairing at
/// `0x0f`. Keeping the dynamic output separate makes it impossible to mistake
/// an off-chain-computed G1 result for verifier input.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FflonkEip2537PlanV1 {
  g1_msm_input: [u8; FFLONK_EIP2537_G1_MSM_INPUT_BYTES],
  pairing_suffix: [u8; PAIRING_SUFFIX_BYTES],
}

impl FflonkEip2537PlanV1 {
  pub fn g1_msm_input(&self) -> &[u8; FFLONK_EIP2537_G1_MSM_INPUT_BYTES] {
    &self.g1_msm_input
  }

  /// Completes the pairing input with the preceding G1 MSM precompile output.
  #[must_use]
  pub fn pairing_input(
    &self,
    g1_msm_output: &[u8; PAIRING_DYNAMIC_OUTPUT_BYTES],
  ) -> [u8; FFLONK_EIP2537_PAIRING_INPUT_BYTES] {
    let mut input = [0_u8; FFLONK_EIP2537_PAIRING_INPUT_BYTES];
    input[..PAIRING_DYNAMIC_OUTPUT_BYTES].copy_from_slice(g1_msm_output);
    input[PAIRING_DYNAMIC_OUTPUT_BYTES..].copy_from_slice(&self.pairing_suffix);
    input
  }
}

/// Builds the exact two-call EIP-2537 curve plan used by the native verifier.
pub fn build_eip2537_verification_plan(
  verification_key: &FflonkVerificationKeyV1,
  proof: &FflonkProofV1,
  public_inputs: &[ark_bls12_381::Fr],
) -> Result<FflonkEip2537PlanV1, FflonkVerificationError> {
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

  let mut g1_msm_input = [0_u8; FFLONK_EIP2537_G1_MSM_INPUT_BYTES];
  for (index, (point, scalar)) in
    equation.msm_points.iter().zip(equation.msm_scalars.iter()).enumerate()
  {
    let offset = index * EIP2537_G1_MSM_TERM_BYTES;
    g1_msm_input[offset..offset + 128]
      .copy_from_slice(&encode_g1_eip2537(point));
    g1_msm_input[offset + 128..offset + EIP2537_G1_MSM_TERM_BYTES]
      .copy_from_slice(&encode_scalar_be(scalar));
  }

  let mut pairing_suffix = [0_u8; PAIRING_SUFFIX_BYTES];
  pairing_suffix[..EIP2537_G2_BYTES]
    .copy_from_slice(&encode_g2_eip2537(&verification_key.kzg().g2));
  pairing_suffix[EIP2537_G2_BYTES..EIP2537_G2_BYTES + 128]
    .copy_from_slice(&encode_g1_eip2537(&(-equation.pairing_rhs)));
  pairing_suffix[EIP2537_G2_BYTES + 128..]
    .copy_from_slice(&encode_g2_eip2537(&verification_key.kzg().tau_g2));

  Ok(FflonkEip2537PlanV1 { g1_msm_input, pairing_suffix })
}

fn encode_g2_eip2537(point: &G2Affine) -> [u8; EIP2537_G2_BYTES] {
  let mut encoded = [0_u8; EIP2537_G2_BYTES];
  if point.infinity {
    return encoded;
  }
  encode_field_be(&point.x.c0, &mut encoded[..EIP2537_BASE_FIELD_BYTES]);
  encode_field_be(
    &point.x.c1,
    &mut encoded[EIP2537_BASE_FIELD_BYTES..2 * EIP2537_BASE_FIELD_BYTES],
  );
  encode_field_be(
    &point.y.c0,
    &mut encoded[2 * EIP2537_BASE_FIELD_BYTES..3 * EIP2537_BASE_FIELD_BYTES],
  );
  encode_field_be(&point.y.c1, &mut encoded[3 * EIP2537_BASE_FIELD_BYTES..]);
  encoded
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::{
    FFLONK_COMMITMENTS, FFLONK_EVALUATIONS, KzgVerifierKeyV1,
    verifier::build_verification_equation, verify_fflonk,
  };
  use ark_bls12_381::{Bls12_381, Fr, G1Affine, G1Projective};
  use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM, pairing::Pairing};
  use ark_ff::{FftField, Field, PrimeField};

  fn point(scalar: Fr) -> G1Affine {
    G1Affine::generator().mul_bigint(scalar.into_bigint()).into_affine()
  }

  fn fixture() -> (FflonkVerificationKeyV1, FflonkProofV1, [Fr; 2]) {
    let tau = Fr::from(13_u64);
    let c0_scalar = Fr::from(7_u64);
    let kzg = KzgVerifierKeyV1 {
      g1: G1Affine::generator(),
      g2: G2Affine::generator(),
      tau_g2: G2Affine::generator().mul_bigint(tau.into_bigint()).into_affine(),
      srs_digest: [11_u8; 32],
    };
    let key = FflonkVerificationKeyV1::new(
      2,
      16,
      Fr::GENERATOR,
      Fr::GENERATOR.square(),
      point(c0_scalar),
      kzg,
    )
    .unwrap();
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
  fn gas_and_call_widths_are_exact() {
    assert_eq!(FFLONK_EIP2537_G1_MSM_INPUT_BYTES, 960);
    assert_eq!(FFLONK_EIP2537_PAIRING_INPUT_BYTES, 768);
    assert_eq!(FFLONK_EIP2537_GAS.g1_msm, 54_000);
    assert_eq!(FFLONK_EIP2537_GAS.pairing, 102_900);
    assert_eq!(FFLONK_EIP2537_GAS.total(), 156_900);
  }

  #[test]
  fn curve_call_plan_matches_native_verification_equation() {
    let (key, proof, public_inputs) = fixture();
    let plan =
      build_eip2537_verification_plan(&key, &proof, &public_inputs).unwrap();
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
    let lhs = G1Projective::msm(&equation.msm_points, &equation.msm_scalars)
      .unwrap()
      .into_affine();
    let msm_output = encode_g1_eip2537(&lhs);
    let pairing_input = plan.pairing_input(&msm_output);

    assert_eq!(&pairing_input[..128], &encode_g1_eip2537(&lhs),);
    assert_eq!(&pairing_input[128..384], &encode_g2_eip2537(&key.kzg().g2),);
    assert_eq!(
      &pairing_input[384..512],
      &encode_g1_eip2537(&(-proof.named_commitments().w2)),
    );
    assert_eq!(&pairing_input[512..], &encode_g2_eip2537(&key.kzg().tau_g2),);
    assert_eq!(
      Bls12_381::pairing(lhs, key.kzg().g2),
      Bls12_381::pairing(proof.named_commitments().w2, key.kzg().tau_g2),
    );
    assert_eq!(verify_fflonk(&key, &proof, &public_inputs), Ok(true));
  }

  #[test]
  fn msm_input_is_canonical_point_scalar_concatenation() {
    let (key, proof, public_inputs) = fixture();
    let plan =
      build_eip2537_verification_plan(&key, &proof, &public_inputs).unwrap();
    assert_eq!(&plan.g1_msm_input()[..128], &encode_g1_eip2537(&key.c0()),);
    assert_eq!(
      &plan.g1_msm_input()[128..160],
      &encode_scalar_be(&Fr::from(1_u64)),
    );
  }

  #[test]
  fn malformed_proof_does_not_reach_a_precompile_plan() {
    let (key, mut proof, public_inputs) = fixture();
    proof.commitments[0] = G1Affine::new_unchecked(
      ark_bls12_381::Fq::from(0_u64),
      ark_bls12_381::Fq::from(1_u64),
    );
    assert_eq!(
      build_eip2537_verification_plan(&key, &proof, &public_inputs),
      Err(FflonkVerificationError::InvalidProofCommitment { index: 0 }),
    );
  }

  #[test]
  fn proof_shape_constants_remain_bound_to_the_plan() {
    assert_eq!(FFLONK_COMMITMENTS, 4);
    assert_eq!(FFLONK_EVALUATIONS, 15);
  }
}
