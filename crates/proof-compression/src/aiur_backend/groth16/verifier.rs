//! Strict BN254 Groth16 verifier with canonical field decoding, curve and
//! prime-order subgroup checks, and 4-term multi-pairing verification.

use super::prover::Proof;
use super::setup::VerifyingKey;
use crate::kzg::curve::{Bn254 as KzgBn254, KzgCurve};
use ark_bn254::{Bn254, Fq, Fq2, Fr, G1Affine, G1Projective, G2Affine};
use ark_ec::{CurveGroup, pairing::Pairing};
use ark_ff::{BigInt, PrimeField, Zero};

/// Decode a 32-byte big-endian unsigned integer as a canonical BN254 base field
/// element (`0 <= val < p`). Rejects any non-canonical value `>= p`.
pub fn decode_fq_be_canonical(bytes: &[u8]) -> Result<Fq, String> {
  if bytes.len() != 32 {
    return Err(format!(
      "invalid Fq byte length: got {}, expected 32",
      bytes.len()
    ));
  }
  let bigint = bigint4_from_be_bytes(bytes);
  if bigint >= Fq::MODULUS {
    return Err("non-canonical BN254 Fq coordinate (>= p)".into());
  }
  Fq::from_bigint(bigint)
    .ok_or_else(|| "failed to convert canonical bigint to Fq".into())
}

/// Decode a 32-byte big-endian unsigned integer as a canonical BN254 scalar
/// field element (`0 <= val < r`). Rejects any non-canonical value `>= r`.
pub fn decode_fr_be_canonical(bytes: &[u8]) -> Result<Fr, String> {
  if bytes.len() != 32 {
    return Err(format!(
      "invalid Fr byte length: got {}, expected 32",
      bytes.len()
    ));
  }
  let bigint = bigint4_from_be_bytes(bytes);
  if bigint >= Fr::MODULUS {
    return Err("non-canonical BN254 Fr scalar (>= r)".into());
  }
  Fr::from_bigint(bigint)
    .ok_or_else(|| "failed to convert canonical bigint to Fr".into())
}

/// Decode a 64-byte uncompressed EIP-196 G1 point (`x || y`, BE) with strict
/// canonical `Fq`, on-curve, and prime-order subgroup checks.
pub fn decode_g1_evm(bytes: &[u8]) -> Result<G1Affine, String> {
  if bytes.len() != 64 {
    return Err(format!(
      "invalid G1 EVM byte length: got {}, expected 64",
      bytes.len()
    ));
  }
  let x = decode_fq_be_canonical(&bytes[0..32])?;
  let y = decode_fq_be_canonical(&bytes[32..64])?;
  if x.is_zero() && y.is_zero() {
    return Ok(G1Affine::identity());
  }
  let pt = G1Affine::new_unchecked(x, y);
  if !pt.is_on_curve() {
    return Err("G1 point is not on the BN254 curve y^2 = x^3 + 3".into());
  }
  if !pt.is_in_correct_subgroup_assuming_on_curve() {
    return Err("G1 point is not in the BN254 prime-order subgroup".into());
  }
  Ok(pt)
}

/// Decode a 128-byte uncompressed EIP-197 G2 point
/// (`x.c1 || x.c0 || y.c1 || y.c0`, BE) with strict canonical `Fq`, on-curve,
/// and prime-order subgroup checks.
pub fn decode_g2_evm(bytes: &[u8]) -> Result<G2Affine, String> {
  if bytes.len() != 128 {
    return Err(format!(
      "invalid G2 EVM byte length: got {}, expected 128",
      bytes.len()
    ));
  }
  let x_c1 = decode_fq_be_canonical(&bytes[0..32])?;
  let x_c0 = decode_fq_be_canonical(&bytes[32..64])?;
  let y_c1 = decode_fq_be_canonical(&bytes[64..96])?;
  let y_c0 = decode_fq_be_canonical(&bytes[96..128])?;
  if x_c0.is_zero() && x_c1.is_zero() && y_c0.is_zero() && y_c1.is_zero() {
    return Ok(G2Affine::identity());
  }
  let pt = G2Affine::new_unchecked(Fq2::new(x_c0, x_c1), Fq2::new(y_c0, y_c1));
  if !pt.is_on_curve() {
    return Err("G2 point is not on the BN254 twist curve".into());
  }
  if !pt.is_in_correct_subgroup_assuming_on_curve() {
    return Err("G2 point is not in the BN254 prime-order subgroup".into());
  }
  Ok(pt)
}

fn bigint4_from_be_bytes(bytes: &[u8]) -> BigInt<4> {
  let l3 = u64::from_be_bytes(bytes[0..8].try_into().expect("8 bytes"));
  let l2 = u64::from_be_bytes(bytes[8..16].try_into().expect("8 bytes"));
  let l1 = u64::from_be_bytes(bytes[16..24].try_into().expect("8 bytes"));
  let l0 = u64::from_be_bytes(bytes[24..32].try_into().expect("8 bytes"));
  BigInt([l0, l1, l2, l3])
}

fn validate_proof_points(proof: &Proof) -> Result<(), String> {
  if !proof.a.is_on_curve()
    || !proof.a.is_in_correct_subgroup_assuming_on_curve()
  {
    return Err("proof.A failed BN254 G1 curve/subgroup validation".into());
  }
  if !proof.b.is_on_curve()
    || !proof.b.is_in_correct_subgroup_assuming_on_curve()
  {
    return Err("proof.B failed BN254 G2 curve/subgroup validation".into());
  }
  if !proof.c.is_on_curve()
    || !proof.c.is_in_correct_subgroup_assuming_on_curve()
  {
    return Err("proof.C failed BN254 G1 curve/subgroup validation".into());
  }
  Ok(())
}

/// Verify a BN254 Groth16 proof `(A, B, C)` against `vk` and `public_inputs`:
///
/// `e(A, B) · e(-α, β) · e(-(IC_0 + Σ x_i · IC_{i+1}), γ) · e(-C, δ) == 1`.
pub fn verify(
  vk: &VerifyingKey,
  public_inputs: &[Fr],
  proof: &Proof,
) -> Result<(), String> {
  vk.validate()?;
  if public_inputs.len() != vk.num_public_inputs() {
    return Err(format!(
      "public input count mismatch: got {}, expected {}",
      public_inputs.len(),
      vk.num_public_inputs()
    ));
  }
  validate_proof_points(proof)?;

  let mut pub_acc = G1Projective::from(vk.ic[0]);
  if !public_inputs.is_empty() {
    pub_acc += KzgBn254::cpu_msm(&vk.ic[1..], public_inputs);
  }
  let pub_affine = pub_acc.into_affine();

  let g1_points = [proof.a, -vk.alpha_g1, -pub_affine, -proof.c];
  let g2_points = [proof.b, vk.beta_g2, vk.gamma_g2, vk.delta_g2];

  let check = Bn254::multi_pairing(g1_points, g2_points);
  if check.is_zero() {
    Ok(())
  } else {
    Err("Groth16 pairing equation failed".into())
  }
}

/// Strictly decode a 256-byte uncompressed EVM proof and verify it against `vk`
/// and `public_inputs`.
pub fn verify_evm_bytes(
  vk: &VerifyingKey,
  public_inputs: &[Fr],
  proof_bytes: &[u8],
) -> Result<(), String> {
  let proof = Proof::from_evm_bytes(proof_bytes)?;
  verify(vk, public_inputs, &proof)
}

/// Strictly decode raw 32-byte big-endian public input scalars (rejecting any
/// `>= r`) and a 256-byte uncompressed EVM proof, then verify against `vk`.
pub fn verify_evm_bytes_raw_publics(
  vk: &VerifyingKey,
  raw_public_inputs_be: &[[u8; 32]],
  proof_bytes: &[u8],
) -> Result<(), String> {
  let mut publics = Vec::with_capacity(raw_public_inputs_be.len());
  for (idx, raw) in raw_public_inputs_be.iter().enumerate() {
    let scalar = decode_fr_be_canonical(raw)
      .map_err(|e| format!("public input[{idx}] invalid: {e}"))?;
    publics.push(scalar);
  }
  verify_evm_bytes(vk, &publics, proof_bytes)
}

/// Strictly decode a 128-byte compressed proof and verify it against `vk` and
/// `public_inputs`.
pub fn verify_compressed_bytes(
  vk: &VerifyingKey,
  public_inputs: &[Fr],
  proof_bytes: &[u8],
) -> Result<(), String> {
  let proof = Proof::from_compressed_bytes(proof_bytes)?;
  verify(vk, public_inputs, &proof)
}
