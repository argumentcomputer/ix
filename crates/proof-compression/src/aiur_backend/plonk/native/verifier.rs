//! Curve-generic PLONK + BSB22 verifier (`Bn254` & `Bls12381`).
//!
//! Verifies both native proofs (`IXNPPR01`) and gnark `MarshalSolidity` proof
//! bytes with strict VK digest pinning, canonical scalar checks, G1 curve and
//! prime-order subgroup checks (essential for BLS12-381), exact gnark-Solidity
//! SHA-256 Fiat-Shamir replay, linearized opening check, and final 2-pairing
//! KZG verification via `C::PairingCurve::multi_pairing`.

use super::preprocess::VerifyingKey;
use super::prover::NativeProof;
use super::solver::batch_invert_in_place;
use super::transcript::{
  derive_alpha, derive_batch_verify_random, derive_beta, derive_gamma,
  derive_gamma_kzg, derive_zeta, hash_fr_bsb22,
};
use crate::kzg::curve::{G1AffineOf, G1ProjectiveOf, KzgCurve};
use ark_ec::{CurveGroup, pairing::Pairing};
use ark_ff::{Field, Zero};

/// Verify a native serialized PLONK proof (`IXNPPR01`) against a VK pinned to
/// `trusted_vk_sha256` and externally supplied `public_inputs`.
pub fn verify_native_bytes<C: KzgCurve>(
  vk: &VerifyingKey<C>,
  trusted_vk_sha256: &[u8; 32],
  proof_bytes: &[u8],
  public_inputs: &[C::Fr],
) -> Result<(), String> {
  let proof = NativeProof::<C>::from_native_bytes(proof_bytes)?;
  verify_inner(vk, trusted_vk_sha256, &proof, public_inputs, true)
}

/// Verify a gnark `MarshalSolidity` proof byte slice against a VK pinned to
/// `trusted_vk_sha256` and externally supplied `public_inputs`.
pub fn verify_solidity_bytes<C: KzgCurve>(
  vk: &VerifyingKey<C>,
  trusted_vk_sha256: &[u8; 32],
  solidity_bytes: &[u8],
  public_inputs: &[C::Fr],
) -> Result<(), String> {
  let proof =
    NativeProof::<C>::unmarshal_solidity(solidity_bytes, vk.qcp.len())?;
  verify_inner(vk, trusted_vk_sha256, &proof, public_inputs, false)
}

/// Verify a decoded [`NativeProof`] against a VK pinned to `trusted_vk_sha256`
/// and externally supplied `public_inputs`.
pub fn verify<C: KzgCurve>(
  vk: &VerifyingKey<C>,
  trusted_vk_sha256: &[u8; 32],
  proof: &NativeProof<C>,
  public_inputs: &[C::Fr],
) -> Result<(), String> {
  verify_inner(vk, trusted_vk_sha256, proof, public_inputs, true)
}

fn check_g1_subgroup<C: KzgCurve>(
  point: G1AffineOf<C>,
  label: &str,
) -> Result<(), String> {
  if !point.is_on_curve() || !point.is_in_correct_subgroup_assuming_on_curve() {
    return Err(format!("{label} is not a valid prime-order G1 point"));
  }
  Ok(())
}

fn verify_inner<C: KzgCurve>(
  vk: &VerifyingKey<C>,
  trusted_vk_sha256: &[u8; 32],
  proof: &NativeProof<C>,
  public_inputs: &[C::Fr],
  check_claimed_lin: bool,
) -> Result<(), String> {
  if &vk.sha256() != trusted_vk_sha256 {
    return Err("verifying key SHA-256 differs from trusted digest".into());
  }
  vk.validate_structure()?;

  let n_bsb = vk.qcp.len();
  if proof.bsb22_commitments.len() != n_bsb {
    return Err(format!(
      "proof BSB22 commitment count {} differs from VK {n_bsb}",
      proof.bsb22_commitments.len()
    ));
  }
  if proof.claimed_values.len() != 6 + n_bsb {
    return Err(format!(
      "proof claimed evaluation count {} differs from expected {}",
      proof.claimed_values.len(),
      6 + n_bsb
    ));
  }
  if public_inputs.len() != vk.num_public_inputs {
    return Err(format!(
      "public input count {} differs from VK {}",
      public_inputs.len(),
      vk.num_public_inputs
    ));
  }

  // Strict curve + prime-order subgroup check on every proof G1 point.
  for (i, &p) in proof.lro.iter().enumerate() {
    check_g1_subgroup::<C>(p, &format!("proof.lro[{i}]"))?;
  }
  check_g1_subgroup::<C>(proof.z, "proof.z")?;
  for (i, &p) in proof.h.iter().enumerate() {
    check_g1_subgroup::<C>(p, &format!("proof.h[{i}]"))?;
  }
  for (i, &p) in proof.bsb22_commitments.iter().enumerate() {
    check_g1_subgroup::<C>(p, &format!("proof.bsb22[{i}]"))?;
  }
  check_g1_subgroup::<C>(proof.w_zeta, "proof.w_zeta")?;
  check_g1_subgroup::<C>(proof.w_zeta_omega, "proof.w_zeta_omega")?;

  // 1. Replay SHA-256 Fiat-Shamir transcript.
  let (gamma_raw, gamma) = derive_gamma::<C>(
    &vk.s,
    &[vk.ql, vk.qr, vk.qm, vk.qo, vk.qk],
    &vk.qcp,
    public_inputs,
    &proof.lro,
  );
  let (beta_raw, beta) = derive_beta::<C>(&gamma_raw);
  let (alpha_raw, alpha) =
    derive_alpha::<C>(&beta_raw, &proof.bsb22_commitments, proof.z);
  let (_, zeta) = derive_zeta::<C>(&alpha_raw, &proof.h);

  let n_u64 = u64::try_from(vk.domain_size).expect("domain fits u64");
  let zeta_n = zeta.pow([n_u64]);
  let zh_zeta = zeta_n - C::FR_ONE;
  if zh_zeta.is_zero() {
    return Err("degenerate Fiat-Shamir challenge zeta in domain H".into());
  }

  // 2. Compute PI(zeta) = Σ_{i<np} pub[i]·L_i(zeta) + Σ_k hash_fr(C_k)·L_{np+cci_k}(zeta).
  let mut pi_zeta = C::FR_ZERO;
  if !public_inputs.is_empty() {
    let mut dens = Vec::with_capacity(public_inputs.len());
    let mut w = C::FR_ONE;
    for _ in 0..public_inputs.len() {
      dens.push(zeta - w);
      w *= vk.omega;
    }
    batch_invert_in_place::<C>(&mut dens)?;
    let zn = zh_zeta * vk.domain_size_inv;
    let mut w = C::FR_ONE;
    for (&pub_val, inv_d) in public_inputs.iter().zip(dens) {
      pi_zeta += pub_val * (w * zn * inv_d);
      w *= vk.omega;
    }
  }
  for (i, &cci) in vk.commitment_constraint_indexes.iter().enumerate() {
    let h_fr = hash_fr_bsb22::<C>(proof.bsb22_commitments[i]);
    let idx = u64::try_from(vk.num_public_inputs).expect("fits u64") + cci;
    let wi = vk.omega.pow([idx]);
    let inv_den =
      (zeta - wi).inverse().ok_or("degenerate zeta at commitment row")?;
    let li = wi * vk.domain_size_inv * zh_zeta * inv_den;
    pi_zeta += h_fr * li;
  }

  // 3. Expected linearized polynomial evaluation at zeta.
  let inv_zeta_m1 =
    (zeta - C::FR_ONE).inverse().ok_or("degenerate zeta == 1")?;
  let l0_zeta = zh_zeta * vk.domain_size_inv * inv_zeta_m1;
  let alpha2_l0 = alpha * alpha * l0_zeta;

  let l_z = proof.claimed_values[1];
  let r_z = proof.claimed_values[2];
  let o_z = proof.claimed_values[3];
  let s1_z = proof.claimed_values[4];
  let s2_z = proof.claimed_values[5];
  let z_wz = proof.z_shifted_eval;

  let expected_lin_eval = -(pi_zeta - alpha2_l0
    + alpha
      * z_wz
      * (l_z + beta * s1_z + gamma)
      * (r_z + beta * s2_z + gamma)
      * (o_z + gamma));

  if check_claimed_lin && proof.claimed_values[0] != expected_lin_eval {
    return Err("PLONK algebraic linearized opening mismatch".into());
  }

  // 4. Recompute linearized polynomial commitment.
  let k1 = vk.coset_shift;
  let k2 = k1 * k1;
  let s1_coeff = alpha
    * z_wz
    * (l_z + beta * s1_z + gamma)
    * (r_z + beta * s2_z + gamma)
    * beta;
  let bz = beta * zeta;
  let coeff_z = alpha2_l0
    - alpha
      * (l_z + bz + gamma)
      * (r_z + k1 * bz + gamma)
      * (o_z + k2 * bz + gamma);
  let rl_z = l_z * r_z;
  let zeta_n2 = zeta.pow([n_u64 + 2]);
  let zeta_2n2 = zeta_n2 * zeta_n2;
  let neg_zh = -zh_zeta;

  let mut lin_com = G1ProjectiveOf::<C>::from(vk.ql) * l_z
    + G1ProjectiveOf::<C>::from(vk.qr) * r_z
    + G1ProjectiveOf::<C>::from(vk.qm) * rl_z
    + G1ProjectiveOf::<C>::from(vk.qo) * o_z
    + G1ProjectiveOf::<C>::from(vk.qk)
    + G1ProjectiveOf::<C>::from(vk.s[2]) * s1_coeff
    + G1ProjectiveOf::<C>::from(proof.z) * coeff_z
    + G1ProjectiveOf::<C>::from(proof.h[0]) * neg_zh
    + G1ProjectiveOf::<C>::from(proof.h[1]) * (neg_zh * zeta_n2)
    + G1ProjectiveOf::<C>::from(proof.h[2]) * (neg_zh * zeta_2n2);
  for i in 0..n_bsb {
    lin_com += G1ProjectiveOf::<C>::from(proof.bsb22_commitments[i])
      * proof.claimed_values[6 + i];
  }
  let lin_com_aff = lin_com.into_affine();

  // 5. Fold batch openings at zeta using gamma_kzg.
  let mut digests = Vec::with_capacity(6 + n_bsb);
  digests.push(lin_com_aff);
  digests.push(proof.lro[0]);
  digests.push(proof.lro[1]);
  digests.push(proof.lro[2]);
  digests.push(vk.s[0]);
  digests.push(vk.s[1]);
  digests.extend_from_slice(&vk.qcp);

  let mut claimed = Vec::with_capacity(6 + n_bsb);
  claimed.push(expected_lin_eval);
  claimed.extend_from_slice(&proof.claimed_values[1..]);

  let gamma_kzg = derive_gamma_kzg::<C>(zeta, &digests, &claimed, z_wz);

  let mut folded_digest = G1ProjectiveOf::<C>::from(digests[0]);
  let mut folded_eval = claimed[0];
  let mut g_pow = gamma_kzg;
  for i in 1..digests.len() {
    folded_digest += G1ProjectiveOf::<C>::from(digests[i]) * g_pow;
    folded_eval += claimed[i] * g_pow;
    g_pow *= gamma_kzg;
  }
  let folded_digest_aff = folded_digest.into_affine();

  // 6. Final 2-pairing KZG check combining openings at zeta and omega*zeta.
  let random = derive_batch_verify_random::<C>(
    folded_digest_aff,
    proof.w_zeta,
    proof.z,
    proof.w_zeta_omega,
    zeta,
    gamma_kzg,
  );
  let total_eval = folded_eval + random * z_wz;
  let zeta_omega = zeta * vk.omega;

  let lhs_g1 = folded_digest + G1ProjectiveOf::<C>::from(proof.z) * random
    - G1ProjectiveOf::<C>::from(vk.g1) * total_eval
    + G1ProjectiveOf::<C>::from(proof.w_zeta) * zeta
    + G1ProjectiveOf::<C>::from(proof.w_zeta_omega) * (random * zeta_omega);
  let rhs_g1 = -(G1ProjectiveOf::<C>::from(proof.w_zeta)
    + G1ProjectiveOf::<C>::from(proof.w_zeta_omega) * random);

  let pairing = C::PairingCurve::multi_pairing(
    [lhs_g1.into_affine(), rhs_g1.into_affine()],
    [vk.g2, vk.tau_g2],
  );
  if !pairing.is_zero() {
    return Err("PLONK final KZG pairing verification failed".into());
  }
  Ok(())
}
