//! Deterministic **DEV / UNSAFE** BN254 Groth16 setup (NO trusted setup ceremony).
//!
//! # Security Warning
//! `setup_dev` derives all trapdoor scalars `(τ, α, β, γ, δ)` deterministically
//! from a public seed via BLAKE3 XOF. Anyone who knows the seed can reconstruct
//! the trapdoors and forge arbitrary proofs. This setup MUST ONLY be used for
//! development, testing, and demonstration circuits — NEVER for production
//! security.

use super::r1cs::R1cs;
use ark_bn254::{Fr, G1Affine, G1Projective, G2Affine, G2Projective};
use ark_ec::{AffineRepr, CurveGroup, PrimeGroup};
use ark_ff::{AdditiveGroup, Field, PrimeField, Zero};
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
use p3_maybe_rayon::prelude::*;

const DEV_SETUP_DOMAIN: &[u8] = b"ix/groth16/bn254/dev-unsafe-setup/v1";

/// BN254 Groth16 verifying key.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifyingKey {
  /// `[α]_1`
  pub alpha_g1: G1Affine,
  /// `[β]_2`
  pub beta_g2: G2Affine,
  /// `[γ]_2`
  pub gamma_g2: G2Affine,
  /// `[δ]_2`
  pub delta_g2: G2Affine,
  /// Public input query points `IC[0..=num_public]`, where
  /// `IC[i] = [(β·u_i(τ) + α·v_i(τ) + w_i(τ)) / γ]_1`.
  pub ic: Vec<G1Affine>,
}

impl VerifyingKey {
  /// Number of public inputs accepted by this verifying key (`ic.len() - 1`).
  pub const fn num_public_inputs(&self) -> usize {
    self.ic.len().saturating_sub(1)
  }

  /// Validate curve membership, prime-order subgroup membership, and structure.
  pub fn validate(&self) -> Result<(), String> {
    if self.ic.is_empty() {
      return Err("verifying key IC vector cannot be empty".into());
    }
    check_g1_valid(&self.alpha_g1, "vk.alpha_g1")?;
    check_g2_valid(&self.beta_g2, "vk.beta_g2")?;
    check_g2_valid(&self.gamma_g2, "vk.gamma_g2")?;
    check_g2_valid(&self.delta_g2, "vk.delta_g2")?;
    if self.gamma_g2.is_zero() {
      return Err("vk.gamma_g2 cannot be the point at infinity".into());
    }
    if self.delta_g2.is_zero() {
      return Err("vk.delta_g2 cannot be the point at infinity".into());
    }
    for (idx, pt) in self.ic.iter().enumerate() {
      check_g1_valid(pt, &format!("vk.ic[{idx}]"))?;
    }
    Ok(())
  }
}

/// BN254 Groth16 proving key containing QAP query tables and R1CS structure.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProvingKey {
  pub vk: VerifyingKey,
  /// `[β]_1`
  pub beta_g1: G1Affine,
  /// `[δ]_1`
  pub delta_g1: G1Affine,
  /// `[u_j(τ)]_1` for every wire `j ∈ 0..num_wires`.
  pub a_query: Vec<G1Affine>,
  /// `[v_j(τ)]_1` for every wire `j ∈ 0..num_wires`.
  pub b_g1_query: Vec<G1Affine>,
  /// `[v_j(τ)]_2` for every wire `j ∈ 0..num_wires`.
  pub b_g2_query: Vec<G2Affine>,
  /// `[(β·u_j(τ) + α·v_j(τ) + w_j(τ)) / δ]_1` for private wires
  /// `j ∈ (1 + num_public)..num_wires`.
  pub l_query: Vec<G1Affine>,
  /// `[τ^k · Z_H(τ) / δ]_1` for `k ∈ 0..(domain_size - 1)`.
  pub h_query: Vec<G1Affine>,
  /// Power-of-two QAP domain size `N`.
  pub domain_size: usize,
  /// Underlying R1CS constraint system.
  pub r1cs: R1cs,
}

fn check_g1_valid(p: &G1Affine, label: &str) -> Result<(), String> {
  if !p.is_on_curve() {
    return Err(format!("{label} is not on the BN254 G1 curve"));
  }
  if !p.is_in_correct_subgroup_assuming_on_curve() {
    return Err(format!("{label} is not in the BN254 G1 prime-order subgroup"));
  }
  Ok(())
}

fn check_g2_valid(p: &G2Affine, label: &str) -> Result<(), String> {
  if !p.is_on_curve() {
    return Err(format!("{label} is not on the BN254 G2 twist curve"));
  }
  if !p.is_in_correct_subgroup_assuming_on_curve() {
    return Err(format!("{label} is not in the BN254 G2 prime-order subgroup"));
  }
  Ok(())
}

fn sample_nonzero_fr(xof: &mut blake3::OutputReader) -> Fr {
  let mut buf = [0u8; 64];
  loop {
    xof.fill(&mut buf);
    let val = Fr::from_le_bytes_mod_order(&buf);
    if !val.is_zero() {
      return val;
    }
  }
}

fn sample_tau_outside_domain(
  xof: &mut blake3::OutputReader,
  domain_size: usize,
) -> Fr {
  let n_u64 = u64::try_from(domain_size).expect("domain_size fits u64");
  loop {
    let tau = sample_nonzero_fr(xof);
    if tau.pow([n_u64]) != Fr::ONE {
      return tau;
    }
  }
}

fn scale_g1_batch(scalars: &[Fr]) -> Vec<G1Affine> {
  let g1 = G1Projective::generator();
  let proj: Vec<G1Projective> = scalars.par_iter().map(|&s| g1 * s).collect();
  G1Projective::normalize_batch(&proj)
}

fn scale_g2_batch(scalars: &[Fr]) -> Vec<G2Affine> {
  let g2 = G2Projective::generator();
  let proj: Vec<G2Projective> = scalars.par_iter().map(|&s| g2 * s).collect();
  G2Projective::normalize_batch(&proj)
}

/// Deterministic **DEV / UNSAFE** BN254 Groth16 setup from an arbitrary seed.
///
/// **WARNING (NO TRUSTED SETUP CEREMONY):** Derives toxic-waste trapdoors
/// `(τ, α, β, γ, δ)` deterministically from `seed` via BLAKE3 XOF. Suitable
/// only for development, testing, and demonstration circuits.
pub fn setup_dev(
  r1cs: &R1cs,
  seed: &[u8],
) -> Result<(ProvingKey, VerifyingKey), String> {
  r1cs.validate()?;
  let domain_size = r1cs.domain_size();
  let domain =
    Radix2EvaluationDomain::<Fr>::new(domain_size).ok_or_else(|| {
      format!("domain size {domain_size} exceeds BN254 2-adicity")
    })?;

  let mut hasher = blake3::Hasher::new();
  hasher.update(DEV_SETUP_DOMAIN);
  hasher.update(&(u64::try_from(domain_size).expect("u64")).to_le_bytes());
  hasher.update(&(u64::try_from(r1cs.num_wires).expect("u64")).to_le_bytes());
  hasher.update(&(u64::try_from(r1cs.num_public).expect("u64")).to_le_bytes());
  hasher.update(
    &(u64::try_from(r1cs.constraints.len()).expect("u64")).to_le_bytes(),
  );
  hasher.update(&(u64::try_from(seed.len()).expect("u64")).to_le_bytes());
  hasher.update(seed);
  let mut xof = hasher.finalize_xof();

  let tau = sample_tau_outside_domain(&mut xof, domain_size);
  let alpha = sample_nonzero_fr(&mut xof);
  let beta = sample_nonzero_fr(&mut xof);
  let gamma = sample_nonzero_fr(&mut xof);
  let delta = sample_nonzero_fr(&mut xof);

  let lagrange = domain.evaluate_all_lagrange_coefficients(tau);

  let mut u_eval = vec![Fr::ZERO; r1cs.num_wires];
  let mut v_eval = vec![Fr::ZERO; r1cs.num_wires];
  let mut w_eval = vec![Fr::ZERO; r1cs.num_wires];

  for (k, con) in r1cs.constraints.iter().enumerate() {
    let lk = lagrange[k];
    for &(wire, coeff) in con.a.terms() {
      u_eval[wire] += coeff * lk;
    }
    for &(wire, coeff) in con.b.terms() {
      v_eval[wire] += coeff * lk;
    }
    for &(wire, coeff) in con.c.terms() {
      w_eval[wire] += coeff * lk;
    }
  }

  // Public-input anchoring rows: z_i · 0 = 0 at k = num_constraints + i.
  let num_instance = r1cs.num_instance_wires();
  let anchor_base = r1cs.constraints.len();
  for i in 0..num_instance {
    u_eval[i] += lagrange[anchor_base + i];
  }

  let gamma_inv = gamma.inverse().expect("gamma is nonzero");
  let delta_inv = delta.inverse().expect("delta is nonzero");

  let ic_scalars: Vec<Fr> = (0..num_instance)
    .map(|i| (beta * u_eval[i] + alpha * v_eval[i] + w_eval[i]) * gamma_inv)
    .collect();

  let l_scalars: Vec<Fr> = (num_instance..r1cs.num_wires)
    .map(|j| (beta * u_eval[j] + alpha * v_eval[j] + w_eval[j]) * delta_inv)
    .collect();

  let z_h_tau = tau
    .pow([u64::try_from(domain_size).expect("domain_size fits u64")])
    - Fr::ONE;
  let mut h_scalars = Vec::with_capacity(domain_size - 1);
  let mut term = z_h_tau * delta_inv;
  for _ in 0..(domain_size - 1) {
    h_scalars.push(term);
    term *= tau;
  }

  let g1 = G1Projective::generator();
  let g2 = G2Projective::generator();
  let alpha_g1 = (g1 * alpha).into_affine();
  let beta_g1 = (g1 * beta).into_affine();
  let delta_g1 = (g1 * delta).into_affine();
  let beta_g2 = (g2 * beta).into_affine();
  let gamma_g2 = (g2 * gamma).into_affine();
  let delta_g2 = (g2 * delta).into_affine();

  let ic = scale_g1_batch(&ic_scalars);
  let a_query = scale_g1_batch(&u_eval);
  let b_g1_query = scale_g1_batch(&v_eval);
  let b_g2_query = scale_g2_batch(&v_eval);
  let l_query = scale_g1_batch(&l_scalars);
  let h_query = scale_g1_batch(&h_scalars);

  let vk = VerifyingKey { alpha_g1, beta_g2, gamma_g2, delta_g2, ic };
  vk.validate()?;

  let pk = ProvingKey {
    vk: vk.clone(),
    beta_g1,
    delta_g1,
    a_query,
    b_g1_query,
    b_g2_query,
    l_query,
    h_query,
    domain_size,
    r1cs: r1cs.clone(),
  };

  Ok((pk, vk))
}
