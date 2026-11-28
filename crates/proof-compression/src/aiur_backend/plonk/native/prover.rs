//! Curve-generic zero-knowledge PLONK + BSB22 prover (`Bn254` & `Bls12381`).
//!
//! Produces both compact native proofs (`IXNPPR01`) and exact gnark
//! `MarshalSolidity` proof bytes compatible with `PlonkVerifier.sol` (BN254)
//! and `Bls12381PlonkVerifier.sol` (BLS12-381).

use super::cuda_accel::PlonkAccelerator;
use super::preprocess::{ProvingKey, permutation_support};
use super::scs_file::ScsFile;
use super::solver::{
  batch_invert_in_place, parse_binary_witness, solve_post_commitment,
  solve_pre_commitment,
};
use super::transcript::{
  decode_fr_be_canonical, decode_g1_raw, derive_alpha, derive_beta,
  derive_gamma, derive_gamma_kzg, derive_zeta, fr_be_bytes, g1_raw_bytes,
  g1_raw_len, hash_fr_bsb22,
};
use crate::kzg::curve::{
  Curve, G1AffineOf, G1ProjectiveOf, KzgCurve, read_g1_compressed_for,
};
use ark_ec::CurveGroup;
use ark_ff::{Field, PrimeField, Zero};
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use p3_maybe_rayon::prelude::*;
use serde::{Deserialize, Serialize};
use std::io::Read;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Instant, SystemTime, UNIX_EPOCH};

const PROOF_MAGIC: &[u8; 8] = b"IXNPPR01";
static RNG_COUNTER: AtomicU64 = AtomicU64::new(0);

/// Timing breakdown for a native PLONK proof generation run.
#[derive(Clone, Copy, Debug, Default, Serialize, Deserialize)]
pub struct ProverTimings {
  pub witness_pre_ms: f64,
  pub bsb22_commit_ms: f64,
  pub witness_post_ms: f64,
  pub commit_lro_ms: f64,
  pub grand_product_ms: f64,
  pub quotient_ms: f64,
  pub opening_ms: f64,
  pub total_ms: f64,
}

/// Serialized proof pair returned by [`super::NativeProver`].
#[derive(Clone, Debug)]
pub struct ProofBundle {
  pub native: Vec<u8>,
  pub solidity: Vec<u8>,
  pub timings: ProverTimings,
}

/// Complete PLONK + BSB22 proof over curve `C`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeProof<C: KzgCurve> {
  pub lro: [G1AffineOf<C>; 3],
  pub z: G1AffineOf<C>,
  pub h: [G1AffineOf<C>; 3],
  pub bsb22_commitments: Vec<G1AffineOf<C>>,
  /// Claimed evaluations at `zeta`: `[r(ζ), L(ζ), R(ζ), O(ζ), S1(ζ), S2(ζ), Qcp_0(ζ), ...]`.
  pub claimed_values: Vec<C::Fr>,
  /// Batched KZG opening witness at `zeta`.
  pub w_zeta: G1AffineOf<C>,
  /// Claimed evaluation `Z(ωζ)`.
  pub z_shifted_eval: C::Fr,
  /// Single KZG opening witness of `Z` at `ωζ`.
  pub w_zeta_omega: G1AffineOf<C>,
}

fn curve_tag<C: KzgCurve>() -> u8 {
  match C::CURVE {
    Curve::Bn254 => 1,
    Curve::Bls12381 => 2,
  }
}

impl<C: KzgCurve> NativeProof<C> {
  /// Serialize to versioned compressed native format (`IXNPPR01`).
  pub fn to_native_bytes(&self) -> Result<Vec<u8>, String> {
    let mut out = Vec::new();
    out.extend_from_slice(PROOF_MAGIC);
    out.push(curve_tag::<C>());
    out.extend_from_slice(
      &u32::try_from(self.bsb22_commitments.len())
        .expect("fits u32")
        .to_le_bytes(),
    );
    for p in self
      .lro
      .iter()
      .chain(core::iter::once(&self.z))
      .chain(self.h.iter())
      .chain(self.bsb22_commitments.iter())
      .chain([&self.w_zeta, &self.w_zeta_omega])
    {
      p.serialize_compressed(&mut out).map_err(|e| e.to_string())?;
    }
    for &v in
      self.claimed_values.iter().chain(core::iter::once(&self.z_shifted_eval))
    {
      v.serialize_compressed(&mut out).map_err(|e| e.to_string())?;
    }
    Ok(out)
  }

  /// Deserialize from native format with strict curve, subgroup, canonicality,
  /// and trailing-byte checks.
  pub fn from_native_bytes(mut input: &[u8]) -> Result<Self, String> {
    if input.len() < 13 || &input[..8] != PROOF_MAGIC {
      return Err("invalid native PLONK proof magic".into());
    }
    if input[8] != curve_tag::<C>() {
      return Err("native PLONK proof curve mismatch".into());
    }
    let n_bsb =
      u32::from_le_bytes(input[9..13].try_into().expect("4 bytes")) as usize;
    if n_bsb > 16 {
      return Err("too many BSB22 commitments in proof".into());
    }
    input = &input[13..];
    let read_g1 = |inp: &mut &[u8]| -> Result<G1AffineOf<C>, String> {
      read_g1_compressed_for::<C>(inp)
        .map_err(|e| format!("invalid proof G1 point: {e}"))
    };
    let read_fr = |inp: &mut &[u8]| -> Result<C::Fr, String> {
      C::Fr::deserialize_compressed(inp)
        .map_err(|e| format!("invalid proof Fr scalar: {e}"))
    };
    let lro =
      [read_g1(&mut input)?, read_g1(&mut input)?, read_g1(&mut input)?];
    let z = read_g1(&mut input)?;
    let h = [read_g1(&mut input)?, read_g1(&mut input)?, read_g1(&mut input)?];
    let mut bsb22_commitments = Vec::with_capacity(n_bsb);
    for _ in 0..n_bsb {
      bsb22_commitments.push(read_g1(&mut input)?);
    }
    let w_zeta = read_g1(&mut input)?;
    let w_zeta_omega = read_g1(&mut input)?;
    let mut claimed_values = Vec::with_capacity(6 + n_bsb);
    for _ in 0..6 + n_bsb {
      claimed_values.push(read_fr(&mut input)?);
    }
    let z_shifted_eval = read_fr(&mut input)?;
    if !input.is_empty() {
      return Err("trailing bytes in native PLONK proof".into());
    }
    Ok(Self {
      lro,
      z,
      h,
      bsb22_commitments,
      claimed_values,
      w_zeta,
      z_shifted_eval,
      w_zeta_omega,
    })
  }

  /// Exact gnark `MarshalSolidity` encoding matching `PlonkVerifier.sol`
  /// (BN254: `0x300 + 0x60 * k` = 864 B for `k = 1`) and
  /// `Bls12381PlonkVerifier.sol` (BLS12-381: `0x420 + 0x80 * k` = 1184 B for `k = 1`).
  pub fn marshal_solidity(&self) -> Vec<u8> {
    let g1_w = g1_raw_len::<C>();
    let n_bsb = self.bsb22_commitments.len();
    assert_eq!(self.claimed_values.len(), 6 + n_bsb);
    let fixed = 9 * g1_w + 6 * 32;
    let mut out = Vec::with_capacity(fixed + n_bsb * (g1_w + 32));
    for &p in &self.lro {
      out.extend_from_slice(&g1_raw_bytes::<C>(p));
    }
    for &p in &self.h {
      out.extend_from_slice(&g1_raw_bytes::<C>(p));
    }
    // L(ζ), R(ζ), O(ζ), S1(ζ), S2(ζ) — skipping claimed_values[0] = r(ζ).
    for &v in &self.claimed_values[1..6] {
      out.extend_from_slice(&fr_be_bytes::<C>(v));
    }
    out.extend_from_slice(&g1_raw_bytes::<C>(self.z));
    out.extend_from_slice(&fr_be_bytes::<C>(self.z_shifted_eval));
    out.extend_from_slice(&g1_raw_bytes::<C>(self.w_zeta));
    out.extend_from_slice(&g1_raw_bytes::<C>(self.w_zeta_omega));
    for &v in &self.claimed_values[6..] {
      out.extend_from_slice(&fr_be_bytes::<C>(v));
    }
    for &p in &self.bsb22_commitments {
      out.extend_from_slice(&g1_raw_bytes::<C>(p));
    }
    out
  }

  /// Decode gnark `MarshalSolidity` bytes with strict curve, subgroup, and
  /// scalar canonicality checks. `claimed_values[0]` (linearized evaluation)
  /// is initialized to zero and recomputed by the verifier.
  pub fn unmarshal_solidity(
    bytes: &[u8],
    num_custom_gates: usize,
  ) -> Result<Self, String> {
    let g1_w = g1_raw_len::<C>();
    let expected = 9 * g1_w + 6 * 32 + num_custom_gates * (g1_w + 32);
    if bytes.len() != expected {
      return Err(format!(
        "wrong Solidity proof length: got {}, expected {expected}",
        bytes.len()
      ));
    }
    let mut off = 0usize;
    let take_g1 = |off: &mut usize| -> Result<G1AffineOf<C>, String> {
      let pt = decode_g1_raw::<C>(&bytes[*off..*off + g1_w])?;
      *off += g1_w;
      Ok(pt)
    };
    let take_fr = |off: &mut usize| -> Result<C::Fr, String> {
      let word: &[u8; 32] =
        bytes[*off..*off + 32].try_into().expect("32 bytes");
      *off += 32;
      decode_fr_be_canonical::<C>(word)
    };
    let lro = [take_g1(&mut off)?, take_g1(&mut off)?, take_g1(&mut off)?];
    let h = [take_g1(&mut off)?, take_g1(&mut off)?, take_g1(&mut off)?];
    let mut claimed_values = Vec::with_capacity(6 + num_custom_gates);
    claimed_values.push(C::FR_ZERO);
    for _ in 0..5 {
      claimed_values.push(take_fr(&mut off)?);
    }
    let z = take_g1(&mut off)?;
    let z_shifted_eval = take_fr(&mut off)?;
    let w_zeta = take_g1(&mut off)?;
    let w_zeta_omega = take_g1(&mut off)?;
    for _ in 0..num_custom_gates {
      claimed_values.push(take_fr(&mut off)?);
    }
    let mut bsb22_commitments = Vec::with_capacity(num_custom_gates);
    for _ in 0..num_custom_gates {
      bsb22_commitments.push(take_g1(&mut off)?);
    }
    if off != bytes.len() {
      return Err(format!(
        "Solidity proof decode offset mismatch: consumed {off}, expected {}",
        bytes.len()
      ));
    }
    Ok(Self {
      lro,
      z,
      h,
      bsb22_commitments,
      claimed_values,
      w_zeta,
      z_shifted_eval,
      w_zeta_omega,
    })
  }
}

/// Cryptographic blinding RNG backed by BLAKE3 XOF seeded from OS `/dev/urandom`
/// (or an explicit seed for deterministic tests).
struct BlindingRng {
  xof: blake3::OutputReader,
}

impl BlindingRng {
  fn from_os() -> Result<Self, String> {
    let mut entropy = [0u8; 32];
    let mut file = std::fs::File::open("/dev/urandom")
      .map_err(|e| format!("failed to open /dev/urandom: {e}"))?;
    file
      .read_exact(&mut entropy)
      .map_err(|e| format!("failed to read OS entropy: {e}"))?;
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"ix-aiur-native-plonk/blinding-os/v1");
    hasher.update(&entropy);
    let nanos =
      SystemTime::now().duration_since(UNIX_EPOCH).map_or(0, |d| d.as_nanos());
    hasher.update(&nanos.to_le_bytes());
    hasher.update(&std::process::id().to_le_bytes());
    hasher.update(&RNG_COUNTER.fetch_add(1, Ordering::Relaxed).to_le_bytes());
    Ok(Self { xof: hasher.finalize_xof() })
  }

  fn from_seed(seed: [u8; 32]) -> Self {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"ix-aiur-native-plonk/blinding-seed/v1");
    hasher.update(&seed);
    Self { xof: hasher.finalize_xof() }
  }

  fn next_fr<C: KzgCurve>(&mut self) -> C::Fr {
    let mut wide = [0u8; 64];
    self.xof.fill(&mut wide);
    C::Fr::from_le_bytes_mod_order(&wide)
  }
}

/// Evaluate polynomial `coeffs` (little-endian degree order) at `x` via Horner.
pub(super) fn eval_poly<C: KzgCurve>(coeffs: &[C::Fr], x: C::Fr) -> C::Fr {
  let mut acc = C::FR_ZERO;
  for &c in coeffs.iter().rev() {
    acc = acc * x + c;
  }
  acc
}

/// Compute `(f(X) - f(a)) / (X - a)` in canonical monomial basis.
fn synthetic_divide<C: KzgCurve>(
  coeffs: &[C::Fr],
  fa: C::Fr,
  a: C::Fr,
) -> Result<Vec<C::Fr>, String> {
  if coeffs.len() < 2 {
    return Ok(Vec::new());
  }
  let mut f = coeffs.to_vec();
  f[0] -= fa;
  for i in (0..f.len() - 1).rev() {
    let carry = f[i + 1] * a;
    f[i] += carry;
  }
  if !f[0].is_zero() {
    return Err(
      "polynomial synthetic division left a nonzero remainder".into(),
    );
  }
  f.remove(0);
  Ok(f)
}

/// Blind a degree-`< N` monomial polynomial `p` by `b(X) * (X^N - 1)`.
fn blind_monomial<C: KzgCurve>(p: &[C::Fr], b: &[C::Fr]) -> Vec<C::Fr> {
  let n = p.len();
  let mut out = Vec::with_capacity(n + b.len());
  out.extend_from_slice(p);
  out.extend_from_slice(b);
  for (i, &bi) in b.iter().enumerate() {
    out[i] -= bi;
  }
  out
}

/// Prove from a gnark-encoded binary witness file/buffer.
pub fn prove_binary_witness<C: KzgCurve>(
  scs: &ScsFile<C>,
  pk: &ProvingKey<C>,
  witness_bytes: &[u8],
  expected_publics: &[C::Fr],
  accel: &PlonkAccelerator<C>,
) -> Result<(NativeProof<C>, ProverTimings), String> {
  let input_wires =
    parse_binary_witness::<C>(witness_bytes, scs.publics, scs.cells)?;
  prove(scs, pk, &input_wires, expected_publics, accel)
}

/// Generate a fresh randomized zero-knowledge PLONK + BSB22 proof.
pub fn prove<C: KzgCurve>(
  scs: &ScsFile<C>,
  pk: &ProvingKey<C>,
  input_wires: &[C::Fr],
  expected_publics: &[C::Fr],
  accel: &PlonkAccelerator<C>,
) -> Result<(NativeProof<C>, ProverTimings), String> {
  let mut rng = BlindingRng::from_os()?;
  prove_internal(scs, pk, input_wires, expected_publics, accel, &mut rng)
}

/// Generate a deterministic PLONK + BSB22 proof from an explicit 32-byte
/// blinding seed (for reproducible tests and benchmarks).
pub fn prove_with_seed<C: KzgCurve>(
  scs: &ScsFile<C>,
  pk: &ProvingKey<C>,
  input_wires: &[C::Fr],
  expected_publics: &[C::Fr],
  accel: &PlonkAccelerator<C>,
  seed: [u8; 32],
) -> Result<(NativeProof<C>, ProverTimings), String> {
  let mut rng = BlindingRng::from_seed(seed);
  prove_internal(scs, pk, input_wires, expected_publics, accel, &mut rng)
}

fn prove_internal<C: KzgCurve>(
  scs: &ScsFile<C>,
  pk: &ProvingKey<C>,
  input_wires: &[C::Fr],
  expected_publics: &[C::Fr],
  accel: &PlonkAccelerator<C>,
  rng: &mut BlindingRng,
) -> Result<(NativeProof<C>, ProverTimings), String> {
  let t_total = Instant::now();
  let mut timings = ProverTimings::default();

  // Check circuit/PK consistency and public statement match.
  if !scs.outputs.is_empty() {
    return Err(format!(
      "native PLONK-SCS does not synthesize in-circuit pairing constraints \
       for deferred scs.outputs (got {} output wires); self-contained \
       outputs == 0 circuits are required",
      scs.outputs.len()
    ));
  }
  let n = pk.vk.domain_size;
  let np = scs.publics;
  let nc = scs.commits.len();
  if np != pk.vk.num_public_inputs
    || scs.pre != pk.pre_gates
    || scs.gates_count != pk.total_gates
    || nc != pk.commits_len
  {
    return Err("proving key shape does not match SCS file".into());
  }
  if expected_publics.len() != np {
    return Err(format!(
      "expected {np} public inputs, got {}",
      expected_publics.len()
    ));
  }
  if input_wires.len() != scs.cells {
    return Err(format!(
      "expected {} input wires, got {}",
      scs.cells,
      input_wires.len()
    ));
  }
  if &input_wires[..np] != expected_publics {
    return Err("witness public inputs differ from expected statement".into());
  }
  if pk.vk.commitment_constraint_indexes.len() != 1 {
    return Err("native PLONK expects exactly one BSB22 commitment".into());
  }
  let commitment_constraint_index =
    usize::try_from(pk.vk.commitment_constraint_indexes[0])
      .map_err(|e| e.to_string())?;
  let expected_commit_idx = scs
    .pre
    .checked_add(nc)
    .ok_or_else(|| "BSB22 commitment index overflow".to_owned())?;
  if commitment_constraint_index != expected_commit_idx {
    return Err(format!(
      "proving key commitment_constraint_index {commitment_constraint_index} \
       differs from SCS pre + commits ({expected_commit_idx})"
    ));
  }
  let commit_row = np
    .checked_add(commitment_constraint_index)
    .ok_or_else(|| "BSB22 commitment row index overflow".to_owned())?;
  if n < 2 || commit_row >= n - 1 {
    return Err(format!(
      "BSB22 commitment row {commit_row} collides with Pi(X) blinding row \
       (domain_size = {n})"
    ));
  }

  // 1. Phase 1 witness solve (pre-commitment).
  let t0 = Instant::now();
  let pre_state = solve_pre_commitment(scs, input_wires)?;
  timings.witness_pre_ms = t0.elapsed().as_secs_f64() * 1e3;

  // 2. BSB22 commitment Pi(X) + challenge hash_fr(C_bsb22).
  let t0 = Instant::now();
  let mut pi_coeffs = vec![C::FR_ZERO; n];
  for (k, &val) in pre_state.committed_values.iter().enumerate() {
    pi_coeffs[np + scs.pre + k] = val;
  }
  // Blind Pi(X) at two distinct rows where qCp == 0.
  pi_coeffs[commit_row] = rng.next_fr::<C>();
  pi_coeffs[n - 1] = rng.next_fr::<C>();
  accel.ifft_in_place(&mut pi_coeffs);
  let c_bsb22 = accel.msm(&pk.srs_g1[..n], &pi_coeffs).into_affine();
  let bsb22_gamma = hash_fr_bsb22::<C>(c_bsb22);
  timings.bsb22_commit_ms = t0.elapsed().as_secs_f64() * 1e3;

  // 3. Phase 2 witness solve (post-commitment).
  let t0 = Instant::now();
  let wires = solve_post_commitment(scs, pre_state, bsb22_gamma)?;
  timings.witness_post_ms = t0.elapsed().as_secs_f64() * 1e3;

  // 4. Populate L, R, O in Lagrange basis (unused slots carry wires[0] = s0).
  let t0 = Instant::now();
  let s0 = wires[0];
  let mut l_eval = vec![s0; n];
  let mut r_eval = vec![s0; n];
  let mut o_eval = vec![s0; n];

  l_eval[..np].copy_from_slice(&wires[..np]);
  for i in 0..scs.pre {
    let row = np + i;
    let g = scs.gate(i);
    l_eval[row] = wires[g.a as usize];
    r_eval[row] = wires[g.b as usize];
    o_eval[row] = wires[g.c as usize];
  }
  for (k, &w) in scs.commits.iter().enumerate() {
    l_eval[np + scs.pre + k] = wires[w as usize];
  }
  l_eval[commit_row] = wires[scs.gamma as usize];
  for i in scs.pre..scs.gates_count {
    let row = np + nc + 1 + i;
    let g = scs.gate(i);
    l_eval[row] = wires[g.a as usize];
    r_eval[row] = wires[g.b as usize];
    o_eval[row] = wires[g.c as usize];
  }

  let mut lro_coeffs = vec![l_eval.clone(), r_eval.clone(), o_eval.clone()];
  accel.ifft_batch(&mut lro_coeffs);
  let mut lro_it = lro_coeffs.into_iter();
  let l_coeffs = lro_it.next().unwrap();
  let r_coeffs = lro_it.next().unwrap();
  let o_coeffs = lro_it.next().unwrap();

  let bl = [rng.next_fr::<C>(), rng.next_fr::<C>()];
  let br = [rng.next_fr::<C>(), rng.next_fr::<C>()];
  let bo = [rng.next_fr::<C>(), rng.next_fr::<C>()];
  let bz = [rng.next_fr::<C>(), rng.next_fr::<C>(), rng.next_fr::<C>()];

  let l_blind = blind_monomial::<C>(&l_coeffs, &bl);
  let r_blind = blind_monomial::<C>(&r_coeffs, &br);
  let o_blind = blind_monomial::<C>(&o_coeffs, &bo);

  let lro_proj = accel.msm_batch(
    &pk.srs_g1[..n + 2],
    &[l_blind.as_slice(), r_blind.as_slice(), o_blind.as_slice()],
  );
  let lro_coms = [
    lro_proj[0].into_affine(),
    lro_proj[1].into_affine(),
    lro_proj[2].into_affine(),
  ];
  timings.commit_lro_ms = t0.elapsed().as_secs_f64() * 1e3;

  // 5. Fiat-Shamir gamma & beta, then build grand-product polynomial Z.
  let t0 = Instant::now();
  let (gamma_raw, gamma_fs) = derive_gamma::<C>(
    &pk.vk.s,
    &[pk.vk.ql, pk.vk.qr, pk.vk.qm, pk.vk.qo, pk.vk.qk],
    &pk.vk.qcp,
    expected_publics,
    &lro_coms,
  );
  let (beta_raw, beta_fs) = derive_beta::<C>(&gamma_raw);

  let omega = pk.vk.omega;
  let k1 = pk.vk.coset_shift;
  let k2 = k1 * k1;
  let support = permutation_support::<C>(n, omega, k1);

  let mut nums = vec![C::FR_ZERO; n];
  let mut dens = vec![C::FR_ZERO; n];
  nums.par_iter_mut().zip(dens.par_iter_mut()).enumerate().for_each(
    |(i, (num_slot, den_slot))| {
      let lv = l_eval[i];
      let rv = r_eval[i];
      let ov = o_eval[i];
      let a = lv + beta_fs * support[i] + gamma_fs;
      let b = rv + beta_fs * support[n + i] + gamma_fs;
      let c = ov + beta_fs * support[2 * n + i] + gamma_fs;
      *num_slot = a * b * c;

      let sa = lv + beta_fs * support[pk.permutation[i] as usize] + gamma_fs;
      let sb =
        rv + beta_fs * support[pk.permutation[n + i] as usize] + gamma_fs;
      let sc =
        ov + beta_fs * support[pk.permutation[2 * n + i] as usize] + gamma_fs;
      *den_slot = sa * sb * sc;
    },
  );
  batch_invert_in_place::<C>(&mut dens)
    .map_err(|e| format!("grand-product denominator inversion failed: {e}"))?;

  let mut z_coeffs = vec![C::FR_ONE; n];
  let mut running = C::FR_ONE;
  for i in 0..n - 1 {
    running *= nums[i] * dens[i];
    z_coeffs[i + 1] = running;
  }
  let closing = running * nums[n - 1] * dens[n - 1];
  if closing != C::FR_ONE {
    return Err("internal error: copy-constraint grand product != 1".into());
  }

  accel.ifft_in_place(&mut z_coeffs);
  let z_blind = blind_monomial::<C>(&z_coeffs, &bz);
  let z_com = accel.msm(&pk.srs_g1[..n + 3], &z_blind).into_affine();
  timings.grand_product_ms = t0.elapsed().as_secs_f64() * 1e3;

  // 6. Fiat-Shamir alpha, complete qK, and compute quotient H on 4 size-N cosets.
  let t0 = Instant::now();
  let (alpha_raw, alpha_fs) = derive_alpha::<C>(&beta_raw, &[c_bsb22], z_com);
  let alpha_sq = alpha_fs * alpha_fs;

  let mut pi_pub_coeffs = vec![C::FR_ZERO; n];
  pi_pub_coeffs[..np].copy_from_slice(expected_publics);
  pi_pub_coeffs[commit_row] = bsb22_gamma;
  accel.ifft_in_place(&mut pi_pub_coeffs);
  let qk_full_coeffs: Vec<C::Fr> =
    pk.qk_coeffs.par_iter().zip(&pi_pub_coeffs).map(|(&a, &b)| a + b).collect();

  let domain4 = Radix2EvaluationDomain::<C::Fr>::new(4 * n)
    .ok_or("4N quotient domain exceeds curve two-adicity")?;
  let w4 = domain4.group_gen();
  if w4.pow([4u64]) != omega {
    return Err("4N quotient domain generator does not match PK omega".into());
  }

  let mut h_evals_4n = vec![C::FR_ZERO; 4 * n];
  let n_u64 = u64::try_from(n).expect("domain fits u64");
  let inv_n = pk.vk.domain_size_inv;

  // Precompute powers of omega once for coset evaluations.
  let mut omega_pows = Vec::with_capacity(n);
  let mut w_acc = C::FR_ONE;
  for _ in 0..n {
    omega_pows.push(w_acc);
    w_acc *= omega;
  }

  let poly_refs: [&[C::Fr]; 14] = [
    &l_coeffs,
    &r_coeffs,
    &o_coeffs,
    &z_coeffs,
    &pk.ql_coeffs,
    &pk.qr_coeffs,
    &pk.qm_coeffs,
    &pk.qo_coeffs,
    &qk_full_coeffs,
    &pk.s1_coeffs,
    &pk.s2_coeffs,
    &pk.s3_coeffs,
    &pk.qcp_coeffs[0],
    &pi_coeffs,
  ];

  let mut s_r = k1;
  for r in 0..4usize {
    let zh_r = s_r.pow([n_u64]) - C::FR_ONE;
    let inv_zh_r =
      zh_r.inverse().ok_or("vanishing polynomial vanished on coset")?;
    let evals = accel.coset_fft_batch(&poly_refs, s_r);

    // Precompute (s_r * ω^j - 1)^{-1} via Montgomery batch inversion for L_0.
    let mut x_minus_1: Vec<C::Fr> =
      omega_pows.par_iter().map(|&wj| s_r * wj - C::FR_ONE).collect();
    batch_invert_in_place::<C>(&mut x_minus_1)?;

    let coset_h: Vec<C::Fr> = (0..n)
      .into_par_iter()
      .map(|j| {
        let x = s_r * omega_pows[j];
        let x_next = s_r * omega_pows[(j + 1) % n];

        let lv = evals[0][j] + zh_r * (bl[0] + bl[1] * x);
        let rv = evals[1][j] + zh_r * (br[0] + br[1] * x);
        let ov = evals[2][j] + zh_r * (bo[0] + bo[1] * x);
        let zv = evals[3][j] + zh_r * (bz[0] + x * (bz[1] + x * bz[2]));
        let zsv = evals[3][(j + 1) % n]
          + zh_r * (bz[0] + x_next * (bz[1] + x_next * bz[2]));

        let gate = evals[4][j] * lv
          + evals[5][j] * rv
          + evals[6][j] * lv * rv
          + evals[7][j] * ov
          + evals[8][j]
          + evals[12][j] * evals[13][j];

        let bx = beta_fs * x;
        let perm_r = zv
          * (lv + bx + gamma_fs)
          * (rv + k1 * bx + gamma_fs)
          * (ov + k2 * bx + gamma_fs);
        let perm_l = zsv
          * (lv + beta_fs * evals[9][j] + gamma_fs)
          * (rv + beta_fs * evals[10][j] + gamma_fs)
          * (ov + beta_fs * evals[11][j] + gamma_fs);
        let perm = perm_l - perm_r;

        // L_0(x) = (zh_r / N) / (x - 1), and dividing by zh_r cancels zh_r.
        let gate_perm = (gate + alpha_fs * perm) * inv_zh_r;
        let boundary = alpha_sq * inv_n * x_minus_1[j] * (zv - C::FR_ONE);
        gate_perm + boundary
      })
      .collect();

    for (j, val) in coset_h.into_iter().enumerate() {
      h_evals_4n[4 * j + r] = val;
    }
    s_r *= w4;
  }

  accel.coset_ifft_in_place(&mut h_evals_4n, k1);

  let shard_len = n + 2;
  let h_expected_len = 3 * shard_len;
  if h_evals_4n[h_expected_len..].iter().any(|c| !c.is_zero()) {
    return Err(
      "internal error: quotient polynomial degree exceeds 3(N+2) - 1".into(),
    );
  }

  // Statistical ZK randomization of quotient shards (cancels identically at X = ζ).
  let r_h0 = rng.next_fr::<C>();
  let r_h1 = rng.next_fr::<C>();
  let mut h0 = Vec::with_capacity(shard_len + 1);
  h0.extend_from_slice(&h_evals_4n[0..shard_len]);
  h0.push(r_h0);

  let mut h1 = Vec::with_capacity(shard_len + 1);
  h1.extend_from_slice(&h_evals_4n[shard_len..2 * shard_len]);
  h1[0] -= r_h0;
  h1.push(r_h1);

  let mut h2 = Vec::with_capacity(shard_len);
  h2.extend_from_slice(&h_evals_4n[2 * shard_len..3 * shard_len]);
  h2[0] -= r_h1;

  let h_proj = accel.msm_batch(
    &pk.srs_g1[..n + 3],
    &[h0.as_slice(), h1.as_slice(), h2.as_slice()],
  );
  let h_coms =
    [h_proj[0].into_affine(), h_proj[1].into_affine(), h_proj[2].into_affine()];
  timings.quotient_ms = t0.elapsed().as_secs_f64() * 1e3;

  // 7. Fiat-Shamir zeta, openings, linearized polynomial, and KZG witnesses.
  let t0 = Instant::now();
  let (_, zeta) = derive_zeta::<C>(&alpha_raw, &h_coms);
  let zeta_omega = zeta * omega;

  let z_shifted_eval = eval_poly::<C>(&z_blind, zeta_omega);
  let q_z = synthetic_divide::<C>(&z_blind, z_shifted_eval, zeta_omega)?;
  let w_zeta_omega = accel.msm(&pk.srs_g1[..q_z.len()], &q_z).into_affine();

  let l_z = eval_poly::<C>(&l_blind, zeta);
  let r_z = eval_poly::<C>(&r_blind, zeta);
  let o_z = eval_poly::<C>(&o_blind, zeta);
  let s1_z = eval_poly::<C>(&pk.s1_coeffs, zeta);
  let s2_z = eval_poly::<C>(&pk.s2_coeffs, zeta);
  let qcp_z = eval_poly::<C>(&pk.qcp_coeffs[0], zeta);

  let zh_zeta = zeta.pow([n_u64]) - C::FR_ONE;
  let inv_zeta_m1 =
    (zeta - C::FR_ONE).inverse().ok_or("Fiat-Shamir challenge zeta == 1")?;
  let l0_zeta = zh_zeta * inv_n * inv_zeta_m1;
  let alpha2_l0 = alpha_sq * l0_zeta;

  let s1_coeff = alpha_fs
    * z_shifted_eval
    * (l_z + beta_fs * s1_z + gamma_fs)
    * (r_z + beta_fs * s2_z + gamma_fs)
    * beta_fs;
  let bz_term = beta_fs * zeta;
  let coeff_z = alpha2_l0
    - alpha_fs
      * (l_z + bz_term + gamma_fs)
      * (r_z + k1 * bz_term + gamma_fs)
      * (o_z + k2 * bz_term + gamma_fs);

  let rl_z = l_z * r_z;
  let zeta_n2 = zeta.pow([u64::try_from(shard_len).expect("fits u64")]);
  let zeta_2n2 = zeta_n2 * zeta_n2;

  let lin_len = n + 3;
  let lin_poly: Vec<C::Fr> = (0..lin_len)
    .into_par_iter()
    .map(|i| {
      let mut v = coeff_z * z_blind[i];
      if i < n {
        v += l_z * pk.ql_coeffs[i]
          + r_z * pk.qr_coeffs[i]
          + rl_z * pk.qm_coeffs[i]
          + o_z * pk.qo_coeffs[i]
          + pk.qk_coeffs[i]
          + qcp_z * pi_coeffs[i]
          + s1_coeff * pk.s3_coeffs[i];
      }
      let h_at = h0[i]
        + zeta_n2 * h1[i]
        + if i < h2.len() { zeta_2n2 * h2[i] } else { C::FR_ZERO };
      v - zh_zeta * h_at
    })
    .collect();
  let lin_eval = eval_poly::<C>(&lin_poly, zeta);

  // Linearized polynomial commitment matches Commit(lin_poly) by KZG
  // homomorphism using only 11 G1 scalar multiplications.
  let neg_zh = -zh_zeta;
  let lin_com: G1AffineOf<C> = (G1ProjectiveOf::<C>::from(pk.vk.ql) * l_z
    + G1ProjectiveOf::<C>::from(pk.vk.qr) * r_z
    + G1ProjectiveOf::<C>::from(pk.vk.qm) * rl_z
    + G1ProjectiveOf::<C>::from(pk.vk.qo) * o_z
    + G1ProjectiveOf::<C>::from(pk.vk.qk)
    + G1ProjectiveOf::<C>::from(c_bsb22) * qcp_z
    + G1ProjectiveOf::<C>::from(pk.vk.s[2]) * s1_coeff
    + G1ProjectiveOf::<C>::from(z_com) * coeff_z
    + G1ProjectiveOf::<C>::from(h_coms[0]) * neg_zh
    + G1ProjectiveOf::<C>::from(h_coms[1]) * (neg_zh * zeta_n2)
    + G1ProjectiveOf::<C>::from(h_coms[2]) * (neg_zh * zeta_2n2))
    .into_affine();

  let digests = [
    lin_com,
    lro_coms[0],
    lro_coms[1],
    lro_coms[2],
    pk.vk.s[0],
    pk.vk.s[1],
    pk.vk.qcp[0],
  ];
  let claimed_values = vec![lin_eval, l_z, r_z, o_z, s1_z, s2_z, qcp_z];
  let gamma_kzg =
    derive_gamma_kzg::<C>(zeta, &digests, &claimed_values, z_shifted_eval);

  let mut gamma_pows = [C::FR_ONE; 7];
  for i in 1..7 {
    gamma_pows[i] = gamma_pows[i - 1] * gamma_kzg;
  }

  let open_polys: [&[C::Fr]; 7] = [
    &lin_poly,
    &l_blind,
    &r_blind,
    &o_blind,
    &pk.s1_coeffs,
    &pk.s2_coeffs,
    &pk.qcp_coeffs[0],
  ];
  let folded_poly: Vec<C::Fr> = (0..lin_len)
    .into_par_iter()
    .map(|i| {
      let mut acc = C::FR_ZERO;
      for (k, poly) in open_polys.iter().enumerate() {
        if i < poly.len() {
          acc += gamma_pows[k] * poly[i];
        }
      }
      acc
    })
    .collect();
  let mut folded_val = C::FR_ZERO;
  for k in 0..7 {
    folded_val += gamma_pows[k] * claimed_values[k];
  }
  let q_batch = synthetic_divide::<C>(&folded_poly, folded_val, zeta)?;
  let w_zeta = accel.msm(&pk.srs_g1[..q_batch.len()], &q_batch).into_affine();
  timings.opening_ms = t0.elapsed().as_secs_f64() * 1e3;
  timings.total_ms = t_total.elapsed().as_secs_f64() * 1e3;

  Ok((
    NativeProof {
      lro: lro_coms,
      z: z_com,
      h: h_coms,
      bsb22_commitments: vec![c_bsb22],
      claimed_values,
      w_zeta,
      z_shifted_eval,
      w_zeta_omega,
    },
    timings,
  ))
}
