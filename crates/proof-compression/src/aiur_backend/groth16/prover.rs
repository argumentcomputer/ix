//! Pure-Rust (+ optional Ix-CUDA `sppark`) BN254 Groth16 zero-knowledge prover.
//!
//! Implements Jens Groth's 2016 protocol with:
//! - Coset-domain QAP quotient `h(X) = (a(X)·b(X) - c(X)) / Z_H(X)` over
//!   `ark_poly::Radix2EvaluationDomain`,
//! - Zero-knowledge blinding `(r, s)` sampled from `/dev/urandom` mixed with
//!   BLAKE3 XOF (plus deterministic `prove_with_blinding` for tests),
//! - GLV 2D parallel CPU G1 MSM (`crate::kzg::curve::Bn254::cpu_msm`) or
//!   `#[cfg(feature = "cuda")]` `libix_bn254_cuda.so` (`sppark`) G1 MSM,
//! - Parallel `ark_ec::VariableBaseMSM` for G2 MSM,
//! - Exact **256-byte uncompressed EVM proof** (`A || B || C`, EIP-196/197)
//!   and **128-byte compressed proof** encodings.

use super::setup::ProvingKey;
use super::verifier::{decode_g1_evm, decode_g2_evm};
use crate::kzg::curve::{Bn254, KzgCurve};
use ark_bn254::{Fq, Fr, G1Affine, G1Projective, G2Affine, G2Projective};
use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ff::{AdditiveGroup, BigInteger, FftField, Field, PrimeField, Zero};
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use p3_maybe_rayon::prelude::*;
use std::fs::File;
use std::io::Read;

const ZK_BLINDING_DOMAIN: &[u8] = b"ix/groth16/bn254/zk-blinding/v1";

#[cfg(feature = "cuda")]
const CUDA_MSM_THRESHOLD: usize = 4096;

/// BN254 Groth16 proof `(A ∈ G1, B ∈ G2, C ∈ G1)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Proof {
  pub a: G1Affine,
  pub b: G2Affine,
  pub c: G1Affine,
}

impl Proof {
  /// Exact EIP-196/197 uncompressed EVM proof size in bytes (`64 + 128 + 64`).
  pub const EVM_BYTES: usize = 256;
  /// Exact compressed BN254 proof size in bytes (`32 + 64 + 32`).
  pub const COMPRESSED_BYTES: usize = 128;

  /// Encode `(A, B, C)` into the exact 256-byte uncompressed EVM format:
  /// `A.x || A.y || B.x.c1 || B.x.c0 || B.y.c1 || B.y.c0 || C.x || C.y`
  /// (each coordinate 32-byte big-endian unsigned integer `< p`, with
  /// point-at-infinity encoded as all zeros).
  pub fn to_evm_bytes(&self) -> [u8; Self::EVM_BYTES] {
    let mut out = [0u8; Self::EVM_BYTES];
    write_g1_evm(&self.a, &mut out[0..64]);
    write_g2_evm(&self.b, &mut out[64..192]);
    write_g1_evm(&self.c, &mut out[192..256]);
    out
  }

  /// Strictly decode a 256-byte uncompressed EVM proof, verifying canonical
  /// `Fq` coordinates (`< p`), curve membership, and prime-order subgroup
  /// membership for `A`, `B`, and `C`.
  pub fn from_evm_bytes(bytes: &[u8]) -> Result<Self, String> {
    if bytes.len() != Self::EVM_BYTES {
      return Err(format!(
        "invalid Groth16 EVM proof length: got {} bytes, expected {}",
        bytes.len(),
        Self::EVM_BYTES
      ));
    }
    let a = decode_g1_evm(&bytes[0..64])
      .map_err(|e| format!("proof.A invalid: {e}"))?;
    let b = decode_g2_evm(&bytes[64..192])
      .map_err(|e| format!("proof.B invalid: {e}"))?;
    let c = decode_g1_evm(&bytes[192..256])
      .map_err(|e| format!("proof.C invalid: {e}"))?;
    Ok(Self { a, b, c })
  }

  /// Encode `(A, B, C)` into 128-byte canonical compressed form
  /// (`A (32 B) || B (64 B) || C (32 B)`).
  pub fn to_compressed_bytes(&self) -> [u8; Self::COMPRESSED_BYTES] {
    let mut out = [0u8; Self::COMPRESSED_BYTES];
    self
      .a
      .serialize_compressed(&mut out[0..32])
      .expect("G1 compressed encoding is 32 bytes");
    self
      .b
      .serialize_compressed(&mut out[32..96])
      .expect("G2 compressed encoding is 64 bytes");
    self
      .c
      .serialize_compressed(&mut out[96..128])
      .expect("G1 compressed encoding is 32 bytes");
    out
  }

  /// Strictly decode a 128-byte canonical compressed proof with full curve and
  /// prime-order subgroup validation.
  pub fn from_compressed_bytes(bytes: &[u8]) -> Result<Self, String> {
    if bytes.len() != Self::COMPRESSED_BYTES {
      return Err(format!(
        "invalid Groth16 compressed proof length: got {} bytes, expected {}",
        bytes.len(),
        Self::COMPRESSED_BYTES
      ));
    }
    let a = G1Affine::deserialize_compressed(&bytes[0..32])
      .map_err(|e| format!("compressed proof.A invalid: {e}"))?;
    let b = G2Affine::deserialize_compressed(&bytes[32..96])
      .map_err(|e| format!("compressed proof.B invalid: {e}"))?;
    let c = G1Affine::deserialize_compressed(&bytes[96..128])
      .map_err(|e| format!("compressed proof.C invalid: {e}"))?;
    Ok(Self { a, b, c })
  }
}

/// Execution backend selector for Groth16 G1 MSMs.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Groth16Accelerator {
  use_cuda: bool,
}

impl Groth16Accelerator {
  /// Parallel CPU execution using Ix's GLV 2D Pippenger G1 MSM.
  pub const fn cpu() -> Self {
    Self { use_cuda: false }
  }

  /// Enable Ix-CUDA (`libix_bn254_cuda.so` / `sppark`) G1 MSM acceleration when
  /// compiled with `--features cuda`.
  pub fn cuda() -> Result<Self, String> {
    #[cfg(feature = "cuda")]
    {
      cuda_impl::ensure_device()?;
      Ok(Self { use_cuda: true })
    }
    #[cfg(not(feature = "cuda"))]
    {
      Err(
        "Groth16 CUDA acceleration requires compiling with --features cuda"
          .into(),
      )
    }
  }

  /// Whether CUDA dispatch is enabled.
  pub const fn is_cuda(self) -> bool {
    self.use_cuda
  }

  /// Compute a BN254 G1 MSM `Σ bases[i] · scalars[i]`.
  pub fn msm_g1(self, bases: &[G1Affine], scalars: &[Fr]) -> G1Projective {
    assert_eq!(bases.len(), scalars.len(), "G1 MSM length mismatch");
    if bases.is_empty() {
      return G1Projective::zero();
    }
    #[cfg(feature = "cuda")]
    if self.use_cuda && bases.len() >= CUDA_MSM_THRESHOLD {
      return cuda_impl::msm_g1(bases, scalars);
    }
    Bn254::cpu_msm(bases, scalars)
  }
}

fn write_fq_be(val: Fq, dst: &mut [u8]) {
  let bytes = val.into_bigint().to_bytes_be();
  dst.fill(0);
  let start = 32 - bytes.len();
  dst[start..32].copy_from_slice(&bytes);
}

fn write_g1_evm(pt: &G1Affine, dst: &mut [u8]) {
  if pt.is_zero() {
    dst.fill(0);
  } else {
    write_fq_be(pt.x, &mut dst[0..32]);
    write_fq_be(pt.y, &mut dst[32..64]);
  }
}

fn write_g2_evm(pt: &G2Affine, dst: &mut [u8]) {
  if pt.is_zero() {
    dst.fill(0);
  } else {
    // EIP-197 Fp2 order: (imaginary c1, real c0).
    write_fq_be(pt.x.c1, &mut dst[0..32]);
    write_fq_be(pt.x.c0, &mut dst[32..64]);
    write_fq_be(pt.y.c1, &mut dst[64..96]);
    write_fq_be(pt.y.c0, &mut dst[96..128]);
  }
}

fn sample_zk_blinding() -> Result<(Fr, Fr), String> {
  let mut entropy = [0u8; 64];
  let mut urandom = File::open("/dev/urandom")
    .map_err(|e| format!("failed to open /dev/urandom for ZK blinding: {e}"))?;
  urandom
    .read_exact(&mut entropy)
    .map_err(|e| format!("failed to read /dev/urandom for ZK blinding: {e}"))?;

  let mut hasher = blake3::Hasher::new();
  hasher.update(ZK_BLINDING_DOMAIN);
  hasher.update(&entropy);
  let mut xof = hasher.finalize_xof();

  let mut r_bytes = [0u8; 64];
  let mut s_bytes = [0u8; 64];
  xof.fill(&mut r_bytes);
  xof.fill(&mut s_bytes);
  Ok((
    Fr::from_le_bytes_mod_order(&r_bytes),
    Fr::from_le_bytes_mod_order(&s_bytes),
  ))
}

/// Generate a zero-knowledge BN254 Groth16 proof on CPU using fresh random
/// blinding `(r, s)` drawn from `/dev/urandom` + BLAKE3 XOF.
pub fn prove(pk: &ProvingKey, assignment: &[Fr]) -> Result<Proof, String> {
  prove_with_accel(pk, assignment, Groth16Accelerator::cpu())
}

/// Generate a zero-knowledge BN254 Groth16 proof with the chosen accelerator.
pub fn prove_with_accel(
  pk: &ProvingKey,
  assignment: &[Fr],
  accel: Groth16Accelerator,
) -> Result<Proof, String> {
  let (r, s) = sample_zk_blinding()?;
  prove_with_blinding_accel(pk, assignment, r, s, accel)
}

/// Generate a deterministic BN254 Groth16 proof using explicit blinding scalars
/// `(r, s)` (for reproducible tests and golden vectors).
pub fn prove_with_blinding(
  pk: &ProvingKey,
  assignment: &[Fr],
  r: Fr,
  s: Fr,
) -> Result<Proof, String> {
  prove_with_blinding_accel(pk, assignment, r, s, Groth16Accelerator::cpu())
}

/// Generate a BN254 Groth16 proof with explicit blinding `(r, s)` and
/// accelerator backend.
pub fn prove_with_blinding_accel(
  pk: &ProvingKey,
  assignment: &[Fr],
  r: Fr,
  s: Fr,
  accel: Groth16Accelerator,
) -> Result<Proof, String> {
  pk.r1cs.is_satisfied(assignment)?;
  let n = pk.domain_size;
  if pk.a_query.len() != pk.r1cs.num_wires
    || pk.b_g1_query.len() != pk.r1cs.num_wires
    || pk.b_g2_query.len() != pk.r1cs.num_wires
    || pk.l_query.len() != pk.r1cs.num_private()
    || pk.h_query.len() != n - 1
  {
    return Err(
      "proving key table lengths do not match R1CS dimensions".into(),
    );
  }

  let domain = Radix2EvaluationDomain::<Fr>::new(n)
    .ok_or_else(|| format!("invalid QAP domain size {n}"))?;
  let coset_shift = Fr::GENERATOR;
  let coset_domain =
    domain.get_coset(coset_shift).ok_or("failed to build coset domain")?;

  // 1. Evaluate a(X), b(X), c(X) on domain H.
  let mut a_poly = vec![Fr::ZERO; n];
  let mut b_poly = vec![Fr::ZERO; n];
  let mut c_poly = vec![Fr::ZERO; n];

  for (k, con) in pk.r1cs.constraints.iter().enumerate() {
    a_poly[k] = con.a.evaluate(assignment);
    b_poly[k] = con.b.evaluate(assignment);
    c_poly[k] = con.c.evaluate(assignment);
  }
  let num_instance = pk.r1cs.num_instance_wires();
  let anchor_base = pk.r1cs.constraints.len();
  a_poly[anchor_base..(anchor_base + num_instance)]
    .copy_from_slice(&assignment[..num_instance]);

  // 2. Interpolate to monomial basis, then evaluate on coset g·H.
  domain.ifft_in_place(&mut a_poly);
  domain.ifft_in_place(&mut b_poly);
  domain.ifft_in_place(&mut c_poly);

  coset_domain.fft_in_place(&mut a_poly);
  coset_domain.fft_in_place(&mut b_poly);
  coset_domain.fft_in_place(&mut c_poly);

  // 3. Compute quotient h(X) = (a(X)·b(X) - c(X)) / (X^N - 1) on coset g·H.
  let z_h_coset =
    coset_shift.pow([u64::try_from(n).expect("n fits u64")]) - Fr::ONE;
  let z_h_inv =
    z_h_coset.inverse().ok_or("vanishing polynomial vanishes on coset")?;

  let mut h_coeffs: Vec<Fr> = (0..n)
    .into_par_iter()
    .map(|i| (a_poly[i] * b_poly[i] - c_poly[i]) * z_h_inv)
    .collect();
  coset_domain.ifft_in_place(&mut h_coeffs);

  if !h_coeffs[n - 1].is_zero() {
    return Err(
      "QAP divisibility check failed: quotient degree exceeded N - 2".into(),
    );
  }

  // 4. Compute proof elements A ∈ G1, B ∈ G2, C ∈ G1.
  let delta_g1 = G1Projective::from(pk.delta_g1);
  let a_proj = G1Projective::from(pk.vk.alpha_g1)
    + accel.msm_g1(&pk.a_query, assignment)
    + delta_g1 * r;

  let b_g1_proj = G1Projective::from(pk.beta_g1)
    + accel.msm_g1(&pk.b_g1_query, assignment)
    + delta_g1 * s;

  let b_g2_msm = G2Projective::msm(&pk.b_g2_query, assignment)
    .map_err(|idx| format!("G2 MSM length mismatch at {idx}"))?;
  let b_g2_proj = G2Projective::from(pk.vk.beta_g2)
    + b_g2_msm
    + G2Projective::from(pk.vk.delta_g2) * s;

  let private_scalars = &assignment[num_instance..];
  let l_acc = accel.msm_g1(&pk.l_query, private_scalars);
  let h_acc = accel.msm_g1(&pk.h_query, &h_coeffs[..n - 1]);

  let c_proj = l_acc + h_acc + a_proj * s + b_g1_proj * r - delta_g1 * (r * s);

  let normalized = G1Projective::normalize_batch(&[a_proj, c_proj]);
  Ok(Proof { a: normalized[0], b: b_g2_proj.into_affine(), c: normalized[1] })
}

#[cfg(feature = "cuda")]
mod cuda_impl {
  use crate::kzg::cuda::CudaCurve;
  use crate::kzg::curve::{Bn254, KzgCurve};
  use ark_bn254::{Fr, G1Affine, G1Projective};
  use ark_ff::PrimeField;
  use std::ffi::c_void;

  pub(super) fn ensure_device() -> Result<i32, String> {
    let fq = Bn254::fq_abi_triple();
    let fr = [Fr::MODULUS.0, Bn254::FR_MONT_ONE, Bn254::FR_MONT_R2];
    let abi_code = unsafe {
      Bn254::ffi_check_field_abi(&fq, size_of_val(&fq), &fr, size_of_val(&fr))
    };
    if abi_code != 0 {
      return Err(format!("CUDA BN254 field ABI check failed ({abi_code})"));
    }
    let mut count = 0i32;
    let code = unsafe { Bn254::ffi_devices(&mut count) };
    if code != 0 || count <= 0 {
      return Err(format!("no visible BN254 CUDA device (status {code})"));
    }
    let mut ordinal = -1i32;
    let code = unsafe { Bn254::ffi_device_ordinal(0, &mut ordinal) };
    if code != 0 {
      return Err(format!("CUDA device ordinal lookup failed ({code})"));
    }
    Ok(ordinal)
  }

  pub(super) fn msm_g1(bases: &[G1Affine], scalars: &[Fr]) -> G1Projective {
    let device = ensure_device().expect("BN254 CUDA device validated");
    let mut context: *mut c_void = std::ptr::null_mut();
    let code = unsafe {
      Bn254::ffi_msm_create(
        device,
        &mut context,
        bases.as_ptr().cast(),
        bases.len(),
      )
    };
    assert_eq!(code, 0, "Groth16 CUDA G1 MSM upload failed ({code})");
    assert!(!context.is_null());

    let mut out = [<Bn254 as CudaCurve>::FqLimbs::default(); 3];
    let invoke_code = unsafe {
      Bn254::ffi_msm_invoke(
        device,
        context,
        &mut out,
        scalars.as_ptr().cast(),
        scalars.len(),
        std::ptr::null(),
      )
    };
    let destroy_code = unsafe { Bn254::ffi_msm_destroy(device, context) };
    assert_eq!(
      invoke_code, 0,
      "Groth16 CUDA G1 MSM invoke failed ({invoke_code})"
    );
    assert_eq!(
      destroy_code, 0,
      "Groth16 CUDA G1 MSM destroy failed ({destroy_code})"
    );

    G1Projective::new_unchecked(
      Bn254::fq_from_mont_limbs_unchecked(out[0]),
      Bn254::fq_from_mont_limbs_unchecked(out[1]),
      Bn254::fq_from_mont_limbs_unchecked(out[2]),
    )
  }
}
