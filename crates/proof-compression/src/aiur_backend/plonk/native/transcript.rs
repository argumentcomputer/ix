//! Gnark-Solidity-compatible SHA-256 Fiat-Shamir transcript, RFC 9380
//! `hash_to_field` (`BSB22-Plonk`), and canonical raw G1/Fr codecs for both
//! BN254 and BLS12-381.
//!
//! Every byte layout matches `contracts/plonk/src/PlonkVerifier.sol` (BN254)
//! and `contracts/plonk/testdata/bls12-381/Bls12381PlonkVerifier.sol`
//! (BLS12-381).

use crate::kzg::curve::{Curve, G1AffineOf, KzgCurve};
use ark_ec::AffineRepr;
use ark_ff::{BigInt, BigInteger, PrimeField};
use sha2::{Digest, Sha256};

/// Domain separation tag for BSB22 PLONK commitment hashing (`RFC 9380` XMD).
pub const BSB22_DST: &[u8] = b"BSB22-Plonk";

/// Length of one uncompressed raw G1 encoding (`64` for BN254, `96` for BLS12-381).
#[inline]
pub const fn g1_raw_len<C: KzgCurve>() -> usize {
  C::G1_UNCOMPRESSED_BYTES
}

/// Encode a scalar field element as 32 canonical big-endian bytes.
#[inline]
pub fn fr_be_bytes<C: KzgCurve>(value: C::Fr) -> [u8; 32] {
  let bytes = value.into_bigint().to_bytes_be();
  bytes.try_into().expect("Fr is 32 bytes")
}

/// Decode a 32-byte big-endian scalar strictly below the scalar modulus `r`.
pub fn decode_fr_be_canonical<C: KzgCurve>(
  bytes: &[u8; 32],
) -> Result<C::Fr, String> {
  let mut limbs = [0u64; 4];
  for (i, limb) in limbs.iter_mut().enumerate() {
    let off = 24 - 8 * i;
    *limb =
      u64::from_be_bytes(bytes[off..off + 8].try_into().expect("8-byte limb"));
  }
  C::Fr::from_bigint(BigInt(limbs))
    .ok_or_else(|| "scalar value is >= Fr modulus".to_owned())
}

/// Encode a G1 affine point in gnark's `RawBytes()` / `Marshal()` format:
/// - BN254 (64 bytes): `x_be_32 || y_be_32`, with infinity as 64 zero bytes.
/// - BLS12-381 (96 bytes): `x_be_48 || y_be_48`, with infinity as `[0x40, 0, ...]`.
pub fn g1_raw_bytes<C: KzgCurve>(point: G1AffineOf<C>) -> Vec<u8> {
  let width = C::FQ_BYTES;
  let mut out = vec![0u8; 2 * width];
  if point.is_zero() {
    if C::CURVE == Curve::Bls12381 {
      out[0] = 0x40;
    }
    return out;
  }
  let x_bytes = point.x.into_bigint().to_bytes_be();
  let y_bytes = point.y.into_bigint().to_bytes_be();
  debug_assert_eq!(x_bytes.len(), width);
  debug_assert_eq!(y_bytes.len(), width);
  out[..width].copy_from_slice(&x_bytes);
  out[width..].copy_from_slice(&y_bytes);
  out
}

/// Decode a G1 affine point from gnark's `RawBytes()` format with strict
/// canonical coordinate checks, curve equation check, and prime-order subgroup
/// membership check.
pub fn decode_g1_raw<C: KzgCurve>(
  bytes: &[u8],
) -> Result<G1AffineOf<C>, String> {
  let width = C::FQ_BYTES;
  if bytes.len() != 2 * width {
    return Err(format!(
      "invalid raw G1 length: expected {}, got {}",
      2 * width,
      bytes.len()
    ));
  }
  match C::CURVE {
    Curve::Bn254 => {
      if bytes.iter().all(|&b| b == 0) {
        return Ok(G1AffineOf::<C>::identity());
      }
    },
    Curve::Bls12381 => {
      let flags = bytes[0] & 0xe0;
      if flags == 0x40 {
        if bytes[1..].iter().all(|&b| b == 0) {
          return Ok(G1AffineOf::<C>::identity());
        }
        return Err("non-canonical BLS12-381 infinity encoding".into());
      }
      if flags != 0 {
        return Err(format!(
          "invalid BLS12-381 uncompressed G1 flags: 0x{flags:02x}"
        ));
      }
    },
  }
  let x = decode_fq_be_canonical::<C>(&bytes[..width])?;
  let y = decode_fq_be_canonical::<C>(&bytes[width..])?;
  let point = G1AffineOf::<C>::new_unchecked(x, y);
  if !point.is_on_curve() {
    return Err("G1 point is not on curve".into());
  }
  if !point.is_in_correct_subgroup_assuming_on_curve() {
    return Err("G1 point is not in the prime-order subgroup".into());
  }
  Ok(point)
}

fn decode_fq_be_canonical<C: KzgCurve>(bytes: &[u8]) -> Result<C::Fq, String> {
  // Parse big-endian bytes into little-endian bytes for `CanonicalDeserialize`
  // or `BigInteger::from_bits_be` via `Fq::from_bigint`.
  let mut le = bytes.to_vec();
  le.reverse();
  let mut bigint = C::FqBigInt::default();
  for (limb_idx, limb) in bigint.as_mut().iter_mut().enumerate() {
    let off = 8 * limb_idx;
    if off + 8 <= le.len() {
      *limb = u64::from_le_bytes(
        le[off..off + 8].try_into().expect("8-byte Fq limb"),
      );
    }
  }
  C::Fq::from_bigint(bigint)
    .ok_or_else(|| "base-field coordinate is >= Fq modulus".to_owned())
}

/// RFC 9380 `expand_message_xmd` (SHA-256, `DST = "BSB22-Plonk"`, `len = 48`)
/// reduced modulo `r`, matching `hash_fr` in `PlonkVerifier.sol` and
/// `Bls12381PlonkVerifier.sol` byte-for-byte.
pub fn hash_fr_bsb22<C: KzgCurve>(commitment: G1AffineOf<C>) -> C::Fr {
  let msg = g1_raw_bytes::<C>(commitment);
  hash_fr_xmd_sha256::<C>(&msg, BSB22_DST)
}

/// Generic RFC 9380 `expand_message_xmd` with SHA-256 producing one `C::Fr`
/// element from `48` expanded uniform bytes (`L = 16 + 32 = 48`).
pub fn hash_fr_xmd_sha256<C: KzgCurve>(msg: &[u8], dst: &[u8]) -> C::Fr {
  assert!(dst.len() <= 255, "DST length must fit u8");
  let dst_len = u8::try_from(dst.len()).expect("dst fits u8");
  const LEN_IN_BYTES: u8 = 48;

  // b0 = SHA256(Z_pad(64) || msg || I2OSP(48, 2) || I2OSP(0, 1) || dst || I2OSP(|dst|, 1))
  let mut h0 = Sha256::new();
  h0.update([0u8; 64]);
  h0.update(msg);
  h0.update([0u8, LEN_IN_BYTES, 0u8]);
  h0.update(dst);
  h0.update([dst_len]);
  let b0: [u8; 32] = h0.finalize().into();

  // b1 = SHA256(b0 || 1 || dst || |dst|)
  let mut h1 = Sha256::new();
  h1.update(b0);
  h1.update([1u8]);
  h1.update(dst);
  h1.update([dst_len]);
  let b1: [u8; 32] = h1.finalize().into();

  // b2 = SHA256((b0 ^ b1) || 2 || dst || |dst|)
  let mut xored = [0u8; 32];
  for i in 0..32 {
    xored[i] = b0[i] ^ b1[i];
  }
  let mut h2 = Sha256::new();
  h2.update(xored);
  h2.update([2u8]);
  h2.update(dst);
  h2.update([dst_len]);
  let b2: [u8; 32] = h2.finalize().into();

  let mut uniform = [0u8; 48];
  uniform[..32].copy_from_slice(&b1);
  uniform[32..48].copy_from_slice(&b2[..16]);
  C::Fr::from_be_bytes_mod_order(&uniform)
}

/// Derive Fiat-Shamir `gamma`:
/// `SHA256("gamma" || S1 || S2 || S3 || Ql || Qr || Qm || Qo || Qk || Qcp... || PI... || L || R || O)`.
/// Returns `(unreduced_32_bytes, reduced_fr)`.
pub fn derive_gamma<C: KzgCurve>(
  s: &[G1AffineOf<C>; 3],
  selectors: &[G1AffineOf<C>; 5],
  qcp: &[G1AffineOf<C>],
  public_inputs: &[C::Fr],
  lro: &[G1AffineOf<C>; 3],
) -> ([u8; 32], C::Fr) {
  let mut h = Sha256::new();
  h.update(b"gamma");
  for &p in s {
    h.update(g1_raw_bytes::<C>(p));
  }
  for &p in selectors {
    h.update(g1_raw_bytes::<C>(p));
  }
  for &p in qcp {
    h.update(g1_raw_bytes::<C>(p));
  }
  for &pi in public_inputs {
    h.update(fr_be_bytes::<C>(pi));
  }
  for &p in lro {
    h.update(g1_raw_bytes::<C>(p));
  }
  let raw: [u8; 32] = h.finalize().into();
  (raw, C::Fr::from_be_bytes_mod_order(&raw))
}

/// Derive Fiat-Shamir `beta`: `SHA256("beta" || gamma_raw)`.
pub fn derive_beta<C: KzgCurve>(gamma_raw: &[u8; 32]) -> ([u8; 32], C::Fr) {
  let mut h = Sha256::new();
  h.update(b"beta");
  h.update(gamma_raw);
  let raw: [u8; 32] = h.finalize().into();
  (raw, C::Fr::from_be_bytes_mod_order(&raw))
}

/// Derive Fiat-Shamir `alpha`: `SHA256("alpha" || beta_raw || bsb22... || Z)`.
pub fn derive_alpha<C: KzgCurve>(
  beta_raw: &[u8; 32],
  bsb22_commitments: &[G1AffineOf<C>],
  z_com: G1AffineOf<C>,
) -> ([u8; 32], C::Fr) {
  let mut h = Sha256::new();
  h.update(b"alpha");
  h.update(beta_raw);
  for &p in bsb22_commitments {
    h.update(g1_raw_bytes::<C>(p));
  }
  h.update(g1_raw_bytes::<C>(z_com));
  let raw: [u8; 32] = h.finalize().into();
  (raw, C::Fr::from_be_bytes_mod_order(&raw))
}

/// Derive Fiat-Shamir `zeta`: `SHA256("zeta" || alpha_raw || H0 || H1 || H2)`.
pub fn derive_zeta<C: KzgCurve>(
  alpha_raw: &[u8; 32],
  h_coms: &[G1AffineOf<C>; 3],
) -> ([u8; 32], C::Fr) {
  let mut h = Sha256::new();
  h.update(b"zeta");
  h.update(alpha_raw);
  for &p in h_coms {
    h.update(g1_raw_bytes::<C>(p));
  }
  let raw: [u8; 32] = h.finalize().into();
  (raw, C::Fr::from_be_bytes_mod_order(&raw))
}

/// Derive KZG batch-opening challenge `gamma_kzg`:
/// `SHA256("gamma" || zeta || digests... || claimed_values... || z_shifted_eval)`.
pub fn derive_gamma_kzg<C: KzgCurve>(
  zeta: C::Fr,
  digests: &[G1AffineOf<C>],
  claimed_values: &[C::Fr],
  z_shifted_eval: C::Fr,
) -> C::Fr {
  let mut h = Sha256::new();
  h.update(b"gamma");
  h.update(fr_be_bytes::<C>(zeta));
  for &d in digests {
    h.update(g1_raw_bytes::<C>(d));
  }
  for &v in claimed_values {
    h.update(fr_be_bytes::<C>(v));
  }
  h.update(fr_be_bytes::<C>(z_shifted_eval));
  let raw: [u8; 32] = h.finalize().into();
  C::Fr::from_be_bytes_mod_order(&raw)
}

/// Derive verifier-local random challenge for batching the two KZG pairing
/// checks (deterministic SHA-256 matching Solidity `batch_verify_multi_points`).
pub fn derive_batch_verify_random<C: KzgCurve>(
  folded_digest: G1AffineOf<C>,
  w_zeta: G1AffineOf<C>,
  z_com: G1AffineOf<C>,
  w_zeta_omega: G1AffineOf<C>,
  zeta: C::Fr,
  gamma_kzg: C::Fr,
) -> C::Fr {
  let mut h = Sha256::new();
  h.update(g1_raw_bytes::<C>(folded_digest));
  h.update(g1_raw_bytes::<C>(w_zeta));
  h.update(g1_raw_bytes::<C>(z_com));
  h.update(g1_raw_bytes::<C>(w_zeta_omega));
  h.update(fr_be_bytes::<C>(zeta));
  h.update(fr_be_bytes::<C>(gamma_kzg));
  let raw: [u8; 32] = h.finalize().into();
  C::Fr::from_be_bytes_mod_order(&raw)
}
