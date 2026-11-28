//! Curve-generic PLONK + BSB22 preprocessing (`Bn254` & `Bls12381`).
//!
//! Computes the radix-2 evaluation domain, selector polynomials
//! `(qL, qR, qM, qO, qK, qCp)`, gnark-compatible copy-constraint permutation
//! `(S1, S2, S3)` with coset shifts `k1 = 5` (BN254) / `k1 = 7` (BLS12-381),
//! and their monomial-basis KZG commitments.

use super::cuda_accel::PlonkAccelerator;
use super::scs_file::{ScsFile, hex_digest};
use crate::kzg::{
  Srs, VerifierParams,
  curve::{Curve, G1AffineOf, G2AffineOf, KzgCurve, read_g1_compressed_for},
};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::Field;
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use p3_maybe_rayon::prelude::*;
use sha2::{Digest, Sha256};

const VK_MAGIC: &[u8; 8] = b"IXNPVK01";
const PK_MAGIC: &[u8; 8] = b"IXNPPK01";

/// Gnark-compatible PLONK coset shift `k1` (`5` on BN254, `7` on BLS12-381).
#[inline]
pub fn coset_shift<C: KzgCurve>() -> C::Fr {
  match C::CURVE {
    Curve::Bn254 => C::Fr::from(5u64),
    Curve::Bls12381 => C::Fr::from(7u64),
  }
}

/// Power-of-two PLONK domain size for `scs`:
/// `next_power_of_two(max(publics + gates + commits.len() + 2, 8))`.
///
/// The `+ 2` guarantees:
/// 1. Room for the BSB22 commitment-injection row (`commitment_index = pre + commits.len()`), and
/// 2. At least one padding row (`N - 1`) with `qCp[N - 1] == 0` distinct from
///    the commitment-injection row for zero-knowledge blinding of `Pi(X)`.
pub fn domain_size_for_scs<C: KzgCurve>(
  scs: &ScsFile<C>,
) -> Result<usize, String> {
  let min_rows = scs
    .publics
    .checked_add(scs.gates_count)
    .and_then(|v| v.checked_add(scs.commits.len()))
    .and_then(|v| v.checked_add(2))
    .ok_or("PLONK domain row count overflow")?;
  let n = min_rows
    .max(8)
    .checked_next_power_of_two()
    .ok_or("PLONK domain size overflow")?;
  if (n.ilog2() as usize) > C::FR_TWO_ADICITY {
    return Err(format!("PLONK domain {n} exceeds {} two-adicity", C::NAME));
  }
  Ok(n)
}

/// Native PLONK + BSB22 verifying key for curve `C`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifyingKey<C: KzgCurve> {
  pub domain_size: usize,
  pub domain_size_inv: C::Fr,
  pub omega: C::Fr,
  pub coset_shift: C::Fr,
  pub num_public_inputs: usize,
  /// Constraint-space index of each BSB22 commitment-injection row
  /// (`VK_INDEX_COMMIT_API_0 = scs.pre + scs.commits.len()`).
  pub commitment_constraint_indexes: Vec<u64>,
  pub ql: G1AffineOf<C>,
  pub qr: G1AffineOf<C>,
  pub qm: G1AffineOf<C>,
  pub qo: G1AffineOf<C>,
  pub qk: G1AffineOf<C>,
  pub s: [G1AffineOf<C>; 3],
  pub qcp: Vec<G1AffineOf<C>>,
  pub g1: G1AffineOf<C>,
  pub g2: G2AffineOf<C>,
  pub tau_g2: G2AffineOf<C>,
}

/// Native PLONK + BSB22 proving key for curve `C`.
#[derive(Clone, Debug)]
pub struct ProvingKey<C: KzgCurve> {
  pub vk: VerifyingKey<C>,
  /// Monomial SRS prefix `[G, τG, ..., τ^{N+2}G]` (exact length `N + 3`).
  pub srs_g1: Vec<G1AffineOf<C>>,
  /// Selector polynomials in monomial (canonical) basis, each length `N`.
  pub ql_coeffs: Vec<C::Fr>,
  pub qr_coeffs: Vec<C::Fr>,
  pub qm_coeffs: Vec<C::Fr>,
  pub qo_coeffs: Vec<C::Fr>,
  /// Incomplete `qK` (zero at `0..publics` and at `publics + commitment_index`).
  pub qk_coeffs: Vec<C::Fr>,
  pub qcp_coeffs: Vec<Vec<C::Fr>>,
  /// Copy-constraint permutation polynomials in monomial basis, each length `N`.
  pub s1_coeffs: Vec<C::Fr>,
  pub s2_coeffs: Vec<C::Fr>,
  pub s3_coeffs: Vec<C::Fr>,
  /// Full permutation array `S` of length `3 * N`.
  pub permutation: Vec<u32>,
  pub pre_gates: usize,
  pub total_gates: usize,
  pub commits_len: usize,
}

fn curve_tag<C: KzgCurve>() -> u8 {
  match C::CURVE {
    Curve::Bn254 => 1,
    Curve::Bls12381 => 2,
  }
}

fn read_u64_le_slice(input: &mut &[u8]) -> Result<u64, String> {
  if input.len() < 8 {
    return Err("unexpected EOF reading u64".into());
  }
  let val = u64::from_le_bytes(input[..8].try_into().expect("8 bytes"));
  *input = &input[8..];
  Ok(val)
}

fn read_u32_le_slice(input: &mut &[u8]) -> Result<u32, String> {
  if input.len() < 4 {
    return Err("unexpected EOF reading u32".into());
  }
  let val = u32::from_le_bytes(input[..4].try_into().expect("4 bytes"));
  *input = &input[4..];
  Ok(val)
}

fn read_fr_compressed<C: KzgCurve>(input: &mut &[u8]) -> Result<C::Fr, String> {
  C::Fr::deserialize_compressed(input)
    .map_err(|e| format!("invalid Fr serialization: {e}"))
}

fn read_g2_compressed<C: KzgCurve>(
  input: &mut &[u8],
) -> Result<G2AffineOf<C>, String> {
  let width = C::G2_COMPRESSED_BYTES;
  if input.len() < width {
    return Err("unexpected EOF reading G2".into());
  }
  let bytes = &input[..width];
  *input = &input[width..];
  let point = G2AffineOf::<C>::deserialize_compressed(bytes)
    .map_err(|e| format!("invalid G2 point: {e}"))?;
  let mut canonical = Vec::with_capacity(width);
  point
    .serialize_compressed(&mut canonical)
    .map_err(|e| format!("G2 re-encode failed: {e}"))?;
  if canonical.as_slice() != bytes {
    return Err("non-canonical G2 encoding".into());
  }
  Ok(point)
}

impl<C: KzgCurve> VerifyingKey<C> {
  /// Serialize to canonical versioned bytes (`IXNPVK01`).
  pub fn to_bytes(&self) -> Result<Vec<u8>, String> {
    let mut out = Vec::new();
    out.extend_from_slice(VK_MAGIC);
    out.push(curve_tag::<C>());
    out.extend_from_slice(
      &u64::try_from(self.domain_size).expect("fits u64").to_le_bytes(),
    );
    self
      .domain_size_inv
      .serialize_compressed(&mut out)
      .map_err(|e| e.to_string())?;
    self.omega.serialize_compressed(&mut out).map_err(|e| e.to_string())?;
    self
      .coset_shift
      .serialize_compressed(&mut out)
      .map_err(|e| e.to_string())?;
    out.extend_from_slice(
      &u64::try_from(self.num_public_inputs).expect("fits u64").to_le_bytes(),
    );
    out.extend_from_slice(
      &u64::try_from(self.commitment_constraint_indexes.len())
        .expect("fits u64")
        .to_le_bytes(),
    );
    for &idx in &self.commitment_constraint_indexes {
      out.extend_from_slice(&idx.to_le_bytes());
    }
    for point in [
      self.ql, self.qr, self.qm, self.qo, self.qk, self.s[0], self.s[1],
      self.s[2],
    ] {
      point.serialize_compressed(&mut out).map_err(|e| e.to_string())?;
    }
    out.extend_from_slice(
      &u64::try_from(self.qcp.len()).expect("fits u64").to_le_bytes(),
    );
    for point in &self.qcp {
      point.serialize_compressed(&mut out).map_err(|e| e.to_string())?;
    }
    self.g1.serialize_compressed(&mut out).map_err(|e| e.to_string())?;
    self.g2.serialize_compressed(&mut out).map_err(|e| e.to_string())?;
    self.tau_g2.serialize_compressed(&mut out).map_err(|e| e.to_string())?;
    Ok(out)
  }

  /// Deserialize with strict curve, subgroup, canonicality, and trailing-byte
  /// validation.
  pub fn from_bytes(mut input: &[u8]) -> Result<Self, String> {
    if input.len() < 9 || &input[..8] != VK_MAGIC {
      return Err("invalid native PLONK verifying key magic".into());
    }
    if input[8] != curve_tag::<C>() {
      return Err("native PLONK verifying key curve mismatch".into());
    }
    input = &input[9..];
    let domain_size = usize::try_from(read_u64_le_slice(&mut input)?)
      .map_err(|e| e.to_string())?;
    let domain_size_inv = read_fr_compressed::<C>(&mut input)?;
    let omega = read_fr_compressed::<C>(&mut input)?;
    let coset_shift = read_fr_compressed::<C>(&mut input)?;
    let num_public_inputs = usize::try_from(read_u64_le_slice(&mut input)?)
      .map_err(|e| e.to_string())?;
    let n_cci = usize::try_from(read_u64_le_slice(&mut input)?)
      .map_err(|e| e.to_string())?;
    if n_cci > 16 {
      return Err("too many BSB22 commitments in verifying key".into());
    }
    let mut commitment_constraint_indexes = Vec::with_capacity(n_cci);
    for _ in 0..n_cci {
      commitment_constraint_indexes.push(read_u64_le_slice(&mut input)?);
    }
    let read_g1 = |inp: &mut &[u8]| -> Result<G1AffineOf<C>, String> {
      read_g1_compressed_for::<C>(inp)
        .map_err(|e| format!("invalid VK G1 point: {e}"))
    };
    let ql = read_g1(&mut input)?;
    let qr = read_g1(&mut input)?;
    let qm = read_g1(&mut input)?;
    let qo = read_g1(&mut input)?;
    let qk = read_g1(&mut input)?;
    let s = [read_g1(&mut input)?, read_g1(&mut input)?, read_g1(&mut input)?];
    let n_qcp = usize::try_from(read_u64_le_slice(&mut input)?)
      .map_err(|e| e.to_string())?;
    if n_qcp != n_cci {
      return Err("VK qcp count differs from commitment index count".into());
    }
    let mut qcp = Vec::with_capacity(n_qcp);
    for _ in 0..n_qcp {
      qcp.push(read_g1(&mut input)?);
    }
    let g1 = read_g1(&mut input)?;
    let g2 = read_g2_compressed::<C>(&mut input)?;
    let tau_g2 = read_g2_compressed::<C>(&mut input)?;
    if !input.is_empty() {
      return Err("trailing bytes in native PLONK verifying key".into());
    }
    let vk = Self {
      domain_size,
      domain_size_inv,
      omega,
      coset_shift,
      num_public_inputs,
      commitment_constraint_indexes,
      ql,
      qr,
      qm,
      qo,
      qk,
      s,
      qcp,
      g1,
      g2,
      tau_g2,
    };
    vk.validate_structure()?;
    Ok(vk)
  }

  /// Verify algebraic well-formedness of domain and setup anchors.
  pub fn validate_structure(&self) -> Result<(), String> {
    if self.domain_size < 8 || !self.domain_size.is_power_of_two() {
      return Err("VK domain_size must be a power of two >= 8".into());
    }
    let domain = Radix2EvaluationDomain::<C::Fr>::new(self.domain_size)
      .ok_or("VK domain_size exceeds curve two-adicity")?;
    if self.omega != domain.group_gen() {
      return Err("VK omega does not match canonical radix-2 generator".into());
    }
    if self.domain_size_inv
      * C::Fr::from(u64::try_from(self.domain_size).expect("fits u64"))
      != C::FR_ONE
    {
      return Err("VK domain_size_inv is not 1/N".into());
    }
    if self.coset_shift != coset_shift::<C>() {
      return Err("VK coset_shift differs from curve standard".into());
    }
    if self.qcp.len() != self.commitment_constraint_indexes.len() {
      return Err("VK qcp length differs from commitment index length".into());
    }
    for &cci in &self.commitment_constraint_indexes {
      let row = self
        .num_public_inputs
        .checked_add(usize::try_from(cci).map_err(|e| e.to_string())?)
        .ok_or("VK commitment row overflow")?;
      if row >= self.domain_size {
        return Err("VK commitment row exceeds domain size".into());
      }
    }
    if self.g1.is_zero() || self.g2.is_zero() || self.tau_g2.is_zero() {
      return Err("VK setup anchor is the point at infinity".into());
    }
    for point in [
      self.ql, self.qr, self.qm, self.qo, self.qk, self.s[0], self.s[1],
      self.s[2], self.g1,
    ]
    .into_iter()
    .chain(self.qcp.iter().copied())
    {
      if !point.is_on_curve()
        || !point.is_in_correct_subgroup_assuming_on_curve()
      {
        return Err("VK G1 point is not in the prime-order subgroup".into());
      }
    }
    for point in [self.g2, self.tau_g2] {
      if !point.is_on_curve()
        || !point.is_in_correct_subgroup_assuming_on_curve()
      {
        return Err("VK G2 point is not in the prime-order subgroup".into());
      }
    }
    Ok(())
  }

  /// Verify that this verifying key's KZG anchors match independently
  /// authenticated [`VerifierParams`].
  pub fn check_anchors(
    &self,
    params: &VerifierParams<C>,
  ) -> Result<(), String> {
    if self.g1 != params.g1[0]
      || self.g2 != params.g2
      || self.tau_g2 != params.tau_g2
    {
      return Err(
        "VK KZG setup anchors differ from trusted VerifierParams".into(),
      );
    }
    Ok(())
  }

  /// Verify that this verifying key's KZG anchors match pinned anchor bytes
  /// produced by [`KzgCurve::encode_plonk_anchors`].
  pub fn check_anchor_bytes(
    &self,
    expected_anchors: &[u8],
  ) -> Result<(), String> {
    let actual = C::encode_plonk_anchors(&self.g1, &self.g2, &self.tau_g2);
    if actual != expected_anchors {
      return Err(
        "VK KZG setup anchors differ from pinned ceremony/setup anchors".into(),
      );
    }
    Ok(())
  }

  /// Classify this verifying key's KZG setup anchors against the compiled-in
  /// production ceremony anchors (`Ignition` on BN254, `Filecoin` on
  /// BLS12-381); any non-matching anchor set is [`crate::pipeline::SetupClass::Development`].
  pub fn setup_class(&self) -> crate::pipeline::SetupClass {
    use crate::kzg::{
      curve::{Bls12381, Bn254},
      srs::filecoin::filecoin_anchors,
    };
    use crate::pipeline::{SetupClass, ignition_parameters};
    let actual = C::encode_plonk_anchors(&self.g1, &self.g2, &self.tau_g2);
    match C::CURVE {
      Curve::Bn254 => {
        if ignition_parameters().is_ok_and(|p| {
          actual == Bn254::encode_plonk_anchors(&p.g1[0], &p.g2, &p.tau_g2)
        }) {
          SetupClass::Ignition
        } else {
          SetupClass::Development
        }
      },
      Curve::Bls12381 => {
        let srs = filecoin_anchors();
        if actual
          == Bls12381::encode_plonk_anchors(&srs.g1[0], &srs.g2, &srs.tau_g2)
        {
          SetupClass::Filecoin
        } else {
          SetupClass::Development
        }
      },
    }
  }

  /// Canonical SHA-256 digest of this verifying key.
  pub fn sha256(&self) -> [u8; 32] {
    let bytes = self.to_bytes().expect("VK serialization infallible");
    Sha256::digest(&bytes).into()
  }

  /// Lowercase hex SHA-256 digest of this verifying key.
  pub fn sha256_hex(&self) -> String {
    hex_digest(&self.sha256())
  }
}

impl<C: KzgCurve> ProvingKey<C> {
  /// Serialize to versioned binary bytes (`IXNPPK01`).
  pub fn to_bytes(&self) -> Result<Vec<u8>, String> {
    let mut out = Vec::new();
    out.extend_from_slice(PK_MAGIC);
    out.push(curve_tag::<C>());
    let vk_bytes = self.vk.to_bytes()?;
    out.extend_from_slice(
      &u64::try_from(vk_bytes.len()).expect("fits u64").to_le_bytes(),
    );
    out.extend_from_slice(&vk_bytes);
    for v in [self.pre_gates, self.total_gates, self.commits_len] {
      out.extend_from_slice(&u64::try_from(v).expect("fits u64").to_le_bytes());
    }
    out.extend_from_slice(
      &u64::try_from(self.srs_g1.len()).expect("fits u64").to_le_bytes(),
    );
    for p in &self.srs_g1 {
      p.serialize_compressed(&mut out).map_err(|e| e.to_string())?;
    }
    let write_poly =
      |out: &mut Vec<u8>, poly: &[C::Fr]| -> Result<(), String> {
        for x in poly {
          x.serialize_compressed(&mut *out).map_err(|e| e.to_string())?;
        }
        Ok(())
      };
    write_poly(&mut out, &self.ql_coeffs)?;
    write_poly(&mut out, &self.qr_coeffs)?;
    write_poly(&mut out, &self.qm_coeffs)?;
    write_poly(&mut out, &self.qo_coeffs)?;
    write_poly(&mut out, &self.qk_coeffs)?;
    write_poly(&mut out, &self.s1_coeffs)?;
    write_poly(&mut out, &self.s2_coeffs)?;
    write_poly(&mut out, &self.s3_coeffs)?;
    for qcp in &self.qcp_coeffs {
      write_poly(&mut out, qcp)?;
    }
    for &p in &self.permutation {
      out.extend_from_slice(&p.to_le_bytes());
    }
    Ok(out)
  }

  /// Deserialize with strict validation of embedded VK, SRS prefix, and sizes.
  pub fn from_bytes(mut input: &[u8]) -> Result<Self, String> {
    if input.len() < 9 || &input[..8] != PK_MAGIC {
      return Err("invalid native PLONK proving key magic".into());
    }
    if input[8] != curve_tag::<C>() {
      return Err("native PLONK proving key curve mismatch".into());
    }
    input = &input[9..];
    let vk_len = usize::try_from(read_u64_le_slice(&mut input)?)
      .map_err(|e| e.to_string())?;
    if input.len() < vk_len {
      return Err("truncated proving key VK".into());
    }
    let vk = VerifyingKey::<C>::from_bytes(&input[..vk_len])?;
    input = &input[vk_len..];
    let pre_gates = usize::try_from(read_u64_le_slice(&mut input)?)
      .map_err(|e| e.to_string())?;
    let total_gates = usize::try_from(read_u64_le_slice(&mut input)?)
      .map_err(|e| e.to_string())?;
    let commits_len = usize::try_from(read_u64_le_slice(&mut input)?)
      .map_err(|e| e.to_string())?;
    let n = vk.domain_size;
    let srs_len = usize::try_from(read_u64_le_slice(&mut input)?)
      .map_err(|e| e.to_string())?;
    if srs_len != n + 3 {
      return Err(format!("PK SRS length {srs_len} != domain + 3 ({})", n + 3));
    }
    let mut srs_g1 = Vec::with_capacity(srs_len);
    for _ in 0..srs_len {
      srs_g1.push(
        read_g1_compressed_for::<C>(&mut input)
          .map_err(|e| format!("invalid PK SRS G1: {e}"))?,
      );
    }
    let read_poly = |inp: &mut &[u8]| -> Result<Vec<C::Fr>, String> {
      let mut v = Vec::with_capacity(n);
      for _ in 0..n {
        v.push(read_fr_compressed::<C>(inp)?);
      }
      Ok(v)
    };
    let ql_coeffs = read_poly(&mut input)?;
    let qr_coeffs = read_poly(&mut input)?;
    let qm_coeffs = read_poly(&mut input)?;
    let qo_coeffs = read_poly(&mut input)?;
    let qk_coeffs = read_poly(&mut input)?;
    let s1_coeffs = read_poly(&mut input)?;
    let s2_coeffs = read_poly(&mut input)?;
    let s3_coeffs = read_poly(&mut input)?;
    let mut qcp_coeffs = Vec::with_capacity(vk.qcp.len());
    for _ in 0..vk.qcp.len() {
      qcp_coeffs.push(read_poly(&mut input)?);
    }
    let perm_len = 3 * n;
    let mut permutation = Vec::with_capacity(perm_len);
    for _ in 0..perm_len {
      let target = read_u32_le_slice(&mut input)?;
      if (target as usize) >= perm_len {
        return Err("PK permutation index out of range".into());
      }
      permutation.push(target);
    }
    if !input.is_empty() {
      return Err("trailing bytes in native PLONK proving key".into());
    }
    Ok(Self {
      vk,
      srs_g1,
      ql_coeffs,
      qr_coeffs,
      qm_coeffs,
      qo_coeffs,
      qk_coeffs,
      qcp_coeffs,
      s1_coeffs,
      s2_coeffs,
      s3_coeffs,
      permutation,
      pre_gates,
      total_gates,
      commits_len,
    })
  }
}

/// Build the permutation support vector `<1, ω, ..., ω^{N-1}> || k1·<...> || k2·<...>`
/// of length `3 * N`.
pub(super) fn permutation_support<C: KzgCurve>(
  n: usize,
  omega: C::Fr,
  k1: C::Fr,
) -> Vec<C::Fr> {
  let k2 = k1 * k1;
  let mut support = vec![C::FR_ZERO; 3 * n];
  let mut w = C::FR_ONE;
  for i in 0..n {
    support[i] = w;
    support[n + i] = k1 * w;
    support[2 * n + i] = k2 * w;
    w *= omega;
  }
  support
}

/// Preprocess a validated `ix-aiur-scs-v1` constraint system with an
/// authenticated KZG [`Srs`] into `(ProvingKey, VerifyingKey)`.
///
/// Fails closed if `!scs.outputs.is_empty()`: native PLONK-SCS does not
/// synthesize in-circuit pairing constraints for deferred `scs.outputs` and
/// requires self-contained `outputs == 0` circuits.
pub fn setup<C: KzgCurve>(
  scs: &ScsFile<C>,
  srs: &Srs<C>,
  accel: &PlonkAccelerator<C>,
) -> Result<(ProvingKey<C>, VerifyingKey<C>), String> {
  if !scs.outputs.is_empty() {
    return Err(format!(
      "native PLONK-SCS does not synthesize in-circuit pairing constraints \
       for deferred scs.outputs (got {} output wires); self-contained \
       outputs == 0 circuits are required",
      scs.outputs.len()
    ));
  }
  let n = domain_size_for_scs(scs)?;
  if srs.g1.len() < n + 3 {
    return Err(format!(
      "KZG SRS too small for domain {n}: have {} G1 points, need {}",
      srs.g1.len(),
      n + 3
    ));
  }
  let domain = Radix2EvaluationDomain::<C::Fr>::new(n)
    .ok_or("failed to build radix-2 domain")?;
  let omega = domain.group_gen();
  let domain_size_inv = C::Fr::from(u64::try_from(n).expect("fits u64"))
    .inverse()
    .ok_or("domain size not invertible")?;
  let k1 = coset_shift::<C>();

  let np = scs.publics;
  let nc = scs.commits.len();
  let commitment_constraint_index = scs.pre + nc;

  // Build Lagrange-basis selector columns (length N).
  let mut ql = vec![C::FR_ZERO; n];
  let mut qr = vec![C::FR_ZERO; n];
  let mut qm = vec![C::FR_ZERO; n];
  let mut qo = vec![C::FR_ZERO; n];
  let mut qk = vec![C::FR_ZERO; n];
  let mut qcp0 = vec![C::FR_ZERO; n];

  // Public input placeholders: -L[i] + PI[i] = 0 for i in 0..np.
  for slot in &mut ql[..np] {
    *slot = C::FR_NEG_ONE;
  }

  // Wire IDs in each column (`L || R || O`), defaulting unused slots to wire 0
  // (matching gnark `setup.go:buildPermutation`).
  let mut lro = vec![0u32; 3 * n];
  for (i, slot) in lro[..np].iter_mut().enumerate() {
    *slot = u32::try_from(i).expect("public index fits u32");
  }

  // 1. Pre-commitment gates: domain rows `np .. np + pre`.
  for i in 0..scs.pre {
    let row = np + i;
    let g = scs.gate(i);
    let c = scs.gate_coeffs(g);
    ql[row] = c.ql;
    qr[row] = c.qr;
    qm[row] = c.qm;
    qo[row] = c.qo;
    qk[row] = c.qc;
    lro[row] = g.a;
    lro[n + row] = g.b;
    lro[2 * n + row] = g.c;
  }

  // 2. BSB22 committed wire rows: `-w + Pi[row] = 0` with `qCp[row] = 1`.
  for (k, &wire) in scs.commits.iter().enumerate() {
    let row = np + scs.pre + k;
    ql[row] = C::FR_NEG_ONE;
    qcp0[row] = C::FR_ONE;
    lro[row] = wire;
  }

  // 3. BSB22 commitment-injection row: `-gamma + hash_fr(C_bsb22) = 0`.
  let commit_row = np + commitment_constraint_index;
  ql[commit_row] = C::FR_NEG_ONE;
  lro[commit_row] = scs.gamma;

  // 4. Post-commitment gates: domain rows `np + nc + 1 + i`.
  for i in scs.pre..scs.gates_count {
    let row = np + nc + 1 + i;
    let g = scs.gate(i);
    let c = scs.gate_coeffs(g);
    ql[row] = c.ql;
    qr[row] = c.qr;
    qm[row] = c.qm;
    qo[row] = c.qo;
    qk[row] = c.qc;
    lro[row] = g.a;
    lro[n + row] = g.b;
    lro[2 * n + row] = g.c;
  }

  // Build gnark-identical permutation cycles over `0..3*N`.
  let perm_len = 3 * n;
  let mut permutation = vec![u32::MAX; perm_len];
  let mut last_seen = vec![u32::MAX; scs.wires];
  for (pos, &wire) in lro.iter().enumerate() {
    let w = wire as usize;
    if last_seen[w] != u32::MAX {
      permutation[pos] = last_seen[w];
    }
    last_seen[w] = u32::try_from(pos).expect("position fits u32");
  }
  for (pos, slot) in permutation.iter_mut().enumerate() {
    if *slot == u32::MAX {
      *slot = last_seen[lro[pos] as usize];
    }
  }

  // Build S1, S2, S3 in Lagrange basis.
  let support = permutation_support::<C>(n, omega, k1);
  let mut s1 = vec![C::FR_ZERO; n];
  let mut s2 = vec![C::FR_ZERO; n];
  let mut s3 = vec![C::FR_ZERO; n];
  s1.par_iter_mut()
    .zip(s2.par_iter_mut())
    .zip(s3.par_iter_mut())
    .enumerate()
    .for_each(|(i, ((a, b), c))| {
      *a = support[permutation[i] as usize];
      *b = support[permutation[n + i] as usize];
      *c = support[permutation[2 * n + i] as usize];
    });

  // Convert all 9 preprocessed columns to monomial basis in one batch.
  let mut polys = vec![ql, qr, qm, qo, qk, qcp0, s1, s2, s3];
  accel.ifft_batch(&mut polys);

  // Commit to all 9 preprocessed columns in monomial basis.
  let refs: Vec<&[C::Fr]> = polys.iter().map(Vec::as_slice).collect();
  let commits_proj = accel.msm_batch(&srs.g1[..n], &refs);
  let commits: Vec<G1AffineOf<C>> =
    commits_proj.into_iter().map(CurveGroup::into_affine).collect();

  let mut it = polys.into_iter();
  let ql_coeffs = it.next().unwrap();
  let qr_coeffs = it.next().unwrap();
  let qm_coeffs = it.next().unwrap();
  let qo_coeffs = it.next().unwrap();
  let qk_coeffs = it.next().unwrap();
  let qcp0_coeffs = it.next().unwrap();
  let s1_coeffs = it.next().unwrap();
  let s2_coeffs = it.next().unwrap();
  let s3_coeffs = it.next().unwrap();

  let vk = VerifyingKey {
    domain_size: n,
    domain_size_inv,
    omega,
    coset_shift: k1,
    num_public_inputs: np,
    commitment_constraint_indexes: vec![
      u64::try_from(commitment_constraint_index).expect("fits u64"),
    ],
    ql: commits[0],
    qr: commits[1],
    qm: commits[2],
    qo: commits[3],
    qk: commits[4],
    qcp: vec![commits[5]],
    s: [commits[6], commits[7], commits[8]],
    g1: srs.g1[0],
    g2: srs.g2,
    tau_g2: srs.tau_g2,
  };
  vk.validate_structure()?;

  let pk = ProvingKey {
    vk: vk.clone(),
    srs_g1: srs.g1[..n + 3].to_vec(),
    ql_coeffs,
    qr_coeffs,
    qm_coeffs,
    qo_coeffs,
    qk_coeffs,
    qcp_coeffs: vec![qcp0_coeffs],
    s1_coeffs,
    s2_coeffs,
    s3_coeffs,
    permutation,
    pre_gates: scs.pre,
    total_gates: scs.gates_count,
    commits_len: nc,
  };

  Ok((pk, vk))
}
