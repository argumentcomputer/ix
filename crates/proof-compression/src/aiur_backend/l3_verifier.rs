//! Standalone verifier and envelope codec for Aiur L3 (`--aiur-stages`) PLONK proofs.
//!
//! # Public-input derivation specification
//!
//! Both L3 (`CompressGL`) and L4 (`CompressGLFixed`) prove a two-layer
//! `CompressWrap` statement over the root `ix_aggr` claim row:
//!
//! 1. **Claim digest**: `claim_digest = BLAKE3(claim_bytes)` (32 bytes).
//! 2. **Root `ix_aggr` claims bytes** (160 bytes, 20 little-endian `u64` words):
//!    `u64le(1) ‖ u64le(18) ‖ root_statement_prefix[0..10] ‖ pack_u32_le(claim_digest)[0..8]`,
//!    where every word of `root_statement_prefix` is canonical (`< p_GL = 2^64 - 2^32 + 1`),
//!    and `pack_u32_le(d)[i] = u32::from_le_bytes(d[4*i .. 4*i+4]) as u64`.
//! 3. **Layer 1 (`CompressWrap`) root statement**:
//!    `root_claims_digest = BLAKE3(root_claims_bytes)` (32 bytes),
//!    `S_root = BLAKE3("ix/compress-wrap/v1\0" ‖ root_vk_blake3 ‖ root_claims_digest)` (32 bytes).
//! 4. **Wrapper claims bytes** (160 bytes, 20 little-endian `u64` words):
//!    `u64le(1) ‖ u64le(18) ‖ wrap_claim_prefix[0..2] ‖ [0u64; 8] ‖ pack_u32_le(S_root)[0..8]`.
//! 5. **Layer 2 (`CompressGL` / `CompressGLFixed`) terminal statement**:
//!    `wrap_claims_digest = BLAKE3(wrap_claims_bytes)` (32 bytes),
//!    `S = BLAKE3("ix/compress-wrap/v1\0" ‖ wrap_key_blake3 ‖ wrap_claims_digest)` (32 bytes).
//! 6. **Terminal PLONK public inputs** (two little-endian 128-bit scalar limbs):
//!    `stmt_low  = u128::from_le_bytes(S[0..16])`,
//!    `stmt_high = u128::from_le_bytes(S[16..32])`.
//!
//! All keys, prefixes, anchors, and the terminal verifying key digest MUST be
//! independently pinned in [`L3VerifierPins`] — never read from untrusted proof
//! bytes or prover directories. Verification runs directly in pure Rust via
//! [`super::plonk::native::verifier`] with zero Go or CGo dependencies.

use super::{
  AiurCurve, compress_gl::WrapPolicy, pairing::final_program, plonk::native,
};
use crate::{
  kzg::{
    Curve, CurveScalar, KzgCurve,
    curve::{Bls12381 as Bls12381Curve, Bn254 as Bn254Curve},
    srs::filecoin::filecoin_anchors,
  },
  pipeline::{SetupClass, ignition_parameters},
};
use multi_stark::{p3_field::PrimeField64, types::Val};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use stark_verifier::compress_wrap::{self, Statement};
use std::{
  fs,
  path::{Path, PathBuf},
};

/// 4-byte family prefix shared by all Aiur L3 compressed proof payloads.
pub const L3_PROOF_FAMILY_PREFIX: &[u8; 4] = b"IXL3";

/// 8-byte envelope tag for BN254 Aiur L3 PLONK proofs.
pub const L3_BN254_PROOF_TAG: &[u8; 8] = b"IXL3BN1\0";

/// 8-byte envelope tag for BLS12-381 Aiur L3 PLONK proofs.
pub const L3_BLS12_381_PROOF_TAG: &[u8; 8] = b"IXL3BL1\0";

/// Maximum accepted native PLONK proof byte length (1 MiB).
pub const MAX_L3_PROOF_BYTES: usize = 1 << 20;

/// Maximum accepted JSON verifier bundle byte length (2 MiB).
const MAX_BUNDLE_BYTES: usize = 2 << 20;

/// Canonical JSON format identifier for pinned L3 verifier bundles.
pub const L3_VERIFIER_BUNDLE_FORMAT: &str = "ix-l3-verifier-v1";

/// Domain separator used in both layers of `CompressWrap` statement hashing.
pub const STATEMENT_DOMAIN: &[u8; 20] = compress_wrap::STATEMENT_DOMAIN;

const ENVELOPE_HEADER_BYTES: usize = 8 + 32;

/// Whether `bytes` begins with the Aiur L3 proof family prefix (`IXL3`).
pub fn is_l3_proof_bytes(bytes: &[u8]) -> bool {
  bytes.starts_with(L3_PROOF_FAMILY_PREFIX)
}

/// Canonical wire envelope for an Aiur L3 PLONK proof carried inside
/// `Ixon.Proof.proof`:
///
/// `magic (8B) ‖ terminal_vk_sha256 (32B) ‖ native_plonk_proof (1..=1 MiB)`
///
/// The envelope carries no statement limbs, verifying key bytes, anchors, or
/// policy metadata; all trust roots come solely from [`L3VerifierPins`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct L3ProofEnvelope {
  pub curve: Curve,
  pub terminal_vk_sha256: [u8; 32],
  pub proof: Vec<u8>,
}

impl L3ProofEnvelope {
  /// Exact 8-byte envelope magic tag for `curve`.
  pub const fn tag_for_curve(curve: Curve) -> &'static [u8; 8] {
    match curve {
      Curve::Bn254 => L3_BN254_PROOF_TAG,
      Curve::Bls12381 => L3_BLS12_381_PROOF_TAG,
    }
  }

  /// Encode this envelope into canonical bytes.
  pub fn encode(&self) -> Result<Vec<u8>, String> {
    if self.proof.is_empty() || self.proof.len() > MAX_L3_PROOF_BYTES {
      return Err(format!(
        "invalid L3 PLONK proof payload length: {}",
        self.proof.len()
      ));
    }
    let mut out = Vec::with_capacity(ENVELOPE_HEADER_BYTES + self.proof.len());
    out.extend_from_slice(Self::tag_for_curve(self.curve));
    out.extend_from_slice(&self.terminal_vk_sha256);
    out.extend_from_slice(&self.proof);
    Ok(out)
  }

  /// Strictly decode a canonical L3 proof envelope, failing closed on any
  /// unknown tag, truncation, empty payload, or oversized payload.
  pub fn decode(bytes: &[u8]) -> Result<Self, String> {
    if bytes.len() < ENVELOPE_HEADER_BYTES {
      return Err("truncated L3 proof envelope header".into());
    }
    let curve = if bytes.starts_with(L3_BN254_PROOF_TAG) {
      Curve::Bn254
    } else if bytes.starts_with(L3_BLS12_381_PROOF_TAG) {
      Curve::Bls12381
    } else if bytes.starts_with(L3_PROOF_FAMILY_PREFIX) {
      return Err("unsupported L3 proof envelope version or curve tag".into());
    } else {
      return Err(
        "invalid magic: expected IXL3BN1\\0 or IXL3BL1\\0 envelope".into(),
      );
    };
    let proof_len = bytes.len() - ENVELOPE_HEADER_BYTES;
    if proof_len == 0 || proof_len > MAX_L3_PROOF_BYTES {
      return Err(format!(
        "invalid L3 PLONK proof payload length: {proof_len}"
      ));
    }
    let mut terminal_vk_sha256 = [0u8; 32];
    terminal_vk_sha256.copy_from_slice(&bytes[8..40]);
    Ok(Self { curve, terminal_vk_sha256, proof: bytes[40..].to_vec() })
  }
}

/// Pack a 32-byte digest into eight little-endian `u32` words zero-extended
/// to `u64` (matching `MultiStark.digestGs` and `stark_verifier::digest_words`).
pub fn pack_digest_u32_le(digest: &[u8; 32]) -> [u64; 8] {
  std::array::from_fn(|i| {
    u64::from(u32::from_le_bytes(digest.as_chunks::<4>().0[i]))
  })
}

fn check_canonical_goldilocks(
  words: &[u64],
  label: &str,
) -> Result<(), String> {
  for (idx, &word) in words.iter().enumerate() {
    if word >= Val::ORDER_U64 {
      return Err(format!(
        "{label}[{idx}] = {word} is not a canonical Goldilocks field element"
      ));
    }
  }
  Ok(())
}

fn parse_hex_32(text: &str, label: &str) -> Result<[u8; 32], String> {
  let clean = text.strip_prefix("0x").unwrap_or(text);
  if clean.len() != 64 || !clean.is_ascii() {
    return Err(format!("{label}: expected 64 hexadecimal characters"));
  }
  let mut out = [0u8; 32];
  for (i, slot) in out.iter_mut().enumerate() {
    *slot = u8::from_str_radix(&clean[2 * i..2 * i + 2], 16)
      .map_err(|e| format!("{label}: invalid hex: {e}"))?;
  }
  Ok(out)
}

fn parse_hex_bytes(text: &str, label: &str) -> Result<Vec<u8>, String> {
  let clean = text.strip_prefix("0x").unwrap_or(text);
  if !clean.is_ascii() || !clean.len().is_multiple_of(2) {
    return Err(format!("{label}: invalid hexadecimal byte string"));
  }
  (0..clean.len())
    .step_by(2)
    .map(|i| {
      u8::from_str_radix(&clean[i..i + 2], 16)
        .map_err(|e| format!("{label}: invalid hex: {e}"))
    })
    .collect()
}

fn encode_hex(bytes: &[u8]) -> String {
  use std::fmt::Write as _;
  let mut out = String::with_capacity(bytes.len() * 2);
  for b in bytes {
    write!(out, "{b:02x}").expect("write to String");
  }
  out
}

fn validate_wrap_policy(policy: &WrapPolicy) -> Result<(), String> {
  let artifact =
    parse_hex_32(&policy.artifact_blake3, "wrap_policy.artifact_blake3")?;
  let key = parse_hex_32(&policy.key_blake3, "wrap_policy.key_blake3")?;
  let layout =
    parse_hex_32(&policy.layout_blake3, "wrap_policy.layout_blake3")?;
  if artifact == [0u8; 32] || key == [0u8; 32] || layout == [0u8; 32] {
    return Err("wrap_policy digests must be nonzero".into());
  }
  check_canonical_goldilocks(&policy.claim_prefix, "wrap_policy.claim_prefix")
}

/// Serialize the canonical 160-byte `ix_aggr` root claims batch from the
/// pinned 10-word backend prefix and 32-byte `claim_digest = BLAKE3(claim_bytes)`.
pub fn derive_root_claims_bytes(
  root_statement_prefix: &[u64; 10],
  claim_digest: &[u8; 32],
) -> Result<[u8; 160], String> {
  check_canonical_goldilocks(root_statement_prefix, "root_statement_prefix")?;
  let mut out = [0u8; 160];
  let mut pos = 0usize;
  let mut push = |word: u64| {
    out[pos..pos + 8].copy_from_slice(&word.to_le_bytes());
    pos += 8;
  };
  push(1);
  push(18);
  for &w in root_statement_prefix {
    push(w);
  }
  for w in pack_digest_u32_le(claim_digest) {
    push(w);
  }
  debug_assert_eq!(pos, 160);
  Ok(out)
}

/// Derive the 32-byte L3 terminal statement digest `S` from pinned
/// `(root_vk_blake3, wrap_policy)` and raw serialized `root_claims_bytes`.
///
/// Exact formula:
/// `S_root = BLAKE3("ix/compress-wrap/v1\0" ‖ root_vk_blake3 ‖ BLAKE3(root_claims_bytes))`
/// `wrap_claims = claims_bytes([[wrap_claim_prefix[0], wrap_claim_prefix[1], 0×8, pack_u32_le(S_root)]])`
/// `S = BLAKE3("ix/compress-wrap/v1\0" ‖ wrap_key_blake3 ‖ BLAKE3(wrap_claims))`.
pub fn derive_l3_statement_from_root_claims(
  root_vk_blake3: &[u8; 32],
  root_claims_bytes: &[u8],
  wrap_policy: &WrapPolicy,
) -> Result<[u8; 32], String> {
  if *root_vk_blake3 == [0u8; 32] {
    return Err("root_vk_blake3 must be nonzero".into());
  }
  if root_claims_bytes.is_empty() {
    return Err("root_claims_bytes must be nonempty".into());
  }
  validate_wrap_policy(wrap_policy)?;
  let root_statement = Statement {
    key_digest: *root_vk_blake3,
    claims_digest: *blake3::hash(root_claims_bytes).as_bytes(),
  };
  let gl_statement = wrap_policy.statement_for(&root_statement)?;
  Ok(*blake3::hash(&gl_statement.preimage()).as_bytes())
}

/// Derive the 32-byte L3 terminal statement digest `S` from a 32-byte
/// `claim_digest = BLAKE3(claim_bytes)` and pinned statement parameters.
pub fn derive_l3_statement_from_claim_digest(
  root_vk_blake3: &[u8; 32],
  root_statement_prefix: &[u64; 10],
  wrap_policy: &WrapPolicy,
  claim_digest: &[u8; 32],
) -> Result<[u8; 32], String> {
  let root_claims_bytes =
    derive_root_claims_bytes(root_statement_prefix, claim_digest)?;
  derive_l3_statement_from_root_claims(
    root_vk_blake3,
    &root_claims_bytes,
    wrap_policy,
  )
}

/// Derive the 32-byte L3 terminal statement digest `S` directly from serialized
/// `claim_bytes` (`Ix.Claim.ser`) and pinned statement parameters.
pub fn derive_l3_statement_from_claim_bytes(
  root_vk_blake3: &[u8; 32],
  root_statement_prefix: &[u64; 10],
  wrap_policy: &WrapPolicy,
  claim_bytes: &[u8],
) -> Result<[u8; 32], String> {
  let claim_digest = *blake3::hash(claim_bytes).as_bytes();
  derive_l3_statement_from_claim_digest(
    root_vk_blake3,
    root_statement_prefix,
    wrap_policy,
    &claim_digest,
  )
}

/// Split a 32-byte terminal statement `S` into its two canonical little-endian
/// 128-bit integer public inputs `[stmt_low, stmt_high]`.
pub fn derive_l3_public_limbs(statement: &[u8; 32]) -> [u128; 2] {
  [
    u128::from_le_bytes(statement.as_chunks::<16>().0[0]),
    u128::from_le_bytes(statement.as_chunks::<16>().0[1]),
  ]
}

/// Split a 32-byte terminal statement `S` into its two pairing-curve scalar
/// public inputs `[stmt_low, stmt_high]` for curve `C`.
pub fn derive_l3_public_inputs_for<C: AiurCurve>(
  statement: &[u8; 32],
) -> [CurveScalar<C>; 2] {
  final_program::statement_arguments_for::<C>(statement)
}

/// Compiled-in ceremony setup anchors for production setups (`Ignition` on
/// BN254 or `Filecoin` on BLS12-381).
pub fn ceremony_anchors(
  setup: SetupClass,
  curve: Curve,
) -> Result<Vec<u8>, String> {
  match (setup, curve) {
    (SetupClass::Ignition, Curve::Bn254) => {
      let params = ignition_parameters().map_err(|e| e.to_string())?;
      Ok(Bn254Curve::encode_plonk_anchors(
        &params.g1[0],
        &params.g2,
        &params.tau_g2,
      ))
    },
    (SetupClass::Filecoin, Curve::Bls12381) => {
      let srs = filecoin_anchors();
      Ok(Bls12381Curve::encode_plonk_anchors(&srs.g1[0], &srs.g2, &srs.tau_g2))
    },
    (SetupClass::Ignition, Curve::Bls12381) => {
      Err("Ignition ceremony setup is only valid for BN254".into())
    },
    (SetupClass::Filecoin, Curve::Bn254) => {
      Err("Filecoin ceremony setup is only valid for BLS12-381".into())
    },
    (SetupClass::Development, _) => {
      Err("development setup has no compiled-in ceremony anchors".into())
    },
    (SetupClass::Groth16, _) => {
      Err("Groth16 setup is not valid for L3 PLONK verification".into())
    },
  }
}

/// Independently pinned verifier trust roots for Aiur L3 PLONK proofs.
///
/// Every field must originate from trusted release pins or a caller-pinned
/// verifier bundle — never from untrusted proof bytes or prover files.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct L3VerifierPins {
  pub curve: Curve,
  pub setup: SetupClass,
  pub root_vk_blake3: [u8; 32],
  pub root_statement_prefix: [u64; 10],
  pub wrap_policy: WrapPolicy,
  pub terminal_vk_sha256: [u8; 32],
  pub terminal_vk: Vec<u8>,
  pub anchors: Vec<u8>,
}

impl L3VerifierPins {
  /// Validate internal consistency, key pin integrity, setup trust policy,
  /// and ceremony anchor authenticity.
  pub fn validate(&self, allow_development: bool) -> Result<(), String> {
    match self.setup {
      SetupClass::Development => {
        if !allow_development {
          return Err(
            "L3 verifier uses a known-trapdoor development setup; pass --dev-srs to accept it (not production-secure)".into(),
          );
        }
      },
      SetupClass::Ignition | SetupClass::Filecoin => {
        let expected_anchors = ceremony_anchors(self.setup, self.curve)?;
        if self.anchors != expected_anchors {
          return Err(format!(
            "L3 verifier anchors do not match the compiled-in {} ceremony parameters",
            self.setup.label()
          ));
        }
      },
      SetupClass::Groth16 => {
        return Err(
          "Groth16 setup class is not valid for L3 PLONK verification".into(),
        );
      },
    }
    let expected_anchor_len = match self.curve {
      Curve::Bn254 => Bn254Curve::PLONK_ANCHOR_BYTES,
      Curve::Bls12381 => Bls12381Curve::PLONK_ANCHOR_BYTES,
    };
    if self.anchors.len() != expected_anchor_len {
      return Err(format!(
        "invalid L3 anchor length for {}: expected {expected_anchor_len}, got {}",
        self.curve.as_str(),
        self.anchors.len()
      ));
    }
    if self.root_vk_blake3 == [0u8; 32] {
      return Err("L3 root_vk_blake3 pin must be nonzero".into());
    }
    check_canonical_goldilocks(
      &self.root_statement_prefix,
      "root_statement_prefix",
    )?;
    validate_wrap_policy(&self.wrap_policy)?;
    if self.terminal_vk_sha256 == [0u8; 32] {
      return Err("L3 terminal_vk_sha256 pin must be nonzero".into());
    }
    if self.terminal_vk.is_empty()
      || self.terminal_vk.len() > MAX_L3_PROOF_BYTES
    {
      return Err("invalid L3 terminal verifying key size".into());
    }
    let actual_vk_sha256: [u8; 32] = Sha256::digest(&self.terminal_vk).into();
    if actual_vk_sha256 != self.terminal_vk_sha256 {
      return Err(
        "L3 terminal verifying key bytes differ from pinned terminal_vk_sha256"
          .into(),
      );
    }
    Ok(())
  }

  /// Recompute the 32-byte terminal statement `S` for `claim_bytes`.
  pub fn derive_statement(
    &self,
    claim_bytes: &[u8],
  ) -> Result<[u8; 32], String> {
    derive_l3_statement_from_claim_bytes(
      &self.root_vk_blake3,
      &self.root_statement_prefix,
      &self.wrap_policy,
      claim_bytes,
    )
  }

  /// Recompute the 32-byte terminal statement `S` for `claim_digest`.
  pub fn derive_statement_from_digest(
    &self,
    claim_digest: &[u8; 32],
  ) -> Result<[u8; 32], String> {
    derive_l3_statement_from_claim_digest(
      &self.root_vk_blake3,
      &self.root_statement_prefix,
      &self.wrap_policy,
      claim_digest,
    )
  }

  /// Recompute the 32-byte terminal statement `S` for raw `root_claims_bytes`.
  pub fn derive_statement_from_root_claims(
    &self,
    root_claims_bytes: &[u8],
  ) -> Result<[u8; 32], String> {
    derive_l3_statement_from_root_claims(
      &self.root_vk_blake3,
      root_claims_bytes,
      &self.wrap_policy,
    )
  }

  /// Recompute `[stmt_low, stmt_high]` for `claim_bytes`.
  pub fn derive_public_limbs(
    &self,
    claim_bytes: &[u8],
  ) -> Result<[u128; 2], String> {
    Ok(derive_l3_public_limbs(&self.derive_statement(claim_bytes)?))
  }

  /// Convert these pins into a self-contained [`L3VerifierBundle`] with
  /// embedded hex verifying key bytes (or referencing `terminal_vk_path`).
  pub fn to_bundle(
    &self,
    terminal_vk_path: Option<PathBuf>,
  ) -> L3VerifierBundle {
    let (terminal_vk_hex, terminal_vk_path) = match terminal_vk_path {
      Some(path) => (None, Some(path)),
      None => (Some(encode_hex(&self.terminal_vk)), None),
    };
    L3VerifierBundle {
      format: L3_VERIFIER_BUNDLE_FORMAT.to_owned(),
      curve: self.curve.as_str().to_owned(),
      setup: self.setup.label().to_owned(),
      root_vk_blake3: encode_hex(&self.root_vk_blake3),
      root_statement_prefix: self.root_statement_prefix,
      wrap_policy: self.wrap_policy.clone(),
      terminal_vk_sha256: encode_hex(&self.terminal_vk_sha256),
      terminal_vk_hex,
      terminal_vk_path,
      anchors_hex: Some(encode_hex(&self.anchors)),
    }
  }
}

/// JSON-serializable L3 verifier bundle (`ix-l3-verifier-v1`), loaded strictly
/// under an independent caller-supplied BLAKE3 pin of its exact bytes.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct L3VerifierBundle {
  pub format: String,
  pub curve: String,
  pub setup: String,
  pub root_vk_blake3: String,
  pub root_statement_prefix: [u64; 10],
  pub wrap_policy: WrapPolicy,
  pub terminal_vk_sha256: String,
  #[serde(default, skip_serializing_if = "Option::is_none")]
  pub terminal_vk_hex: Option<String>,
  #[serde(default, skip_serializing_if = "Option::is_none")]
  pub terminal_vk_path: Option<PathBuf>,
  #[serde(default, skip_serializing_if = "Option::is_none")]
  pub anchors_hex: Option<String>,
}

fn parse_setup_class(label: &str) -> Result<SetupClass, String> {
  match label {
    "ignition" => Ok(SetupClass::Ignition),
    "filecoin" => Ok(SetupClass::Filecoin),
    "development" => Ok(SetupClass::Development),
    other => Err(format!(
      "unknown L3 setup class {other:?} (expected ignition, filecoin, or development)"
    )),
  }
}

impl L3VerifierBundle {
  /// Authenticate `bytes` against `expected_blake3`, parse strictly, and
  /// resolve into [`L3VerifierPins`].
  pub fn from_pinned_bytes(
    bytes: &[u8],
    expected_blake3: &[u8; 32],
    base_dir: Option<&Path>,
  ) -> Result<L3VerifierPins, String> {
    if bytes.len() > MAX_BUNDLE_BYTES {
      return Err("L3 verifier bundle exceeds maximum size limit".into());
    }
    let actual = *blake3::hash(bytes).as_bytes();
    if &actual != expected_blake3 {
      return Err(format!(
        "L3 verifier bundle BLAKE3 {} differs from pinned {}",
        encode_hex(&actual),
        encode_hex(expected_blake3)
      ));
    }
    let bundle: Self = serde_json::from_slice(bytes)
      .map_err(|e| format!("invalid L3 verifier bundle JSON: {e}"))?;
    if bundle.format != L3_VERIFIER_BUNDLE_FORMAT {
      return Err(format!(
        "unsupported L3 verifier bundle format {:?} (expected {L3_VERIFIER_BUNDLE_FORMAT:?})",
        bundle.format
      ));
    }
    let curve = Curve::parse(&bundle.curve)?;
    let setup = parse_setup_class(&bundle.setup)?;
    let root_vk_blake3 =
      parse_hex_32(&bundle.root_vk_blake3, "root_vk_blake3")?;
    let terminal_vk_sha256 =
      parse_hex_32(&bundle.terminal_vk_sha256, "terminal_vk_sha256")?;
    let terminal_vk = match (&bundle.terminal_vk_hex, &bundle.terminal_vk_path)
    {
      (Some(hex), None) => parse_hex_bytes(hex, "terminal_vk_hex")?,
      (None, Some(path)) => {
        let resolved = if path.is_absolute() {
          path.clone()
        } else if let Some(base) = base_dir {
          base.join(path)
        } else {
          return Err(
            "relative terminal_vk_path requires a bundle file base directory"
              .into(),
          );
        };
        fs::read(&resolved)
          .map_err(|e| format!("{}: {e}", resolved.display()))?
      },
      (Some(_), Some(_)) => {
        return Err(
          "L3 verifier bundle must set exactly one of terminal_vk_hex or terminal_vk_path"
            .into(),
        );
      },
      (None, None) => {
        return Err(
          "L3 verifier bundle is missing terminal_vk_hex / terminal_vk_path"
            .into(),
        );
      },
    };
    let anchors = match (setup, &bundle.anchors_hex) {
      (SetupClass::Development, None) => {
        return Err(
          "development L3 verifier bundle must supply anchors_hex".into(),
        );
      },
      (SetupClass::Ignition | SetupClass::Filecoin, None) => {
        ceremony_anchors(setup, curve)?
      },
      (
        SetupClass::Development | SetupClass::Ignition | SetupClass::Filecoin,
        Some(hex),
      ) => parse_hex_bytes(hex, "anchors_hex")?,
      (SetupClass::Groth16, _) => {
        return Err(
          "Groth16 setup class is not valid for L3 PLONK verification".into(),
        );
      },
    };
    let pins = L3VerifierPins {
      curve,
      setup,
      root_vk_blake3,
      root_statement_prefix: bundle.root_statement_prefix,
      wrap_policy: bundle.wrap_policy,
      terminal_vk_sha256,
      terminal_vk,
      anchors,
    };
    // Validate structural integrity and ceremony anchor match here; the
    // development opt-in check runs at verification time.
    pins.validate(true)?;
    Ok(pins)
  }

  /// Read a bundle file from disk, check its exact bytes against
  /// `expected_blake3_hex`, and resolve into [`L3VerifierPins`].
  pub fn from_pinned_file(
    path: &Path,
    expected_blake3_hex: &str,
  ) -> Result<L3VerifierPins, String> {
    let expected = parse_hex_32(expected_blake3_hex, "l3-verifier-blake3")?;
    let bytes =
      fs::read(path).map_err(|e| format!("{}: {e}", path.display()))?;
    Self::from_pinned_bytes(&bytes, &expected, path.parent())
  }
}

/// Verify an Aiur L3 proof envelope against `claim_bytes` and independently
/// pinned production verifier parameters.
///
/// Refuses development keys; call [`verify_l3_proof_with_options`] with
/// `allow_development = true` to explicitly opt into development verification.
pub fn verify_l3_proof(
  claim_bytes: &[u8],
  proof_bytes: &[u8],
  pins: &L3VerifierPins,
) -> Result<SetupClass, String> {
  verify_l3_proof_with_options(claim_bytes, proof_bytes, pins, false)
}

/// Verify an Aiur L3 proof envelope against `claim_bytes` and independently
/// pinned verifier parameters, with explicit opt-in for development setups.
pub fn verify_l3_proof_with_options(
  claim_bytes: &[u8],
  proof_bytes: &[u8],
  pins: &L3VerifierPins,
  allow_development: bool,
) -> Result<SetupClass, String> {
  pins.validate(allow_development)?;
  let root_claims_bytes = derive_root_claims_bytes(
    &pins.root_statement_prefix,
    blake3::hash(claim_bytes).as_bytes(),
  )?;
  verify_l3_proof_from_root_claims(
    &root_claims_bytes,
    proof_bytes,
    pins,
    allow_development,
  )
}

/// Verify an Aiur L3 proof envelope against raw serialized `root_claims_bytes`
/// and independently pinned verifier parameters.
pub fn verify_l3_proof_from_root_claims(
  root_claims_bytes: &[u8],
  proof_bytes: &[u8],
  pins: &L3VerifierPins,
  allow_development: bool,
) -> Result<SetupClass, String> {
  pins.validate(allow_development)?;
  let envelope = L3ProofEnvelope::decode(proof_bytes)?;
  if envelope.curve != pins.curve {
    return Err(format!(
      "L3 proof curve {} differs from pinned verifier curve {}",
      envelope.curve.as_str(),
      pins.curve.as_str()
    ));
  }
  if envelope.terminal_vk_sha256 != pins.terminal_vk_sha256 {
    return Err(
      "L3 proof envelope names a different terminal PLONK verifying key than the pin"
        .into(),
    );
  }
  let statement = pins.derive_statement_from_root_claims(root_claims_bytes)?;
  verify_terminal_plonk(pins, &envelope.proof, &statement)?;
  Ok(pins.setup)
}

fn verify_terminal_plonk_for<C: AiurCurve>(
  pins: &L3VerifierPins,
  proof: &[u8],
  statement: &[u8; 32],
) -> Result<(), String> {
  let vk = native::VerifyingKey::<C>::from_bytes(&pins.terminal_vk)
    .map_err(|e| format!("L3 {} terminal VK decode failed: {e}", C::NAME))?;
  vk.check_anchor_bytes(&pins.anchors)?;
  let expected = derive_l3_public_inputs_for::<C>(statement);
  let public_inputs = [expected[0].0, expected[1].0];
  native::verify_native_bytes::<C>(
    &vk,
    &pins.terminal_vk_sha256,
    proof,
    &public_inputs,
  )
  .map_err(|e| format!("L3 {} PLONK verification failed: {e}", C::NAME))
}

fn verify_terminal_plonk(
  pins: &L3VerifierPins,
  proof: &[u8],
  statement: &[u8; 32],
) -> Result<(), String> {
  match pins.curve {
    Curve::Bn254 => {
      verify_terminal_plonk_for::<Bn254Curve>(pins, proof, statement)
    },
    Curve::Bls12381 => {
      verify_terminal_plonk_for::<Bls12381Curve>(pins, proof, statement)
    },
  }
}

#[cfg(test)]
mod tests {
  use super::super::l3_verifier_test_fixture as fx;
  use super::*;
  use crate::kzg::{
    Srs,
    srs::filecoin::{
      FILECOIN_PREFIX_2P8_FIXTURE, FILECOIN_PREFIX_2P8_MANIFEST_BLAKE3,
      load_filecoin_cache,
    },
  };
  use multi_stark::p3_field::PrimeCharacteristicRing;

  fn sample_wrap_policy(wrap_key_byte: u8) -> WrapPolicy {
    WrapPolicy {
      artifact_blake3: encode_hex(&[0x11; 32]),
      key_blake3: encode_hex(&[wrap_key_byte; 32]),
      layout_blake3: encode_hex(&[0x33; 32]),
      claim_prefix: [1, 0],
    }
  }

  /// Release-0.5 `STATEMENT_PREFIX` from `pipeline/verifying_keys.rs`.
  const RELEASE_05_PREFIX: [u64; 10] = [
    1, 0, 2736370005, 1983549104, 896032380, 1564468090, 1137178757,
    4223943773, 1723211272, 3024343524,
  ];

  #[test]
  fn two_layer_statement_matches_wrap_policy_and_claim_encoding() {
    let root_vk_blake3 = [0x42u8; 32];
    let policy = sample_wrap_policy(0x22);
    let claim_bytes = b"sample-ix-claim-payload";
    let claim_digest = *blake3::hash(claim_bytes).as_bytes();

    // Independently build the 18-word root claim row via stark_verifier::claims_bytes.
    let mut row = Vec::with_capacity(18);
    row.extend(RELEASE_05_PREFIX.into_iter().map(Val::from_u64));
    row
      .extend(pack_digest_u32_le(&claim_digest).into_iter().map(Val::from_u64));
    let expected_root_claims = stark_verifier::claims_bytes(&[row]);
    assert_eq!(expected_root_claims.len(), 160);

    let derived_root_claims =
      derive_root_claims_bytes(&RELEASE_05_PREFIX, &claim_digest).unwrap();
    assert_eq!(derived_root_claims.as_slice(), expected_root_claims.as_slice());

    // Layer 1 + Layer 2 via WrapPolicy::statement_for.
    let s_root = Statement {
      key_digest: root_vk_blake3,
      claims_digest: *blake3::hash(&expected_root_claims).as_bytes(),
    };
    let s_gl = policy.statement_for(&s_root).unwrap();
    let expected_terminal = *blake3::hash(&s_gl.preimage()).as_bytes();

    let derived_terminal = derive_l3_statement_from_claim_bytes(
      &root_vk_blake3,
      &RELEASE_05_PREFIX,
      &policy,
      claim_bytes,
    )
    .unwrap();
    assert_eq!(derived_terminal, expected_terminal);

    // Limb splitting must match statement_arguments_for on both curves.
    let limbs = derive_l3_public_limbs(&derived_terminal);
    let bn_args = derive_l3_public_inputs_for::<Bn254Curve>(&derived_terminal);
    assert_eq!(bn_args[0].0, ark_bn254::Fr::from(limbs[0]));
    assert_eq!(bn_args[1].0, ark_bn254::Fr::from(limbs[1]));
    let bls_args =
      derive_l3_public_inputs_for::<Bls12381Curve>(&derived_terminal);
    assert_eq!(bls_args[0].0, ark_bls12_381::Fr::from(limbs[0]));
    assert_eq!(bls_args[1].0, ark_bls12_381::Fr::from(limbs[1]));

    // Every input component must affect the terminal statement.
    let mut alt_root_vk = root_vk_blake3;
    alt_root_vk[0] ^= 1;
    assert_ne!(
      derive_l3_statement_from_claim_bytes(
        &alt_root_vk,
        &RELEASE_05_PREFIX,
        &policy,
        claim_bytes
      )
      .unwrap(),
      derived_terminal
    );
    let alt_policy = sample_wrap_policy(0x23);
    assert_ne!(
      derive_l3_statement_from_claim_bytes(
        &root_vk_blake3,
        &RELEASE_05_PREFIX,
        &alt_policy,
        claim_bytes
      )
      .unwrap(),
      derived_terminal
    );
    let mut alt_prefix = RELEASE_05_PREFIX;
    alt_prefix[1] = 1;
    assert_ne!(
      derive_l3_statement_from_claim_bytes(
        &root_vk_blake3,
        &alt_prefix,
        &policy,
        claim_bytes
      )
      .unwrap(),
      derived_terminal
    );
    let mut alt_wrap_prefix = policy.clone();
    alt_wrap_prefix.claim_prefix[1] = 7;
    assert_ne!(
      derive_l3_statement_from_claim_bytes(
        &root_vk_blake3,
        &RELEASE_05_PREFIX,
        &alt_wrap_prefix,
        claim_bytes
      )
      .unwrap(),
      derived_terminal
    );
    assert_ne!(
      derive_l3_statement_from_claim_bytes(
        &root_vk_blake3,
        &RELEASE_05_PREFIX,
        &policy,
        b"different-claim"
      )
      .unwrap(),
      derived_terminal
    );
  }

  #[test]
  fn deterministic_solidity_parity_vector() {
    // Fixed test vector mirrored in contracts/plonk/test/IxL3PlonkVerifier.t.sol
    // so Rust and pure-Solidity BLAKE3 statement derivation stay byte-identical.
    let root_vk_blake3 = parse_hex_32(
      "d3813ae554af0aa6a24c5c72c796e17403756aa1f9cabbb08519ed4d767c9f13",
      "root_vk",
    )
    .unwrap();
    let wrap_key_blake3 =
      "1bc0cd05e3d1ad8d0102030405060708090a0b0c0d0e0f101112131415161718";
    let policy = WrapPolicy {
      artifact_blake3:
        "9db8e6585bfc730ba7859e0c387f26daebdc1ae3625eebed76d6f4da7364d548"
          .to_owned(),
      key_blake3: wrap_key_blake3.to_owned(),
      layout_blake3:
        "81b62471a48b5ec8000000000000000000000000000000000000000000000001"
          .to_owned(),
      claim_prefix: [1, 0],
    };
    let claim_digest = parse_hex_32(
      "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
      "claim_digest",
    )
    .unwrap();
    let root_claims =
      derive_root_claims_bytes(&RELEASE_05_PREFIX, &claim_digest).unwrap();
    let root_claims_digest = *blake3::hash(&root_claims).as_bytes();
    let s_root = *blake3::hash(
      &Statement {
        key_digest: root_vk_blake3,
        claims_digest: root_claims_digest,
      }
      .preimage(),
    )
    .as_bytes();
    let s_term = derive_l3_statement_from_claim_digest(
      &root_vk_blake3,
      &RELEASE_05_PREFIX,
      &policy,
      &claim_digest,
    )
    .unwrap();
    let [stmt_low, stmt_high] = derive_l3_public_limbs(&s_term);

    // Pin the exact hex digests and u128 limbs (cross-checked identically in Foundry).
    assert_eq!(
      encode_hex(&root_claims_digest),
      "fbb5f303d20295349bc0ef398479dfaf2ff87ff7dd12208dcb8e2ef2752cc88f"
    );
    let _ = s_root;
    assert_eq!(
      encode_hex(&s_term),
      "4ff9237e250652a41232734d32290ff46ccc00f54cccafeb52cf50c6f985da51"
    );
    assert_eq!(stmt_low, 324410350988568979522366464252184885583u128);
    assert_eq!(stmt_high, 108802105723404254921887945212305656940u128);
  }

  #[test]
  fn envelope_roundtrip_and_fail_closed_decoding() {
    let env = L3ProofEnvelope {
      curve: Curve::Bn254,
      terminal_vk_sha256: [0x5Au8; 32],
      proof: vec![1, 2, 3, 4],
    };
    let encoded = env.encode().unwrap();
    assert!(is_l3_proof_bytes(&encoded));
    assert_eq!(&encoded[..8], L3_BN254_PROOF_TAG);
    assert_eq!(L3ProofEnvelope::decode(&encoded).unwrap(), env);

    let bls_env = L3ProofEnvelope {
      curve: Curve::Bls12381,
      terminal_vk_sha256: [0xA5u8; 32],
      proof: vec![9, 8, 7],
    };
    let bls_encoded = bls_env.encode().unwrap();
    assert_eq!(&bls_encoded[..8], L3_BLS12_381_PROOF_TAG);
    assert_eq!(L3ProofEnvelope::decode(&bls_encoded).unwrap(), bls_env);

    // Truncated header, empty proof, unknown IXL3 version, wrong magic, oversized.
    assert!(L3ProofEnvelope::decode(&encoded[..39]).is_err());
    assert!(L3ProofEnvelope::decode(&encoded[..40]).is_err());
    let mut bad_ver = encoded.clone();
    bad_ver[6] = b'9';
    assert!(is_l3_proof_bytes(&bad_ver));
    assert!(L3ProofEnvelope::decode(&bad_ver).is_err());
    let mut bad_magic = encoded.clone();
    bad_magic[0] = b'X';
    assert!(L3ProofEnvelope::decode(&bad_magic).is_err());
    let mut oversized = encoded[..40].to_vec();
    oversized.resize(40 + MAX_L3_PROOF_BYTES + 1, 1);
    assert!(L3ProofEnvelope::decode(&oversized).is_err());
  }

  #[test]
  fn pins_and_bundle_enforce_trust_policy_and_ceremony_anchors() {
    let vk = vec![0x77u8; 64];
    let vk_sha256: [u8; 32] = Sha256::digest(&vk).into();
    let ignition_anchors =
      ceremony_anchors(SetupClass::Ignition, Curve::Bn254).unwrap();
    assert_eq!(ignition_anchors.len(), Bn254Curve::PLONK_ANCHOR_BYTES);
    let filecoin_anchors =
      ceremony_anchors(SetupClass::Filecoin, Curve::Bls12381).unwrap();
    assert_eq!(filecoin_anchors.len(), Bls12381Curve::PLONK_ANCHOR_BYTES);

    let pins = L3VerifierPins {
      curve: Curve::Bn254,
      setup: SetupClass::Ignition,
      root_vk_blake3: [0x11; 32],
      root_statement_prefix: RELEASE_05_PREFIX,
      wrap_policy: sample_wrap_policy(0x22),
      terminal_vk_sha256: vk_sha256,
      terminal_vk: vk.clone(),
      anchors: ignition_anchors.clone(),
    };
    pins.validate(false).unwrap();

    // Bundle round-trip under exact BLAKE3 pin.
    let bundle_bytes = serde_json::to_vec(&pins.to_bundle(None)).unwrap();
    let bundle_pin = *blake3::hash(&bundle_bytes).as_bytes();
    let loaded =
      L3VerifierBundle::from_pinned_bytes(&bundle_bytes, &bundle_pin, None)
        .unwrap();
    assert_eq!(loaded, pins);

    // Wrong bundle BLAKE3 pin must fail closed.
    let mut wrong_pin = bundle_pin;
    wrong_pin[0] ^= 1;
    assert!(
      L3VerifierBundle::from_pinned_bytes(&bundle_bytes, &wrong_pin, None)
        .is_err()
    );

    // Spoofed Ignition anchors must be refused.
    let mut bad_anchors = pins.clone();
    bad_anchors.anchors[0] ^= 1;
    assert!(bad_anchors.validate(true).is_err());

    // Development setup refused by default, accepted only with explicit opt-in.
    let dev_pins = L3VerifierPins {
      setup: SetupClass::Development,
      anchors: vec![0x99; Bn254Curve::PLONK_ANCHOR_BYTES],
      ..pins.clone()
    };
    assert!(dev_pins.validate(false).is_err());
    assert!(dev_pins.validate(true).is_ok());

    // Non-canonical Goldilocks prefix word rejected.
    let mut bad_prefix = pins.clone();
    bad_prefix.root_statement_prefix[0] = Val::ORDER_U64;
    assert!(bad_prefix.validate(true).is_err());

    // VK digest mismatch rejected.
    let mut bad_vk = pins.clone();
    bad_vk.terminal_vk[0] ^= 1;
    assert!(bad_vk.validate(true).is_err());

    // Envelope targeting wrong curve or wrong VK digest rejected before PLONK.
    let wrong_vk_env = L3ProofEnvelope {
      curve: Curve::Bn254,
      terminal_vk_sha256: [0xEE; 32],
      proof: vec![1, 2, 3],
    }
    .encode()
    .unwrap();
    assert!(verify_l3_proof(b"claim", &wrong_vk_env, &pins).is_err());

    let wrong_curve_env = L3ProofEnvelope {
      curve: Curve::Bls12381,
      terminal_vk_sha256: vk_sha256,
      proof: vec![1, 2, 3],
    }
    .encode()
    .unwrap();
    assert!(verify_l3_proof(b"claim", &wrong_curve_env, &pins).is_err());
  }

  fn check_native_plonk_l3_controls<C: AiurCurve>(
    srs: &Srs<C>,
    setup_class: SetupClass,
  ) {
    let fixture = fx::NativeL3Fixture::<C>::new(srs);
    let root_vk = parse_hex_32(fx::ROOT_VK_HEX, "root_vk").unwrap();
    let rogue_root_vk =
      parse_hex_32(fx::ROGUE_ROOT_KEY_HEX, "rogue_root_vk").unwrap();
    let wrap_policy = WrapPolicy {
      artifact_blake3: encode_hex(&[0x11; 32]),
      key_blake3: fx::WRAP_KEY_HEX.to_owned(),
      layout_blake3: encode_hex(&[0x33; 32]),
      claim_prefix: [1, 0],
    };
    let rogue_wrap_policy = WrapPolicy {
      key_blake3: fx::ROGUE_WRAP_KEY_HEX.to_owned(),
      ..wrap_policy.clone()
    };

    let pins = L3VerifierPins {
      curve: C::CURVE,
      setup: setup_class,
      root_vk_blake3: root_vk,
      root_statement_prefix: RELEASE_05_PREFIX,
      wrap_policy: wrap_policy.clone(),
      terminal_vk_sha256: fixture.vk_sha256,
      terminal_vk: fixture.vk_bytes.clone(),
      anchors: fixture.anchors.clone(),
    };

    let honest_stmt = pins.derive_statement(fx::CLAIM_BYTES).unwrap();
    let honest_args = derive_l3_public_inputs_for::<C>(&honest_stmt);
    let honest_proof =
      fixture.prove([honest_args[0].0, honest_args[1].0], [1u8; 32]);
    let honest_env = L3ProofEnvelope {
      curve: C::CURVE,
      terminal_vk_sha256: fixture.vk_sha256,
      proof: honest_proof,
    }
    .encode()
    .unwrap();

    // 1. Setup policy: development refused by default; ceremony accepted directly.
    if setup_class == SetupClass::Development {
      assert!(verify_l3_proof(fx::CLAIM_BYTES, &honest_env, &pins).is_err());
    } else {
      assert_eq!(
        verify_l3_proof(fx::CLAIM_BYTES, &honest_env, &pins).unwrap(),
        setup_class
      );
    }

    // 2. Positive control: honest L3 proof verifies.
    assert_eq!(
      verify_l3_proof_with_options(fx::CLAIM_BYTES, &honest_env, &pins, true)
        .unwrap(),
      setup_class
    );

    // 3. Wrong claim_bytes is rejected.
    assert!(
      verify_l3_proof_with_options(b"wrong-claim", &honest_env, &pins, true)
        .is_err()
    );

    // 4. Critical negative control A: valid native PLONK proof for a foreign
    // wrapper STARK key K* under the SAME terminal PLONK verifying key.
    let rogue_wrap_stmt = derive_l3_statement_from_claim_bytes(
      &root_vk,
      &RELEASE_05_PREFIX,
      &rogue_wrap_policy,
      fx::CLAIM_BYTES,
    )
    .unwrap();
    let rogue_wrap_args = derive_l3_public_inputs_for::<C>(&rogue_wrap_stmt);
    let rogue_wrap_proof =
      fixture.prove([rogue_wrap_args[0].0, rogue_wrap_args[1].0], [2u8; 32]);
    // Sanity check: raw native::verify_native_bytes ACCEPTS this proof on S* under the SAME VK!
    native::verify_native_bytes::<C>(
      &fixture.vk,
      &fixture.vk_sha256,
      &rogue_wrap_proof,
      &[rogue_wrap_args[0].0, rogue_wrap_args[1].0],
    )
    .unwrap();
    let rogue_wrap_env = L3ProofEnvelope {
      curve: C::CURVE,
      terminal_vk_sha256: fixture.vk_sha256,
      proof: rogue_wrap_proof,
    }
    .encode()
    .unwrap();
    assert!(
      verify_l3_proof_with_options(
        fx::CLAIM_BYTES,
        &rogue_wrap_env,
        &pins,
        true
      )
      .is_err(),
      "valid L3 proof for foreign wrapper STARK key K* must be rejected"
    );

    // 5. Critical negative control B: valid native PLONK proof for a foreign
    // root STARK key K_root* under the SAME terminal PLONK verifying key.
    let rogue_root_stmt = derive_l3_statement_from_claim_bytes(
      &rogue_root_vk,
      &RELEASE_05_PREFIX,
      &wrap_policy,
      fx::CLAIM_BYTES,
    )
    .unwrap();
    let rogue_root_args = derive_l3_public_inputs_for::<C>(&rogue_root_stmt);
    let rogue_root_proof =
      fixture.prove([rogue_root_args[0].0, rogue_root_args[1].0], [3u8; 32]);
    native::verify_native_bytes::<C>(
      &fixture.vk,
      &fixture.vk_sha256,
      &rogue_root_proof,
      &[rogue_root_args[0].0, rogue_root_args[1].0],
    )
    .unwrap();
    let rogue_root_env = L3ProofEnvelope {
      curve: C::CURVE,
      terminal_vk_sha256: fixture.vk_sha256,
      proof: rogue_root_proof,
    }
    .encode()
    .unwrap();
    assert!(
      verify_l3_proof_with_options(
        fx::CLAIM_BYTES,
        &rogue_root_env,
        &pins,
        true
      )
      .is_err(),
      "valid L3 proof for foreign root STARK key K_root* must be rejected"
    );

    // 6. Anchor mismatch between pinned anchors and embedded VK anchors fails closed.
    if setup_class == SetupClass::Development {
      let mut spoofed_anchor_pins = pins.clone();
      spoofed_anchor_pins.anchors[0] ^= 1;
      assert!(
        verify_l3_proof_with_options(
          fx::CLAIM_BYTES,
          &honest_env,
          &spoofed_anchor_pins,
          true
        )
        .is_err()
      );
    }

    // 7. Pinned JSON bundle round-trip + tampered proof byte rejection.
    let bundle_bytes = serde_json::to_vec(&pins.to_bundle(None)).unwrap();
    let bundle_pin = *blake3::hash(&bundle_bytes).as_bytes();
    let loaded =
      L3VerifierBundle::from_pinned_bytes(&bundle_bytes, &bundle_pin, None)
        .unwrap();
    assert_eq!(
      verify_l3_proof_with_options(fx::CLAIM_BYTES, &honest_env, &loaded, true)
        .unwrap(),
      setup_class
    );
    let mut tampered = honest_env.clone();
    *tampered.last_mut().unwrap() ^= 1;
    assert!(
      verify_l3_proof_with_options(fx::CLAIM_BYTES, &tampered, &loaded, true)
        .is_err()
    );
  }

  /// Pure-Rust native BN254 PLONK L3 verification tests: positive control,
  /// default dev-key refusal, wrong claim rejection, foreign wrapper STARK key
  /// K* negative control, foreign root STARK key K_root* negative control,
  /// anchor binding, and pinned JSON bundle round-trip.
  #[test]
  fn real_native_plonk_accepts_honest_l3_and_rejects_foreign_stark_key_bn254() {
    let srs = Srs::<Bn254Curve>::unsafe_dev_setup(16, b"l3-native-bn254-test");
    check_native_plonk_l3_controls::<Bn254Curve>(&srs, SetupClass::Development);
  }

  /// Pure-Rust native BLS12-381 PLONK L3 verification tests using the real
  /// pinned Filecoin ceremony SRS fixture (`SetupClass::Filecoin`, accepted
  /// without `--dev-srs`) plus foreign STARK key negative controls.
  #[test]
  fn real_native_plonk_accepts_honest_l3_and_rejects_foreign_stark_key_bls12_381()
   {
    let fixture_dir =
      Path::new(env!("CARGO_MANIFEST_DIR")).join(FILECOIN_PREFIX_2P8_FIXTURE);
    let srs = load_filecoin_cache(
      &fixture_dir,
      FILECOIN_PREFIX_2P8_MANIFEST_BLAKE3,
      16,
    )
    .unwrap();
    check_native_plonk_l3_controls::<Bls12381Curve>(&srs, SetupClass::Filecoin);
  }
}
