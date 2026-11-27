//! Explicitly pinned, portable verifiers for locally generated final keys.
//!
//! Legacy Go/gnark final verification has been retired; this module validates
//! bundle pins, formats, tags, and key hashes before returning a crisp pure-Rust
//! retirement error pointing to `aiur_backend::plonk::native` or
//! `aiur_backend::groth16`.

use super::final_proof::{decode_hex, digest};
use super::{FinalSystem, Result, SetupClass};
use crate::kzg::curve::{Bls12381, Bn254, Curve, KzgCurve};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

const FORMAT: &str = "ix-development-verifier-v1";
const MAX_BYTES: usize = 4 << 20;

fn default_bn254() -> String {
  Bn254::NAME.to_owned()
}

/// The caller authorizes this entire object by its BLAKE3 digest. A proof's
/// embedded key identifier is never sufficient to authorize another circuit.
#[derive(Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Verifier {
  format: String,
  #[serde(default = "default_bn254")]
  curve: String,
  system: FinalSystem,
  inner_setup: String,
  inner_vk_blake3: String,
  schema_sha256: String,
  statement_prefix: [u64; 10],
  verifying_key_sha256: String,
  verifying_key: String,
  plonk_srs_anchors: Option<String>,
}

impl Verifier {
  fn validate(&self) -> Result<Curve> {
    let curve = Curve::parse(&self.curve)?;
    if self.format != FORMAT
      || !matches!(
        self.inner_setup.as_str(),
        "ignition" | "filecoin" | "development"
      )
      || self.system == FinalSystem::None
      || self.verifying_key.len() > 2 << 20
    {
      return Err("invalid development verifier bundle".into());
    }
    digest(&self.inner_vk_blake3)?;
    digest(&self.schema_sha256)?;
    let key = decode_hex(&self.verifying_key)?;
    if key.is_empty()
      || Sha256::digest(&key).as_slice() != digest(&self.verifying_key_sha256)?
    {
      return Err("development verifying key differs from its pin".into());
    }
    let expected_anchor_bytes = match curve {
      Curve::Bn254 => Bn254::PLONK_ANCHOR_BYTES,
      Curve::Bls12381 => Bls12381::PLONK_ANCHOR_BYTES,
    };
    match (&self.system, &self.plonk_srs_anchors) {
      (FinalSystem::Plonk, Some(anchors))
        if decode_hex(anchors)?.len() == expected_anchor_bytes => {},
      (FinalSystem::Groth16, None) => {},
      _ => return Err("development verifier setup anchors differ".into()),
    }
    Ok(curve)
  }
}

/// Verify a final proof under an independently pinned development verifier.
/// The pin must be supplied by the caller, not read from the proof or bundle.
pub fn verify_with_development_verifier(
  proof: &[u8],
  _claim: &[u8],
  bundle: &[u8],
  trusted_digest: &[u8; 32],
  allow_development: bool,
) -> Result<SetupClass> {
  if !allow_development {
    return Err("development verifier requires --dev-srs".into());
  }
  if bundle.len() > MAX_BYTES
    || blake3::hash(bundle).as_bytes() != trusted_digest
  {
    return Err(
      "development verifier bundle differs from its independent pin".into(),
    );
  }
  let verifier: Verifier = serde_json::from_slice(bundle)?;
  let curve = verifier.validate()?;
  if proof.len() > (1 << 20) + 40 {
    return Err("development proof exceeds its size limit".into());
  }
  let tag = match (curve, verifier.system) {
    (Curve::Bn254, FinalSystem::Plonk) => super::plonk::PROOF_TAG,
    (Curve::Bls12381, FinalSystem::Plonk) => super::plonk::BLS12_381_PROOF_TAG,
    (Curve::Bn254, FinalSystem::Groth16) => super::groth16::PROOF_TAG,
    (Curve::Bls12381, FinalSystem::Groth16) => {
      super::groth16::BLS12_381_PROOF_TAG
    },
    (_, FinalSystem::None) => {
      return Err("development verifier has no final proof system".into());
    },
  };
  let packet = proof
    .strip_prefix(tag.as_slice())
    .ok_or("proof system differs from development verifier")?;
  let key_hash = digest(&verifier.verifying_key_sha256)?;
  if packet.get(..32) != Some(key_hash.as_slice()) {
    return Err("proof key differs from development verifier".into());
  }
  match verifier.system {
    FinalSystem::Plonk => Err(super::plonk::retired_error()),
    FinalSystem::Groth16 => Err(super::groth16::retired_error()),
    FinalSystem::None => {
      Err("development verifier has no final proof system".into())
    },
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn development_permission_and_pin_precede_decoding() {
    let bundle = b"not json";
    let pin = *blake3::hash(bundle).as_bytes();
    let error = verify_with_development_verifier(b"", b"", bundle, &pin, false)
      .unwrap_err();
    assert!(error.to_string().contains("--dev-srs"));
    let error =
      verify_with_development_verifier(b"", b"", bundle, &[0; 32], true)
        .unwrap_err();
    assert!(error.to_string().contains("independent pin"));
  }

  #[test]
  fn valid_bundle_reports_retirement_after_pin_and_key_checks() -> Result<()> {
    let key = b"sample-vk";
    let key_hash: [u8; 32] = Sha256::digest(key).into();
    let hex_bytes =
      |bs: &[u8]| -> String { bs.iter().map(|b| format!("{b:02x}")).collect() };
    let verifier = Verifier {
      format: FORMAT.into(),
      curve: Bn254::NAME.into(),
      system: FinalSystem::Groth16,
      inner_setup: "development".into(),
      inner_vk_blake3: "00".repeat(32),
      schema_sha256: "11".repeat(32),
      statement_prefix: [0; 10],
      verifying_key_sha256: hex_bytes(&key_hash),
      verifying_key: hex_bytes(key),
      plonk_srs_anchors: None,
    };
    let bytes = serde_json::to_vec(&verifier)?;
    let pin = *blake3::hash(&bytes).as_bytes();
    let mut envelope = super::super::groth16::PROOF_TAG.to_vec();
    envelope.extend(key_hash);
    envelope.extend([0u8; 196]);
    let err =
      verify_with_development_verifier(&envelope, b"claim", &bytes, &pin, true)
        .unwrap_err()
        .to_string();
    assert!(
      err.contains("retired") && err.contains("aiur_backend::groth16"),
      "{err}"
    );
    Ok(())
  }
}
