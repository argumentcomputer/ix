//! Explicitly pinned, portable verifiers for locally generated final keys.
use super::final_proof::{decode_hex, digest};
use super::{FinalSystem, Result, SetupClass};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

#[cfg(any(feature = "plonk", feature = "groth16"))]
use super::{SetupConfig, final_proof::hex, statement, storage};
#[cfg(any(feature = "plonk", feature = "groth16"))]
use std::{fs, path::Path};

#[cfg(any(feature = "plonk", feature = "groth16"))]
pub(super) const FILE: &str = "development-verifier.json";
const FORMAT: &str = "ix-development-verifier-v1";
const MAX_BYTES: usize = 4 << 20;

/// The caller authorizes this entire object by its BLAKE3 digest. A proof's
/// embedded key identifier is never sufficient to authorize another circuit.
#[derive(Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(super) struct Verifier {
  format: String,
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
  #[cfg(any(feature = "plonk", feature = "groth16"))]
  pub(super) fn new(
    system: FinalSystem,
    inner_vk: &Path,
    schema: &[u8],
    expected: &statement::Statement,
    inner_setup: &SetupConfig,
    key: &[u8],
    anchors: Option<&[u8]>,
  ) -> Result<Self> {
    let value = Self {
      format: FORMAT.into(),
      system,
      inner_setup: inner_setup.class().label().into(),
      inner_vk_blake3: blake3::hash(&fs::read(inner_vk)?).to_hex().to_string(),
      schema_sha256: hex(&Sha256::digest(schema)),
      statement_prefix: expected[..10].try_into()?,
      verifying_key_sha256: hex(&Sha256::digest(key)),
      verifying_key: hex(key),
      plonk_srs_anchors: anchors.map(hex),
    };
    value.validate()?;
    Ok(value)
  }

  fn validate(&self) -> Result<()> {
    if self.format != FORMAT
      || !matches!(self.inner_setup.as_str(), "ignition" | "development")
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
    match (&self.system, &self.plonk_srs_anchors) {
      (FinalSystem::Plonk, Some(anchors))
        if decode_hex(anchors)?.len() == 320 => {},
      (FinalSystem::Groth16, None) => {},
      _ => return Err("development verifier setup anchors differ".into()),
    }
    Ok(())
  }

  #[cfg(any(feature = "plonk", feature = "groth16"))]
  pub(super) fn write(&self, dir: &Path) -> Result<()> {
    self.validate()?;
    let bytes = serde_json::to_vec_pretty(self)?;
    let pin = blake3::hash(&bytes).to_hex().to_string();
    storage::write_atomic(&dir.join(FILE), &bytes)?;
    storage::write_atomic(
      &dir.join("development-verifier.blake3"),
      format!("{pin}\n").as_bytes(),
    )?;
    eprintln!(
      "development verifier: {} (BLAKE3 {pin})",
      dir.join(FILE).display()
    );
    Ok(())
  }

  #[cfg(any(feature = "plonk", feature = "groth16"))]
  pub(super) fn check_saved(&self, dir: &Path) -> Result<()> {
    let bytes = super::final_proof::read_bounded(&dir.join(FILE), MAX_BYTES)?;
    let saved: Self = serde_json::from_slice(&bytes)?;
    saved.validate()?;
    if saved != *self {
      return Err("saved development verifier differs from the prepared circuit and setup".into());
    }
    let pin = fs::read_to_string(dir.join("development-verifier.blake3"))?;
    if digest(pin.trim())? != *blake3::hash(&bytes).as_bytes() {
      return Err("saved development verifier pin differs".into());
    }
    Ok(())
  }
}

/// Verify a final proof under an independently pinned development verifier.
/// The pin must be supplied by the caller, not read from the proof or bundle.
pub fn verify_with_development_verifier(
  proof: &[u8],
  claim: &[u8],
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
  verifier.validate()?;
  if proof.len() > (1 << 20) + 40 {
    return Err("development proof exceeds its size limit".into());
  }
  let tag = match verifier.system {
    FinalSystem::Plonk => super::plonk::PROOF_TAG,
    FinalSystem::Groth16 => super::groth16::PROOF_TAG,
    FinalSystem::None => {
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
  #[cfg(any(feature = "plonk", feature = "groth16"))]
  let key = decode_hex(&verifier.verifying_key)?;
  #[cfg(any(feature = "plonk", feature = "groth16"))]
  let claim_hash = blake3::hash(claim);
  #[cfg(not(any(feature = "plonk", feature = "groth16")))]
  let _ = claim;
  let checked: Result<()> = match verifier.system {
    #[cfg(feature = "plonk")]
    FinalSystem::Plonk => super::gnark::verify(
      &key,
      &key_hash,
      &packet[32..],
      claim_hash.as_bytes(),
      &decode_hex(
        verifier
          .plonk_srs_anchors
          .as_deref()
          .ok_or("missing PLONK setup anchors")?,
      )?,
    ),
    #[cfg(not(feature = "plonk"))]
    FinalSystem::Plonk => {
      Err("this ix was built without PLONK; rebuild with IX_PLONK=1".into())
    },
    #[cfg(feature = "groth16")]
    FinalSystem::Groth16 => super::gnark::verify_groth16(
      &key,
      &key_hash,
      &packet[32..],
      claim_hash.as_bytes(),
    ),
    #[cfg(not(feature = "groth16"))]
    FinalSystem::Groth16 => {
      Err("this ix was built without Groth16; rebuild with IX_GROTH16=1".into())
    },
    FinalSystem::None => {
      Err("development verifier has no final proof system".into())
    },
  };
  checked?;
  Ok(SetupClass::Development)
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

  #[cfg(any(feature = "plonk", feature = "groth16"))]
  fn fixture_bundle(
    system: FinalSystem,
    key: &[u8],
    anchors: Option<String>,
  ) -> Verifier {
    let schema: serde_json::Value = serde_json::from_slice(include_bytes!(
      "../../../../tools/plonk-wrapper/testdata/bn254/vk.json"
    ))
    .unwrap();
    Verifier {
      format: FORMAT.into(),
      system,
      inner_setup: "ignition".into(),
      inner_vk_blake3: "00".repeat(32),
      schema_sha256: hex(&Sha256::digest(include_bytes!(
        "../../../../tools/plonk-wrapper/testdata/bn254/vk.json"
      ))),
      statement_prefix: serde_json::from_value(schema["prefix"].clone())
        .unwrap(),
      verifying_key_sha256: hex(&Sha256::digest(key)),
      verifying_key: hex(key),
      plonk_srs_anchors: anchors,
    }
  }

  #[cfg(any(feature = "plonk", feature = "groth16"))]
  fn check_fixture(verifier: Verifier, tag: &[u8], proof: &[u8]) -> Result<()> {
    let mut envelope = tag.to_vec();
    envelope.extend(digest(&verifier.verifying_key_sha256)?);
    envelope.extend(proof);
    let bytes = serde_json::to_vec(&verifier)?;
    let pin = *blake3::hash(&bytes).as_bytes();
    let claim = include_bytes!("../../tests/fixtures/init-fri/claim.bin");
    assert_eq!(
      verify_with_development_verifier(&envelope, claim, &bytes, &pin, true)?,
      SetupClass::Development
    );
    assert!(
      verify_with_development_verifier(&envelope, claim, &bytes, &pin, false)
        .is_err()
    );
    assert!(
      verify_with_development_verifier(
        &envelope,
        b"another claim",
        &bytes,
        &pin,
        true
      )
      .is_err()
    );
    let mut wrong_key = envelope.clone();
    wrong_key[8] ^= 1;
    assert!(
      verify_with_development_verifier(&wrong_key, claim, &bytes, &pin, true)
        .is_err()
    );
    let mut wrong_system = envelope.clone();
    wrong_system[7] ^= 1;
    assert!(
      verify_with_development_verifier(
        &wrong_system,
        claim,
        &bytes,
        &pin,
        true
      )
      .is_err()
    );
    let mut corrupted = envelope.clone();
    *corrupted.last_mut().unwrap() ^= 1;
    assert!(
      verify_with_development_verifier(&corrupted, claim, &bytes, &pin, true)
        .is_err()
    );
    assert!(super::super::verify(&envelope, claim, true).is_err());
    let mut tampered = verifier;
    tampered.statement_prefix[0] ^= 1;
    assert!(
      verify_with_development_verifier(
        &envelope,
        claim,
        &serde_json::to_vec(&tampered)?,
        &pin,
        true
      )
      .is_err()
    );
    Ok(())
  }

  #[test]
  #[cfg(feature = "groth16")]
  fn pinned_groth16_fixture_checks_claim_and_rejects_default_trust()
  -> Result<()> {
    check_fixture(
      fixture_bundle(
        FinalSystem::Groth16,
        include_bytes!("../../tests/fixtures/groth16/verifying-key.bin"),
        None,
      ),
      super::super::groth16::PROOF_TAG,
      include_bytes!("../../tests/fixtures/groth16/proof.bin"),
    )
  }

  #[test]
  #[cfg(feature = "plonk")]
  fn pinned_plonk_fixture_checks_claim_and_rejects_default_trust() -> Result<()>
  {
    let provenance: serde_json::Value = serde_json::from_slice(
      include_bytes!("../../tests/fixtures/plonk/provenance.json"),
    )?;
    check_fixture(
      fixture_bundle(
        FinalSystem::Plonk,
        include_bytes!("../../tests/fixtures/plonk/verifying-key.bin"),
        Some(provenance["anchors"].as_str().unwrap().to_string()),
      ),
      super::super::plonk::PROOF_TAG,
      include_bytes!("../../tests/fixtures/plonk/proof.bin"),
    )
  }
}
