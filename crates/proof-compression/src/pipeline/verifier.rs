//! Verifier verifying keys authenticated by a release bundle or an independent
//! digest. Bundles pin an aggregation program; local verifying keys require its
//! independently supplied statement as well as the certificate claim.
use super::{
  Result,
  setup::SetupClass,
  statement,
  wrap::{PreparedVerifyingKey, VerifyingKey},
};
use std::sync::OnceLock;

struct BundledVerifier {
  id: &'static str,
  digest: &'static str,
  /// Backend and entrypoint words of the aggregation program whose roots
  /// this verifying key compresses.
  statement_prefix: [u64; 10],
  setup: SetupClass,
  ignition_admission: Option<BundledIgnitionAdmission>,
  bytes: &'static [u8],
  decoded: OnceLock<std::result::Result<PreparedVerifyingKey, String>>,
}

struct BundledIgnitionAdmission {
  bytes: &'static [u8],
  digest: [u8; 32],
}

impl BundledIgnitionAdmission {
  fn decode(&self) -> Result<crate::kzg::srs::ignition::IgnitionAdmission> {
    Ok(crate::kzg::srs::ignition::IgnitionAdmission::from_bytes(
      self.bytes,
      self.digest,
    )?)
  }
}

static VERIFIERS: [BundledVerifier; 0] = [];

impl BundledVerifier {
  fn check_release_class(&self) -> Result<()> {
    if self.setup != SetupClass::Ignition {
      return Err(
        "BN254 release verifier catalog admits only Ignition setups".into(),
      );
    }
    Ok(())
  }

  fn vk(&self) -> Result<&PreparedVerifyingKey> {
    self
      .decoded
      .get_or_init(|| {
        self.check_release_class().map_err(|error| error.to_string())?;
        if blake3::hash(self.bytes).to_hex().as_str() != self.digest {
          return Err("bundled compression verifier digest differs".into());
        }
        let vk = VerifyingKey::from_bytes(self.bytes)
          .map_err(|error| error.to_string())?;
        {
          let admission = self
            .ignition_admission
            .as_ref()
            .ok_or("bundled Ignition verifier has no trusted admission")?
            .decode()
            .map_err(|error| error.to_string())?;
          vk.check_ignition_admission(&admission)
            .map_err(|error| error.to_string())?;
        }
        if blake3::Hash::from_bytes(vk.id()).to_hex().as_str() != self.id {
          return Err("bundled compression verifier metadata differs".into());
        }
        vk.prepare().map_err(|error| error.to_string())
      })
      .as_ref()
      .map_err(|error| error.clone().into())
  }
}

fn bundled(id: &[u8; 32]) -> Option<&'static BundledVerifier> {
  let id = blake3::Hash::from_bytes(*id).to_hex();
  VERIFIERS.iter().find(|verifier| verifier.id == id.as_str())
}

/// The statement prefix a bundled verifying key pins, if `id` names one.
pub(super) fn bundled_prefix(id: &[u8; 32]) -> Option<&'static [u64; 10]> {
  bundled(id).map(|verifier| &verifier.statement_prefix)
}

pub(super) fn verify(
  packet: &[u8],
  claim: &[u8],
  allow_development: bool,
) -> Result<SetupClass> {
  let id: [u8; 32] =
    packet.get(..32).ok_or("truncated compressed proof")?.try_into()?;
  let verifier = bundled(&id).ok_or(
    "compressed proof uses a verifying key not bundled with this application",
  )?;
  verifier.check_release_class()?;
  if verifier.setup == SetupClass::Development && !allow_development {
    return Err("compressed proof uses the known-trapdoor development setup; pass --dev-srs to accept it (not production-secure)".into());
  }
  let statement = statement::with_claim(&verifier.statement_prefix, claim);
  verifier.vk()?.verify(packet, &statement)?;
  Ok(verifier.setup)
}

/// Verify using an independently authenticated verifying key and expected statement.
pub(super) fn verify_with_vk(
  packet: &[u8],
  claim: &[u8],
  expected: &statement::Statement,
  vk: &[u8],
  trusted_digest: &[u8; 32],
  allow_development: bool,
) -> Result<SetupClass> {
  if blake3::hash(vk).as_bytes() != trusted_digest {
    return Err(
      "local verifying key digest differs from the trusted digest".into(),
    );
  }
  statement::bind_claim(claim, expected)?;
  let vk = VerifyingKey::from_bytes(vk)?;
  let setup = SetupClass::of(&vk.verifier_params()?);
  vk.check_setup_class(setup)?;
  if setup == SetupClass::Development && !allow_development {
    return Err("compressed proof uses the known-trapdoor development setup; pass --dev-srs to accept it (not production-secure)".into());
  }
  vk.verify(packet, expected)?;
  Ok(setup)
}

/// Verify with an independently authenticated verifying key and ceremony admission.
/// The admission contains the verifier anchors; no proving cache is required.
pub(super) fn verify_with_ignition_admission(
  packet: &[u8],
  claim: &[u8],
  expected: &statement::Statement,
  vk: &[u8],
  trusted_digest: &[u8; 32],
  admission: &crate::kzg::srs::ignition::IgnitionAdmission,
) -> Result<SetupClass> {
  if blake3::hash(vk).as_bytes() != trusted_digest {
    return Err(
      "local verifying key digest differs from the trusted digest".into(),
    );
  }
  statement::bind_claim(claim, expected)?;
  let vk = VerifyingKey::from_bytes(vk)?;
  vk.check_ignition_admission(admission)?;
  vk.verify(packet, expected)?;
  Ok(SetupClass::Ignition)
}

#[cfg(test)]
mod bn254_tests {
  use super::*;

  #[test]
  fn bn254_release_catalog_rejects_non_ignition_classes() {
    {
      let verifier = BundledVerifier {
        id: "",
        digest: "",
        statement_prefix: [0; 10],
        setup: SetupClass::Development,
        ignition_admission: None,
        bytes: &[],
        decoded: OnceLock::new(),
      };
      assert!(verifier.check_release_class().is_err());
      assert!(
        verifier
          .vk()
          .err()
          .unwrap()
          .to_string()
          .contains("admits only Ignition")
      );
    }
  }

  #[test]
  fn bundled_ignition_admission_requires_its_release_pin() {
    let (admission, _) = crate::kzg::srs::ignition::test_admission(7, 16, 43);
    let bytes: &'static [u8] =
      Box::leak(admission.to_bytes().unwrap().into_boxed_slice());
    let digest = *blake3::hash(bytes).as_bytes();
    let bundled = BundledIgnitionAdmission { bytes, digest };
    assert_eq!(
      bundled.decode().unwrap().public_setup(),
      admission.public_setup()
    );
    let mut wrong_digest = digest;
    wrong_digest[0] ^= 1;
    assert!(
      BundledIgnitionAdmission { bytes, digest: wrong_digest }
        .decode()
        .is_err()
    );
  }

  #[test]
  fn bn254_requires_an_explicit_trusted_vk() {
    assert!(bundled(&[0; 32]).is_none());
    let packet = [0; 32];
    assert!(
      verify(&packet, b"claim", true)
        .unwrap_err()
        .to_string()
        .contains("not bundled")
    );
  }
}
