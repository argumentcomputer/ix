//! Verifier profiles authenticated by the application release. A packet
//! names its profile; the profile pins the aggregation program its proofs
//! attest, so the statement for a claim follows without the proving backend.
use super::{
  Result,
  setup::SetupClass,
  statement,
  wrap::{PreparedVerifierProfile, VerifierProfile},
};
use std::sync::OnceLock;

struct BundledVerifier {
  id: &'static str,
  digest: &'static str,
  /// Backend and entrypoint words of the aggregation program whose roots
  /// this profile compresses.
  statement_prefix: [u64; 10],
  setup: SetupClass,
  bytes: &'static [u8],
  decoded: OnceLock<std::result::Result<PreparedVerifierProfile, String>>,
}

const AGGREGATE_PREFIX: [u64; 10] = [
  0, 293, 3008464260, 3936129970, 1088962797, 1141056675, 2347219926,
  1176003176, 683533119, 3085659920,
];

static VERIFIERS: [BundledVerifier; 1] = [BundledVerifier {
  id: "9df1e701e9ae98e5cec80b10489e298f4f625c1047f42dc0a2763a3ee70e647e",
  digest: "25793564ff2d58536ec1055f0d3954cf7bba41cad88459834ea379b5a05ce42d",
  statement_prefix: AGGREGATE_PREFIX,
  setup: SetupClass::Filecoin,
  bytes: include_bytes!("../../profiles/aggregate-filecoin-v5.bin"),
  decoded: OnceLock::new(),
}];

impl BundledVerifier {
  fn profile(&self) -> Result<&PreparedVerifierProfile> {
    self
      .decoded
      .get_or_init(|| {
        if blake3::hash(self.bytes).to_hex().as_str() != self.digest {
          return Err("bundled compression verifier digest differs".into());
        }
        let profile = VerifierProfile::from_bytes(self.bytes)
          .map_err(|error| error.to_string())?;
        profile
          .check_setup_class(self.setup)
          .map_err(|error| error.to_string())?;
        if blake3::Hash::from_bytes(profile.id()).to_hex().as_str() != self.id {
          return Err("bundled compression verifier metadata differs".into());
        }
        profile.prepare().map_err(|error| error.to_string())
      })
      .as_ref()
      .map_err(|error| error.clone().into())
  }
}

fn bundled(id: &[u8; 32]) -> Option<&'static BundledVerifier> {
  let id = blake3::Hash::from_bytes(*id).to_hex();
  VERIFIERS.iter().find(|verifier| verifier.id == id.as_str())
}

/// The statement prefix a bundled profile pins, if `id` names one.
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
    "compressed proof uses a verifier profile not bundled with this application",
  )?;
  if verifier.setup == SetupClass::Development && !allow_development {
    return Err("compressed proof uses the known-trapdoor development setup; pass --dev-srs to accept it (not production-secure)".into());
  }
  let statement = statement::with_claim(&verifier.statement_prefix, claim);
  verifier.profile()?.verify(packet, &statement)?;
  Ok(verifier.setup)
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::pipeline::{self, PROOF_TAG};
  const PACKET: &[u8] =
    include_bytes!("../../tests/fixtures/aggregate-kzg/filecoin-v5-packet.bin");
  const CLAIM: &[u8] =
    include_bytes!("../../tests/fixtures/aggregate-kzg/filecoin-claim.bin");

  fn envelope(packet: &[u8]) -> Vec<u8> {
    [PROOF_TAG.as_slice(), packet].concat()
  }

  fn verify(
    proof: &[u8],
    claim: &[u8],
    development: bool,
  ) -> Result<SetupClass> {
    pipeline::verify(proof, claim, development)
  }

  #[test]
  fn bundled_filecoin_packet_verifies_without_a_registry_or_srs() {
    assert_eq!(
      verify(&envelope(PACKET), CLAIM, false).unwrap(),
      SetupClass::Filecoin
    );
    for verifier in &VERIFIERS {
      verifier.profile().unwrap();
    }
  }

  #[test]
  fn bundled_filecoin_metadata_matches_artifacts() {
    let metadata: serde_json::Value = serde_json::from_str(include_str!(
      "../../profiles/aggregate-filecoin-v5.json"
    ))
    .unwrap();
    let id = PACKET[..32].try_into().unwrap();
    let verifier = bundled(&id).unwrap();
    assert_eq!(metadata["profile_id"], verifier.id);
    assert_eq!(metadata["verifier_blake3"], verifier.digest);
    assert_eq!(
      metadata["packet_blake3"],
      blake3::hash(PACKET).to_hex().as_str()
    );
    assert_eq!(
      metadata["claim"]["blake3"],
      blake3::hash(CLAIM).to_hex().as_str()
    );
    assert_eq!(
      metadata["statement_prefix"],
      serde_json::json!(verifier.statement_prefix)
    );
  }

  #[test]
  fn bundled_filecoin_packet_binds_all_statement_words() {
    let id = PACKET[..32].try_into().unwrap();
    let verifier = bundled(&id).unwrap();
    assert_eq!(verifier.setup, SetupClass::Filecoin);
    let statement = statement::with_claim(&verifier.statement_prefix, CLAIM);
    let profile = verifier.profile().unwrap();
    profile.verify(PACKET, &statement).unwrap();
    for index in 0..statement.len() {
      let mut wrong = statement;
      wrong[index] ^= 1;
      assert!(profile.verify(PACKET, &wrong).is_err());
    }
    for index in [0, 32 + 18 * 8, PACKET.len() - 1] {
      let mut packet = PACKET.to_vec();
      packet[index] ^= 1;
      assert!(profile.verify(&packet, &statement).is_err());
    }
  }

  #[test]
  fn claim_is_supplied_independently_of_the_packet() {
    let mut wrong = CLAIM.to_vec();
    wrong[3] ^= 1;
    assert!(verify(&envelope(PACKET), &wrong, false).is_err());
    let mut wrong_prefix = PACKET.to_vec();
    wrong_prefix[32] ^= 1;
    assert!(verify(&envelope(&wrong_prefix), CLAIM, false).is_err());
  }

  #[test]
  fn changed_profiles_points_and_proof_lengths_are_rejected() {
    for index in [0, 32 + 10 * 8, 32 + 18 * 8, PACKET.len() - 1] {
      let mut packet = PACKET.to_vec();
      packet[index] ^= 1;
      assert!(verify(&envelope(&packet), CLAIM, false).is_err());
      assert!(verify(&envelope(&packet), CLAIM, true).is_err());
    }
    for end in [0, 31, 32, 32 + 18 * 8, PACKET.len() - 1] {
      assert!(verify(&envelope(&PACKET[..end]), CLAIM, false).is_err());
    }
    let mut extra = PACKET.to_vec();
    extra.push(0);
    assert!(verify(&envelope(&extra), CLAIM, false).is_err());
    let mut wrong_version = envelope(PACKET);
    wrong_version[7] ^= 1;
    assert!(verify(&wrong_version, CLAIM, false).is_err());
  }
}
