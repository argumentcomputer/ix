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

static VERIFIERS: [BundledVerifier; 2] = [
  BundledVerifier {
    id: "d1c6951a06e9fc4712dcf1cb0e59bc4660719c93bef6dcf0e0b66487e0456081",
    digest: "1d0632635c4e97fbc9cae36cff4c41061e3c1cb2ce216ea231f93af0c90d0d3d",
    statement_prefix: AGGREGATE_PREFIX,
    setup: SetupClass::Filecoin,
    bytes: include_bytes!("../../profiles/aggregate-filecoin-v5.bin"),
    decoded: OnceLock::new(),
  },
  BundledVerifier {
    id: "9f95f0fcfc2163b0b1d95ed4f9e56f557c3a611d5f1c1b8ef6b59485bce8f16b",
    digest: "65c5497e830433133b1ce6b8625d608a78a274a5615e7d7b8187a4a32dc1f7e2",
    statement_prefix: AGGREGATE_PREFIX,
    setup: SetupClass::Development,
    bytes: include_bytes!("../../profiles/init-development-v5.bin"),
    decoded: OnceLock::new(),
  },
];

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
  const DEVELOPMENT_PACKET: &[u8] = include_bytes!(
    "../../tests/fixtures/aggregate-kzg/development-v5-packet.bin"
  );

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

  #[test]
  fn development_profile_still_requires_explicit_opt_in() {
    assert!(
      verify(&envelope(DEVELOPMENT_PACKET), CLAIM, false)
        .unwrap_err()
        .to_string()
        .contains("--dev-srs")
    );
    let verifier = VERIFIERS
      .iter()
      .find(|verifier| verifier.setup == SetupClass::Development)
      .unwrap();
    verifier
      .profile()
      .unwrap()
      .verify(DEVELOPMENT_PACKET, &super::super::init_claim::INIT_PUBLIC_WORDS)
      .unwrap();
    assert_eq!(
      verify(&envelope(DEVELOPMENT_PACKET), CLAIM, true).unwrap(),
      SetupClass::Development
    );
  }
}
