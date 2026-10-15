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
    id: "4b033424efd56486ed972b04b773349149d9df6159d753e303f11aed89928302",
    digest: "8779b34ad026a9e7075c253f036f50e553348b9d3f5c7baab21ddf487301d7cb",
    statement_prefix: AGGREGATE_PREFIX,
    setup: SetupClass::Filecoin,
    bytes: include_bytes!("../../profiles/aggregate-filecoin-v5.bin"),
    decoded: OnceLock::new(),
  },
  BundledVerifier {
    id: "304340325a2fff6bbfbca27e0b58b335cd9f0731b7698ef8e9d9f2f23fe408a1",
    digest: "e3e06165a20328dbd48964a0539341dd54b2c3e89accba313a09f4321d2f48b9",
    statement_prefix: AGGREGATE_PREFIX,
    setup: SetupClass::Development,
    bytes: include_bytes!("../../profiles/aggregate-development-v5.bin"),
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
  const DEVELOPMENT_PACKET: &[u8] = include_bytes!(
    "../../tests/fixtures/aggregate-kzg/development-v5-packet.bin"
  );
  const CLAIM: &[u8] =
    include_bytes!("../../tests/fixtures/aggregate-kzg/filecoin-claim.bin");

  fn fixtures() -> [(&'static [u8], SetupClass, &'static str); 2] {
    [
      (
        PACKET,
        SetupClass::Filecoin,
        include_str!("../../profiles/aggregate-filecoin-v5.json"),
      ),
      (
        DEVELOPMENT_PACKET,
        SetupClass::Development,
        include_str!("../../profiles/aggregate-development-v5.json"),
      ),
    ]
  }

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
  fn bundled_packets_verify_without_a_registry_or_srs() {
    for (packet, setup, _) in fixtures() {
      assert_eq!(
        verify(&envelope(packet), CLAIM, setup == SetupClass::Development)
          .unwrap(),
        setup
      );
    }
  }

  #[test]
  fn development_profile_requires_explicit_opt_in() {
    assert!(
      verify(&envelope(DEVELOPMENT_PACKET), CLAIM, false)
        .unwrap_err()
        .to_string()
        .contains("--dev-srs")
    );
    assert_eq!(
      verify(&envelope(DEVELOPMENT_PACKET), CLAIM, true).unwrap(),
      SetupClass::Development
    );
  }

  #[test]
  fn bundled_metadata_matches_artifacts() {
    let source = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
      .join("tests/fixtures/init-fri");
    for (packet, setup, json) in fixtures() {
      let metadata: serde_json::Value = serde_json::from_str(json).unwrap();
      let id = packet[..32].try_into().unwrap();
      let verifier = bundled(&id).unwrap();
      assert_eq!(verifier.setup, setup);
      assert_eq!(metadata["setup"], setup.label());
      assert_eq!(metadata["known_trapdoor"], setup == SetupClass::Development);
      assert_eq!(metadata["profile_id"], verifier.id);
      assert_eq!(metadata["verifier_blake3"], verifier.digest);
      assert_eq!(
        metadata["packet_blake3"],
        blake3::hash(packet).to_hex().as_str()
      );
      assert_eq!(
        metadata["claim"]["blake3"],
        blake3::hash(CLAIM).to_hex().as_str()
      );
      assert_eq!(
        metadata["statement_prefix"],
        serde_json::json!(verifier.statement_prefix)
      );
      for (file, key) in [
        ("outer-vk.bin", "source_fri_verifier_blake3"),
        ("outer-proof.bin", "source_fri_proof_blake3"),
      ] {
        let bytes = std::fs::read(source.join(file)).unwrap();
        assert_eq!(metadata[key], blake3::hash(&bytes).to_hex().as_str());
      }
    }
  }

  #[test]
  fn bundled_packets_bind_all_statement_words() {
    for (packet, _, _) in fixtures() {
      let id = packet[..32].try_into().unwrap();
      let verifier = bundled(&id).unwrap();
      let statement = statement::with_claim(&verifier.statement_prefix, CLAIM);
      let profile = verifier.profile().unwrap();
      profile.verify(packet, &statement).unwrap();
      for index in 0..statement.len() {
        let mut wrong = statement;
        wrong[index] ^= 1;
        assert!(profile.verify(packet, &wrong).is_err());
      }
      for index in [0, 32 + 18 * 8, packet.len() - 1] {
        let mut packet = packet.to_vec();
        packet[index] ^= 1;
        assert!(profile.verify(&packet, &statement).is_err());
      }
    }
  }

  #[test]
  fn claim_is_supplied_independently_of_the_packet() {
    for (packet, setup, _) in fixtures() {
      let development = setup == SetupClass::Development;
      let mut wrong = CLAIM.to_vec();
      wrong[3] ^= 1;
      let error =
        verify(&envelope(packet), &wrong, development).unwrap_err().to_string();
      assert!(error.contains("packet statement differs"), "{error}");
      let mut wrong_prefix = packet.to_vec();
      wrong_prefix[32] ^= 1;
      assert!(verify(&envelope(&wrong_prefix), CLAIM, development).is_err());
    }
  }

  #[test]
  fn changed_profiles_points_and_proof_lengths_are_rejected() {
    for (packet, _, _) in fixtures() {
      for index in [0, 32 + 10 * 8, 32 + 18 * 8, packet.len() - 1] {
        let mut packet = packet.to_vec();
        packet[index] ^= 1;
        assert!(verify(&envelope(&packet), CLAIM, true).is_err());
      }
      for end in [0, 31, 32, 32 + 18 * 8, packet.len() - 1] {
        assert!(verify(&envelope(&packet[..end]), CLAIM, true).is_err());
      }
      let mut extra = packet.to_vec();
      extra.push(0);
      assert!(verify(&envelope(&extra), CLAIM, true).is_err());
      let mut wrong_version = envelope(packet);
      wrong_version[7] ^= 1;
      assert!(verify(&wrong_version, CLAIM, true).is_err());
    }
  }
}
