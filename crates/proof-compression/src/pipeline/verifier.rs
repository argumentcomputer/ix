//! Verifier profiles authenticated by a release bundle or an independent
//! digest. Bundles pin an aggregation program; local profiles require its
//! independently supplied statement as well as the certificate claim.
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

#[cfg(not(feature = "bn254"))]
const AGGREGATE_PREFIX: [u64; 10] = [
  0, 293, 3008464260, 3936129970, 1088962797, 1141056675, 2347219926,
  1176003176, 683533119, 3085659920,
];

#[cfg(not(feature = "bn254"))]
static VERIFIERS: [BundledVerifier; 4] = [
  BundledVerifier {
    id: "4224c47197ed387320dfb9b8bbf2369fa326f72c54e1cbc65907f5e6e8541ca0",
    digest: "12ce28356f86ba34afb11b8e3b2c142f47ab9259e9c3f5751069bd1c41609084",
    statement_prefix: AGGREGATE_PREFIX,
    setup: SetupClass::Filecoin,
    bytes: include_bytes!("../../profiles/aggregate-filecoin-v6.bin"),
    decoded: OnceLock::new(),
  },
  BundledVerifier {
    id: "b0db3d47f5f9e08b3710499adaba92ad6c5bd160393d45aef1a505c5909cd580",
    digest: "116c668b17db0a1bd95ea8cce9d080af14b16031db128c47a3dcd46443147678",
    statement_prefix: AGGREGATE_PREFIX,
    setup: SetupClass::Development,
    bytes: include_bytes!("../../profiles/aggregate-development-v6.bin"),
    decoded: OnceLock::new(),
  },
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

#[cfg(feature = "bn254")]
static VERIFIERS: [BundledVerifier; 0] = [];

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

/// Verify using an independently authenticated profile and expected statement.
pub(super) fn verify_with_profile(
  packet: &[u8],
  claim: &[u8],
  expected: &statement::Statement,
  profile: &[u8],
  trusted_digest: &[u8; 32],
  allow_development: bool,
) -> Result<SetupClass> {
  if blake3::hash(profile).as_bytes() != trusted_digest {
    return Err(
      "local verifier profile digest differs from the trusted digest".into(),
    );
  }
  statement::bind_claim(claim, expected)?;
  let profile = VerifierProfile::from_bytes(profile)?;
  let setup = SetupClass::of(&profile.verifier_params()?);
  profile.check_setup_class(setup)?;
  if setup == SetupClass::Development && !allow_development {
    return Err("compressed proof uses the known-trapdoor development setup; pass --dev-srs to accept it (not production-secure)".into());
  }
  profile.verify(packet, expected)?;
  Ok(setup)
}

#[cfg(all(test, not(feature = "bn254")))]
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
  fn blake3_profiles_derive_from_authenticated_circuit_metadata() {
    for (source, target) in [(2, 0), (3, 1)] {
      let (bytes, id) =
        VerifierProfile::reencode_blake3(VERIFIERS[source].bytes).unwrap();
      assert_eq!(bytes, VERIFIERS[target].bytes);
      assert_eq!(
        blake3::Hash::from_bytes(id).to_hex().as_str(),
        VERIFIERS[target].id
      );
      VERIFIERS[target].profile().unwrap();
    }
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

#[cfg(all(test, feature = "bn254"))]
mod bn254_tests {
  use super::*;

  #[test]
  fn bn254_requires_an_explicit_trusted_profile() {
    assert!(bundled(&[0; 32]).is_none());
    let bls_packet = include_bytes!(
      "../../tests/fixtures/aggregate-kzg/development-v5-packet.bin"
    );
    assert!(verify(bls_packet, b"claim", true).is_err());
    assert!(
      VerifierProfile::from_bytes(include_bytes!(
        "../../profiles/aggregate-development-v6.bin"
      ))
      .is_err()
    );
  }
}
