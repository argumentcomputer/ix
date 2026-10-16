//! Verifying keys authenticated by the application release. Each catalog
//! entry pins the aggregation program its proofs attest, so the statement
//! for a claim follows without the proving backend.
use super::{
  Result,
  setup::SetupClass,
  statement,
  wrap::{PreparedVerifyingKey, VerifyingKey},
};
use std::sync::OnceLock;

struct VerifyingKeyEntry {
  id: &'static str,
  digest: &'static str,
  /// Backend and entrypoint words of the aggregation program whose roots
  /// this key verifies.
  statement_prefix: [u64; 10],
  bytes: &'static [u8],
  decoded: OnceLock<std::result::Result<PreparedVerifyingKey, String>>,
}

const AGGREGATE_PREFIX: [u64; 10] = [
  0, 293, 3008464260, 3936129970, 1088962797, 1141056675, 2347219926,
  1176003176, 683533119, 3085659920,
];

static VERIFYING_KEYS: [VerifyingKeyEntry; 1] = [VerifyingKeyEntry {
  id: "e4cb15b1b9ed7e4cc8a00aa331122e99e29d42f193e4cf0c052717f6defcbb4f",
  digest: "8779b34ad026a9e7075c253f036f50e553348b9d3f5c7baab21ddf487301d7cb",
  statement_prefix: AGGREGATE_PREFIX,
  bytes: include_bytes!("../../verifying-keys/aggregate-filecoin-v5.bin"),
  decoded: OnceLock::new(),
}];

impl VerifyingKeyEntry {
  fn key(&self) -> Result<&PreparedVerifyingKey> {
    self
      .decoded
      .get_or_init(|| {
        if blake3::hash(self.bytes).to_hex().as_str() != self.digest {
          return Err("production verifying key digest differs".into());
        }
        let key = VerifyingKey::from_bytes(self.bytes)
          .map_err(|error| error.to_string())?;
        key
          .check_setup_class(SetupClass::Filecoin)
          .map_err(|error| error.to_string())?;
        if blake3::Hash::from_bytes(key.id()).to_hex().as_str() != self.id {
          return Err("production verifying key metadata differs".into());
        }
        key.prepare().map_err(|error| error.to_string())
      })
      .as_ref()
      .map_err(|error| error.clone().into())
  }
}

fn lookup_key(id: &[u8; 32]) -> Option<&'static VerifyingKeyEntry> {
  let id = blake3::Hash::from_bytes(*id).to_hex();
  VERIFYING_KEYS.iter().find(|verifier| verifier.id == id.as_str())
}

/// The statement prefix the catalog pins for a verifying key, if `id` names one.
pub(super) fn key_statement_prefix(
  id: &[u8; 32],
) -> Option<&'static [u64; 10]> {
  lookup_key(id).map(|verifier| &verifier.statement_prefix)
}

pub(super) fn verify(packet: &[u8], claim: &[u8]) -> Result<SetupClass> {
  let id: [u8; 32] =
    packet.get(..32).ok_or("truncated compressed proof")?.try_into()?;
  let verifier = lookup_key(&id)
    .ok_or("compressed proof uses an unrecognized production verifying key")?;
  let statement = statement::with_claim(&verifier.statement_prefix, claim);
  verifier.key()?.verify(packet, &statement)?;
  Ok(SetupClass::Filecoin)
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
  const DEVELOPMENT_KEY: &[u8] = include_bytes!(
    "../../tests/fixtures/aggregate-kzg/development-v5-verifier.bin"
  );
  const CLAIM: &[u8] =
    include_bytes!("../../tests/fixtures/aggregate-kzg/filecoin-claim.bin");

  fn fixtures() -> [(&'static [u8], SetupClass, &'static str); 2] {
    [
      (
        PACKET,
        SetupClass::Filecoin,
        include_str!("../../verifying-keys/aggregate-filecoin-v5.json"),
      ),
      (
        DEVELOPMENT_PACKET,
        SetupClass::Development,
        include_str!("../../tests/fixtures/aggregate-kzg/development-v5.json"),
      ),
    ]
  }

  fn envelope(packet: &[u8]) -> Vec<u8> {
    [PROOF_TAG.as_slice(), packet].concat()
  }

  fn key_bytes(setup: SetupClass) -> &'static [u8] {
    match setup {
      SetupClass::Filecoin => {
        include_bytes!("../../verifying-keys/aggregate-filecoin-v5.bin")
      },
      SetupClass::Development => DEVELOPMENT_KEY,
    }
  }

  fn expected_statement(claim: &[u8]) -> statement::Statement {
    statement::with_claim(
      pipeline::init_claim::INIT_PUBLIC_WORDS[..10].try_into().unwrap(),
      claim,
    )
  }

  fn verify(
    proof: &[u8],
    claim: &[u8],
    development: bool,
  ) -> Result<SetupClass> {
    if development {
      pipeline::verify_development(
        proof,
        claim,
        &statement::to_claims_bytes(&expected_statement(claim)),
        DEVELOPMENT_KEY,
      )?;
      Ok(SetupClass::Development)
    } else {
      pipeline::verify(proof, claim)
    }
  }

  #[test]
  fn production_and_explicit_development_keys_verify_without_a_registry_or_srs()
  {
    for (packet, setup, _) in fixtures() {
      assert_eq!(
        verify(&envelope(packet), CLAIM, setup == SetupClass::Development)
          .unwrap(),
        setup
      );
    }
  }

  #[test]
  fn development_key_is_not_accepted_by_the_production_catalog() {
    assert!(lookup_key(DEVELOPMENT_PACKET[..32].try_into().unwrap()).is_none());
    assert!(
      verify(&envelope(DEVELOPMENT_PACKET), CLAIM, false)
        .unwrap_err()
        .to_string()
        .contains("unrecognized production verifying key")
    );
    assert_eq!(
      verify(&envelope(DEVELOPMENT_PACKET), CLAIM, true).unwrap(),
      SetupClass::Development
    );
  }

  #[test]
  fn obsolete_key_ids_are_rejected() {
    let old_ids = [
      "4b033424efd56486ed972b04b773349149d9df6159d753e303f11aed89928302",
      "304340325a2fff6bbfbca27e0b58b335cd9f0731b7698ef8e9d9f2f23fe408a1",
    ];
    for ((packet, setup, _), old_id) in fixtures().into_iter().zip(old_ids) {
      let mut packet = packet.to_vec();
      packet[..32]
        .copy_from_slice(blake3::Hash::from_hex(old_id).unwrap().as_bytes());
      assert!(
        verify(&envelope(&packet), CLAIM, setup == SetupClass::Development)
          .is_err()
      );
    }
  }

  #[test]
  fn development_verification_requires_the_matching_development_key() {
    let proof = envelope(DEVELOPMENT_PACKET);
    let expected = statement::to_claims_bytes(&expected_statement(CLAIM));
    for key in [
      b"".as_slice(),
      b"invalid key".as_slice(),
      key_bytes(SetupClass::Filecoin),
    ] {
      assert!(
        pipeline::verify_development(&proof, CLAIM, &expected, key).is_err()
      );
    }
    assert!(
      pipeline::verify_development(
        &envelope(PACKET),
        CLAIM,
        &expected,
        DEVELOPMENT_KEY,
      )
      .is_err()
    );
    let error = pipeline::verify_development(
      &envelope(PACKET),
      CLAIM,
      &expected,
      key_bytes(SetupClass::Filecoin),
    )
    .unwrap_err()
    .to_string();
    assert!(error.contains("setup class differs"), "{error}");
  }

  #[test]
  fn development_statement_is_supplied_independently_of_the_packet_and_key() {
    let proof = envelope(DEVELOPMENT_PACKET);
    for index in 0..statement::WORDS {
      let mut expected = expected_statement(CLAIM);
      expected[index] ^= 1;
      assert!(
        pipeline::verify_development(
          &proof,
          CLAIM,
          &statement::to_claims_bytes(&expected),
          DEVELOPMENT_KEY,
        )
        .is_err()
      );
    }
    let mut wrong_claim = CLAIM.to_vec();
    wrong_claim[0] ^= 1;
    assert!(
      pipeline::verify_development(
        &proof,
        &wrong_claim,
        &statement::to_claims_bytes(&expected_statement(CLAIM)),
        DEVELOPMENT_KEY,
      )
      .is_err()
    );
  }

  #[test]
  fn key_metadata_matches_artifacts() {
    let source = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
      .join("tests/fixtures/init-fri");
    for (packet, setup, json) in fixtures() {
      let metadata: serde_json::Value = serde_json::from_str(json).unwrap();
      let id = packet[..32].try_into().unwrap();
      let key = VerifyingKey::from_bytes(key_bytes(setup)).unwrap();
      key.check_setup_class(setup).unwrap();
      assert_eq!(key.id(), id);
      if setup == SetupClass::Filecoin {
        let verifier = lookup_key(&id).unwrap();
        assert_eq!(metadata["verifying_key_id"], verifier.id);
        assert_eq!(metadata["verifying_key_blake3"], verifier.digest);
        assert_eq!(verifier.statement_prefix, expected_statement(CLAIM)[..10]);
      } else {
        assert!(lookup_key(&id).is_none());
      }
      assert_eq!(metadata["setup"], setup.label());
      assert_eq!(metadata["known_trapdoor"], setup == SetupClass::Development);
      assert_eq!(metadata["verifying_key_version"], 5);
      assert_eq!(
        metadata["verifying_key_id_domain"],
        "init-kzg-recursive-verifying-key/v5"
      );
      assert_eq!(
        metadata["verifying_key_id"],
        blake3::Hash::from_bytes(id).to_hex().as_str()
      );
      assert_eq!(
        metadata["verifying_key_blake3"],
        blake3::hash(key_bytes(setup)).to_hex().as_str()
      );
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
        serde_json::json!(&expected_statement(CLAIM)[..10])
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
  fn both_keys_bind_all_statement_words() {
    for (packet, setup, _) in fixtures() {
      let statement = expected_statement(CLAIM);
      let key =
        VerifyingKey::from_bytes(key_bytes(setup)).unwrap().prepare().unwrap();
      key.verify(packet, &statement).unwrap();
      for index in 0..statement.len() {
        let mut wrong = statement;
        wrong[index] ^= 1;
        assert!(key.verify(packet, &wrong).is_err());
      }
      for index in [0, 32 + 18 * 8, packet.len() - 1] {
        let mut packet = packet.to_vec();
        packet[index] ^= 1;
        assert!(key.verify(&packet, &statement).is_err());
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
  fn changed_key_ids_points_and_proof_lengths_are_rejected() {
    for (packet, setup, _) in fixtures() {
      let development = setup == SetupClass::Development;
      for index in [0, 32 + 10 * 8, 32 + 18 * 8, packet.len() - 1] {
        let mut packet = packet.to_vec();
        packet[index] ^= 1;
        assert!(verify(&envelope(&packet), CLAIM, development).is_err());
      }
      for end in [0, 31, 32, 32 + 18 * 8, packet.len() - 1] {
        assert!(verify(&envelope(&packet[..end]), CLAIM, development).is_err());
      }
      let mut extra = packet.to_vec();
      extra.push(0);
      assert!(verify(&envelope(&extra), CLAIM, development).is_err());
      let mut wrong_version = envelope(packet);
      wrong_version[7] ^= 1;
      assert!(verify(&wrong_version, CLAIM, development).is_err());
    }
  }
}
