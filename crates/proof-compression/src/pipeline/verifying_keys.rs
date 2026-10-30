//! The verifying keys this build compresses to and verifies, one per proof
//! system, with the aggregation backend and fixed root layout they were derived
//! for. A proof verifies only under these keys; there is no catalog of alternatives.
use super::{
  FixedRoot, Result,
  setup::SetupClass,
  statement,
  wrap::{PreparedVerifyingKey, VerifyingKey},
};
use crate::kzg::{Srs, VerifierParams};

/// Version of the bundled verifying keys and the layout they were derived for.
const VERSION: &str = "0.1";

/// Log2 of the first KZG stage's partition height the keys were derived for.
pub(super) const FIRST_LOG_HEIGHT: usize = 24;

/// Serialized aggregation backend key whose roots the layout normalizes.
const ROOT_VK_BLAKE3: &str =
  "f0c635f096bb2b9ff8fbeaf947c406978c11ce3bc447df94e43d6e9fe3cc6fbc";
const LAYOUT: &str = include_str!("../../verifying-keys/0.1/layout.json");

/// Backend and entrypoint words of the aggregation program, the statement
/// prefix every compressed claim of this release carries.
pub(super) const STATEMENT_PREFIX: [u64; 10] = [
  0, 293, 3849420707, 4087085283, 470000540, 2154705852, 3686466056,
  4052325645, 2284798839, 2062413424,
];

pub(super) const RECURSIVE_VK: &[u8] =
  include_bytes!("../../verifying-keys/0.1/recursive-vk.bin");
const RECURSIVE_VK_BLAKE3: &str =
  "b4c58f798380d2fd91594763613874fdaf2d407631cee98fe361a287265d074a";
/// The identifier a recursive KZG packet begins with.
pub(super) const RECURSIVE_VK_ID: &str =
  "376163d7ec5afa644e393d0d1828b3fc46be2f80cc5e4d122c739e9b28129330";

#[cfg(any(feature = "plonk", test))]
pub(super) const PLONK_VK: &[u8] =
  include_bytes!("../../verifying-keys/0.1/plonk-verifying-key.bin");
/// SHA-256 of the gnark PLONK verifying key, which a PLONK packet begins with.
#[cfg(any(feature = "plonk", test))]
pub(super) const PLONK_VK_SHA256: &str =
  "7123a80f9c56b25138ffe8ec47a53c6b0b22b64bf183380d63e5c80a7e3144a9";

/// SHA-256 of the exported recursive verifier description that both final
/// circuits prove.
pub(super) const FINAL_SCHEMA_SHA256: &str =
  "d5d07c29ad8c3c795146fe728f73e30812a344c6b62a8f32888033b1a6aba4bf";

/// The release Groth16 key comes from a development setup: whoever ran it can
/// forge proofs, so it verifies only when development setups are accepted.
#[cfg(any(feature = "groth16", test))]
pub(super) const GROTH16_VK: &[u8] = include_bytes!(
  "../../verifying-keys/0.1/groth16-development-verifying-key.bin"
);
/// SHA-256 of the gnark Groth16 verifying key, which a Groth16 packet begins with.
pub(super) const GROTH16_VK_SHA256: &str =
  "954d1d7ad6418ca64fbf8c8ea9041abacf822f748912e08089833cd27f13ce6d";
pub(super) const GROTH16_CIRCUIT_SHA256: &str =
  "cf226140822f7579846ea188f74081a360da720e02525307d47b57006a774edb";

/// The setup class of the release Groth16 key, if `allow_development` admits it.
pub(super) fn groth16_setup(allow_development: bool) -> Result<SetupClass> {
  if !allow_development {
    return Err("the release Groth16 key uses a development setup; use --dev-final-srs for compression or --dev-srs for verification (not production-secure)".into());
  }
  Ok(SetupClass::Development)
}

/// A pinned digest, decoded strictly.
pub(super) fn decode(hex: &str) -> Result<[u8; 32]> {
  super::final_proof::digest(hex)
}

/// The layout for an aggregation backend's serialized key. Circuit order and
/// fixed-table heights are meaningful only under the release's backend.
pub fn release_root_layout(root_vk: &[u8]) -> Result<&'static str> {
  if blake3::hash(root_vk).to_hex().as_str() != ROOT_VK_BLAKE3 {
    return Err(format!(
      "aggregation backend differs from the one verifying keys {VERSION} were derived for"
    )
    .into());
  }
  FixedRoot::from_json(LAYOUT)?;
  Ok(LAYOUT)
}

/// The release key fixes the Ignition identity, public degree and anchors.
pub(crate) fn ignition_parameters() -> Result<VerifierParams> {
  // Only the parameter section is needed here, not a prepared circuit verifier.
  let (vk, consumed): (VerifyingKey, usize) =
    bincode::serde::decode_from_slice(
      RECURSIVE_VK,
      bincode::config::standard(),
    )?;
  if consumed != RECURSIVE_VK.len() {
    return Err("trailing bundled recursive key data".into());
  }
  vk.verifier_params()
}

pub(super) fn ignition_anchors() -> Result<Srs> {
  let params = ignition_parameters()?;
  Ok(Srs {
    g1: params.g1.to_vec(),
    g2: params.g2,
    tau_g2: params.tau_g2,
    public_setup: params.public_setup,
  })
}

/// The bundled recursive key's prepared verifier.
fn recursive_vk() -> Result<PreparedVerifyingKey> {
  if blake3::hash(RECURSIVE_VK).to_hex().as_str() != RECURSIVE_VK_BLAKE3 {
    return Err("bundled recursive verifying key differs from its pin".into());
  }
  let (vk, prepared) = VerifyingKey::prepared_from_bytes(RECURSIVE_VK)?;
  if vk.id() != decode(RECURSIVE_VK_ID)? {
    return Err("bundled recursive verifying key identifier differs".into());
  }
  vk.check_setup_class(SetupClass::Ignition)?;
  Ok(prepared)
}

/// Verify a recursive KZG packet of `claim` under the release key.
pub(super) fn verify_recursive(
  packet: &[u8],
  claim: &[u8],
) -> Result<SetupClass> {
  let id = packet.get(..32).ok_or("truncated compressed proof")?;
  if id != decode(RECURSIVE_VK_ID)? {
    return Err(format!(
      "compressed proof uses a verifying key other than the version {VERSION} key"
    )
    .into());
  }
  let statement = statement::with_claim(&STATEMENT_PREFIX, claim);
  recursive_vk()?.verify(packet, &statement)?;
  Ok(SetupClass::Ignition)
}

/// Whether a compression of a `root_vk` root under `setup` must produce the
/// bundled keys: the root is this version's backend and the setup is Ignition.
pub(super) fn bundled_for(root_vk: &[u8], setup: &super::SetupConfig) -> bool {
  blake3::hash(root_vk).to_hex().as_str() == ROOT_VK_BLAKE3
    && setup.class() == SetupClass::Ignition
}

/// A recursive key proved for this version's backend under Ignition must be
/// the bundled key.
pub(super) fn check_recursive_key(
  root_vk: &[u8],
  setup: &super::SetupConfig,
  vk: &[u8],
) -> Result<()> {
  if bundled_for(root_vk, setup) && vk != RECURSIVE_VK {
    return Err(
      format!("recursive verifying key differs from version {VERSION}'s")
        .into(),
    );
  }
  Ok(())
}

/// Check a compression's statement belongs to the release when its recursive
/// key is the release key.
pub(super) fn check_statement(
  id: &[u8],
  words: &statement::Statement,
) -> Result<()> {
  if id == decode(RECURSIVE_VK_ID)? && words[..10] != STATEMENT_PREFIX {
    return Err(format!(
      "the version {VERSION} key compresses a different aggregation program than this build's backend"
    )
    .into());
  }
  Ok(())
}

#[cfg(test)]
mod tests {
  use super::*;
  use sha2::{Digest, Sha256};

  #[test]
  fn bundled_release_files_match_their_pins() {
    recursive_vk().unwrap();
    assert_eq!(
      Sha256::digest(PLONK_VK).as_slice(),
      decode(PLONK_VK_SHA256).unwrap()
    );
    assert_eq!(
      Sha256::digest(GROTH16_VK).as_slice(),
      decode(GROTH16_VK_SHA256).unwrap()
    );
    assert!(groth16_setup(false).is_err());
    assert_eq!(groth16_setup(true).unwrap(), SetupClass::Development);
    FixedRoot::from_json(LAYOUT).unwrap();
    statement::from_claims_bytes(&statement::to_claims_bytes(
      &statement::with_claim(&STATEMENT_PREFIX, b""),
    ))
    .unwrap();
  }

  #[test]
  fn other_keys_and_backends_are_rejected() {
    let mut packet = vec![0; 64];
    assert!(verify_recursive(&packet, b"claim").is_err());
    packet[..32].copy_from_slice(&decode(RECURSIVE_VK_ID).unwrap());
    assert!(verify_recursive(&packet, b"claim").is_err());
    assert!(release_root_layout(b"another backend").is_err());
  }
}
