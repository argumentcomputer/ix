//! The verifying keys this build compresses to and verifies, one per proof
//! system, with the aggregation backend and fixed root layout they were derived
//! for. A proof verifies only under these keys; there is no catalog of alternatives.
//! A caller may instead verify under its own key, authenticated by a digest it
//! trusts independently of the proof.
use super::{
  FixedRoot, Result,
  setup::SetupClass,
  statement,
  wrap::{PreparedVerifyingKey, VerifyingKey},
};
use crate::kzg::{Srs, VerifierParams};

/// Version of the bundled verifying keys and the layout they were derived for.
const VERSION: &str = "0.2";

/// Log2 of the first KZG stage's partition height the keys were derived for.
pub(super) const FIRST_LOG_HEIGHT: usize = 24;

/// Serialized aggregation backend key whose roots the layout normalizes: the
/// formal aggregation program under `aiur::trace::stark::Parameters::DEFAULT`.
const ROOT_VK_BLAKE3: &str =
  "d286b37b8b9167fff7de272b70a577d1a8e5fb7ba66dd68488d3b79467820c02";
/// The root layout (`.ixl`, see `FixedRoot`) and its content address.
const LAYOUT: &[u8] =
  include_bytes!("../../verifying-keys/0.2/root-layout.ixl");
const LAYOUT_BLAKE3: &str =
  "708e3b5d7494d3657e78c104d15a276df89299cc589b4444fa1b4ade80cdd928";

/// Backend and entrypoint words of the aggregation program, the statement
/// prefix every compressed claim of this release carries
/// ([`statement::backend_prefix`] of the IxVM and aggregation keys).
pub(super) const STATEMENT_PREFIX: [u64; 10] = [
  1, 0, 860334012, 1220120966, 1187167253, 3205439471, 3112596009, 4264259287,
  80555980, 4021139237,
];

pub(super) const RECURSIVE_VK: &[u8] =
  include_bytes!("../../verifying-keys/0.2/recursive-vk.bin");
const RECURSIVE_VK_BLAKE3: &str =
  "81ca053b35d43bf4d17447e8c21749ad74d24573abc367da5682b4bb6506c7fd";
/// The identifier a recursive KZG packet begins with.
pub(super) const RECURSIVE_VK_ID: &str =
  "2546e82d4da4c117e5f545223d623f162e9601f7d72dd6132f3b2335bc9d2634";

/// Identity of the first stage's FRI verifier plan for the bundled backend
/// and layout, half of its fixed-cache identity. Independent of the KZG setup.
pub(super) const FIRST_PLAN_ID: &str =
  "82dfa4c4a13a4c5f743e6a662dea693a0adfaa5d6302cead56077d1e63efaad3";
/// Identity of the recursive stage's verifier frontend over the first stage
/// under Ignition, half of its fixed-cache identity.
pub(super) const RECURSIVE_FRONTEND_ID: &str =
  "050bf45b9b729c0839d4b31f72b2115676218d2cab666e350b89569bc121e66b";

#[cfg(any(feature = "plonk", test))]
pub(super) const PLONK_VK: &[u8] =
  include_bytes!("../../verifying-keys/0.2/plonk-verifying-key.bin");
/// SHA-256 of the gnark PLONK verifying key, which a PLONK packet begins with.
#[cfg(any(feature = "plonk", test))]
pub(super) const PLONK_VK_SHA256: &str =
  "78d4ad2af7a510248071d484d8184bdf62d31e3421805b23b725b54c5643f040";

/// SHA-256 of the exported recursive verifier description that both final
/// circuits prove.
pub(super) const FINAL_SCHEMA_SHA256: &str =
  "1964851792e31a40fdfcafb5ec0e5ac7fa76632614828b83946834e64e7383e5";

/// The release Groth16 key comes from a development setup: whoever ran it can
/// forge proofs, so it verifies only when development setups are accepted.
#[cfg(any(feature = "groth16", test))]
pub(super) const GROTH16_VK: &[u8] = include_bytes!(
  "../../verifying-keys/0.2/groth16-development-verifying-key.bin"
);
/// SHA-256 of the gnark Groth16 verifying key, which a Groth16 packet begins with.
pub(super) const GROTH16_VK_SHA256: &str =
  "542e9688b77c6b8fded02f13bc3eaafb692836ab59ff18c8e7cafe65cb34da9a";
pub(super) const GROTH16_CIRCUIT_SHA256: &str =
  "cfc498275ccd65c485037eac2046084be997721e5adba5bf461b0f86651b2753";

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

/// The layout (`.ixl` bytes) for an aggregation backend's serialized key.
/// Circuit order and fixed-table heights are meaningful only under the
/// release's backend.
pub fn release_root_layout(root_vk: &[u8]) -> Result<&'static [u8]> {
  if blake3::hash(root_vk).to_hex().as_str() != ROOT_VK_BLAKE3 {
    return Err(format!(
      "aggregation backend differs from the one verifying keys {VERSION} were derived for"
    )
    .into());
  }
  if blake3::hash(LAYOUT).as_bytes() != &decode(LAYOUT_BLAKE3)? {
    return Err("bundled root layout differs from its pin".into());
  }
  FixedRoot::from_bytes(LAYOUT)?;
  Ok(LAYOUT)
}

/// Check that `words` is a statement of the release's aggregation program:
/// the IxVM and aggregation backends the keys were derived for.
pub(super) fn check_release_prefix(words: &statement::Statement) -> Result<()> {
  if words[..10] != STATEMENT_PREFIX {
    return Err(
      format!(
        "the statement's aggregation backend differs from the one verifying \
         keys {VERSION} were derived for"
      )
      .into(),
    );
  }
  Ok(())
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

/// Verify a recursive KZG packet under a verifying key the caller supplies
/// with an independently trusted digest, against an independently expected
/// statement.
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
    assert_eq!(
      blake3::hash(LAYOUT).as_bytes(),
      &decode(LAYOUT_BLAKE3).unwrap()
    );
    assert_eq!(FixedRoot::from_bytes(LAYOUT).unwrap().to_bytes(), LAYOUT);
    // The prefix names the call channel; its digest words are u32s.
    assert_eq!(STATEMENT_PREFIX[0], 1);
    assert!(STATEMENT_PREFIX[2..].iter().all(|&w| u32::try_from(w).is_ok()));
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
    let mut words = statement::with_claim(&STATEMENT_PREFIX, b"claim");
    check_release_prefix(&words).unwrap();
    words[1] += 1;
    assert!(check_release_prefix(&words).is_err());
  }
}
