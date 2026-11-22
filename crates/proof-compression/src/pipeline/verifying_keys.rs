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
const VERSION: &str = "0.4";

/// Log2 of the first KZG stage's partition height the keys were derived for.
pub(super) const FIRST_LOG_HEIGHT: usize = 24;

/// Serialized aggregation backend key whose roots the layout normalizes: the
/// formal aggregation program under `aiur::trace::stark::Parameters::DEFAULT`.
const ROOT_VK_BLAKE3: &str =
  "81e744bbeec1f680ae1ad845f19a722d9e17cf07d409e48ea4b22a56f2d6f32d";
/// The root layout (`.ixl`, see `FixedRoot`) and its content address.
const LAYOUT: &[u8] =
  include_bytes!("../../verifying-keys/0.4/root-layout.ixl");
const LAYOUT_BLAKE3: &str =
  "eafc38aa323f4fbdebcbb61c8ba98eb56c0e9e2f4522c6aa91fc7a83dc2a6878";

/// Backend and entrypoint words of the aggregation program, the statement
/// prefix every compressed claim of this release carries
/// ([`statement::backend_prefix`] of the IxVM and aggregation keys).
pub(super) const STATEMENT_PREFIX: [u64; 10] = [
  1, 0, 1907407806, 1976644094, 1433916289, 2735973493, 3333184735, 1597739955,
  2163936245, 1626235737,
];

pub(super) const RECURSIVE_VK: &[u8] =
  include_bytes!("../../verifying-keys/0.4/recursive-vk.bin");
const RECURSIVE_VK_BLAKE3: &str =
  "c57f3938d3dd0f5b1b0f343d74594cb01fec4dd3adc32d17006b7a16be591988";
/// The identifier a recursive KZG packet begins with.
pub(super) const RECURSIVE_VK_ID: &str =
  "01a27eaaf9cc588848739503c9e5f94780558a408789107767b27474881faa2a";

/// Identity of the first stage's FRI verifier plan for the bundled backend
/// and layout, half of its fixed-cache identity. Independent of the KZG setup.
pub(super) const FIRST_PLAN_ID: &str =
  "f62e507cb503411a270b023b8dcabc80dc114e75e62e0f0783c1755ee9032a35";
/// Identity of the recursive stage's verifier frontend over the first stage
/// under Ignition, half of its fixed-cache identity.
pub(super) const RECURSIVE_FRONTEND_ID: &str =
  "332922398311bd0f03f8165a6522f4d800fcd6787db9a4b0ffa66214f9c51c06";

#[cfg(any(feature = "plonk", test))]
pub(super) const PLONK_VK: &[u8] =
  include_bytes!("../../verifying-keys/0.4/plonk-verifying-key.bin");
/// SHA-256 of the gnark PLONK verifying key, which a PLONK packet begins with.
#[cfg(any(feature = "plonk", test))]
pub(super) const PLONK_VK_SHA256: &str =
  "032ff41ec34de4488553485a361d80d23e0dde1e8acbb07457e4625c85aa324b";

/// SHA-256 of the exported recursive verifier description that both final
/// circuits prove.
pub(super) const FINAL_SCHEMA_SHA256: &str =
  "a4ef5493e0b00a4f9bd3d989b7a19812eff6ff31e9e9691c54ae96fc088107de";

/// The release Groth16 key comes from a development setup: whoever ran it can
/// forge proofs, so it verifies only when development setups are accepted.
#[cfg(any(feature = "groth16", test))]
pub(super) const GROTH16_VK: &[u8] = include_bytes!(
  "../../verifying-keys/0.4/groth16-development-verifying-key.bin"
);
/// SHA-256 of the gnark Groth16 verifying key, which a Groth16 packet begins with.
pub(super) const GROTH16_VK_SHA256: &str =
  "57e71f84961ab3f6d5d38e278156ec191a0736ba47432af5a469b4f69842ec03";
pub(super) const GROTH16_CIRCUIT_SHA256: &str =
  "5ffbd511b8a209e585f84498451f9428ee1cd25a473fc345f21020b11d5cbb26";

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
