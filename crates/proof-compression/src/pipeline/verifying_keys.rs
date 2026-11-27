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
use crate::kzg::{
  Srs, VerifierParams,
  curve::{Curve, KzgCurve},
};

/// Version of the bundled verifying keys and the layout they were derived for.
const VERSION: &str = "0.5";

/// Log2 of the first KZG stage's partition height the keys were derived for.
pub(super) const FIRST_LOG_HEIGHT: usize = 24;

/// Serialized aggregation backend key whose roots the layout normalizes: the
/// formal aggregation program under `aiur::trace::stark::Parameters::DEFAULT`.
const ROOT_VK_BLAKE3: &str =
  "d3813ae554af0aa6a24c5c72c796e17403756aa1f9cabbb08519ed4d767c9f13";
/// The root layout (`.ixl`, see `FixedRoot`) and its content address.
const LAYOUT: &[u8] =
  include_bytes!("../../verifying-keys/0.5/root-layout.ixl");
const LAYOUT_BLAKE3: &str =
  "035f3b31e438becfe9294b792e7b0cb9aef8a10d073216731ac171c10cdd5748";

/// Backend and entrypoint words of the aggregation program, the statement
/// prefix every compressed claim of this release carries
/// ([`statement::backend_prefix`] of the IxVM and aggregation keys).
pub(super) const STATEMENT_PREFIX: [u64; 10] = [
  1, 0, 2736370005, 1983549104, 896032380, 1564468090, 1137178757, 4223943773,
  1723211272, 3024343524,
];

pub(super) const RECURSIVE_VK: &[u8] =
  include_bytes!("../../verifying-keys/0.5/recursive-vk.bin");
const RECURSIVE_VK_BLAKE3: &str =
  "adb2415c05975b848ad38f123a5e49d718ad6a63a094d2e852634da9923e1aa5";
/// The identifier a recursive KZG packet begins with.
pub(super) const RECURSIVE_VK_ID: &str =
  "07b533959666cf26b9ed44baeda8a2c26bc839591b329c2ccc3d2f8622976914";

/// Identity of the first stage's FRI verifier plan for the bundled backend
/// and layout, half of its fixed-cache identity. Independent of the KZG setup.
pub(super) const FIRST_PLAN_ID: &str =
  "72e4cff851093d7dbb7836324b6f3ccde0f0bfcea8d90609359f8565aa25a224";
/// Identity of the recursive stage's verifier frontend over the first stage
/// under Ignition, half of its fixed-cache identity.
pub(super) const RECURSIVE_FRONTEND_ID: &str =
  "d82bb2ffb899fa22c711582b8dc4a92b01224d7d3e6f4851465980f0f41838e7";

#[cfg(test)]
const PLONK_VK: &[u8] =
  include_bytes!("../../verifying-keys/0.5/plonk-verifying-key.bin");
/// SHA-256 of the archived legacy PLONK verifying key.
#[cfg(test)]
const PLONK_VK_SHA256: &str =
  "ae9638f047b26990e810bf46dc664d2cc1fd502e8f09e01fc9fb3b192bca2c25";

/// SHA-256 of the exported recursive verifier description (with the key-bound
/// KZG transcript seed).
#[cfg(all(test, feature = "plonk"))]
pub(super) const FINAL_SCHEMA_SHA256: &str =
  "481d99bb117b8769dcf78be33bdef23b894a7745d810072a5a1204fa2abf1e6d";

/// Archived legacy Groth16 development verifying key.
#[cfg(test)]
const GROTH16_VK: &[u8] = include_bytes!(
  "../../verifying-keys/0.5/groth16-development-verifying-key.bin"
);
/// SHA-256 of the archived legacy Groth16 verifying key.
#[cfg(test)]
const GROTH16_VK_SHA256: &str =
  "3e6bb1fffcb17910c573c95459344f6161d6f17357dbd79fbca7476b1bafbed9";

/// The setup class of the archived Groth16 development key, if
/// `allow_development` admits it.
#[cfg(test)]
fn groth16_setup(allow_development: bool) -> Result<SetupClass> {
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
         keys {VERSION} were derived for: prefix {:?}",
        &words[..10]
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

/// Verify a BN254 recursive KZG packet of `claim` under the release key.
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

/// Reject BLS12-381 recursive KZG packets when no explicit `--vk` is supplied.
pub(super) fn verify_recursive_bls12_381(
  packet: &[u8],
  _claim: &[u8],
) -> Result<SetupClass> {
  let _id = packet.get(..32).ok_or("truncated compressed proof")?;
  Err(
    "BLS12-381 recursive KZG proofs have no bundled release verifying key yet, and ix verify has no option to supply one".into(),
  )
}

/// Verify a recursive KZG packet under a verifying key the caller supplies
/// with an independently trusted digest, against an independently expected
/// statement.
pub(super) fn verify_with_vk_for<C: KzgCurve>(
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
  let vk = VerifyingKey::<C>::from_bytes(vk)?;
  let setup = SetupClass::of(&vk.verifier_params()?);
  vk.check_setup_class(setup)?;
  if setup == SetupClass::Development && !allow_development {
    return Err("compressed proof uses the known-trapdoor development setup; pass --dev-srs to accept it (not production-secure)".into());
  }
  vk.verify(packet, expected)?;
  Ok(setup)
}

#[cfg(test)]
pub(super) fn verify_with_vk(
  packet: &[u8],
  claim: &[u8],
  expected: &statement::Statement,
  vk: &[u8],
  trusted_digest: &[u8; 32],
  allow_development: bool,
) -> Result<SetupClass> {
  verify_with_vk_for::<crate::kzg::curve::Bn254>(
    packet,
    claim,
    expected,
    vk,
    trusted_digest,
    allow_development,
  )
}

/// Whether a compression of a `root_vk` root under `setup` must produce the
/// bundled keys: BN254, this version's backend, and Ignition.
pub(super) fn bundled_for(
  curve: Curve,
  root_vk: &[u8],
  setup: &super::SetupConfig,
) -> bool {
  curve == Curve::Bn254
    && blake3::hash(root_vk).to_hex().as_str() == ROOT_VK_BLAKE3
    && setup.class() == SetupClass::Ignition
}

/// A recursive key proved for BN254 and this version's backend under Ignition
/// must be the bundled key.
pub(super) fn check_recursive_key(
  curve: Curve,
  root_vk: &[u8],
  setup: &super::SetupConfig,
  vk: &[u8],
) -> Result<()> {
  if bundled_for(curve, root_vk, setup) && vk != RECURSIVE_VK {
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
  curve: Curve,
  id: &[u8],
  words: &statement::Statement,
) -> Result<()> {
  if curve == Curve::Bn254
    && id == decode(RECURSIVE_VK_ID)?
    && words[..10] != STATEMENT_PREFIX
  {
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

  /// `ROOT_VK_BLAKE3`, `STATEMENT_PREFIX` and the layout's key binding follow
  /// from the release's IxVM and aggregation keys (the `ixvm-proof key` and
  /// `stark-verifier key` directories). Part of the release-consistency gate
  /// `tools/rederive-release-keys.sh`.
  #[test]
  #[ignore = "needs IX_IXVM_KEY_DIR and IX_AGGR_KEY_DIR, each with key.bin \
              and identity.json"]
  fn release_prefix_matches_the_release_keys() {
    let load = |variable: &str| -> (Vec<u8>, u64) {
      let dir = std::path::PathBuf::from(
        std::env::var_os(variable)
          .unwrap_or_else(|| panic!("{variable} is not set")),
      );
      let key = std::fs::read(dir.join("key.bin")).unwrap();
      let identity: serde_json::Value = serde_json::from_slice(
        &std::fs::read(dir.join("identity.json")).unwrap(),
      )
      .unwrap();
      assert_eq!(identity["call_channel"].as_u64(), Some(1));
      assert_eq!(
        identity["key_digest"].as_str(),
        Some(blake3::hash(&key).to_hex().as_str())
      );
      (key, identity["function_index"].as_u64().unwrap())
    };
    let (ixvm, ixvm_index) = load("IX_IXVM_KEY_DIR");
    let (aggr, aggr_index) = load("IX_AGGR_KEY_DIR");
    assert_eq!(
      blake3::hash(&aggr).as_bytes(),
      &decode(ROOT_VK_BLAKE3).unwrap(),
      "ROOT_VK_BLAKE3"
    );
    assert_eq!(
      statement::backend_prefix(&ixvm, ixvm_index, &aggr, aggr_index),
      STATEMENT_PREFIX,
      "STATEMENT_PREFIX"
    );
    assert_eq!(release_root_layout(&aggr).unwrap(), LAYOUT);
  }

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
