//! Historical arithmetic/Merkle conformance identities, not an Exec configuration.

use anyhow::Result;
use flock_prover::{
  pcs::{PcsParams, ligerito::embedded_initial_k_or_default},
  union::UnionInstance,
};

use flock_prover::{
  hash::HashKind, pcs::ligerito::LigeritoProfile,
  r1cs_hashes::blake3::Blake3Setup,
};

pub const FLOCK_UPSTREAM_REVISION: &str =
  "b310f35f35f68095537150a1c8c0a43caca9a29e";
pub const STAGE3_TRANSCRIPT_DOMAIN: &[u8] = b"ix:flock-stage3:fri-verifier:v1";
pub const ARITHMETIC_CONFORMANCE_TRANSCRIPT_DOMAIN: &[u8] =
  b"ix:flock-stage3:goldilocks-arithmetic-conformance:v1";
pub const MERKLE_CONFORMANCE_TRANSCRIPT_DOMAIN: &[u8] =
  b"ix:flock-stage3:blake3-merkle-conformance:v1";
const CONFIG_DOMAIN: &[u8; 8] = b"IXFLKCF1";
const FIELD_F128: u8 = 1;
const PROFILE_FAST128: u8 = 1;
const MERKLE_BLAKE3: u8 = 1;
const TRANSCRIPT_CHAINED_BLAKE3: u8 = 1;

/// Historical configuration used only by the retained gadget conformance vectors.
/// The generic IxBy execution protocol must have its own domain and identity.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ConformanceConfigV1;

impl ConformanceConfigV1 {
  /// Canonical bytes committed by every Stage 3 statement:
  /// `IXFLKCF1 || len(rev) u16 LE || rev || field || profile || merkle ||
  /// transcript || len(domain) u16 LE || domain`.
  ///
  /// The four one-byte IDs are respectively F128=1, Fast128=1, BLAKE3=1,
  /// and chained-BLAKE3=1. New choices require a new configuration version.
  pub fn to_bytes(self) -> Vec<u8> {
    let revision = FLOCK_UPSTREAM_REVISION.as_bytes();
    let domain = STAGE3_TRANSCRIPT_DOMAIN;
    let mut bytes =
      Vec::with_capacity(8 + 2 + revision.len() + 4 + 2 + domain.len());
    bytes.extend_from_slice(CONFIG_DOMAIN);
    bytes.extend_from_slice(
      &u16::try_from(revision.len()).expect("revision length").to_le_bytes(),
    );
    bytes.extend_from_slice(revision);
    bytes.extend_from_slice(&[
      FIELD_F128,
      PROFILE_FAST128,
      MERKLE_BLAKE3,
      TRANSCRIPT_CHAINED_BLAKE3,
    ]);
    bytes.extend_from_slice(
      &u16::try_from(domain.len()).expect("domain length").to_le_bytes(),
    );
    bytes.extend_from_slice(domain);
    bytes
  }

  pub fn digest(self) -> [u8; 32] {
    *blake3::hash(&self.to_bytes()).as_bytes()
  }

  pub const fn profile(self) -> LigeritoProfile {
    LigeritoProfile::Fast128
  }

  pub const fn merkle_hash(self) -> HashKind {
    HashKind::Blake3
  }

  /// Construct the pinned Flock BLAKE3 relation used by the engine smoke test.
  pub fn blake3_setup(self, n_blocks: usize) -> Blake3Setup {
    let mut setup = Blake3Setup::with_profile(n_blocks, self.profile());
    setup.pcs_params.merkle_hash = self.merkle_hash();
    setup
  }
}

pub fn pcs_params(union: &UnionInstance<'_>) -> PcsParams {
  let profile = ConformanceConfigV1.profile();
  let m = union.dense_m();
  let log_batch_size = embedded_initial_k_or_default(m, profile);
  PcsParams {
    m,
    log_inv_rate: profile.log_inv_rate(),
    log_batch_size,
    profile,
    num_lanes: union.commit_lanes(log_batch_size),
    merkle_hash: ConformanceConfigV1.merkle_hash(),
  }
}

/// Patching the experimental dependency must not widen any V1 endpoint.
pub fn ensure_baseline_pcs(params: &PcsParams) -> Result<()> {
  anyhow::ensure!(
    (22..=35).contains(&params.m),
    "legacy/baseline PCS m={} is outside the approved registry 22..=35",
    params.m
  );
  Ok(())
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn config_is_explicit_and_domain_separated() {
    let bytes = ConformanceConfigV1.to_bytes();
    assert_eq!(&bytes[..8], CONFIG_DOMAIN);
    assert!(
      bytes
        .windows(FLOCK_UPSTREAM_REVISION.len())
        .any(|window| window == FLOCK_UPSTREAM_REVISION.as_bytes())
    );
    assert!(
      bytes
        .windows(STAGE3_TRANSCRIPT_DOMAIN.len())
        .any(|window| window == STAGE3_TRANSCRIPT_DOMAIN)
    );
    assert_eq!(ConformanceConfigV1.profile(), LigeritoProfile::Fast128);
    assert_eq!(ConformanceConfigV1.merkle_hash(), HashKind::Blake3);
    assert_eq!(
      blake3::Hash::from_bytes(ConformanceConfigV1.digest()).to_hex().as_str(),
      "1897ad7e36bc1a11a9dc4170552b1b48f5689b8f04ecc3c3825ce0273ecfaffc"
    );
  }
}
