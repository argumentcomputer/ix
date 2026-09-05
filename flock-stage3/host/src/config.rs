use flock_prover::{
  hash::HashKind, pcs::ligerito::LigeritoProfile,
  r1cs_hashes::blake3::Blake3Setup,
};

pub const FLOCK_UPSTREAM_REVISION: &str =
  "b310f35f35f68095537150a1c8c0a43caca9a29e";
pub const STAGE3_TRANSCRIPT_DOMAIN: &[u8] = b"ix:flock-stage3:fri-verifier:v1";
pub const ENGINE_CONFORMANCE_TRANSCRIPT_DOMAIN: &[u8] =
  b"ix:flock-stage3:blake3-engine-conformance:v1";
pub const ARITHMETIC_CONFORMANCE_TRANSCRIPT_DOMAIN: &[u8] =
  b"ix:flock-stage3:goldilocks-arithmetic-conformance:v1";
pub const MERKLE_CONFORMANCE_TRANSCRIPT_DOMAIN: &[u8] =
  b"ix:flock-stage3:blake3-merkle-conformance:v1";
pub const FRI_FOLD_CONFORMANCE_TRANSCRIPT_DOMAIN: &[u8] =
  b"ix:flock-stage3:authenticated-fri-fold-conformance:v1";
pub const FRI_QUERY_CONFORMANCE_TRANSCRIPT_DOMAIN: &[u8] =
  b"ix:flock-stage3:fri-commit-phase-query-conformance:v1";
pub const PCS_REDUCTION_CONFORMANCE_TRANSCRIPT_DOMAIN: &[u8] =
  b"ix:flock-stage3:pcs-reduced-opening-conformance:v1";
pub const STAGE2_TRANSCRIPT_CONFORMANCE_TRANSCRIPT_DOMAIN: &[u8] =
  b"ix:flock-stage3:stage2-transcript-conformance:v1";
pub const TRANSCRIPT_BOUND_PCS_CONFORMANCE_TRANSCRIPT_DOMAIN: &[u8] =
  b"ix:flock-stage3:transcript-bound-pcs-conformance:v1";
pub const TRANSCRIPT_BOUND_FRI_CONFORMANCE_TRANSCRIPT_DOMAIN: &[u8] =
  b"ix:flock-stage3:transcript-bound-fri-query-conformance:v1";
pub const TRANSCRIPT_BOUND_FRI_QUERIES_CONFORMANCE_TRANSCRIPT_DOMAIN: &[u8] =
  b"ix:flock-stage3:transcript-bound-fri-all-queries-conformance:v1";
pub const TRANSCRIPT_BOUND_PCS_FRI_QUERIES_CONFORMANCE_TRANSCRIPT_DOMAIN:
  &[u8] =
  b"ix:flock-stage3:transcript-bound-pcs-fri-all-queries-conformance:v1";
pub const STAGE2_AIR_PCS_FRI_CONFORMANCE_TRANSCRIPT_DOMAIN: &[u8] =
  b"ix:flock-stage3:stage2-air-pcs-fri-conformance:v1";

const CONFIG_DOMAIN: &[u8; 8] = b"IXFLKCF1";
const FIELD_F128: u8 = 1;
const PROFILE_FAST128: u8 = 1;
const MERKLE_BLAKE3: u8 = 1;
const TRANSCRIPT_CHAINED_BLAKE3: u8 = 1;

/// The only Flock protocol configuration accepted by this backend version.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct FlockConfigV1;

impl FlockConfigV1 {
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
  /// The production Stage 2-verifier relation will reuse these PCS parameters.
  pub(crate) fn blake3_setup(self, n_blocks: usize) -> Blake3Setup {
    let mut setup = Blake3Setup::with_profile(n_blocks, self.profile());
    setup.pcs_params.merkle_hash = self.merkle_hash();
    setup
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn config_is_explicit_and_domain_separated() {
    let bytes = FlockConfigV1.to_bytes();
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
    assert_eq!(FlockConfigV1.profile(), LigeritoProfile::Fast128);
    assert_eq!(FlockConfigV1.merkle_hash(), HashKind::Blake3);
    assert_eq!(
      blake3::Hash::from_bytes(FlockConfigV1.digest()).to_hex().as_str(),
      "1897ad7e36bc1a11a9dc4170552b1b48f5689b8f04ecc3c3825ce0273ecfaffc"
    );
  }
}
