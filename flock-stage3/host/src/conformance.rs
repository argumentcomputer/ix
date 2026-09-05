//! A real Flock/BLAKE3 round trip used to lock the upstream engine API.
//!
//! This is intentionally not exposed as a Stage 3 proof: the standalone
//! upstream BLAKE3 batch relation has existential (unbound) I/O.

use anyhow::{Context, Result, bail};
use flock_prover::{
  challenger::FsChallenger, proof_io::R1csProofBundleLigerito,
  r1cs_hashes::blake3::Compression,
};

use crate::config::{ENGINE_CONFORMANCE_TRANSCRIPT_DOMAIN, FlockConfigV1};

const MAGIC: &[u8; 8] = b"IXFLKB3C";
const VERSION: u16 = 1;
const HEADER_BYTES: usize = 8 + 2 + 32 + 4 + 8;
const MIN_BLOCKS: usize = 256;
const MAX_BLOCKS: usize = 1 << 20;
const MAX_BUNDLE_BYTES: usize = 64 * 1024 * 1024;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EngineConformanceArtifact {
  n_blocks: usize,
  bundle_bytes: Vec<u8>,
}

impl EngineConformanceArtifact {
  pub fn to_bytes(&self) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(HEADER_BYTES + self.bundle_bytes.len());
    bytes.extend_from_slice(MAGIC);
    bytes.extend_from_slice(&VERSION.to_le_bytes());
    bytes.extend_from_slice(&FlockConfigV1.digest());
    bytes.extend_from_slice(
      &u32::try_from(self.n_blocks).expect("block count").to_le_bytes(),
    );
    bytes.extend_from_slice(
      &u64::try_from(self.bundle_bytes.len())
        .expect("bundle length")
        .to_le_bytes(),
    );
    bytes.extend_from_slice(&self.bundle_bytes);
    bytes
  }

  pub fn from_bytes(bytes: &[u8]) -> Result<Self> {
    if bytes.len() < HEADER_BYTES {
      bail!("truncated Flock conformance artifact");
    }
    if &bytes[..8] != MAGIC {
      bail!("invalid Flock conformance artifact magic");
    }
    let version = u16::from_le_bytes(bytes[8..10].try_into().unwrap());
    if version != VERSION {
      bail!("unsupported Flock conformance artifact version {version}");
    }
    if bytes[10..42] != FlockConfigV1.digest() {
      bail!("Flock conformance artifact configuration mismatch");
    }
    let n_blocks =
      usize::try_from(u32::from_le_bytes(bytes[42..46].try_into().unwrap()))
        .expect("u32 fits usize");
    validate_n_blocks(n_blocks)?;
    let bundle_len =
      usize::try_from(u64::from_le_bytes(bytes[46..54].try_into().unwrap()))
        .map_err(|_| {
          anyhow::anyhow!("Flock bundle length does not fit usize")
        })?;
    if bundle_len == 0 || bundle_len > MAX_BUNDLE_BYTES {
      bail!("invalid Flock bundle length {bundle_len}");
    }
    let expected_len = HEADER_BYTES
      .checked_add(bundle_len)
      .ok_or_else(|| anyhow::anyhow!("Flock artifact length overflow"))?;
    if bytes.len() != expected_len {
      bail!(
        "Flock conformance artifact is {} bytes; header declares {expected_len}",
        bytes.len()
      );
    }
    Ok(Self { n_blocks, bundle_bytes: bytes[HEADER_BYTES..].to_vec() })
  }

  pub fn n_blocks(&self) -> usize {
    self.n_blocks
  }

  pub fn bundle_bytes(&self) -> &[u8] {
    &self.bundle_bytes
  }
}

/// Prove an existential batch of valid BLAKE3 compression rows using the
/// exact hash/profile choices intended for Stage 3.
pub fn prove_engine_conformance(
  blocks: &[Compression],
) -> Result<EngineConformanceArtifact> {
  validate_n_blocks(blocks.len())?;
  let setup = FlockConfigV1.blake3_setup(blocks.len());
  let mut challenger =
    FsChallenger::with_chained_blake3(ENGINE_CONFORMANCE_TRANSCRIPT_DOMAIN);
  let (proof, commitment, _) = setup.prove_fast(blocks, &mut challenger);
  let bundle = R1csProofBundleLigerito { commitment, proof };
  let bundle_bytes = bundle.to_bytes();
  if bundle_bytes.len() > MAX_BUNDLE_BYTES {
    bail!("Flock proof bundle exceeds {MAX_BUNDLE_BYTES} bytes");
  }
  Ok(EngineConformanceArtifact { n_blocks: blocks.len(), bundle_bytes })
}

pub fn verify_engine_conformance(
  artifact: &EngineConformanceArtifact,
) -> Result<()> {
  validate_n_blocks(artifact.n_blocks)?;
  let bundle = R1csProofBundleLigerito::from_bytes(&artifact.bundle_bytes)
    .context("decode Flock proof bundle")?;
  let setup = FlockConfigV1.blake3_setup(artifact.n_blocks);
  let mut challenger =
    FsChallenger::with_chained_blake3(ENGINE_CONFORMANCE_TRANSCRIPT_DOMAIN);
  setup.verify(&bundle.commitment, &bundle.proof, &mut challenger).map_err(
    |error| anyhow::anyhow!("Flock engine proof rejected: {error:?}"),
  )?;
  Ok(())
}

fn validate_n_blocks(n_blocks: usize) -> Result<()> {
  if !(MIN_BLOCKS..=MAX_BLOCKS).contains(&n_blocks) {
    bail!(
      "Flock conformance batch has {n_blocks} blocks; expected {MIN_BLOCKS}..={MAX_BLOCKS}"
    );
  }
  Ok(())
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn envelope_is_strict_and_configuration_bound() {
    let artifact = EngineConformanceArtifact {
      n_blocks: MIN_BLOCKS,
      bundle_bytes: vec![1, 2, 3],
    };
    let bytes = artifact.to_bytes();
    assert_eq!(
      EngineConformanceArtifact::from_bytes(&bytes).unwrap(),
      artifact
    );

    let mut extended = bytes.clone();
    extended.push(0);
    assert!(EngineConformanceArtifact::from_bytes(&extended).is_err());

    let mut wrong_config = bytes;
    wrong_config[10] ^= 1;
    assert!(EngineConformanceArtifact::from_bytes(&wrong_config).is_err());
  }

  #[test]
  #[ignore = "large upstream Flock proof; run explicitly for revision conformance"]
  fn real_fast128_blake3_round_trip() {
    let blocks: Vec<Compression> = (0..MIN_BLOCKS)
      .map(|index| {
        let mut message = [0u32; 16];
        message[0] = u32::try_from(index).unwrap();
        ([0u32; 8], message, index as u64, 64, 0)
      })
      .collect();
    let artifact = prove_engine_conformance(&blocks).expect("prove");
    eprintln!(
      "Flock Fast128/BLAKE3 conformance bundle: {} bytes",
      artifact.bundle_bytes().len()
    );
    let encoded = artifact.to_bytes();
    let decoded = EngineConformanceArtifact::from_bytes(&encoded).unwrap();
    verify_engine_conformance(&decoded).expect("verify");

    let mut mutated = decoded;
    let flip_at = mutated.bundle_bytes.len() / 2;
    mutated.bundle_bytes[flip_at] ^= 1;
    assert!(
      verify_engine_conformance(&mutated).is_err(),
      "mutated Flock proof must be rejected"
    );
  }
}
