use anyhow::{Context, Result, bail};
use bincode::Options;
use ix_terminal::Stage2RootStatementV1;
use serde::{Deserialize, Serialize};

use crate::config::FlockConfigV1;

pub const STAGE3_STATEMENT_DOMAIN: &[u8; 8] = b"IXFLK301";
pub const STAGE3_STATEMENT_BYTES: usize = 8 + 32 + 32 + 32;
const ARTIFACT_MAGIC: &[u8; 8] = b"IXFLOCK3";
const ARTIFACT_VERSION: u16 = 1;
const ARTIFACT_HEADER_BYTES: usize = 8 + 2 + 4 + 8;
const MAX_PROOF_BYTES: usize = 64 * 1024 * 1024;
const PRODUCTION_PAYLOAD_MAGIC: [u8; 8] = *b"IXFLK3P1";
const PRODUCTION_PAYLOAD_VERSION: u16 = 1;

/// Public input to the complete Flock Stage 3 relation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stage3StatementV1 {
  stage2_root_digest: [u8; 32],
  relation_digest: [u8; 32],
  config_digest: [u8; 32],
}

impl Stage3StatementV1 {
  pub fn new(
    stage2_root: &Stage2RootStatementV1,
    relation_digest: [u8; 32],
  ) -> Self {
    Self {
      stage2_root_digest: stage2_root.digest(),
      relation_digest,
      config_digest: FlockConfigV1.digest(),
    }
  }

  pub fn from_bytes(bytes: &[u8]) -> Result<Self> {
    if bytes.len() != STAGE3_STATEMENT_BYTES {
      bail!(
        "Stage 3 statement is {} bytes; expected {STAGE3_STATEMENT_BYTES}",
        bytes.len()
      );
    }
    if &bytes[..8] != STAGE3_STATEMENT_DOMAIN {
      bail!("invalid Stage 3 statement domain");
    }
    let mut stage2_root_digest = [0u8; 32];
    stage2_root_digest.copy_from_slice(&bytes[8..40]);
    let mut relation_digest = [0u8; 32];
    relation_digest.copy_from_slice(&bytes[40..72]);
    let mut config_digest = [0u8; 32];
    config_digest.copy_from_slice(&bytes[72..104]);
    if config_digest != FlockConfigV1.digest() {
      bail!("Stage 3 statement uses a different Flock configuration");
    }
    Ok(Self { stage2_root_digest, relation_digest, config_digest })
  }

  pub fn to_bytes(&self) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(STAGE3_STATEMENT_BYTES);
    bytes.extend_from_slice(STAGE3_STATEMENT_DOMAIN);
    bytes.extend_from_slice(&self.stage2_root_digest);
    bytes.extend_from_slice(&self.relation_digest);
    bytes.extend_from_slice(&self.config_digest);
    bytes
  }

  pub fn digest(&self) -> [u8; 32] {
    *blake3::hash(&self.to_bytes()).as_bytes()
  }

  pub fn stage2_root_digest(&self) -> &[u8; 32] {
    &self.stage2_root_digest
  }

  pub fn relation_digest(&self) -> &[u8; 32] {
    &self.relation_digest
  }

  pub fn config_digest(&self) -> &[u8; 32] {
    &self.config_digest
  }
}

/// Strict transport framing for a complete Stage 3 proof.
///
/// Parsing establishes canonical framing only; cryptographic acceptance also
/// requires `FlockStage3Backend::verify_stage2` with an expected statement.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stage3ArtifactV1 {
  statement: Stage3StatementV1,
  proof: Vec<u8>,
}

impl Stage3ArtifactV1 {
  pub(crate) fn new(
    statement: Stage3StatementV1,
    proof: Vec<u8>,
  ) -> Result<Self> {
    if proof.is_empty() {
      bail!("Stage 3 proof is empty");
    }
    if proof.len() > MAX_PROOF_BYTES {
      bail!("Stage 3 proof exceeds {MAX_PROOF_BYTES} bytes");
    }
    Ok(Self { statement, proof })
  }

  pub fn to_bytes(&self) -> Vec<u8> {
    let statement = self.statement.to_bytes();
    let mut bytes = Vec::with_capacity(
      ARTIFACT_HEADER_BYTES + statement.len() + self.proof.len(),
    );
    bytes.extend_from_slice(ARTIFACT_MAGIC);
    bytes.extend_from_slice(&ARTIFACT_VERSION.to_le_bytes());
    bytes.extend_from_slice(
      &u32::try_from(statement.len()).expect("statement length").to_le_bytes(),
    );
    bytes.extend_from_slice(
      &u64::try_from(self.proof.len()).expect("proof length").to_le_bytes(),
    );
    bytes.extend_from_slice(&statement);
    bytes.extend_from_slice(&self.proof);
    bytes
  }

  pub fn from_bytes(bytes: &[u8]) -> Result<Self> {
    if bytes.len() < ARTIFACT_HEADER_BYTES {
      bail!("truncated Stage 3 artifact header");
    }
    if &bytes[..8] != ARTIFACT_MAGIC {
      bail!("invalid Stage 3 artifact magic");
    }
    let version = read_u16(&bytes[8..10]);
    if version != ARTIFACT_VERSION {
      bail!("unsupported Stage 3 artifact version {version}");
    }
    let statement_len =
      usize::try_from(read_u32(&bytes[10..14])).expect("u32 fits in usize");
    if statement_len != STAGE3_STATEMENT_BYTES {
      bail!("invalid Stage 3 statement length {statement_len}");
    }
    let proof_len =
      usize::try_from(read_u64(&bytes[14..22])).map_err(|_| {
        anyhow::anyhow!("Stage 3 proof length does not fit usize")
      })?;
    if proof_len == 0 {
      bail!("Stage 3 proof is empty");
    }
    if proof_len > MAX_PROOF_BYTES {
      bail!("Stage 3 proof exceeds {MAX_PROOF_BYTES} bytes");
    }
    let expected_len = ARTIFACT_HEADER_BYTES
      .checked_add(statement_len)
      .and_then(|len| len.checked_add(proof_len))
      .ok_or_else(|| anyhow::anyhow!("Stage 3 artifact length overflow"))?;
    if bytes.len() != expected_len {
      bail!(
        "Stage 3 artifact is {} bytes; header declares {expected_len}",
        bytes.len()
      );
    }
    let statement_end = ARTIFACT_HEADER_BYTES + statement_len;
    let statement = Stage3StatementV1::from_bytes(
      &bytes[ARTIFACT_HEADER_BYTES..statement_end],
    )?;
    Self::new(statement, bytes[statement_end..].to_vec())
  }

  pub fn ensure_statement(&self, expected: &Stage3StatementV1) -> Result<()> {
    if &self.statement != expected {
      bail!("Stage 3 artifact statement does not match the expected root");
    }
    Ok(())
  }

  pub fn statement(&self) -> &Stage3StatementV1 {
    &self.statement
  }

  pub fn proof_bytes(&self) -> &[u8] {
    &self.proof
  }
}

/// Canonical host transport needed to reconstruct the Flock public input.
///
/// The compact Stage 2 inputs are not trusted by verification: they are
/// decoded again, lowered into the fixed relation, and checked against the
/// proof. Keeping them here avoids making Rust's serializer part of the Flock
/// circuit while giving Stage 4 a deterministic source for the verifier
/// witness.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Stage3ProductionPayloadV1 {
  magic: [u8; 8],
  version: u16,
  config_digest: [u8; 32],
  vk_bytes: Vec<u8>,
  claim_bytes: Vec<u8>,
  stage2_proof_bytes: Vec<u8>,
  circuit_digest: [u8; 32],
  flock_proof_bundle_bytes: Vec<u8>,
}

impl Stage3ProductionPayloadV1 {
  pub(crate) fn new(
    vk_bytes: &[u8],
    claim_bytes: &[u8],
    stage2_proof_bytes: &[u8],
    circuit_digest: [u8; 32],
    flock_proof_bundle_bytes: &[u8],
  ) -> Result<Self> {
    let payload = Self {
      magic: PRODUCTION_PAYLOAD_MAGIC,
      version: PRODUCTION_PAYLOAD_VERSION,
      config_digest: FlockConfigV1.digest(),
      vk_bytes: vk_bytes.to_vec(),
      claim_bytes: claim_bytes.to_vec(),
      stage2_proof_bytes: stage2_proof_bytes.to_vec(),
      circuit_digest,
      flock_proof_bundle_bytes: flock_proof_bundle_bytes.to_vec(),
    };
    payload.validate()?;
    Ok(payload)
  }

  pub(crate) fn encode(&self) -> Result<Vec<u8>> {
    self.validate()?;
    let bytes = bincode::DefaultOptions::new()
      .with_fixint_encoding()
      .serialize(self)
      .context("encode Stage 3 production payload")?;
    if bytes.len() > MAX_PROOF_BYTES {
      bail!("Stage 3 production payload exceeds {MAX_PROOF_BYTES} bytes");
    }
    Ok(bytes)
  }

  pub(crate) fn decode(bytes: &[u8]) -> Result<Self> {
    let payload: Self = bincode::DefaultOptions::new()
      .with_fixint_encoding()
      .with_limit(MAX_PROOF_BYTES as u64)
      .reject_trailing_bytes()
      .deserialize(bytes)
      .context("invalid Stage 3 production payload")?;
    payload.validate()?;
    Ok(payload)
  }

  fn validate(&self) -> Result<()> {
    if self.magic != PRODUCTION_PAYLOAD_MAGIC {
      bail!("invalid Stage 3 production payload magic");
    }
    if self.version != PRODUCTION_PAYLOAD_VERSION {
      bail!("unsupported Stage 3 production payload version {}", self.version);
    }
    if self.config_digest != FlockConfigV1.digest() {
      bail!("Stage 3 production payload configuration mismatch");
    }
    for (bytes, label) in [
      (self.vk_bytes.as_slice(), "verifying key"),
      (self.claim_bytes.as_slice(), "claim"),
      (self.stage2_proof_bytes.as_slice(), "Stage 2 proof"),
      (self.flock_proof_bundle_bytes.as_slice(), "Flock proof bundle"),
    ] {
      if bytes.is_empty() {
        bail!("Stage 3 production payload has an empty {label}");
      }
    }
    Ok(())
  }

  pub(crate) fn vk_bytes(&self) -> &[u8] {
    &self.vk_bytes
  }

  pub(crate) fn claim_bytes(&self) -> &[u8] {
    &self.claim_bytes
  }

  pub(crate) fn stage2_proof_bytes(&self) -> &[u8] {
    &self.stage2_proof_bytes
  }

  pub(crate) const fn circuit_digest(&self) -> [u8; 32] {
    self.circuit_digest
  }

  pub(crate) fn flock_proof_bundle_bytes(&self) -> &[u8] {
    &self.flock_proof_bundle_bytes
  }
}

fn read_u16(bytes: &[u8]) -> u16 {
  u16::from_le_bytes(bytes.try_into().expect("fixed u16"))
}

fn read_u32(bytes: &[u8]) -> u32 {
  u32::from_le_bytes(bytes.try_into().expect("fixed u32"))
}

fn read_u64(bytes: &[u8]) -> u64 {
  u64::from_le_bytes(bytes.try_into().expect("fixed u64"))
}

#[cfg(test)]
mod tests {
  use super::*;
  use multi_stark::types::FriParameters;

  fn statement() -> Stage3StatementV1 {
    let fri = FriParameters {
      log_final_poly_len: 0,
      max_log_arity: 1,
      num_queries: 100,
      commit_proof_of_work_bits: 0,
      query_proof_of_work_bits: 20,
    };
    let claim: Vec<u8> = (0..18u64).flat_map(u64::to_le_bytes).collect();
    let root = Stage2RootStatementV1::new(b"vk", &claim, &fri).unwrap();
    Stage3StatementV1::new(&root, [7; 32])
  }

  #[test]
  fn artifact_round_trip_rejects_extensions_and_mutations() {
    let artifact = Stage3ArtifactV1::new(statement(), vec![1, 2, 3]).unwrap();
    assert_eq!(
      blake3::Hash::from_bytes(artifact.statement().digest()).to_hex().as_str(),
      "9f8062ce1801b29ed755cfb394fe888d5d82af77fe1ba2e5f539567e14e8b00d"
    );
    let bytes = artifact.to_bytes();
    assert_eq!(Stage3ArtifactV1::from_bytes(&bytes).unwrap(), artifact);

    let mut extended = bytes.clone();
    extended.push(0);
    assert!(Stage3ArtifactV1::from_bytes(&extended).is_err());

    let mut wrong_domain = bytes.clone();
    wrong_domain[ARTIFACT_HEADER_BYTES] ^= 1;
    assert!(Stage3ArtifactV1::from_bytes(&wrong_domain).is_err());

    let mut wrong_config = bytes;
    wrong_config[ARTIFACT_HEADER_BYTES + 72] ^= 1;
    assert!(Stage3ArtifactV1::from_bytes(&wrong_config).is_err());
  }

  #[test]
  fn expected_statement_is_checked_before_crypto() {
    let artifact = Stage3ArtifactV1::new(statement(), vec![1]).unwrap();
    assert!(artifact.ensure_statement(&statement()).is_ok());
    let mut other = statement();
    other.relation_digest[0] ^= 1;
    assert!(artifact.ensure_statement(&other).is_err());
  }

  #[test]
  fn production_payload_is_strict_and_configuration_bound() {
    let payload = Stage3ProductionPayloadV1::new(
      b"vk",
      b"claim",
      b"stage2 proof",
      [9; 32],
      b"flock proof",
    )
    .unwrap();
    let bytes = payload.encode().unwrap();
    assert_eq!(Stage3ProductionPayloadV1::decode(&bytes).unwrap(), payload);

    let mut extended = bytes.clone();
    extended.push(0);
    assert!(Stage3ProductionPayloadV1::decode(&extended).is_err());

    let mut wrong_magic = bytes;
    wrong_magic[0] ^= 1;
    assert!(Stage3ProductionPayloadV1::decode(&wrong_magic).is_err());

    let mut wrong_config = payload;
    wrong_config.config_digest[0] ^= 1;
    assert!(wrong_config.encode().is_err());
  }
}
