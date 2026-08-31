//! Canonical public boundary for the Flock-backed Stage 2.
//!
//! This module deliberately contains no Flock prover implementation. It owns
//! the byte strings that the native verifier, terminal circuit, Lean
//! specification, cache, and deployment policy must agree on.

use anyhow::{Result, bail};

pub const FLOCK_AGGREGATE_CLAIM_DOMAIN: &[u8; 8] = b"IXF2CL01";
pub const FLOCK_AGGREGATE_CLAIM_BYTES: usize = 8 + 32 * 3;

pub const FLOCK_STAGE2_ROOT_STATEMENT_DOMAIN: &[u8; 8] = b"IXFLK201";
pub const FLOCK_STAGE2_ROOT_STATEMENT_BYTES: usize = 8 + 32 * 5;

pub const FLOCK_STAGE2_ROOT_ARTIFACT_MAGIC: &[u8; 8] = b"IXFLOCK2";
const FLOCK_STAGE2_ROOT_ARTIFACT_VERSION: u16 = 1;
const FLOCK_STAGE2_ROOT_ARTIFACT_HEADER_BYTES: usize = 8 + 2 + 4 + 8;
const MAX_FLOCK_STAGE2_PROOF_BYTES: usize = 64 * 1024 * 1024;

/// Uniform public claim carried by every Flock Stage 2 leaf and outer proof.
///
/// The protocol manifest describes semantic acceptance rules. The relation
/// catalog separately identifies compiled verifier material, avoiding a hash
/// cycle when the catalog contains the root relation itself.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FlockAggregateClaimV1 {
  protocol_digest: [u8; 32],
  relation_catalog_digest: [u8; 32],
  output_claim_digest: [u8; 32],
}

impl FlockAggregateClaimV1 {
  pub const fn new(
    protocol_digest: [u8; 32],
    relation_catalog_digest: [u8; 32],
    output_claim_digest: [u8; 32],
  ) -> Self {
    Self { protocol_digest, relation_catalog_digest, output_claim_digest }
  }

  pub fn from_bytes(bytes: &[u8]) -> Result<Self> {
    if bytes.len() != FLOCK_AGGREGATE_CLAIM_BYTES {
      bail!(
        "Flock aggregate claim is {} bytes; expected {FLOCK_AGGREGATE_CLAIM_BYTES}",
        bytes.len()
      );
    }
    if &bytes[..8] != FLOCK_AGGREGATE_CLAIM_DOMAIN {
      bail!("invalid Flock aggregate claim domain");
    }
    Ok(Self {
      protocol_digest: digest_at(bytes, 8),
      relation_catalog_digest: digest_at(bytes, 40),
      output_claim_digest: digest_at(bytes, 72),
    })
  }

  pub fn to_bytes(&self) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(FLOCK_AGGREGATE_CLAIM_BYTES);
    bytes.extend_from_slice(FLOCK_AGGREGATE_CLAIM_DOMAIN);
    bytes.extend_from_slice(&self.protocol_digest);
    bytes.extend_from_slice(&self.relation_catalog_digest);
    bytes.extend_from_slice(&self.output_claim_digest);
    debug_assert_eq!(bytes.len(), FLOCK_AGGREGATE_CLAIM_BYTES);
    bytes
  }

  pub fn digest(&self) -> [u8; 32] {
    *blake3::hash(&self.to_bytes()).as_bytes()
  }

  pub const fn protocol_digest(&self) -> &[u8; 32] {
    &self.protocol_digest
  }

  pub const fn relation_catalog_digest(&self) -> &[u8; 32] {
    &self.relation_catalog_digest
  }

  pub const fn output_claim_digest(&self) -> &[u8; 32] {
    &self.output_claim_digest
  }
}

/// Canonical handoff from Flock Stage 2 to the terminal proof.
///
/// The Flock proof publishes [FlockAggregateClaimV1]. Native verification
/// additionally selects one root relation and one Flock configuration. This
/// statement binds those two views into the exact bytes hashed by Stage 3.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FlockStage2RootStatementV1 {
  aggregate_claim: FlockAggregateClaimV1,
  root_relation_digest: [u8; 32],
  flock_config_digest: [u8; 32],
}

impl FlockStage2RootStatementV1 {
  pub const fn new(
    aggregate_claim: FlockAggregateClaimV1,
    root_relation_digest: [u8; 32],
    flock_config_digest: [u8; 32],
  ) -> Self {
    Self { aggregate_claim, root_relation_digest, flock_config_digest }
  }

  pub fn from_bytes(bytes: &[u8]) -> Result<Self> {
    if bytes.len() != FLOCK_STAGE2_ROOT_STATEMENT_BYTES {
      bail!(
        "Flock Stage 2 root statement is {} bytes; expected {FLOCK_STAGE2_ROOT_STATEMENT_BYTES}",
        bytes.len()
      );
    }
    if &bytes[..8] != FLOCK_STAGE2_ROOT_STATEMENT_DOMAIN {
      bail!("invalid Flock Stage 2 root statement domain");
    }
    Ok(Self {
      aggregate_claim: FlockAggregateClaimV1::new(
        digest_at(bytes, 8),
        digest_at(bytes, 40),
        digest_at(bytes, 136),
      ),
      root_relation_digest: digest_at(bytes, 72),
      flock_config_digest: digest_at(bytes, 104),
    })
  }

  pub fn to_bytes(&self) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(FLOCK_STAGE2_ROOT_STATEMENT_BYTES);
    bytes.extend_from_slice(FLOCK_STAGE2_ROOT_STATEMENT_DOMAIN);
    bytes.extend_from_slice(self.aggregate_claim.protocol_digest());
    bytes.extend_from_slice(self.aggregate_claim.relation_catalog_digest());
    bytes.extend_from_slice(&self.root_relation_digest);
    bytes.extend_from_slice(&self.flock_config_digest);
    bytes.extend_from_slice(self.aggregate_claim.output_claim_digest());
    debug_assert_eq!(bytes.len(), FLOCK_STAGE2_ROOT_STATEMENT_BYTES);
    bytes
  }

  pub fn digest(&self) -> [u8; 32] {
    *blake3::hash(&self.to_bytes()).as_bytes()
  }

  pub const fn aggregate_claim(&self) -> &FlockAggregateClaimV1 {
    &self.aggregate_claim
  }

  pub const fn root_relation_digest(&self) -> &[u8; 32] {
    &self.root_relation_digest
  }

  pub const fn flock_config_digest(&self) -> &[u8; 32] {
    &self.flock_config_digest
  }
}

/// Strict transport for a final Flock Stage 2 root proof.
///
/// Parsing establishes only canonical framing. Acceptance also requires a
/// native or in-circuit Flock verifier under an externally expected statement,
/// relation, catalog, and configuration.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FlockStage2RootArtifactV1 {
  statement: FlockStage2RootStatementV1,
  proof: Vec<u8>,
}

impl FlockStage2RootArtifactV1 {
  pub fn new(
    statement: FlockStage2RootStatementV1,
    proof: Vec<u8>,
  ) -> Result<Self> {
    if proof.is_empty() {
      bail!("Flock Stage 2 root proof is empty");
    }
    if proof.len() > MAX_FLOCK_STAGE2_PROOF_BYTES {
      bail!(
        "Flock Stage 2 root proof exceeds {MAX_FLOCK_STAGE2_PROOF_BYTES} bytes"
      );
    }
    Ok(Self { statement, proof })
  }

  pub fn from_bytes(bytes: &[u8]) -> Result<Self> {
    if bytes.len() < FLOCK_STAGE2_ROOT_ARTIFACT_HEADER_BYTES {
      bail!("truncated Flock Stage 2 root artifact header");
    }
    if &bytes[..8] != FLOCK_STAGE2_ROOT_ARTIFACT_MAGIC {
      bail!("invalid Flock Stage 2 root artifact magic");
    }
    let version = u16::from_le_bytes(bytes[8..10].try_into().expect("2 bytes"));
    if version != FLOCK_STAGE2_ROOT_ARTIFACT_VERSION {
      bail!("unsupported Flock Stage 2 root artifact version {version}");
    }
    let statement_len = usize::try_from(u32::from_le_bytes(
      bytes[10..14].try_into().expect("4 bytes"),
    ))
    .expect("u32 fits usize");
    if statement_len != FLOCK_STAGE2_ROOT_STATEMENT_BYTES {
      bail!("invalid Flock Stage 2 root statement length {statement_len}");
    }
    let proof_len = usize::try_from(u64::from_le_bytes(
      bytes[14..22].try_into().expect("8 bytes"),
    ))
    .map_err(|_length_error| {
      anyhow::anyhow!("Flock Stage 2 proof length does not fit usize")
    })?;
    if proof_len == 0 {
      bail!("Flock Stage 2 root proof is empty");
    }
    if proof_len > MAX_FLOCK_STAGE2_PROOF_BYTES {
      bail!(
        "Flock Stage 2 root proof exceeds {MAX_FLOCK_STAGE2_PROOF_BYTES} bytes"
      );
    }
    let expected_len = FLOCK_STAGE2_ROOT_ARTIFACT_HEADER_BYTES
      .checked_add(statement_len)
      .and_then(|length| length.checked_add(proof_len))
      .ok_or_else(|| {
        anyhow::anyhow!("Flock Stage 2 artifact length overflow")
      })?;
    if bytes.len() != expected_len {
      bail!(
        "Flock Stage 2 root artifact is {} bytes; header declares {expected_len}",
        bytes.len()
      );
    }
    let statement_end = FLOCK_STAGE2_ROOT_ARTIFACT_HEADER_BYTES + statement_len;
    let statement = FlockStage2RootStatementV1::from_bytes(
      &bytes[FLOCK_STAGE2_ROOT_ARTIFACT_HEADER_BYTES..statement_end],
    )?;
    Self::new(statement, bytes[statement_end..].to_vec())
  }

  pub fn to_bytes(&self) -> Vec<u8> {
    let statement = self.statement.to_bytes();
    let mut bytes = Vec::with_capacity(
      FLOCK_STAGE2_ROOT_ARTIFACT_HEADER_BYTES
        + statement.len()
        + self.proof.len(),
    );
    bytes.extend_from_slice(FLOCK_STAGE2_ROOT_ARTIFACT_MAGIC);
    bytes.extend_from_slice(&FLOCK_STAGE2_ROOT_ARTIFACT_VERSION.to_le_bytes());
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

  pub fn ensure_statement(
    &self,
    expected: &FlockStage2RootStatementV1,
  ) -> Result<()> {
    if &self.statement != expected {
      bail!(
        "Flock Stage 2 artifact statement does not match the expected root"
      );
    }
    Ok(())
  }

  pub const fn statement(&self) -> &FlockStage2RootStatementV1 {
    &self.statement
  }

  pub fn proof_bytes(&self) -> &[u8] {
    &self.proof
  }
}

fn digest_at(bytes: &[u8], offset: usize) -> [u8; 32] {
  bytes[offset..offset + 32].try_into().expect("digest slice")
}

#[cfg(test)]
mod tests {
  use super::*;

  fn aggregate_claim() -> FlockAggregateClaimV1 {
    FlockAggregateClaimV1::new([0x11; 32], [0x22; 32], [0x55; 32])
  }

  fn statement() -> FlockStage2RootStatementV1 {
    FlockStage2RootStatementV1::new(aggregate_claim(), [0x33; 32], [0x44; 32])
  }

  #[test]
  fn aggregate_claim_round_trip_is_exact() {
    let claim = aggregate_claim();
    let bytes = claim.to_bytes();
    assert_eq!(bytes.len(), FLOCK_AGGREGATE_CLAIM_BYTES);
    assert_eq!(&bytes[..8], FLOCK_AGGREGATE_CLAIM_DOMAIN);
    assert_eq!(&bytes[8..40], &[0x11; 32]);
    assert_eq!(&bytes[40..72], &[0x22; 32]);
    assert_eq!(&bytes[72..104], &[0x55; 32]);
    assert_eq!(FlockAggregateClaimV1::from_bytes(&bytes).unwrap(), claim);
  }

  #[test]
  fn root_statement_round_trip_preserves_field_order() {
    let statement = statement();
    let bytes = statement.to_bytes();
    assert_eq!(bytes.len(), FLOCK_STAGE2_ROOT_STATEMENT_BYTES);
    assert_eq!(&bytes[..8], FLOCK_STAGE2_ROOT_STATEMENT_DOMAIN);
    assert_eq!(&bytes[8..40], &[0x11; 32]);
    assert_eq!(&bytes[40..72], &[0x22; 32]);
    assert_eq!(&bytes[72..104], &[0x33; 32]);
    assert_eq!(&bytes[104..136], &[0x44; 32]);
    assert_eq!(&bytes[136..168], &[0x55; 32]);
    assert_eq!(
      FlockStage2RootStatementV1::from_bytes(&bytes).unwrap(),
      statement
    );
  }

  #[test]
  fn statement_parsers_reject_wrong_domains_and_extensions() {
    let mut claim = aggregate_claim().to_bytes();
    claim[0] ^= 1;
    assert!(FlockAggregateClaimV1::from_bytes(&claim).is_err());

    let mut root = statement().to_bytes();
    root.push(0);
    assert!(FlockStage2RootStatementV1::from_bytes(&root).is_err());
  }

  #[test]
  fn root_artifact_has_strict_framing_and_expected_statement() {
    let statement = statement();
    let artifact =
      FlockStage2RootArtifactV1::new(statement.clone(), vec![1, 2, 3]).unwrap();
    let bytes = artifact.to_bytes();
    let decoded = FlockStage2RootArtifactV1::from_bytes(&bytes).unwrap();
    assert_eq!(decoded, artifact);
    decoded.ensure_statement(&statement).unwrap();

    let wrong = FlockStage2RootStatementV1::new(
      aggregate_claim(),
      [0xaa; 32],
      [0x44; 32],
    );
    assert!(decoded.ensure_statement(&wrong).is_err());

    let mut extended = bytes.clone();
    extended.push(0);
    assert!(FlockStage2RootArtifactV1::from_bytes(&extended).is_err());

    let mut wrong_magic = bytes;
    wrong_magic[0] ^= 1;
    assert!(FlockStage2RootArtifactV1::from_bytes(&wrong_magic).is_err());
  }
}
