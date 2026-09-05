use anyhow::{Context, Result, bail};
use bincode::Options;
use ix_terminal::Stage2RootStatementV1;
use serde::{Deserialize, Serialize};
use std::{
  ffi::OsString,
  fs::{self, File, OpenOptions},
  io::{ErrorKind, Read, Write},
  path::{Path, PathBuf},
  sync::atomic::{AtomicU64, Ordering},
};

use crate::config::FlockConfigV1;

pub const STAGE3_STATEMENT_DOMAIN: &[u8; 8] = b"IXFLK301";
pub const STAGE3_STATEMENT_BYTES: usize = 8 + 32 + 32 + 32;
const ARTIFACT_MAGIC: &[u8; 8] = b"IXFLOCK3";
const ARTIFACT_VERSION: u16 = 1;
const ARTIFACT_HEADER_BYTES: usize = 8 + 2 + 4 + 8;
pub const MAX_STAGE3_PROOF_BYTES: usize = 64 * 1024 * 1024;
pub const MAX_STAGE3_ARTIFACT_BYTES: usize =
  ARTIFACT_HEADER_BYTES + STAGE3_STATEMENT_BYTES + MAX_STAGE3_PROOF_BYTES;
const PRODUCTION_PAYLOAD_MAGIC: [u8; 8] = *b"IXFLK3P1";
const PRODUCTION_PAYLOAD_VERSION: u16 = 1;
static NEXT_TEMP_FILE: AtomicU64 = AtomicU64::new(0);

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
    if proof.len() > MAX_STAGE3_PROOF_BYTES {
      bail!("Stage 3 proof exceeds {MAX_STAGE3_PROOF_BYTES} bytes");
    }
    Ok(Self { statement, proof })
  }

  pub fn to_bytes(&self) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(self.encoded_len());
    self.write_encoded(&mut bytes).expect("write artifact to Vec");
    bytes
  }

  pub fn encoded_len(&self) -> usize {
    ARTIFACT_HEADER_BYTES + STAGE3_STATEMENT_BYTES + self.proof.len()
  }

  fn write_encoded(&self, writer: &mut impl Write) -> std::io::Result<()> {
    writer.write_all(ARTIFACT_MAGIC)?;
    writer.write_all(&ARTIFACT_VERSION.to_le_bytes())?;
    writer.write_all(&(STAGE3_STATEMENT_BYTES as u32).to_le_bytes())?;
    writer.write_all(&(self.proof.len() as u64).to_le_bytes())?;
    writer.write_all(&self.statement.to_bytes())?;
    writer.write_all(&self.proof)
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
    if proof_len > MAX_STAGE3_PROOF_BYTES {
      bail!("Stage 3 proof exceeds {MAX_STAGE3_PROOF_BYTES} bytes");
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

  /// Read a strictly bounded artifact without first allocating according to
  /// an untrusted file size.
  pub fn read_from_path(path: impl AsRef<Path>) -> Result<Self> {
    let path = path.as_ref();
    let file = File::open(path)
      .with_context(|| format!("open Stage 3 artifact {}", path.display()))?;
    let declared_len = file
      .metadata()
      .with_context(|| format!("stat Stage 3 artifact {}", path.display()))?
      .len();
    let maximum = u64::try_from(MAX_STAGE3_ARTIFACT_BYTES)
      .expect("Stage 3 artifact limit fits u64");
    if declared_len > maximum {
      bail!(
        "Stage 3 artifact {} is {declared_len} bytes; maximum is {maximum}",
        path.display()
      );
    }

    let mut bytes = Vec::with_capacity(
      usize::try_from(declared_len).context("Stage 3 artifact size")?,
    );
    file
      .take(maximum + 1)
      .read_to_end(&mut bytes)
      .with_context(|| format!("read Stage 3 artifact {}", path.display()))?;
    if bytes.len() > MAX_STAGE3_ARTIFACT_BYTES {
      bail!(
        "Stage 3 artifact {} grew beyond {MAX_STAGE3_ARTIFACT_BYTES} bytes while being read",
        path.display()
      );
    }
    Self::from_bytes(&bytes)
      .with_context(|| format!("decode Stage 3 artifact {}", path.display()))
  }

  /// Durably install an artifact in the destination directory. Temporary
  /// files are created exclusively, and an existing destination is never
  /// overwritten.
  pub fn write_atomic(&self, path: impl AsRef<Path>) -> Result<()> {
    Stage3ArtifactWriterV1::reserve(path)?.write(self)
  }
}

/// Reserve an exclusive temporary file before doing expensive proving work.
/// This checks destination existence, directory writability and hard-link
/// support, but does not promise free disk space or lock the final name.
/// Installation still atomically refuses a concurrent writer's destination.
pub struct Stage3ArtifactWriterV1 {
  destination: PathBuf,
  temporary: PathBuf,
  file: File,
}

impl Stage3ArtifactWriterV1 {
  pub fn reserve(path: impl AsRef<Path>) -> Result<Self> {
    let path = path.as_ref();
    if path.file_name().is_none() {
      bail!("Stage 3 artifact path has no file name: {}", path.display());
    }
    match fs::symlink_metadata(path) {
      Ok(_) => {
        bail!("refusing to overwrite Stage 3 artifact {}", path.display())
      },
      Err(error) if error.kind() == ErrorKind::NotFound => {},
      Err(error) => {
        return Err(error).with_context(|| {
          format!("stat artifact destination {}", path.display())
        });
      },
    }
    let parent = artifact_parent(path);
    let (temporary, file) = create_temporary(parent)?;
    let reservation = Self { destination: path.to_owned(), temporary, file };
    // A predictable but exclusively created scratch name is safe here: a
    // competing entry fails closed and is never removed by this reservation.
    let probe = reservation.temporary.with_extension("link-probe");
    fs::hard_link(&reservation.temporary, &probe).with_context(|| {
      format!("check atomic artifact installation in {}", parent.display())
    })?;
    fs::remove_file(&probe).with_context(|| {
      format!("remove artifact link probe {}", probe.display())
    })?;
    Ok(reservation)
  }

  pub fn write(mut self, artifact: &Stage3ArtifactV1) -> Result<()> {
    artifact.write_encoded(&mut self.file).with_context(|| {
      format!("write temporary artifact {}", self.temporary.display())
    })?;
    self.file.sync_all().with_context(|| {
      format!("sync temporary artifact {}", self.temporary.display())
    })?;

    fs::hard_link(&self.temporary, &self.destination).with_context(|| {
      if fs::symlink_metadata(&self.destination).is_ok() {
        format!(
          "refusing to overwrite Stage 3 artifact {}",
          self.destination.display()
        )
      } else {
        format!("install Stage 3 artifact {}", self.destination.display())
      }
    })?;
    fs::remove_file(&self.temporary).with_context(|| {
      format!("remove temporary artifact {}", self.temporary.display())
    })?;
    let parent = artifact_parent(&self.destination);
    File::open(parent)
      .and_then(|directory| directory.sync_all())
      .with_context(|| {
        format!(
          "artifact installed at {} but directory sync failed",
          self.destination.display()
        )
      })?;
    Ok(())
  }
}

impl Drop for Stage3ArtifactWriterV1 {
  fn drop(&mut self) {
    let _ = fs::remove_file(&self.temporary);
  }
}

fn artifact_parent(path: &Path) -> &Path {
  path
    .parent()
    .filter(|parent| !parent.as_os_str().is_empty())
    .unwrap_or_else(|| Path::new("."))
}

fn create_temporary(parent: &Path) -> Result<(PathBuf, File)> {
  for _ in 0..1_024 {
    let nonce = NEXT_TEMP_FILE.fetch_add(1, Ordering::Relaxed);
    let temporary_name = OsString::from(format!(
      ".ix-flock-stage3-{}-{nonce}.tmp",
      std::process::id()
    ));
    let temporary = parent.join(temporary_name);
    match OpenOptions::new().write(true).create_new(true).open(&temporary) {
      Ok(file) => return Ok((temporary, file)),
      Err(error) if error.kind() == ErrorKind::AlreadyExists => {},
      Err(error) => {
        return Err(error).with_context(|| {
          format!("create temporary artifact {}", temporary.display())
        });
      },
    }
  }
  bail!(
    "could not reserve a unique temporary Stage 3 artifact in {}",
    parent.display()
  )
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
    if bytes.len() > MAX_STAGE3_PROOF_BYTES {
      bail!(
        "Stage 3 production payload exceeds {MAX_STAGE3_PROOF_BYTES} bytes"
      );
    }
    Ok(bytes)
  }

  pub(crate) fn decode(bytes: &[u8]) -> Result<Self> {
    let payload: Self = bincode::DefaultOptions::new()
      .with_fixint_encoding()
      .with_limit(MAX_STAGE3_PROOF_BYTES as u64)
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
    assert_eq!(artifact.encoded_len(), bytes.len());
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

  #[test]
  fn artifact_file_io_is_bounded_atomic_and_no_clobber() {
    let nonce = NEXT_TEMP_FILE.fetch_add(1, Ordering::Relaxed);
    let directory = std::env::temp_dir().join(format!(
      "ix-flock-stage3-artifact-test-{}-{nonce}",
      std::process::id()
    ));
    fs::create_dir(&directory).unwrap();
    let path = directory.join("root.stage3.flock");

    let artifact = Stage3ArtifactV1::new(statement(), vec![1, 2, 3]).unwrap();
    // An abandoned reservation removes only its own scratch file and never
    // creates the final destination, including after a failed preflight.
    let reservation = Stage3ArtifactWriterV1::reserve(&path).unwrap();
    assert!(!path.exists());
    assert_eq!(fs::read_dir(&directory).unwrap().count(), 1);
    drop(reservation);
    assert_eq!(fs::read_dir(&directory).unwrap().count(), 0);
    assert!(
      Stage3ArtifactWriterV1::reserve(directory.join("missing/root.flock"))
        .is_err()
    );

    artifact.write_atomic(&path).unwrap();
    assert_eq!(Stage3ArtifactV1::read_from_path(&path).unwrap(), artifact);

    let replacement = Stage3ArtifactV1::new(statement(), vec![4, 5]).unwrap();
    let error = replacement.write_atomic(&path).unwrap_err().to_string();
    assert!(error.contains("refusing to overwrite"));
    assert_eq!(Stage3ArtifactV1::read_from_path(&path).unwrap(), artifact);
    assert_eq!(fs::read_dir(&directory).unwrap().count(), 1);

    fs::remove_file(&path).unwrap();
    let concurrent_path =
      std::sync::Arc::new(directory.join("concurrent.flock"));
    let contenders = [artifact.clone(), replacement.clone()].map(|artifact| {
      let path = std::sync::Arc::clone(&concurrent_path);
      std::thread::spawn(move || artifact.write_atomic(path.as_path()))
    });
    let outcomes = contenders.map(|thread| thread.join().unwrap());
    assert_eq!(outcomes.iter().filter(|outcome| outcome.is_ok()).count(), 1);
    let installed =
      Stage3ArtifactV1::read_from_path(concurrent_path.as_path()).unwrap();
    assert!(installed == artifact || installed == replacement);
    assert_eq!(fs::read_dir(&directory).unwrap().count(), 1);
    fs::remove_file(concurrent_path.as_path()).unwrap();

    let oversized = directory.join("oversized.stage3.flock");
    File::create(&oversized)
      .unwrap()
      .set_len(u64::try_from(MAX_STAGE3_ARTIFACT_BYTES).unwrap() + 1)
      .unwrap();
    assert!(Stage3ArtifactV1::read_from_path(&oversized).is_err());
    fs::remove_file(oversized).unwrap();
    fs::remove_dir(directory).unwrap();
  }
}
