//! Normalized Ignition prefixes authenticated by an externally pinned receipt.

use std::{
  fs::{self, File, OpenOptions},
  io::{self, Read, Seek, SeekFrom, Write},
  path::{Path, PathBuf},
  sync::atomic::{AtomicU64, Ordering},
};

use ark_bn254::{Bn254, G1Affine, G2Affine};
use ark_ec::{AffineRepr, pairing::Pairing};
use ark_ff::Zero;
use p3_maybe_rayon::prelude::*;

use super::super::{PublicSetup, Srs};
use super::{
  Anchors, MAX_G1_POINTS, MAX_PREFIX_LEN,
  points::{decode_g1, decode_g2, encode_g1, encode_g2},
};

const MAGIC: &[u8] = b"multi-stark/bn254/ignition-srs/v1\0";
const G1_BYTES: usize = 64;
const G2_BYTES: usize = 128;
const BLOCK_POINTS: usize = 1 << 16;
const HEADER_BYTES: usize =
  MAGIC.len() + 64 + 3 * 8 + 2 * G1_BYTES + 2 * G2_BYTES;
static NEXT_TEMP: AtomicU64 = AtomicU64::new(0);

/// Pin `digest` through trusted configuration after a successful import.
/// It authenticates the source identity, complete public degree, shifted
/// generators, retained prefix length and every retained G1 chunk digest.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct IgnitionCacheIdentity {
  pub prefix_len: usize,
  pub digest: [u8; 32],
  pub public_setup: PublicSetup,
  pub source_manifest_digest: [u8; 32],
}

fn invalid(
  message: impl Into<Box<dyn std::error::Error + Send + Sync>>,
) -> io::Error {
  io::Error::new(io::ErrorKind::InvalidData, message)
}

fn validate_prefix(prefix_len: usize) -> io::Result<()> {
  if prefix_len < 2
    || !prefix_len.is_power_of_two()
    || prefix_len > MAX_PREFIX_LEN
  {
    return Err(io::Error::new(
      io::ErrorKind::InvalidInput,
      format!("Ignition prefix must be a power of two in 2..={MAX_PREFIX_LEN}"),
    ));
  }
  Ok(())
}

fn validate_degree(
  public_setup: PublicSetup,
  prefix_len: usize,
) -> io::Result<()> {
  if public_setup.max_degree >= MAX_G1_POINTS
    || public_setup.max_degree < prefix_len - 1
  {
    return Err(invalid("Ignition public degree does not cover the prefix"));
  }
  Ok(())
}

pub(super) fn validate_anchors(
  g1: &[G1Affine; 2],
  g2: G2Affine,
  tau_g2: G2Affine,
) -> io::Result<()> {
  if g1.iter().any(|point| point.is_zero() || !point.is_on_curve())
    || [g2, tau_g2].iter().any(|point| {
      point.is_zero()
        || !point.is_on_curve()
        || !point.is_in_correct_subgroup_assuming_on_curve()
    })
    || g2 != G2Affine::generator()
  {
    return Err(invalid("invalid Ignition cache anchors"));
  }
  if !Bn254::multi_pairing([g1[0], -G1Affine::generator()], [g2, tau_g2])
    .is_zero()
    || !Bn254::multi_pairing([g1[1], -g1[0]], [g2, tau_g2]).is_zero()
  {
    return Err(invalid("Ignition cache anchors are not a shifted tau basis"));
  }
  Ok(())
}

fn encode_header(
  prefix_len: usize,
  public_setup: PublicSetup,
  source_manifest_digest: [u8; 32],
  anchors: &Anchors,
) -> Vec<u8> {
  let mut header = Vec::with_capacity(HEADER_BYTES);
  header.extend_from_slice(MAGIC);
  header.extend_from_slice(&public_setup.id);
  header.extend_from_slice(&source_manifest_digest);
  header.extend_from_slice(&(public_setup.max_degree as u64).to_le_bytes());
  header.extend_from_slice(&(prefix_len as u64).to_le_bytes());
  header.extend_from_slice(&(BLOCK_POINTS as u64).to_le_bytes());
  for point in &anchors.g1 {
    header.extend_from_slice(&encode_g1(point));
  }
  header.extend_from_slice(&encode_g2(&G2Affine::generator()));
  header.extend_from_slice(&encode_g2(&anchors.tau_g2));
  header
}

fn block_digest(index: usize, bytes: &[u8]) -> [u8; 32] {
  let mut hasher = blake3::Hasher::new();
  hasher.update(b"multi-stark/kzg/bn254/ignition-cache-block/v1");
  hasher.update(&(index as u64).to_le_bytes());
  hasher.update(&(bytes.len() as u64).to_le_bytes());
  hasher.update(bytes);
  *hasher.finalize().as_bytes()
}

fn manifest_digest(header: &[u8], index: &[u8]) -> [u8; 32] {
  let mut hasher = blake3::Hasher::new();
  hasher.update(b"multi-stark/kzg/bn254/ignition-cache-manifest/v1");
  hasher.update(header);
  hasher.update(index);
  *hasher.finalize().as_bytes()
}

struct Temporary(PathBuf);

impl Temporary {
  fn create(destination: &Path) -> io::Result<(Self, File)> {
    if destination.try_exists()? {
      return Err(io::Error::new(
        io::ErrorKind::AlreadyExists,
        "Ignition cache already exists",
      ));
    }
    loop {
      let path = destination.with_extension(format!(
        "{}.{}.partial",
        std::process::id(),
        NEXT_TEMP.fetch_add(1, Ordering::Relaxed)
      ));
      match OpenOptions::new().write(true).create_new(true).open(&path) {
        Ok(file) => return Ok((Self(path), file)),
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {},
        Err(error) => return Err(error),
      }
    }
  }

  fn publish(&self, destination: &Path) -> io::Result<()> {
    // Hard-link publication is atomic and never replaces an existing cache.
    fs::hard_link(&self.0, destination)
  }
}

impl Drop for Temporary {
  fn drop(&mut self) {
    let _ = fs::remove_file(&self.0);
  }
}

pub(super) struct CacheWriter {
  output: File,
  temporary: Temporary,
  destination: PathBuf,
  prefix_len: usize,
  public_setup: PublicSetup,
  source_manifest_digest: [u8; 32],
  points_written: usize,
  first_g1: [Option<G1Affine>; 2],
  pending: Vec<u8>,
  index: Vec<u8>,
  failed: bool,
}

impl CacheWriter {
  pub(super) fn create(
    cache: &Path,
    prefix_len: usize,
    public_setup: PublicSetup,
    source_manifest_digest: [u8; 32],
  ) -> io::Result<Self> {
    validate_prefix(prefix_len)?;
    validate_degree(public_setup, prefix_len)?;
    let (temporary, mut output) = Temporary::create(cache)?;
    output.write_all(&[0; HEADER_BYTES])?;
    Ok(Self {
      output,
      temporary,
      destination: cache.to_path_buf(),
      prefix_len,
      public_setup,
      source_manifest_digest,
      points_written: 0,
      first_g1: [None; 2],
      pending: Vec::with_capacity(prefix_len.min(BLOCK_POINTS) * G1_BYTES),
      index: Vec::with_capacity(prefix_len.div_ceil(BLOCK_POINTS) * 32),
      failed: false,
    })
  }

  pub(super) fn push(&mut self, points: &[G1Affine]) -> io::Result<()> {
    if self.failed {
      return Err(invalid("Ignition cache writer has already failed"));
    }
    let result = self.push_inner(points);
    if result.is_err() {
      self.failed = true;
    }
    result
  }

  fn push_inner(&mut self, points: &[G1Affine]) -> io::Result<()> {
    if points.len() > self.prefix_len - self.points_written {
      return Err(invalid("too many points for the Ignition cache prefix"));
    }
    for point in points {
      if self.points_written < 2 {
        self.first_g1[self.points_written] = Some(*point);
      }
      self.pending.extend_from_slice(&encode_g1(point));
      self.points_written += 1;
      if self.pending.len() == BLOCK_POINTS * G1_BYTES {
        self.flush_block()?;
      }
    }
    Ok(())
  }

  fn flush_block(&mut self) -> io::Result<()> {
    if !self.pending.is_empty() {
      self.output.write_all(&self.pending)?;
      self
        .index
        .extend_from_slice(&block_digest(self.index.len() / 32, &self.pending));
      self.pending.clear();
    }
    Ok(())
  }

  /// Call only after source authentication and complete prefix progression
  /// checks. Until this point the temporary file has no valid cache header.
  pub(super) fn finish(
    mut self,
    anchors: &Anchors,
  ) -> io::Result<IgnitionCacheIdentity> {
    if self.failed || self.points_written != self.prefix_len {
      return Err(invalid("incomplete Ignition cache prefix"));
    }
    if self.first_g1 != anchors.g1.map(Some) {
      return Err(invalid("Ignition cache prefix disagrees with its anchors"));
    }
    validate_anchors(&anchors.g1, G2Affine::generator(), anchors.tau_g2)?;
    self.flush_block()?;
    let header = encode_header(
      self.prefix_len,
      self.public_setup,
      self.source_manifest_digest,
      anchors,
    );
    let digest = manifest_digest(&header, &self.index);
    self.output.write_all(&self.index)?;
    self.output.write_all(&digest)?;
    self.output.seek(SeekFrom::Start(0))?;
    self.output.write_all(&header)?;
    self.output.sync_all()?;
    drop(self.output);
    self.temporary.publish(&self.destination)?;
    Ok(IgnitionCacheIdentity {
      prefix_len: self.prefix_len,
      digest,
      public_setup: self.public_setup,
      source_manifest_digest: self.source_manifest_digest,
    })
  }
}

/// Authenticate the cache with a receipt supplied by trusted configuration.
/// A two-point load reads only the manifest and validates its anchors. Larger
/// loads authenticate complete overlapping chunks before decoding requested
/// points; unrequested chunks are not read. Prefix loads preserve the complete
/// ceremony's public degree and setup identity.
pub fn load_ignition_cache(
  cache: &Path,
  expected_manifest_digest: [u8; 32],
  prefix_len: usize,
) -> io::Result<Srs> {
  load_ignition_cache_with_identity(cache, expected_manifest_digest, prefix_len)
    .map(|(srs, _)| srs)
}

/// Load a prefix and the authenticated identity of its complete cache.
/// The identity's prefix length describes the stored cache, which may be
/// larger than the requested prefix.
pub fn load_ignition_cache_with_identity(
  cache: &Path,
  expected_manifest_digest: [u8; 32],
  prefix_len: usize,
) -> io::Result<(Srs, IgnitionCacheIdentity)> {
  validate_prefix(prefix_len)?;
  if !fs::metadata(cache)?.is_file() {
    return Err(invalid("Ignition cache must be a regular file"));
  }
  let mut file = File::open(cache)?;
  if !file.metadata()?.is_file() {
    return Err(invalid("Ignition cache must be a regular file"));
  }
  let mut header = [0; HEADER_BYTES];
  file.read_exact(&mut header)?;
  if !header.starts_with(MAGIC) {
    return Err(invalid("Ignition cache format or curve mismatch"));
  }
  let numbers = MAGIC.len() + 64;
  let number = |offset: usize| {
    u64::from_le_bytes(
      header[numbers + offset..numbers + offset + 8]
        .try_into()
        .expect("fixed header field"),
    )
  };
  let stored_len = usize::try_from(number(8)).map_err(invalid)?;
  validate_prefix(stored_len).map_err(invalid)?;
  let public_setup = PublicSetup {
    max_degree: usize::try_from(number(0)).map_err(invalid)?,
    id: header[MAGIC.len()..MAGIC.len() + 32]
      .try_into()
      .expect("fixed header field"),
  };
  validate_degree(public_setup, stored_len)?;
  if number(16) != BLOCK_POINTS as u64 {
    return Err(invalid("Ignition cache block size mismatch"));
  }
  if prefix_len > stored_len {
    return Err(invalid("Ignition cache prefix is smaller than requested"));
  }
  let index_bytes = stored_len
    .div_ceil(BLOCK_POINTS)
    .checked_mul(32)
    .ok_or_else(|| invalid("Ignition cache index length overflow"))?;
  let index_offset = u64::try_from(stored_len)
    .map_err(invalid)?
    .checked_mul(G1_BYTES as u64)
    .and_then(|bytes| bytes.checked_add(HEADER_BYTES as u64))
    .ok_or_else(|| invalid("Ignition cache data length overflow"))?;
  let expected_bytes = index_offset
    .checked_add(u64::try_from(index_bytes).map_err(invalid)?)
    .and_then(|bytes| bytes.checked_add(32))
    .ok_or_else(|| invalid("Ignition cache total length overflow"))?;
  if file.metadata()?.len() != expected_bytes {
    return Err(invalid("Ignition cache has the wrong length"));
  }
  file.seek(SeekFrom::Start(index_offset))?;
  let mut index = vec![0; index_bytes];
  file.read_exact(&mut index)?;
  let mut declared_digest = [0; 32];
  file.read_exact(&mut declared_digest)?;
  if declared_digest != expected_manifest_digest
    || manifest_digest(&header, &index) != expected_manifest_digest
  {
    return Err(invalid(
      "Ignition cache does not match the pinned manifest digest",
    ));
  }
  let g1_offset = numbers + 24;
  let g2_offset = g1_offset + 2 * G1_BYTES;
  let g1_anchors = [
    decode_g1(&header[g1_offset..g1_offset + G1_BYTES])?,
    decode_g1(&header[g1_offset + G1_BYTES..g2_offset])?,
  ];
  let g2 = decode_g2(&header[g2_offset..g2_offset + G2_BYTES])?;
  let tau_g2 = decode_g2(&header[g2_offset + G2_BYTES..])?;
  validate_anchors(&g1_anchors, g2, tau_g2)?;
  let mut g1 = Vec::new();
  g1.try_reserve_exact(prefix_len).map_err(io::Error::other)?;
  if prefix_len == 2 {
    g1.extend_from_slice(&g1_anchors);
  } else {
    file.seek(SeekFrom::Start(HEADER_BYTES as u64))?;
    let mut buffer = vec![0; stored_len.min(BLOCK_POINTS) * G1_BYTES];
    for block_index in 0..prefix_len.div_ceil(BLOCK_POINTS) {
      let start = block_index * BLOCK_POINTS;
      let count = (stored_len - start).min(BLOCK_POINTS);
      let bytes = &mut buffer[..count * G1_BYTES];
      file.read_exact(bytes)?;
      if block_digest(block_index, bytes)
        != index[block_index * 32..(block_index + 1) * 32]
      {
        return Err(invalid(format!(
          "Ignition cache chunk {block_index} digest mismatch"
        )));
      }
      let needed = (prefix_len - start).min(count);
      let points = bytes[..needed * G1_BYTES]
        .par_chunks_exact(G1_BYTES)
        .map(decode_g1)
        .collect::<io::Result<Vec<_>>>()?;
      g1.extend(points);
    }
    if g1[..2] != g1_anchors {
      return Err(invalid(
        "Ignition cache G1 anchors disagree with its prefix",
      ));
    }
  }
  let identity = IgnitionCacheIdentity {
    prefix_len: stored_len,
    digest: expected_manifest_digest,
    public_setup,
    source_manifest_digest: header[MAGIC.len() + 32..MAGIC.len() + 64]
      .try_into()
      .expect("fixed header field"),
  };
  Ok((Srs { g1, g2, tau_g2, public_setup }, identity))
}
