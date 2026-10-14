//! Authenticated import of Filecoin's stock phase-one `challenge_19`.
//!
//! The source pin is the final Golem participant's published BLAKE2b-512 digest:
//! <https://github.com/arielgabizon/perpetualpowersoftau/blob/master/0018_GolemFactory_response/README.md>.
//! Filecoin identifies this artifact, without an additional randomness beacon, at
//! <https://github.com/filecoin-project/phase2-attestations#phase1>.
//!
//! Import verifies the entire source digest, and checks canonical coordinates,
//! curve membership, subgroup membership and the power progression of the retained
//! G1 prefix against the G2 anchors. It does not repeat the ceremony transcript.
//! The normalized cache has an independently pinned manifest and authenticated
//! chunks, so subsequent loads need read only the requested prefix. Its manifest
//! digest must come from the successful import through trusted configuration;
//! reading a digest supplied alongside an untrusted cache would not authenticate it.

use std::{
  fs::{self, File, OpenOptions},
  io::{self, Read, Seek, SeekFrom, Write},
  path::{Path, PathBuf},
  sync::atomic::{AtomicU64, Ordering},
};

use ark_bls12_381::{Bls12_381, Fr, G1Affine, G1Projective, G2Affine};
use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM, pairing::Pairing};
use ark_ff::{Field, PrimeField, Zero};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use p3_maybe_rayon::prelude::*;

use super::{PublicSetup, Srs};

/// Official uncompressed phase-one output, approximately 72 GiB.
pub const FILECOIN_CHALLENGE_19_URL: &str =
  "https://trusted-setup.filecoin.io/phase1/challenge_19";
/// Avail's complete copy of the same file. Any mirror is acceptable: the import
/// authenticates the bytes against the published digest.
pub const FILECOIN_CHALLENGE_19_MIRROR_URL: &str =
  "https://srs.availproject.org/challenge_19";
/// Maximum supported honest polynomial length; this is not a public degree bound.
pub const FILECOIN_MAX_TRACE_LEN: usize = 1 << 27;
/// The ceremony publishes G1 powers with exponents `0..=2^28-2`.
pub const FILECOIN_PUBLIC_MAX_DEGREE: usize = (1 << 28) - 2;
/// BLAKE2b-512 of the complete artifact, including its 64-byte transcript header.
pub const FILECOIN_CHALLENGE_19_BLAKE2B: [u8; 64] = [
  0x5a, 0x26, 0x01, 0x5b, 0xa2, 0x7d, 0x81, 0x64, 0x15, 0x24, 0x07, 0xda, 0x8f,
  0x9b, 0x87, 0xe4, 0x75, 0x93, 0xf1, 0x7a, 0xe4, 0xc2, 0x60, 0xe4, 0x67, 0xba,
  0xc2, 0xba, 0x9d, 0xda, 0x6f, 0x66, 0xc1, 0x5f, 0xa3, 0x52, 0x48, 0x76, 0x04,
  0xd1, 0x35, 0x0e, 0xf3, 0x3a, 0x3b, 0xfe, 0xdb, 0x0d, 0x99, 0xe3, 0x7b, 0x61,
  0x91, 0x61, 0xe2, 0x75, 0x45, 0x01, 0x73, 0x66, 0x27, 0x4d, 0xf7, 0x6b,
];

/// Manifest receipt of the complete `2^27` prefix cache that
/// [`import_filecoin_challenge`] produces from the authenticated source. The
/// import is deterministic, so an independent import reproduces this digest.
pub const FILECOIN_PREFIX_2P27_MANIFEST_BLAKE3: [u8; 32] = [
  0x14, 0x42, 0x38, 0x60, 0x05, 0xc4, 0xe4, 0xa2, 0xeb, 0xc2, 0x3c, 0x10, 0x96,
  0x94, 0xeb, 0x9b, 0xb1, 0x6f, 0xe5, 0x4b, 0xc5, 0x70, 0x8f, 0x03, 0x80, 0x65,
  0x8a, 0xc9, 0x9a, 0x37, 0xf1, 0x0a,
];
/// Manifest receipt of the 256-power prefix cache used by opt-in tests.
pub const FILECOIN_PREFIX_2P8_MANIFEST_BLAKE3: [u8; 32] = [
  0x18, 0x5c, 0x55, 0x6e, 0x5f, 0x5f, 0x0c, 0x67, 0xdd, 0xc0, 0xc8, 0xac, 0x21,
  0x0c, 0x8b, 0x11, 0xd1, 0xa4, 0x85, 0x74, 0xde, 0xfb, 0xc4, 0x42, 0x99, 0xdc,
  0x71, 0x27, 0x47, 0xa0, 0x50, 0x7d,
];

const MAGIC: &[u8] = b"multi-stark/bls12-381/filecoin-srs/v1\0";
const G1_BYTES: usize = 96;
const G2_BYTES: usize = 192;
const BLOCK_POINTS: usize = 1 << 18;
const HEADER_BYTES: usize =
  MAGIC.len() + 64 + 3 * 8 + 2 * G1_BYTES + 2 * G2_BYTES;
static NEXT_TEMP: AtomicU64 = AtomicU64::new(0);

#[derive(Clone, Copy)]
struct ChallengeSpec {
  power: u32,
  digest: [u8; 64],
  block_points: usize,
}

const FILECOIN: ChallengeSpec = ChallengeSpec {
  power: 27,
  digest: FILECOIN_CHALLENGE_19_BLAKE2B,
  block_points: BLOCK_POINTS,
};

impl ChallengeSpec {
  fn max_len(self) -> usize {
    1usize << self.power
  }

  fn max_degree(self) -> usize {
    2 * self.max_len() - 2
  }

  fn g2_offset(self) -> u64 {
    64 + (self.max_degree() as u64 + 1) * G1_BYTES as u64
  }

  fn source_bytes(self) -> u64 {
    // Header, tau G1, tau G2, alpha G1, beta G1, and beta G2.
    64 + (self.max_degree() as u64 + 1) * G1_BYTES as u64
      + self.max_len() as u64 * (G2_BYTES + 2 * G1_BYTES) as u64
      + G2_BYTES as u64
  }

  fn setup_id(self) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"multi-stark/kzg/filecoin-challenge19/v1");
    hasher.update(&self.digest);
    hasher.update(&(self.max_degree() as u64).to_le_bytes());
    *hasher.finalize().as_bytes()
  }
}

/// Stable ceremony identity, independent of retained prefix or cache layout.
pub fn filecoin_setup_id() -> [u8; 32] {
  FILECOIN.setup_id()
}

/// A receipt for a successfully authenticated import.
///
/// Pin `digest` in trusted prover/verifier configuration. It authenticates the
/// manifest, including the anchors and every G1 chunk digest, not merely a file
/// checksum declared by the cache itself.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct FilecoinCacheIdentity {
  pub prefix_len: usize,
  pub digest: [u8; 32],
}

/// Validate stock `challenge_19` and atomically create a normalized prefix cache.
///
/// This is one-time provisioning: it reads all 72 GiB of the source and performs
/// subgroup and batched progression checks for `prefix_len` G1 powers. Working
/// memory is bounded by a chunk, independent of the retained prefix length. The
/// destination must not exist. A failed import never publishes a usable cache.
pub fn import_filecoin_challenge(
  source: &Path,
  cache: &Path,
  prefix_len: usize,
) -> io::Result<FilecoinCacheIdentity> {
  import_challenge(source, cache, prefix_len, FILECOIN)
}

/// Load a requested prefix using an externally pinned import receipt.
///
/// `prefix_len == 2` reads only the small authenticated manifest. Larger prefixes
/// authenticate their chunks before decoding. Unrequested chunks are not read.
/// Subgroup and progression checks are inherited from the authenticated import;
/// reloads check canonical coordinates and curve membership, plus all four
/// manifest anchors. This avoids repeating an expensive provisioning operation.
pub fn load_filecoin_cache(
  cache: &Path,
  expected_manifest_digest: [u8; 32],
  prefix_len: usize,
) -> io::Result<Srs> {
  load_cache(cache, expected_manifest_digest, prefix_len, FILECOIN)
}

fn invalid(message: impl ToString) -> io::Error {
  io::Error::new(io::ErrorKind::InvalidData, message.to_string())
}

fn validate_prefix(prefix_len: usize, spec: ChallengeSpec) -> io::Result<()> {
  if prefix_len < 2
    || !prefix_len.is_power_of_two()
    || prefix_len > spec.max_len()
  {
    return Err(io::Error::new(
      io::ErrorKind::InvalidInput,
      format!(
        "Filecoin prefix must be a power of two in 2..={}",
        spec.max_len()
      ),
    ));
  }
  Ok(())
}

fn decode_g1(bytes: &[u8], subgroup: bool) -> io::Result<G1Affine> {
  // Both Filecoin's pairing 0.16.2 and arkworks 0.5 use big-endian x || y,
  // with the standard compression/infinity/sign flags in the first byte.
  let point =
    G1Affine::deserialize_uncompressed_unchecked(bytes).map_err(invalid)?;
  if point.is_zero()
    || !point.is_on_curve()
    || (subgroup && !point.is_in_correct_subgroup_assuming_on_curve())
  {
    return Err(invalid("invalid Filecoin G1 point"));
  }
  Ok(point)
}

fn decode_g2(bytes: &[u8]) -> io::Result<G2Affine> {
  // The component order is x.c1 || x.c0 || y.c1 || y.c0, not Fq2 serde order.
  let point =
    G2Affine::deserialize_uncompressed_unchecked(bytes).map_err(invalid)?;
  if point.is_zero()
    || !point.is_on_curve()
    || !point.is_in_correct_subgroup_assuming_on_curve()
  {
    return Err(invalid("invalid Filecoin G2 point"));
  }
  Ok(point)
}

struct Anchors {
  g1: [G1Affine; 2],
  g2: [G2Affine; 2],
}

impl Anchors {
  fn read(source: &mut File, spec: ChallengeSpec) -> io::Result<Self> {
    let mut g1 = [0; 2 * G1_BYTES];
    source.seek(SeekFrom::Start(64))?;
    source.read_exact(&mut g1)?;
    let mut g2 = [0; 2 * G2_BYTES];
    source.seek(SeekFrom::Start(spec.g2_offset()))?;
    source.read_exact(&mut g2)?;
    Self::decode(&g1, &g2)
  }

  fn decode(g1: &[u8], g2: &[u8]) -> io::Result<Self> {
    let anchors = Self {
      g1: [
        decode_g1(&g1[..G1_BYTES], true)?,
        decode_g1(&g1[G1_BYTES..], true)?,
      ],
      g2: [decode_g2(&g2[..G2_BYTES])?, decode_g2(&g2[G2_BYTES..])?],
    };
    if anchors.g1[0] != G1Affine::generator()
      || anchors.g2[0] != G2Affine::generator()
    {
      return Err(invalid("Filecoin generators do not match BLS12-381"));
    }
    if !Bls12_381::multi_pairing(
      [anchors.g1[1], -anchors.g1[0]],
      [anchors.g2[0], anchors.g2[1]],
    )
    .is_zero()
    {
      return Err(invalid("Filecoin G1/G2 tau anchors disagree"));
    }
    Ok(anchors)
  }
}

fn encode_header(
  spec: ChallengeSpec,
  prefix_len: usize,
  anchors: &Anchors,
) -> io::Result<Vec<u8>> {
  let mut header = Vec::with_capacity(HEADER_BYTES);
  header.extend_from_slice(MAGIC);
  header.extend_from_slice(&spec.digest);
  header.extend_from_slice(&(spec.max_degree() as u64).to_le_bytes());
  header.extend_from_slice(&(prefix_len as u64).to_le_bytes());
  header.extend_from_slice(&(spec.block_points as u64).to_le_bytes());
  for point in &anchors.g1 {
    point.serialize_uncompressed(&mut header).map_err(invalid)?;
  }
  for point in &anchors.g2 {
    point.serialize_uncompressed(&mut header).map_err(invalid)?;
  }
  Ok(header)
}

fn block_digest(index: usize, bytes: &[u8]) -> [u8; 32] {
  let mut hasher = blake3::Hasher::new();
  hasher.update(b"multi-stark/kzg/filecoin-cache-block/v1");
  hasher.update(&(index as u64).to_le_bytes());
  hasher.update(&(bytes.len() as u64).to_le_bytes());
  hasher.update(bytes);
  *hasher.finalize().as_bytes()
}

fn manifest_digest(header: &[u8], index: &[u8]) -> [u8; 32] {
  let mut hasher = blake3::Hasher::new();
  hasher.update(b"multi-stark/kzg/filecoin-cache-manifest/v1");
  hasher.update(header);
  hasher.update(index);
  *hasher.finalize().as_bytes()
}

struct ProgressionCheck {
  r: Fr,
  next_power: Fr,
  previous: Option<G1Affine>,
  low: G1Projective,
  high: G1Projective,
}

impl ProgressionCheck {
  fn new(spec: ChallengeSpec, prefix_len: usize) -> Self {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"multi-stark/kzg/filecoin-prefix-progression/v1");
    hasher.update(&spec.digest);
    hasher.update(&(prefix_len as u64).to_le_bytes());
    let mut reader = hasher.finalize_xof();
    let r = loop {
      let mut wide = [0; 64];
      reader.fill(&mut wide);
      let r = Fr::from_le_bytes_mod_order(&wide);
      if !r.is_zero() {
        break r;
      }
    };
    Self {
      r,
      next_power: Fr::ONE,
      previous: None,
      low: G1Projective::zero(),
      high: G1Projective::zero(),
    }
  }

  fn absorb(&mut self, points: &[G1Affine]) {
    if let Some(previous) = self.previous {
      // This pair crosses chunk boundaries and cannot be omitted.
      self.low += previous * self.next_power;
      self.high += points[0] * self.next_power;
      self.next_power *= self.r;
    }
    let scalars: Vec<_> = (0..points.len() - 1)
      .map(|_| {
        let scalar = self.next_power;
        self.next_power *= self.r;
        scalar
      })
      .collect();
    self.low += G1Projective::msm(&points[..points.len() - 1], &scalars)
      .expect("equal lengths");
    self.high +=
      G1Projective::msm(&points[1..], &scalars).expect("equal lengths");
    self.previous = points.last().copied();
  }

  fn verify(self, anchors: &Anchors) -> io::Result<()> {
    if !Bls12_381::multi_pairing(
      [self.high.into_affine(), (-self.low).into_affine()],
      anchors.g2,
    )
    .is_zero()
    {
      return Err(invalid("Filecoin G1 prefix is not one tau progression"));
    }
    Ok(())
  }
}

struct Temporary(PathBuf);

impl Temporary {
  fn create(destination: &Path) -> io::Result<(Self, File)> {
    if destination.try_exists()? {
      return Err(io::Error::new(
        io::ErrorKind::AlreadyExists,
        "Filecoin cache already exists",
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
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
        Err(error) => return Err(error),
      }
    }
  }

  fn publish(&self, destination: &Path) -> io::Result<()> {
    // A hard link is atomic and refuses to overwrite an existing receipt's file.
    fs::hard_link(&self.0, destination)
  }
}

impl Drop for Temporary {
  fn drop(&mut self) {
    let _ = fs::remove_file(&self.0);
  }
}

fn hash_exact(
  source: &mut File,
  hasher: &mut blake2b_simd::State,
  mut remaining: u64,
  buffer: &mut [u8],
) -> io::Result<()> {
  while remaining != 0 {
    let count = remaining.min(buffer.len() as u64) as usize;
    source.read_exact(&mut buffer[..count])?;
    hasher.update(&buffer[..count]);
    remaining -= count as u64;
  }
  Ok(())
}

fn import_challenge(
  source: &Path,
  cache: &Path,
  prefix_len: usize,
  spec: ChallengeSpec,
) -> io::Result<FilecoinCacheIdentity> {
  validate_prefix(prefix_len, spec)?;
  let mut source = File::open(source)?;
  if source.metadata()?.len() != spec.source_bytes() {
    return Err(invalid("Filecoin challenge has the wrong length"));
  }
  let anchors = Anchors::read(&mut source, spec)?;
  let header = encode_header(spec, prefix_len, &anchors)?;
  let (temporary, mut output) = Temporary::create(cache)?;
  output.write_all(&header)?;
  let mut index =
    Vec::with_capacity(prefix_len.div_ceil(spec.block_points) * 32);
  let mut hasher = blake2b_simd::State::new();
  let mut previous_digest = [0; 64];
  source.seek(SeekFrom::Start(0))?;
  source.read_exact(&mut previous_digest)?;
  hasher.update(&previous_digest);
  let mut buffer =
    vec![0; (prefix_len.min(spec.block_points) * G1_BYTES).max(1 << 20)];
  let mut progression = ProgressionCheck::new(spec, prefix_len);
  for (block_index, start) in
    (0..prefix_len).step_by(spec.block_points).enumerate()
  {
    let count = (prefix_len - start).min(spec.block_points);
    let bytes = &mut buffer[..count * G1_BYTES];
    source.read_exact(bytes)?;
    hasher.update(bytes);
    let points = bytes
      .par_chunks_exact(G1_BYTES)
      .map(|bytes| decode_g1(bytes, true))
      .collect::<io::Result<Vec<_>>>()?;
    if start == 0 && points[..2] != anchors.g1 {
      return Err(invalid("Filecoin source anchors changed during import"));
    }
    progression.absorb(&points);
    index.extend_from_slice(&block_digest(block_index, bytes));
    output.write_all(bytes)?;
  }
  let remaining_g1_bytes =
    (spec.max_degree() + 1 - prefix_len) as u64 * G1_BYTES as u64;
  hash_exact(&mut source, &mut hasher, remaining_g1_bytes, &mut buffer)?;
  let mut g2_bytes = [0; 2 * G2_BYTES];
  source.read_exact(&mut g2_bytes)?;
  hasher.update(&g2_bytes);
  if g2_bytes != header[HEADER_BYTES - 2 * G2_BYTES..] {
    return Err(invalid("Filecoin source G2 anchors changed during import"));
  }
  let remaining =
    spec.source_bytes() - spec.g2_offset() - g2_bytes.len() as u64;
  hash_exact(&mut source, &mut hasher, remaining, &mut buffer)?;
  if source.read(&mut [0])? != 0 {
    return Err(invalid("trailing bytes in Filecoin challenge"));
  }
  if hasher.finalize().as_bytes() != spec.digest {
    return Err(invalid(
      "Filecoin challenge does not match the published BLAKE2b digest",
    ));
  }
  progression.verify(&anchors)?;
  let digest = manifest_digest(&header, &index);
  output.write_all(&index)?;
  output.write_all(&digest)?;
  output.sync_all()?;
  drop(output);
  temporary.publish(cache)?;
  Ok(FilecoinCacheIdentity { prefix_len, digest })
}

fn load_cache(
  cache: &Path,
  expected_manifest_digest: [u8; 32],
  prefix_len: usize,
  spec: ChallengeSpec,
) -> io::Result<Srs> {
  validate_prefix(prefix_len, spec)?;
  let mut file = File::open(cache)?;
  let mut header = vec![0; HEADER_BYTES];
  file.read_exact(&mut header)?;
  if !header.starts_with(MAGIC)
    || header[MAGIC.len()..MAGIC.len() + 64] != spec.digest
  {
    return Err(invalid("Filecoin cache format or ceremony identity mismatch"));
  }
  let numbers = MAGIC.len() + 64;
  let number = |offset: usize| {
    u64::from_le_bytes(
      header[numbers + offset..numbers + offset + 8].try_into().unwrap(),
    )
  };
  if number(0) != spec.max_degree() as u64
    || number(16) != spec.block_points as u64
  {
    return Err(invalid("Filecoin cache degree range or block size mismatch"));
  }
  let stored_len = usize::try_from(number(8)).map_err(invalid)?;
  validate_prefix(stored_len, spec).map_err(invalid)?;
  if prefix_len > stored_len {
    return Err(invalid("Filecoin cache prefix is smaller than requested"));
  }
  let index_bytes = stored_len.div_ceil(spec.block_points) * 32;
  let index_offset = HEADER_BYTES as u64 + stored_len as u64 * G1_BYTES as u64;
  if file.metadata()?.len() != index_offset + index_bytes as u64 + 32 {
    return Err(invalid("Filecoin cache has the wrong length"));
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
      "Filecoin cache does not match the pinned manifest digest",
    ));
  }
  let g1_offset = numbers + 24;
  let g2_offset = g1_offset + 2 * G1_BYTES;
  let anchors =
    Anchors::decode(&header[g1_offset..g2_offset], &header[g2_offset..])?;
  let mut g1 = Vec::new();
  g1.try_reserve_exact(prefix_len).map_err(io::Error::other)?;
  if prefix_len == 2 {
    g1.extend_from_slice(&anchors.g1);
  } else {
    file.seek(SeekFrom::Start(HEADER_BYTES as u64))?;
    let mut buffer = vec![0; stored_len.min(spec.block_points) * G1_BYTES];
    for block_index in 0..prefix_len.div_ceil(spec.block_points) {
      let start = block_index * spec.block_points;
      let count = (stored_len - start).min(spec.block_points);
      let bytes = &mut buffer[..count * G1_BYTES];
      file.read_exact(bytes)?;
      if block_digest(block_index, bytes)
        != index[block_index * 32..(block_index + 1) * 32]
      {
        return Err(invalid(format!(
          "Filecoin cache chunk {block_index} digest mismatch"
        )));
      }
      let needed = (prefix_len - start).min(count);
      let points = bytes[..needed * G1_BYTES]
        .par_chunks_exact(G1_BYTES)
        .map(|bytes| decode_g1(bytes, false))
        .collect::<io::Result<Vec<_>>>()?;
      g1.extend(points);
    }
    if g1[..2] != anchors.g1 {
      return Err(invalid(
        "Filecoin cache G1 anchors disagree with its prefix",
      ));
    }
  }
  Ok(Srs {
    g1,
    g2: anchors.g2[0],
    tau_g2: anchors.g2[1],
    public_setup: PublicSetup {
      max_degree: spec.max_degree(),
      id: spec.setup_id(),
    },
  })
}

#[cfg(test)]
mod tests {
  use super::*;
  use ark_bls12_381::{Fq, Fq2, G2Projective};
  use ark_ec::PrimeGroup;
  use ark_ff::BigInteger;

  struct Fixture {
    directory: PathBuf,
    source: PathBuf,
    cache: PathBuf,
    spec: ChallengeSpec,
    points: Vec<G1Affine>,
  }

  impl Fixture {
    fn new() -> Self {
      let directory = std::env::temp_dir().join(format!(
        "ix-filecoin-import-{}-{}",
        std::process::id(),
        NEXT_TEMP.fetch_add(1, Ordering::Relaxed)
      ));
      fs::create_dir(&directory).unwrap();
      let mut spec =
        ChallengeSpec { power: 3, digest: [0; 64], block_points: 4 };
      let source = directory.join("challenge");
      let cache = directory.join("cache");
      let tau = Fr::from(7u64);
      let mut bytes = vec![42; 64];
      let points: Vec<_> = (0..=spec.max_degree())
        .map(|i| {
          (G1Projective::generator() * tau.pow([i as u64])).into_affine()
        })
        .collect();
      for point in &points {
        point.serialize_uncompressed(&mut bytes).unwrap();
      }
      for i in 0..spec.max_len() {
        (G2Projective::generator() * tau.pow([i as u64]))
          .into_affine()
          .serialize_uncompressed(&mut bytes)
          .unwrap();
      }
      for scale in [Fr::from(11u64), Fr::from(13u64)] {
        for point in points.iter().take(spec.max_len()) {
          (*point * scale)
            .into_affine()
            .serialize_uncompressed(&mut bytes)
            .unwrap();
        }
      }
      (G2Projective::generator() * Fr::from(13u64))
        .into_affine()
        .serialize_uncompressed(&mut bytes)
        .unwrap();
      assert_eq!(bytes.len() as u64, spec.source_bytes());
      spec.digest = *blake2b_simd::blake2b(&bytes).as_array();
      fs::write(&source, bytes).unwrap();
      Self { directory, source, cache, spec, points }
    }

    fn repin(&mut self) {
      self.spec.digest =
        *blake2b_simd::blake2b(&fs::read(&self.source).unwrap()).as_array();
    }

    fn import(&self) -> io::Result<FilecoinCacheIdentity> {
      import_challenge(
        &self.source,
        &self.cache,
        self.spec.max_len(),
        self.spec,
      )
    }
  }

  impl Drop for Fixture {
    fn drop(&mut self) {
      fs::remove_dir_all(&self.directory).unwrap();
    }
  }

  fn hex<const N: usize>(input: &str) -> [u8; N] {
    assert_eq!(input.len(), N * 2);
    std::array::from_fn(|i| {
      u8::from_str_radix(&input[2 * i..2 * i + 2], 16).unwrap()
    })
  }

  #[test]
  fn pinned_filecoin_encoding_matches_pairing_generator_vectors() {
    let g1 = hex::<96>(concat!(
      "17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb",
      "08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1",
    ));
    let g2 = hex::<192>(concat!(
      "13e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e",
      "024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8",
      "0606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be",
      "0ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801",
    ));
    assert_eq!(decode_g1(&g1, true).unwrap(), G1Affine::generator());
    assert_eq!(decode_g2(&g2).unwrap(), G2Affine::generator());
    let mut serialized = Vec::new();
    G1Affine::generator().serialize_uncompressed(&mut serialized).unwrap();
    assert_eq!(serialized, g1);
    serialized.clear();
    G2Affine::generator().serialize_uncompressed(&mut serialized).unwrap();
    assert_eq!(serialized, g2);
    let mut swapped = g2;
    swapped[..48].copy_from_slice(&g2[48..96]);
    swapped[48..96].copy_from_slice(&g2[..48]);
    assert!(decode_g2(&swapped).is_err());
  }

  #[test]
  fn source_pin_and_public_range_are_exact() {
    assert_eq!(
      FILECOIN_CHALLENGE_19_BLAKE2B,
      hex::<64>(concat!(
        "5a26015ba27d8164152407da8f9b87e47593f17ae4c260e467bac2ba9dda6f66c",
        "15fa352487604d1350ef33a3bfedb0d99e37b619161e27545017366274df76b",
      ))
    );
    assert_eq!(FILECOIN.max_degree(), FILECOIN_PUBLIC_MAX_DEGREE);
    assert_eq!(FILECOIN.source_bytes(), 77_309_411_488);
    assert_eq!(FILECOIN.max_len(), FILECOIN_MAX_TRACE_LEN);
  }

  #[test]
  fn authenticated_prefix_and_manifest_only_loads_preserve_public_degree() {
    let fixture = Fixture::new();
    let receipt = fixture.import().unwrap();
    for prefix_len in [2, 4, 8] {
      let srs =
        load_cache(&fixture.cache, receipt.digest, prefix_len, fixture.spec)
          .unwrap();
      assert_eq!(srs.g1, fixture.points[..prefix_len]);
      let setup = srs.public_setup;
      assert_eq!(setup.max_degree, 14);
      assert_eq!(setup.id, fixture.spec.setup_id());
    }
    assert!(fixture.import().is_err());
    assert!(load_filecoin_cache(&fixture.cache, receipt.digest, 2).is_err());
  }

  #[test]
  fn incorrect_source_pin_and_changed_unused_tail_never_publish_cache() {
    let fixture = Fixture::new();
    let mut bytes = fs::read(&fixture.source).unwrap();
    *bytes.last_mut().unwrap() ^= 1;
    fs::write(&fixture.source, bytes).unwrap();
    assert!(fixture.import().unwrap_err().to_string().contains("BLAKE2b"));
    assert!(!fixture.cache.exists());
    assert_eq!(fs::read_dir(&fixture.directory).unwrap().count(), 1);
  }

  #[test]
  fn malformed_source_length_is_rejected_before_allocation() {
    let fixture = Fixture::new();
    let original = fs::read(&fixture.source).unwrap();
    for bad in [
      original[..original.len() - 1].to_vec(),
      [original.as_slice(), &[0]].concat(),
    ] {
      fs::write(&fixture.source, bad).unwrap();
      assert!(
        fixture.import().unwrap_err().to_string().contains("wrong length")
      );
      assert!(!fixture.cache.exists());
    }
    for prefix in [0, 1, 3, 16, usize::MAX] {
      assert!(
        import_challenge(&fixture.source, &fixture.cache, prefix, fixture.spec)
          .is_err()
      );
    }
  }

  #[test]
  fn checked_decoding_rejects_flags_noncanonical_coordinates_curve_and_subgroup_errors()
   {
    let mut generator = Vec::new();
    G1Affine::generator().serialize_uncompressed(&mut generator).unwrap();
    for flag in [0x20, 0x40, 0x80] {
      let mut bytes = generator.clone();
      bytes[0] |= flag;
      assert!(decode_g1(&bytes, true).is_err());
    }
    let mut noncanonical = generator;
    noncanonical[..48].copy_from_slice(&Fq::MODULUS.to_bytes_be());
    assert!(decode_g1(&noncanonical, true).is_err());
    let mut identity = [0; G1_BYTES];
    identity[0] = 0x40;
    assert!(decode_g1(&identity, true).is_err());
    let mut invalid_curve = [0; G1_BYTES];
    invalid_curve[47] = 1;
    invalid_curve[95] = 1;
    assert!(decode_g1(&invalid_curve, true).is_err());
    let torsion = G1Affine::new_unchecked(Fq::zero(), Fq::from(2u64));
    assert!(torsion.is_on_curve());
    assert!(!torsion.is_in_correct_subgroup_assuming_on_curve());
    let mut bytes = Vec::new();
    torsion.serialize_uncompressed(&mut bytes).unwrap();
    assert!(decode_g1(&bytes, true).is_err());
    assert_eq!(decode_g1(&bytes, false).unwrap(), torsion);
  }

  #[test]
  fn source_interior_subgroup_failure_never_publishes_cache() {
    let mut fixture = Fixture::new();
    let mut bytes = fs::read(&fixture.source).unwrap();
    let mut encoded = Vec::new();
    G1Affine::new_unchecked(Fq::zero(), Fq::from(2u64))
      .serialize_uncompressed(&mut encoded)
      .unwrap();
    bytes[64 + 3 * G1_BYTES..64 + 4 * G1_BYTES].copy_from_slice(&encoded);
    fs::write(&fixture.source, bytes).unwrap();
    fixture.repin();
    assert!(fixture.import().unwrap_err().to_string().contains("G1 point"));
    assert!(!fixture.cache.exists());
  }

  #[test]
  fn g2_decoding_rejects_identity_flags_noncanonical_and_wrong_subgroup() {
    let mut bytes = Vec::new();
    G2Affine::generator().serialize_uncompressed(&mut bytes).unwrap();
    for flag in [0x20, 0x40, 0x80] {
      let mut invalid = bytes.clone();
      invalid[0] |= flag;
      assert!(decode_g2(&invalid).is_err());
    }
    bytes[..48].copy_from_slice(&Fq::MODULUS.to_bytes_be());
    assert!(decode_g2(&bytes).is_err());
    let mut identity = [0; G2_BYTES];
    identity[0] = 0x40;
    assert!(decode_g2(&identity).is_err());
    let outside_subgroup = (0u64..)
      .filter_map(|x| G2Affine::get_point_from_x_unchecked(Fq2::from(x), false))
      .find(|point| !point.is_in_correct_subgroup_assuming_on_curve())
      .unwrap();
    assert!(outside_subgroup.is_on_curve());
    bytes.clear();
    outside_subgroup.serialize_uncompressed(&mut bytes).unwrap();
    assert!(decode_g2(&bytes).is_err());
  }

  #[test]
  fn progression_includes_chunk_boundaries() {
    let mut fixture = Fixture::new();
    let mut bytes = fs::read(&fixture.source).unwrap();
    for i in 4..8 {
      let mut encoded = Vec::new();
      (fixture.points[i] * Fr::from(2u64))
        .into_affine()
        .serialize_uncompressed(&mut encoded)
        .unwrap();
      bytes[64 + i * G1_BYTES..64 + (i + 1) * G1_BYTES]
        .copy_from_slice(&encoded);
    }
    fs::write(&fixture.source, bytes).unwrap();
    fixture.repin();
    assert!(fixture.import().unwrap_err().to_string().contains("progression"));
    assert!(!fixture.cache.exists());
  }

  #[test]
  fn cache_rejects_wrong_receipt_header_index_and_requested_chunk() {
    let fixture = Fixture::new();
    let receipt = fixture.import().unwrap();
    assert!(load_cache(&fixture.cache, [0; 32], 8, fixture.spec).is_err());
    let original = fs::read(&fixture.cache).unwrap();
    for offset in [
      0,
      MAGIC.len(),
      MAGIC.len() + 64,
      HEADER_BYTES - 1,
      HEADER_BYTES,
      HEADER_BYTES + 8 * G1_BYTES,
      original.len() - 1,
    ] {
      let mut bytes = original.clone();
      bytes[offset] ^= 1;
      fs::write(&fixture.cache, bytes).unwrap();
      assert!(
        load_cache(&fixture.cache, receipt.digest, 8, fixture.spec).is_err(),
        "offset {offset}"
      );
    }
    for bad in [
      original[..original.len() - 1].to_vec(),
      [original.as_slice(), &[0]].concat(),
    ] {
      fs::write(&fixture.cache, bad).unwrap();
      assert!(
        load_cache(&fixture.cache, receipt.digest, 8, fixture.spec).is_err()
      );
    }
  }

  #[test]
  fn prefix_reads_authenticate_needed_chunks_without_reading_unused_tail() {
    let fixture = Fixture::new();
    let receipt = fixture.import().unwrap();
    let mut bytes = fs::read(&fixture.cache).unwrap();
    bytes[HEADER_BYTES + 4 * G1_BYTES] ^= 1;
    fs::write(&fixture.cache, bytes).unwrap();
    assert!(
      load_cache(&fixture.cache, receipt.digest, 2, fixture.spec).is_ok()
    );
    assert!(
      load_cache(&fixture.cache, receipt.digest, 4, fixture.spec).is_ok()
    );
    assert!(
      load_cache(&fixture.cache, receipt.digest, 8, fixture.spec).is_err()
    );
  }
}
