use std::{
  fs::{self, File},
  io::{self, Read},
  path::{Path, PathBuf},
};

use p3_maybe_rayon::prelude::*;
use serde::{Deserialize, Serialize};

use super::{
  Anchors,
  points::{decode_source_g1, decode_source_g2},
};
use crate::kzg::{
  curve::{self, G1Affine, G2Affine},
  srs::PublicSetup,
};

pub const SOURCE_FORMAT: &str = "ix-bn254-ignition-source-v1";
pub const SHIFTED_TAU_BASIS: &str = "shifted-tau";
const MAX_MANIFEST_BYTES: u64 = 1 << 20;
const MAX_G1_POINTS: u32 = 100_800_000;
const MAX_TRANSCRIPTS: u32 = 32;
const BLOCK_POINTS: usize = 1 << 16;

/// A separately authenticated description of the complete ceremony snapshot.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SourceManifest {
  pub format: String,
  pub ceremony: String,
  pub basis: String,
  pub num_g1_points: u32,
  pub points_per_transcript: u32,
  pub contribution: Contribution,
  pub predecessor: Option<Contribution>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Contribution {
  pub position: u32,
  pub address: String,
  pub transcripts: Vec<Transcript>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Transcript {
  pub index: u32,
  /// BLAKE2b-512 of the complete file, including its embedded checksum.
  pub blake2b512: String,
}

fn invalid(
  message: impl Into<Box<dyn std::error::Error + Send + Sync>>,
) -> io::Error {
  io::Error::new(io::ErrorKind::InvalidData, message)
}

fn open_regular_file(path: &Path) -> io::Result<File> {
  if !fs::metadata(path)?.is_file() {
    return Err(invalid("Ignition input must be a regular file"));
  }
  let file = File::open(path)?;
  if !file.metadata()?.is_file() {
    return Err(invalid("Ignition input must be a regular file"));
  }
  Ok(file)
}

fn validate_participant(position: u32, address: &str) -> io::Result<()> {
  if position > 9999
    || address.len() != 42
    || !address.starts_with("0x")
    || !address.as_bytes()[2..]
      .iter()
      .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(byte))
  {
    return Err(invalid("invalid Ignition contribution position or address"));
  }
  Ok(())
}

fn decode_digest(text: &str) -> io::Result<[u8; 64]> {
  if text.len() != 128 || !text.as_bytes().iter().all(u8::is_ascii_hexdigit) {
    return Err(invalid("invalid Ignition BLAKE2b-512 digest"));
  }
  let mut bytes = [0; 64];
  for (byte, hex) in bytes.iter_mut().zip(text.as_bytes().as_chunks::<2>().0) {
    let digit = |value: u8| {
      if value.is_ascii_digit() {
        value - b'0'
      } else {
        value.to_ascii_lowercase() - b'a' + 10
      }
    };
    *byte = digit(hex[0]) * 16 + digit(hex[1]);
  }
  Ok(bytes)
}

fn encode_digest(bytes: &[u8; 64]) -> String {
  const HEX: &[u8; 16] = b"0123456789abcdef";
  let mut text = String::with_capacity(128);
  for byte in bytes {
    text.push(char::from(HEX[usize::from(byte >> 4)]));
    text.push(char::from(HEX[usize::from(byte & 15)]));
  }
  text
}

impl SourceManifest {
  pub fn validate(&self) -> io::Result<()> {
    if self.format != SOURCE_FORMAT
      || self.basis != SHIFTED_TAU_BASIS
      || self.ceremony.trim().is_empty()
      || self.ceremony.len() > 256
      || self.ceremony.chars().any(char::is_control)
      || !(2..=MAX_G1_POINTS).contains(&self.num_g1_points)
      || self.points_per_transcript == 0
      || self.points_per_transcript > self.num_g1_points
    {
      return Err(invalid("invalid Ignition source manifest metadata"));
    }
    let count = self.num_g1_points.div_ceil(self.points_per_transcript);
    if count > MAX_TRANSCRIPTS {
      return Err(invalid("too many Ignition transcripts"));
    }
    for contribution in
      std::iter::once(&self.contribution).chain(self.predecessor.iter())
    {
      validate_participant(contribution.position, &contribution.address)?;
      if contribution.transcripts.len() != count as usize {
        return Err(invalid("wrong number of Ignition transcript digests"));
      }
      for (expected, transcript) in (0..count).zip(&contribution.transcripts) {
        if transcript.index != expected {
          return Err(invalid(
            "Ignition transcript indices are not contiguous",
          ));
        }
        decode_digest(&transcript.blake2b512)?;
      }
    }
    if self
      .predecessor
      .as_ref()
      .is_some_and(|previous| previous.position >= self.contribution.position)
    {
      return Err(invalid("Ignition predecessor must precede contribution"));
    }
    Ok(())
  }

  /// The shifted basis starts at `τG`, so N points allow degree N−1.
  /// Optional predecessor evidence does not change the selected setup's identity.
  pub fn public_setup(&self) -> io::Result<PublicSetup> {
    self.validate()?;
    let mut hash = blake3::Hasher::new();
    hash.update(b"multi-stark/kzg/bn254/ignition-public-setup/v1");
    for text in [
      curve::NAME,
      &self.format,
      &self.basis,
      &self.ceremony,
      &self.contribution.address,
    ] {
      hash.update(&(text.len() as u64).to_le_bytes());
      hash.update(text.as_bytes());
    }
    hash.update(&self.num_g1_points.to_le_bytes());
    hash.update(&self.points_per_transcript.to_le_bytes());
    hash.update(&self.contribution.position.to_le_bytes());
    for transcript in &self.contribution.transcripts {
      hash.update(&transcript.index.to_le_bytes());
      hash.update(&decode_digest(&transcript.blake2b512)?);
    }
    Ok(PublicSetup {
      max_degree: self.num_g1_points as usize - 1,
      id: *hash.finalize().as_bytes(),
    })
  }
}

/// The expected digest must come from trusted configuration, independently of
/// the source directory and its manifest. It covers the exact JSON bytes.
pub fn read_source_manifest(
  path: &Path,
  expected: [u8; 32],
) -> io::Result<SourceManifest> {
  read_source_manifest_bytes(path, expected).map(|(_, manifest)| manifest)
}

pub(super) fn read_source_manifest_bytes(
  path: &Path,
  expected: [u8; 32],
) -> io::Result<(Vec<u8>, SourceManifest)> {
  let mut bytes = Vec::new();
  open_regular_file(path)?
    .take(MAX_MANIFEST_BYTES + 1)
    .read_to_end(&mut bytes)?;
  let manifest = parse_source_manifest(&bytes, expected)?;
  Ok((bytes, manifest))
}

pub(super) fn parse_source_manifest(
  bytes: &[u8],
  expected: [u8; 32],
) -> io::Result<SourceManifest> {
  if bytes.len() as u64 > MAX_MANIFEST_BYTES {
    return Err(invalid("Ignition source manifest exceeds 1 MiB"));
  }
  if blake3::hash(bytes).as_bytes() != &expected {
    return Err(invalid("Ignition source manifest digest mismatch"));
  }
  let manifest: SourceManifest =
    serde_json::from_slice(bytes).map_err(invalid)?;
  manifest.validate()?;
  Ok(manifest)
}

fn transcript_path(
  root: &Path,
  contribution: &Contribution,
  index: u32,
) -> PathBuf {
  root
    .join(format!("{:03}_{}", contribution.position, contribution.address))
    .join(format!("transcript{index:02}.dat"))
}

fn parse_header(bytes: &[u8; 28]) -> [u32; 7] {
  let mut header = [0; 7];
  for (word, bytes) in header.iter_mut().zip(bytes.as_chunks::<4>().0) {
    *word = u32::from_be_bytes(*bytes);
  }
  header
}

fn expected_header(manifest: &SourceManifest, index: u32) -> [u32; 7] {
  let start = index * manifest.points_per_transcript;
  [
    index,
    manifest.num_g1_points.div_ceil(manifest.points_per_transcript),
    manifest.num_g1_points,
    1,
    manifest.points_per_transcript.min(manifest.num_g1_points - start),
    if index == 0 { 2 } else { 0 },
    start,
  ]
}

struct FileResult {
  digest: [u8; 64],
  first_g1: Vec<G1Affine>,
  g2: Option<[G2Affine; 2]>,
}

fn stream_file(
  root: &Path,
  manifest: &SourceManifest,
  contribution: &Contribution,
  index: u32,
  prefix_len: usize,
  visit: &mut impl FnMut(&[G1Affine]) -> io::Result<()>,
) -> io::Result<FileResult> {
  let path = transcript_path(root, contribution, index);
  let mut file = open_regular_file(&path)?;
  let mut bytes = [0; 28];
  file.read_exact(&mut bytes)?;
  let header = parse_header(&bytes);
  if header != expected_header(manifest, index) {
    return Err(invalid(format!(
      "Ignition header mismatch in {}",
      path.display()
    )));
  }
  let expected_bytes =
    28 + u64::from(header[4]) * 64 + u64::from(header[5]) * 128 + 64;
  if file.metadata()?.len() != expected_bytes {
    return Err(invalid(format!(
      "Ignition file length mismatch in {}",
      path.display()
    )));
  }
  let mut checksum = blake2b_simd::Params::new().hash_length(64).to_state();
  checksum.update(&bytes);
  let mut first_g1 = Vec::with_capacity(2);
  let mut buffer = vec![0; BLOCK_POINTS * 64];
  let mut consumed = 0;
  let count = header[4] as usize;
  let retained = prefix_len.saturating_sub(header[6] as usize).min(count);
  while consumed < count {
    let chunk_len = (count - consumed).min(BLOCK_POINTS);
    let chunk = &mut buffer[..chunk_len * 64];
    file.read_exact(chunk)?;
    checksum.update(chunk);
    let retained_chunk = retained.saturating_sub(consumed).min(chunk_len);
    if retained_chunk != 0 {
      let points: Vec<_> = chunk[..retained_chunk * 64]
        .par_chunks_exact(64)
        .map(decode_source_g1)
        .collect::<io::Result<_>>()?;
      first_g1.extend(points.iter().take(2 - first_g1.len()).copied());
      visit(&points)?;
    }
    consumed += chunk_len;
  }
  let g2 = if index == 0 {
    let mut bytes = [0; 256];
    file.read_exact(&mut bytes)?;
    checksum.update(&bytes);
    Some([decode_source_g2(&bytes[..128])?, decode_source_g2(&bytes[128..])?])
  } else {
    None
  };
  let mut stored_checksum = [0; 64];
  file.read_exact(&mut stored_checksum)?;
  let mut trailing = [0; 1];
  if file.read(&mut trailing)? != 0 {
    return Err(invalid("trailing bytes in Ignition transcript"));
  }
  if checksum.finalize().as_bytes() != stored_checksum {
    return Err(invalid(format!(
      "Ignition internal checksum mismatch in {}",
      path.display()
    )));
  }
  checksum.update(&stored_checksum);
  let digest = checksum.finalize().as_bytes().try_into().expect("BLAKE2b-512");
  Ok(FileResult { digest, first_g1, g2 })
}

/// Read and authenticate complete files, decoding only the retained prefix.
/// The visitor must keep its output private until this function succeeds.
pub(super) fn stream_contribution(
  root: &Path,
  manifest: &SourceManifest,
  contribution: &Contribution,
  prefix_len: usize,
  mut visit: impl FnMut(&[G1Affine]) -> io::Result<()>,
) -> io::Result<Anchors> {
  manifest.validate()?;
  if contribution != &manifest.contribution
    && manifest.predecessor.as_ref() != Some(contribution)
  {
    return Err(invalid(
      "Ignition contribution is absent from source manifest",
    ));
  }
  if prefix_len < 2 || prefix_len > manifest.num_g1_points as usize {
    return Err(invalid("Ignition retained prefix is outside source bounds"));
  }
  let mut first_g1 = Vec::with_capacity(2);
  let mut anchors_g2 = None;
  for transcript in &contribution.transcripts {
    let result = stream_file(
      root,
      manifest,
      contribution,
      transcript.index,
      prefix_len,
      &mut visit,
    )?;
    if result.digest != decode_digest(&transcript.blake2b512)? {
      return Err(invalid(format!(
        "Ignition source digest mismatch at transcript {}",
        transcript.index,
      )));
    }
    first_g1.extend(result.first_g1.into_iter().take(2 - first_g1.len()));
    if result.g2.is_some() {
      anchors_g2 = result.g2;
    }
  }
  let [tau_g2, contribution_g2] =
    anchors_g2.ok_or_else(|| invalid("missing Ignition G2 anchors"))?;
  Ok(Anchors {
    g1: first_g1
      .try_into()
      .map_err(|_points| invalid("missing Ignition G1 anchors"))?,
    tau_g2,
    contribution_g2,
  })
}

/// Produce an untrusted inventory, not evidence of ceremony provenance.
/// Checksums can detect damage but an attacker can replace both data and hashes.
pub fn inspect_ignition_source(
  root: &Path,
  position: u32,
  address: &str,
  predecessor: Option<(u32, &str)>,
) -> io::Result<SourceManifest> {
  validate_participant(position, address)?;
  if let Some((position, address)) = predecessor {
    validate_participant(position, address)?;
  }
  let contribution = Contribution {
    position,
    address: address.to_owned(),
    transcripts: Vec::new(),
  };
  let mut bytes = [0; 28];
  open_regular_file(&transcript_path(root, &contribution, 0))?
    .read_exact(&mut bytes)?;
  let header = parse_header(&bytes);
  let mut manifest = SourceManifest {
    format: SOURCE_FORMAT.to_owned(),
    ceremony: "MAIN IGNITION".to_owned(),
    basis: SHIFTED_TAU_BASIS.to_owned(),
    num_g1_points: header[2],
    points_per_transcript: header[4],
    contribution,
    predecessor: predecessor.map(|(position, address)| Contribution {
      position,
      address: address.to_owned(),
      transcripts: Vec::new(),
    }),
  };
  if header[1] == 0 || header[1] > MAX_TRANSCRIPTS {
    return Err(invalid("invalid Ignition transcript count"));
  }
  let placeholders: Vec<_> = (0..header[1])
    .map(|index| Transcript { index, blake2b512: "0".repeat(128) })
    .collect();
  manifest.contribution.transcripts = placeholders.clone();
  if let Some(previous) = &mut manifest.predecessor {
    previous.transcripts = placeholders;
  }
  manifest.validate()?;
  let inspect = |contribution: &Contribution| -> io::Result<Vec<Transcript>> {
    contribution
      .transcripts
      .iter()
      .map(|transcript| {
        let result = stream_file(
          root,
          &manifest,
          contribution,
          transcript.index,
          0,
          &mut |_| Ok(()),
        )?;
        Ok(Transcript {
          index: transcript.index,
          blake2b512: encode_digest(&result.digest),
        })
      })
      .collect()
  };
  let current = inspect(&manifest.contribution)?;
  let previous = manifest.predecessor.as_ref().map(inspect).transpose()?;
  manifest.contribution.transcripts = current;
  if let Some(previous) = previous {
    manifest.predecessor.as_mut().expect("requested predecessor").transcripts =
      previous;
  }
  Ok(manifest)
}
