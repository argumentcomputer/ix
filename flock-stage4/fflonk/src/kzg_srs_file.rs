use crate::kzg::{
  MSM_BATCH_POINTS, SRS_DIGEST_DOMAIN, bounded_msm, live_coefficient_count,
  srs_batch_challenge,
};
use crate::{
  KzgCommitmentSourceV1, KzgCommitmentV1, KzgError, KzgVerifierKeyV1,
};
use ark_bls12_381::{Bls12_381, Fr, G1Affine, G1Projective, G2Affine};
use ark_ec::{AffineRepr, CurveGroup, pairing::Pairing};
use ark_ff::{One, Zero};
use ark_serialize::{
  CanonicalDeserialize, CanonicalSerialize, Compress, Validate,
};
use std::io::{BufWriter, Read, Seek, SeekFrom, Write};
use std::sync::Mutex;

const MAGIC: &[u8; 16] = b"IX-KZG-SRS-V1\0\0\0";
const G1_BYTES: usize = 48;
const G1_UNCOMPRESSED_BYTES: usize = 96;
const G2_BYTES: usize = 96;
const CHUNK_DIGEST_DOMAIN: &[u8] = b"ix:stage4:kzg-srs-file-chunk:bls12-381:v1";

/// Magic/version/encoding, little-endian u64 count, compressed G2 and tau-G2.
pub const KZG_SRS_FILE_HEADER_BYTES: usize = 16 + 8 + 2 * G2_BYTES;
/// Maximum number of G1 points decoded at once by the file-backed SRS.
pub const KZG_SRS_FILE_CHUNK_POINTS: usize = MSM_BATCH_POINTS;

/// Point storage for a v1 SRS archive. Both encodings have the same canonical
/// SRS digest and verifier key. Uncompressed storage avoids square-root work
/// on every commitment read; compressed storage halves the point payload.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum KzgSrsFileEncodingV1 {
  Compressed,
  Uncompressed,
}

impl KzgSrsFileEncodingV1 {
  #[must_use]
  pub const fn point_bytes(self) -> usize {
    match self {
      Self::Compressed => G1_BYTES,
      Self::Uncompressed => G1_UNCOMPRESSED_BYTES,
    }
  }

  fn compression(self) -> Compress {
    match self {
      Self::Compressed => Compress::Yes,
      Self::Uncompressed => Compress::No,
    }
  }

  fn tag(self) -> u8 {
    match self {
      Self::Compressed => 0,
      Self::Uncompressed => 1,
    }
  }
}

/// A validated, seekable powers-of-tau archive, normally backed by a `File`.
///
/// Opening makes two passes: subgroup validation and the canonical SRS digest,
/// then the same Fiat--Shamir batched consistency check as the in-memory SRS.
/// It retains only the reader, verifier key, and one 32-byte digest per chunk.
/// Every later read authenticates the exact bytes before decoding or MSM, so
/// a file modified after validation cannot silently change a commitment.
///
/// With a `File` reader, point buffers are bounded by 65,536 points. The chunk
/// index costs `32 * ceil(point_count / 65_536)` bytes. A caller-supplied reader
/// may retain its own buffers. The reader's cursor is protected by a mutex;
/// commitments using the same source run serially.
#[derive(Debug)]
pub struct KzgFileSrsV1<R> {
  reader: Mutex<R>,
  point_count: usize,
  chunk_points: usize,
  encoding: KzgSrsFileEncodingV1,
  chunk_digests: Vec<[u8; 32]>,
  verifier_key: KzgVerifierKeyV1,
}

impl<R: Read + Seek> KzgFileSrsV1<R> {
  /// Validate an entire v1 archive from offset zero, rejecting trailing bytes.
  /// Structural validation does not establish a ceremony's trustworthiness;
  /// select the SRS digest through the same trusted setup configuration as
  /// the in-memory backend.
  pub fn open(reader: R) -> Result<Self, KzgError> {
    Self::open_with_chunk_points(reader, KZG_SRS_FILE_CHUNK_POINTS)
  }

  fn open_with_chunk_points(
    mut reader: R,
    chunk_points: usize,
  ) -> Result<Self, KzgError> {
    if chunk_points == 0 || chunk_points > KZG_SRS_FILE_CHUNK_POINTS {
      return Err(KzgError::InternalShape);
    }
    reader.seek(SeekFrom::Start(0))?;
    let mut header = [0u8; KZG_SRS_FILE_HEADER_BYTES];
    reader.read_exact(&mut header)?;
    if header[..13] != MAGIC[..13] || header[14..16] != [0, 0] {
      return Err(KzgError::InvalidSrsFile("magic or version"));
    }
    let encoding = match header[13] {
      0 => KzgSrsFileEncodingV1::Compressed,
      1 => KzgSrsFileEncodingV1::Uncompressed,
      _ => return Err(KzgError::InvalidSrsFile("point encoding")),
    };
    let count = u64::from_le_bytes(
      header[16..24].try_into().map_err(|_| KzgError::InternalShape)?,
    );
    let point_count = usize::try_from(count)
      .map_err(|_| KzgError::InvalidSrsFile("power count exceeds usize"))?;
    if point_count < 2 {
      return Err(KzgError::InsufficientPowers {
        required: 2,
        available: point_count,
      });
    }
    if reader.seek(SeekFrom::End(0))? != file_length(count, encoding)? {
      return Err(KzgError::InvalidSrsFile(
        "length does not match power count",
      ));
    }
    let g2 = G2Affine::deserialize_compressed(&header[24..24 + G2_BYTES])
      .map_err(|_| KzgError::NonCanonicalGenerator)?;
    if g2 != G2Affine::generator() {
      return Err(KzgError::NonCanonicalGenerator);
    }
    let tau_g2 = G2Affine::deserialize_compressed(&header[24 + G2_BYTES..])
      .map_err(|_| KzgError::InvalidTauG2)?;
    if tau_g2.is_zero() {
      return Err(KzgError::IdentityInSrs);
    }

    let mut hasher = blake3::Hasher::new();
    hasher.update(SRS_DIGEST_DOMAIN);
    hasher.update(&count.to_le_bytes());
    let mut chunk_digests = Vec::new();
    chunk_digests
      .try_reserve_exact(point_count.div_ceil(chunk_points))
      .map_err(|_| KzgError::InvalidSrsFile("chunk index allocation"))?;
    let point_bytes = encoding.point_bytes();
    let mut encoded = vec![0u8; point_count.min(chunk_points) * point_bytes];
    reader.seek(SeekFrom::Start(KZG_SRS_FILE_HEADER_BYTES as u64))?;
    for start in (0..point_count).step_by(chunk_points) {
      let length = (point_count - start).min(chunk_points) * point_bytes;
      let bytes = &mut encoded[..length];
      reader.read_exact(bytes)?;
      for (offset, bytes) in bytes.chunks_exact(point_bytes).enumerate() {
        let index = start + offset;
        let point = G1Affine::deserialize_with_mode(
          bytes,
          encoding.compression(),
          Validate::No,
        )
        .map_err(|_| KzgError::InvalidG1Power { index })?;
        // Uncompressed decoding does not establish curve membership. Check it
        // before calling the subgroup routine that assumes it.
        if !point.is_on_curve()
          || !point.is_in_correct_subgroup_assuming_on_curve()
        {
          return Err(KzgError::InvalidG1Power { index });
        }
        if point.is_zero() {
          return Err(KzgError::IdentityInSrs);
        }
        if index == 0 && point != G1Affine::generator() {
          return Err(KzgError::NonCanonicalGenerator);
        }
        // SRS identity uses compressed points regardless of file storage.
        hash_encoded_point(&mut hasher, &encode_point::<_, G1_BYTES>(&point)?);
      }
      chunk_digests.push(chunk_digest(start, bytes));
    }
    hash_encoded_point(&mut hasher, &header[24..24 + G2_BYTES]);
    hash_encoded_point(&mut hasher, &header[24 + G2_BYTES..]);
    drop(encoded);
    let source = Self {
      reader: Mutex::new(reader),
      point_count,
      chunk_points,
      encoding,
      chunk_digests,
      verifier_key: KzgVerifierKeyV1 {
        g1: G1Affine::generator(),
        g2,
        tau_g2,
        srs_digest: *hasher.finalize().as_bytes(),
      },
    };
    source.check_consistency()?;
    Ok(source)
  }

  #[must_use]
  pub const fn max_degree(&self) -> usize {
    self.point_count - 1
  }

  #[must_use]
  pub const fn digest(&self) -> [u8; 32] {
    self.verifier_key.srs_digest
  }

  #[must_use]
  pub const fn verifier_key(&self) -> KzgVerifierKeyV1 {
    self.verifier_key
  }

  #[must_use]
  pub const fn encoding(&self) -> KzgSrsFileEncodingV1 {
    self.encoding
  }

  /// Requested heap bytes retained by the authentication index, excluding
  /// the reader and fixed-size metadata. No decoded point vector is retained.
  #[must_use]
  pub fn authentication_bytes(&self) -> usize {
    self.chunk_digests.capacity() * size_of::<[u8; 32]>()
  }

  fn check_consistency(&self) -> Result<(), KzgError> {
    let challenge = srs_batch_challenge(self.digest());
    let mut current = Fr::one();
    let mut preceding = Fr::zero();
    let mut left = G1Projective::zero();
    let mut right = G1Projective::zero();
    let mut scalars =
      Vec::with_capacity(self.point_count.min(self.chunk_points));
    self.for_each_chunk(self.point_count, |start, points| {
      scalars.clear();
      for index in start..start + points.len() {
        scalars.push(if index == self.point_count - 1 {
          Fr::zero()
        } else {
          current
        });
        current *= challenge;
      }
      left += bounded_msm(points, &scalars)?;
      // Shift r^i weights to r^(i-1), preserving the cross-chunk edge.
      // P_0 has no right weight and the final power has no left weight.
      let next_preceding = *scalars.last().ok_or(KzgError::InternalShape)?;
      scalars.rotate_right(1);
      scalars[0] = preceding;
      right += bounded_msm(points, &scalars)?;
      preceding = next_preceding;
      Ok(())
    })?;
    if Bls12_381::pairing(left.into_affine(), self.verifier_key.tau_g2)
      != Bls12_381::pairing(right.into_affine(), self.verifier_key.g2)
    {
      return Err(KzgError::InconsistentPowers);
    }
    Ok(())
  }

  fn for_each_chunk(
    &self,
    live_len: usize,
    mut consume: impl FnMut(usize, &[G1Affine]) -> Result<(), KzgError>,
  ) -> Result<(), KzgError> {
    if live_len > self.point_count {
      return Err(KzgError::InternalShape);
    }
    let mut reader =
      self.reader.lock().map_err(|_| KzgError::SrsStoragePoisoned)?;
    reader.seek(SeekFrom::Start(KZG_SRS_FILE_HEADER_BYTES as u64))?;
    let batch = self.point_count.min(self.chunk_points);
    let point_bytes = self.encoding.point_bytes();
    let mut encoded = vec![0u8; batch * point_bytes];
    let mut points = Vec::with_capacity(batch);
    for start in (0..live_len).step_by(self.chunk_points) {
      let count = (self.point_count - start).min(self.chunk_points);
      let bytes = &mut encoded[..count * point_bytes];
      reader.read_exact(bytes)?;
      let index = start / self.chunk_points;
      if chunk_digest(start, bytes) != self.chunk_digests[index] {
        return Err(KzgError::SrsChunkChanged { index });
      }
      points.clear();
      for bytes in bytes.chunks_exact(point_bytes).take(live_len - start) {
        // These exact bytes already passed subgroup validation in the first
        // pass, and have just been authenticated in this local buffer. Skip
        // repeating curve/subgroup checks, retaining canonical field decoding.
        points.push(
          G1Affine::deserialize_with_mode(
            bytes,
            self.encoding.compression(),
            Validate::No,
          )
          .map_err(|_| KzgError::InternalShape)?,
        );
      }
      consume(start, &points)?;
    }
    Ok(())
  }
}

impl<R: Read + Seek> KzgCommitmentSourceV1 for KzgFileSrsV1<R> {
  fn max_degree(&self) -> usize {
    self.max_degree()
  }

  fn verifier_key(&self) -> KzgVerifierKeyV1 {
    self.verifier_key()
  }

  fn commit(&self, coefficients: &[Fr]) -> Result<KzgCommitmentV1, KzgError> {
    let live_len = live_coefficient_count(coefficients);
    if live_len == 0 {
      return Ok(KzgCommitmentV1(G1Affine::identity()));
    }
    self.ensure_degree(live_len - 1)?;
    let mut commitment = G1Projective::zero();
    self.for_each_chunk(live_len, |start, points| {
      commitment +=
        bounded_msm(points, &coefficients[start..start + points.len()])?;
      Ok(())
    })?;
    Ok(KzgCommitmentV1(commitment.into_affine()))
  }
}

/// Encode a v1 archive from a point iterator without collecting the powers.
///
/// The format is a 216-byte header followed by exactly `point_count` canonical
/// 48-byte compressed or 96-byte uncompressed G1 records. The encoding tag is
/// byte 13 of the header; bytes 14 and 15 are reserved zeros.
/// Writing checks the count and propagates I/O
/// errors; it does not validate the setup. Open the completed archive with
/// `KzgFileSrsV1::open` before use. A failed write can leave a partial archive.
/// The caller owns file creation, truncation, durability, and publication.
pub fn write_kzg_srs_file(
  writer: &mut impl Write,
  point_count: usize,
  powers: impl IntoIterator<Item = G1Affine>,
  g2: G2Affine,
  tau_g2: G2Affine,
  encoding: KzgSrsFileEncodingV1,
) -> Result<(), KzgError> {
  if point_count < 2 {
    return Err(KzgError::InsufficientPowers {
      required: 2,
      available: point_count,
    });
  }
  let count =
    u64::try_from(point_count).map_err(|_| KzgError::InternalShape)?;
  file_length(count, encoding)?;
  let mut writer = BufWriter::with_capacity(65_536, writer);
  let mut magic = *MAGIC;
  magic[13] = encoding.tag();
  writer.write_all(&magic)?;
  writer.write_all(&count.to_le_bytes())?;
  writer.write_all(&encode_point::<_, G2_BYTES>(&g2)?)?;
  writer.write_all(&encode_point::<_, G2_BYTES>(&tau_g2)?)?;
  let mut powers = powers.into_iter();
  let mut encoded = [0u8; G1_UNCOMPRESSED_BYTES];
  for available in 0..point_count {
    let point = powers.next().ok_or(KzgError::InsufficientPowers {
      required: point_count,
      available,
    })?;
    let bytes = &mut encoded[..encoding.point_bytes()];
    point
      .serialize_with_mode(&mut *bytes, encoding.compression())
      .map_err(|_| KzgError::Serialization)?;
    writer.write_all(bytes)?;
  }
  if powers.next().is_some() {
    return Err(KzgError::InvalidSrsFile("more powers than declared"));
  }
  writer.flush()?;
  Ok(())
}

fn file_length(
  point_count: u64,
  encoding: KzgSrsFileEncodingV1,
) -> Result<u64, KzgError> {
  point_count
    .checked_mul(encoding.point_bytes() as u64)
    .and_then(|bytes| bytes.checked_add(KZG_SRS_FILE_HEADER_BYTES as u64))
    .ok_or(KzgError::InvalidSrsFile("file length overflow"))
}

fn encode_point<P: CanonicalSerialize, const N: usize>(
  point: &P,
) -> Result<[u8; N], KzgError> {
  let mut bytes = [0u8; N];
  point
    .serialize_compressed(&mut bytes[..])
    .map_err(|_| KzgError::Serialization)?;
  Ok(bytes)
}

fn hash_encoded_point(hasher: &mut blake3::Hasher, bytes: &[u8]) {
  hasher.update(&(bytes.len() as u64).to_le_bytes());
  hasher.update(bytes);
}

fn chunk_digest(start: usize, bytes: &[u8]) -> [u8; 32] {
  let mut hasher = blake3::Hasher::new();
  hasher.update(CHUNK_DIGEST_DOMAIN);
  hasher.update(&(start as u64).to_le_bytes());
  hasher.update(&(bytes.len() as u64).to_le_bytes());
  hasher.update(bytes);
  *hasher.finalize().as_bytes()
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::{
    KzgUniversalSrsV1, commit_polynomial, evaluate_polynomial, open_polynomial,
    verify_opening,
  };
  use ark_bls12_381::{Fq, Fq2};
  use ark_ff::{BigInteger, Field, PrimeField};
  use std::cell::{Cell, RefCell};
  use std::io::Cursor;
  use std::rc::Rc;

  fn test_srs(count: usize, tau: Fr) -> KzgUniversalSrsV1 {
    let mut scalar = Fr::one();
    let powers = (0..count)
      .map(|_| {
        let point = G1Affine::generator().mul_bigint(scalar.into_bigint());
        scalar *= tau;
        point.into_affine()
      })
      .collect();
    KzgUniversalSrsV1::new(
      powers,
      G2Affine::generator(),
      G2Affine::generator().mul_bigint(tau.into_bigint()).into_affine(),
    )
    .unwrap()
  }

  fn encode_srs(srs: &KzgUniversalSrsV1) -> Vec<u8> {
    encode_srs_with_encoding(srs, KzgSrsFileEncodingV1::Compressed)
  }

  fn encode_srs_with_encoding(
    srs: &KzgUniversalSrsV1,
    encoding: KzgSrsFileEncodingV1,
  ) -> Vec<u8> {
    let key = srs.verifier_key();
    let mut bytes = Vec::new();
    write_kzg_srs_file(
      &mut bytes,
      srs.powers_of_g1().len(),
      srs.powers_of_g1().iter().copied(),
      key.g2,
      key.tau_g2,
      encoding,
    )
    .unwrap();
    bytes
  }

  #[test]
  fn file_srs_matches_native_digest_commitments_and_openings() {
    let memory = test_srs(19, Fr::from(23u64));
    let encoded = encode_srs(&memory);
    assert_eq!(encoded.len(), KZG_SRS_FILE_HEADER_BYTES + 19 * G1_BYTES);
    // Vary boundaries independently of polynomial length and global exponents.
    for chunk in [1, 2, 3, 7, KZG_SRS_FILE_CHUNK_POINTS] {
      let file =
        KzgFileSrsV1::open_with_chunk_points(Cursor::new(&encoded), chunk)
          .unwrap();
      assert_eq!(file.digest(), memory.digest());
      assert_eq!(file.verifier_key(), memory.verifier_key());
      assert_eq!(file.max_degree(), memory.max_degree());
      for length in [0, 1, 2, 6, 7, 8, 18, 19] {
        let coefficients = (0..length)
          .map(|i| Fr::from(u64::try_from(i).unwrap() + 3).pow([17]))
          .collect::<Vec<_>>();
        let commitment = commit_polynomial(&file, &coefficients).unwrap();
        assert_eq!(
          commitment,
          commit_polynomial(&memory, &coefficients).unwrap()
        );
        let opening =
          open_polynomial(&file, &coefficients, Fr::from(11u64)).unwrap();
        assert_eq!(
          opening,
          open_polynomial(&memory, &coefficients, Fr::from(11u64)).unwrap(),
        );
        assert!(verify_opening(&file.verifier_key(), &commitment, &opening));
        let mut padded = coefficients;
        padded.resize(25, Fr::zero());
        assert_eq!(commit_polynomial(&file, &padded).unwrap(), commitment);
      }
      assert_eq!(
        commit_polynomial(&file, &[Fr::one(); 20]),
        Err(KzgError::DegreeTooLarge { degree: 19, max_degree: 18 }),
      );
    }
  }

  struct ObservedReader<R> {
    inner: R,
    largest_request: Rc<Cell<usize>>,
    maximum_read: usize,
  }

  impl<R: Read> Read for ObservedReader<R> {
    fn read(&mut self, bytes: &mut [u8]) -> std::io::Result<usize> {
      self.largest_request.set(self.largest_request.get().max(bytes.len()));
      let length = bytes.len().min(self.maximum_read);
      self.inner.read(&mut bytes[..length])
    }
  }

  impl<R: Seek> Seek for ObservedReader<R> {
    fn seek(&mut self, from: SeekFrom) -> std::io::Result<u64> {
      self.inner.seek(from)
    }
  }

  #[test]
  fn production_chunk_boundary_and_tail_use_bounded_reads() {
    for encoding in
      [KzgSrsFileEncodingV1::Compressed, KzgSrsFileEncodingV1::Uncompressed]
    {
      check_production_chunk_boundary(encoding);
    }
  }

  fn check_production_chunk_boundary(encoding: KzgSrsFileEncodingV1) {
    let count = KZG_SRS_FILE_CHUNK_POINTS + 3;
    // Public test-only tau -1 makes this large storage test inexpensive.
    // The small-boundary test above uses distinct powers of tau 23.
    let generator = G1Affine::generator();
    let mut encoded = Vec::new();
    write_kzg_srs_file(
      &mut encoded,
      count,
      (0..count).map(|i| if i % 2 == 0 { generator } else { -generator }),
      G2Affine::generator(),
      -G2Affine::generator(),
      encoding,
    )
    .unwrap();
    let largest_request = Rc::new(Cell::new(0));
    let file = KzgFileSrsV1::open(ObservedReader {
      inner: Cursor::new(encoded),
      largest_request: Rc::clone(&largest_request),
      maximum_read: 4_093,
    })
    .unwrap();
    assert_eq!(file.authentication_bytes(), 64);
    let coefficients = (0..count)
      .map(|i| Fr::from(u64::try_from(i).unwrap() + 3).pow([17]))
      .collect::<Vec<_>>();
    let commitment = commit_polynomial(&file, &coefficients).unwrap();
    let expected = generator
      .mul_bigint(evaluate_polynomial(&coefficients, -Fr::one()).into_bigint())
      .into_affine();
    assert_eq!(commitment.0, expected);
    assert_eq!(
      largest_request.get(),
      KZG_SRS_FILE_CHUNK_POINTS * encoding.point_bytes()
    );
  }

  #[test]
  fn rejects_bad_headers_lengths_and_point_encodings() {
    let memory = test_srs(5, Fr::from(13u64));
    let original = encode_srs(&memory);
    let mut cases = Vec::new();
    let mut changed = original.clone();
    changed[0] ^= 1;
    cases.push(changed);
    for (offset, value) in [(13, 2), (14, 1), (15, 1)] {
      let mut changed = original.clone();
      changed[offset] = value;
      cases.push(changed);
    }
    let mut changed = original.clone();
    changed.push(0);
    cases.push(changed);
    for length in [0, 15, 24, KZG_SRS_FILE_HEADER_BYTES, original.len() - 1] {
      cases.push(original[..length].to_vec());
    }
    for count in [0u64, 1, 4, 6, u64::MAX] {
      let mut changed = original.clone();
      changed[16..24].copy_from_slice(&count.to_le_bytes());
      cases.push(changed);
    }
    let mut changed = original.clone();
    changed[KZG_SRS_FILE_HEADER_BYTES] &= 0x7f; // Missing compressed flag.
    cases.push(changed);
    let mut changed = original.clone();
    let start = KZG_SRS_FILE_HEADER_BYTES + G1_BYTES;
    changed[start..start + G1_BYTES]
      .copy_from_slice(&Fq::MODULUS.to_bytes_be());
    changed[start] |= 0x80; // Noncanonical field coordinate equal to modulus.
    cases.push(changed);
    for changed in cases {
      assert!(KzgFileSrsV1::open(Cursor::new(changed)).is_err());
    }
  }

  #[test]
  fn rejects_identities_torsion_and_inconsistent_powers() {
    let memory = test_srs(7, Fr::from(13u64));
    let original = encode_srs(&memory);
    let replace_g1 = |index: usize, point: G1Affine| {
      let mut changed = original.clone();
      let start = KZG_SRS_FILE_HEADER_BYTES + G1_BYTES * index;
      changed[start..start + G1_BYTES]
        .copy_from_slice(&encode_point::<_, G1_BYTES>(&point).unwrap());
      changed
    };
    assert!(matches!(
      KzgFileSrsV1::open(Cursor::new(replace_g1(2, G1Affine::identity()))),
      Err(KzgError::IdentityInSrs),
    ));
    assert!(matches!(
      KzgFileSrsV1::open(Cursor::new(replace_g1(0, -G1Affine::generator()))),
      Err(KzgError::NonCanonicalGenerator),
    ));
    let torsion = G1Affine::new_unchecked(Fq::zero(), Fq::from(2u64));
    assert!(torsion.is_on_curve());
    assert!(!torsion.is_in_correct_subgroup_assuming_on_curve());
    assert!(matches!(
      KzgFileSrsV1::open(Cursor::new(replace_g1(2, torsion))),
      Err(KzgError::InvalidG1Power { index: 2 }),
    ));
    // Break every adjacency location, including the last power and boundaries.
    for index in 1..7 {
      assert!(matches!(
        KzgFileSrsV1::open_with_chunk_points(
          Cursor::new(replace_g1(index, G1Affine::generator())),
          3,
        ),
        Err(KzgError::InconsistentPowers),
      ));
    }
    let mut changed = original.clone();
    changed[24..24 + G2_BYTES].copy_from_slice(
      &encode_point::<_, G2_BYTES>(&-G2Affine::generator()).unwrap(),
    );
    assert!(matches!(
      KzgFileSrsV1::open(Cursor::new(changed)),
      Err(KzgError::NonCanonicalGenerator),
    ));
    let torsion = (0u64..)
      .find_map(|x| {
        G2Affine::get_point_from_x_unchecked(Fq2::from(x), false)
          .filter(|point| !point.is_in_correct_subgroup_assuming_on_curve())
      })
      .unwrap();
    for point in [G2Affine::identity(), torsion, G2Affine::generator()] {
      let mut changed = original.clone();
      changed[24 + G2_BYTES..KZG_SRS_FILE_HEADER_BYTES]
        .copy_from_slice(&encode_point::<_, G2_BYTES>(&point).unwrap());
      assert!(KzgFileSrsV1::open(Cursor::new(changed)).is_err());
    }
  }

  #[derive(Clone)]
  struct SharedReader(Rc<RefCell<Cursor<Vec<u8>>>>);

  impl Read for SharedReader {
    fn read(&mut self, bytes: &mut [u8]) -> std::io::Result<usize> {
      self.0.borrow_mut().read(bytes)
    }
  }

  impl Seek for SharedReader {
    fn seek(&mut self, from: SeekFrom) -> std::io::Result<u64> {
      self.0.borrow_mut().seek(from)
    }
  }

  #[test]
  fn authenticates_each_read_even_for_a_partial_last_chunk() {
    let original = encode_srs(&test_srs(10, Fr::from(17u64)));
    let shared =
      SharedReader(Rc::new(RefCell::new(Cursor::new(original.clone()))));
    let file = KzgFileSrsV1::open_with_chunk_points(shared.clone(), 3).unwrap();
    assert_eq!(
      commit_polynomial(&file, &[Fr::one()]).unwrap().0,
      G1Affine::generator()
    );

    // This power is not used by a constant polynomial, but belongs to its
    // authenticated first chunk. Check all bytes before decoding the prefix.
    shared.0.borrow_mut().get_mut()
      [KZG_SRS_FILE_HEADER_BYTES + 2 * G1_BYTES] ^= 1;
    assert_eq!(
      commit_polynomial(&file, &[Fr::one()]),
      Err(KzgError::SrsChunkChanged { index: 0 }),
    );
    *shared.0.borrow_mut().get_mut() = original.clone();
    shared.0.borrow_mut().get_mut()
      [KZG_SRS_FILE_HEADER_BYTES + 4 * G1_BYTES] ^= 1;
    assert_eq!(
      commit_polynomial(&file, &[Fr::one(); 8]),
      Err(KzgError::SrsChunkChanged { index: 1 }),
    );
    // An untouched prefix still represents the validated SRS correctly.
    assert_eq!(
      commit_polynomial(&file, &[Fr::one()]).unwrap().0,
      G1Affine::generator()
    );
    shared.0.borrow_mut().get_mut().truncate(KZG_SRS_FILE_HEADER_BYTES);
    assert_eq!(
      commit_polynomial(&file, &[Fr::one()]),
      Err(KzgError::Io(std::io::ErrorKind::UnexpectedEof)),
    );
    assert_eq!(
      commit_polynomial(&file, &[Fr::one(); 11]),
      Err(KzgError::DegreeTooLarge { degree: 10, max_degree: 9 }),
    );
    assert!(commit_polynomial(&file, &[Fr::zero(); 20]).unwrap().0.is_zero());
  }

  struct ChangeBetweenPasses {
    cursor: Cursor<Vec<u8>>,
    payload_seeks: usize,
  }

  impl Read for ChangeBetweenPasses {
    fn read(&mut self, bytes: &mut [u8]) -> std::io::Result<usize> {
      self.cursor.read(bytes)
    }
  }

  impl Seek for ChangeBetweenPasses {
    fn seek(&mut self, from: SeekFrom) -> std::io::Result<u64> {
      if from == SeekFrom::Start(KZG_SRS_FILE_HEADER_BYTES as u64) {
        self.payload_seeks += 1;
        if self.payload_seeks == 2 {
          self.cursor.get_mut()[KZG_SRS_FILE_HEADER_BYTES + G1_BYTES] ^= 1;
        }
      }
      self.cursor.seek(from)
    }
  }

  #[test]
  fn rejects_changes_between_subgroup_and_pairing_passes() {
    let reader = ChangeBetweenPasses {
      cursor: Cursor::new(encode_srs(&test_srs(5, Fr::from(19u64)))),
      payload_seeks: 0,
    };
    assert!(matches!(
      KzgFileSrsV1::open(reader),
      Err(KzgError::SrsChunkChanged { index: 0 }),
    ));
  }

  #[test]
  fn archive_writer_rejects_wrong_counts_and_propagates_io_errors() {
    let memory = test_srs(5, Fr::from(13u64));
    let key = memory.verifier_key();
    for declared in [0, 1, 4, 6] {
      assert!(
        write_kzg_srs_file(
          &mut Vec::new(),
          declared,
          memory.powers_of_g1().iter().copied(),
          key.g2,
          key.tau_g2,
          KzgSrsFileEncodingV1::Compressed,
        )
        .is_err(),
      );
    }
    struct BrokenWriter(bool);
    impl Write for BrokenWriter {
      fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
        if self.0 {
          Ok(bytes.len())
        } else {
          Err(std::io::ErrorKind::WriteZero.into())
        }
      }
      fn flush(&mut self) -> std::io::Result<()> {
        Err(std::io::ErrorKind::BrokenPipe.into())
      }
    }
    for (flush_only, kind) in [
      (false, std::io::ErrorKind::WriteZero),
      (true, std::io::ErrorKind::BrokenPipe),
    ] {
      assert_eq!(
        write_kzg_srs_file(
          &mut BrokenWriter(flush_only),
          memory.powers_of_g1().len(),
          memory.powers_of_g1().iter().copied(),
          key.g2,
          key.tau_g2,
          KzgSrsFileEncodingV1::Compressed,
        ),
        Err(KzgError::Io(kind)),
      );
    }
  }

  struct TestFile(std::path::PathBuf);

  impl TestFile {
    fn new() -> (Self, std::fs::File) {
      use std::sync::atomic::{AtomicU64, Ordering};
      static NEXT: AtomicU64 = AtomicU64::new(0);
      loop {
        let path = std::env::temp_dir().join(format!(
          "ix-stage4-srs-{}-{}.bin",
          std::process::id(),
          NEXT.fetch_add(1, Ordering::Relaxed),
        ));
        match std::fs::OpenOptions::new()
          .create_new(true)
          .read(true)
          .write(true)
          .open(&path)
        {
          Ok(file) => return (Self(path), file),
          Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {},
          Err(error) => panic!("create test SRS archive: {error}"),
        }
      }
    }
  }

  impl Drop for TestFile {
    fn drop(&mut self) {
      let _ = std::fs::remove_file(&self.0);
    }
  }

  #[test]
  fn real_file_preprocessing_and_proving_match_the_memory_backend() {
    for encoding in
      [KzgSrsFileEncodingV1::Compressed, KzgSrsFileEncodingV1::Uncompressed]
    {
      check_file_preprocessing_and_proving(encoding);
    }
  }

  fn check_file_preprocessing_and_proving(encoding: KzgSrsFileEncodingV1) {
    use crate::{
      FflonkBlindingV1, FflonkProverError, arithmetize_r1cs, preprocess_fflonk,
      prove_fflonk, required_fflonk_srs_degree, verify_fflonk,
    };
    use ix_terminal_circuit::{
      ConstraintPhase, LinearCombination, R1csBuilder,
    };

    let mut builder = R1csBuilder::new();
    let public = builder.alloc_public(Fr::from(3u64)).unwrap();
    let private = builder.alloc_private(Fr::from(5u64)).unwrap();
    let product = builder.alloc_private(Fr::from(15u64)).unwrap();
    builder.enforce(
      ConstraintPhase::Statement,
      LinearCombination::from_variable(public),
      LinearCombination::from_variable(private),
      LinearCombination::from_variable(product),
    );
    let (r1cs, witness) = builder.finish().unwrap();
    let arithmetization = arithmetize_r1cs(&r1cs).unwrap();
    let degree =
      required_fflonk_srs_degree(arithmetization.census().domain_size).unwrap();
    let memory =
      test_srs(usize::try_from(degree).unwrap() + 1, Fr::from(29u64));
    let (path, mut archive) = TestFile::new();
    write_kzg_srs_file(
      &mut archive,
      memory.powers_of_g1().len(),
      memory.powers_of_g1().iter().copied(),
      memory.verifier_key().g2,
      memory.verifier_key().tau_g2,
      encoding,
    )
    .unwrap();
    drop(archive);
    let file =
      KzgFileSrsV1::open(std::fs::File::open(&path.0).unwrap()).unwrap();
    assert_eq!(file.encoding(), encoding);
    assert_eq!(file.digest(), memory.digest());
    let memory_key =
      preprocess_fflonk(&memory, arithmetization.clone()).unwrap();
    let file_key = preprocess_fflonk(&file, arithmetization).unwrap();
    assert_eq!(file_key, memory_key);
    let blinding = FflonkBlindingV1 {
      wire_evaluations: core::array::from_fn(|index| {
        Fr::from(index as u64 + 31)
      }),
      z_coefficients: [Fr::from(41u64), Fr::from(43u64), Fr::from(47u64)],
    };
    let expected =
      prove_fflonk(&memory, &memory_key, &r1cs, &witness, blinding).unwrap();
    let actual =
      prove_fflonk(&file, &file_key, &r1cs, &witness, blinding).unwrap();
    assert_eq!(actual.proof.to_bytes(), expected.proof.to_bytes());
    assert_eq!(actual.public_inputs, expected.public_inputs);
    assert_eq!(
      verify_fflonk(
        &file_key.verification_key(),
        &actual.proof,
        &actual.public_inputs
      ),
      Ok(true),
    );
    let other_memory = test_srs(memory.powers_of_g1().len(), Fr::from(31u64));
    let other_file =
      KzgFileSrsV1::open(Cursor::new(encode_srs(&other_memory))).unwrap();
    assert_eq!(
      prove_fflonk(&other_file, &file_key, &r1cs, &witness, blinding),
      Err(FflonkProverError::SrsMismatch),
    );
    // An external writer cannot replace a power after the source was opened.
    let mut writer =
      std::fs::OpenOptions::new().write(true).open(&path.0).unwrap();
    writer
      .seek(SeekFrom::Start(
        (KZG_SRS_FILE_HEADER_BYTES + encoding.point_bytes()) as u64,
      ))
      .unwrap();
    writer
      .write_all(&encode_point::<_, G1_BYTES>(&G1Affine::generator()).unwrap())
      .unwrap();
    writer.flush().unwrap();
    assert_eq!(
      prove_fflonk(&file, &file_key, &r1cs, &witness, blinding),
      Err(FflonkProverError::Kzg(KzgError::SrsChunkChanged { index: 0 })),
    );
  }

  #[test]
  fn uncompressed_import_checks_curve_membership_before_subgroup() {
    let encoding = KzgSrsFileEncodingV1::Uncompressed;
    let original =
      encode_srs_with_encoding(&test_srs(5, Fr::from(17u64)), encoding);
    let start = KZG_SRS_FILE_HEADER_BYTES + 2 * encoding.point_bytes();
    for point in [
      G1Affine::new_unchecked(Fq::zero(), Fq::zero()),
      G1Affine::new_unchecked(Fq::zero(), Fq::one()),
      G1Affine::new_unchecked(Fq::zero(), Fq::from(2u64)),
    ] {
      let mut changed = original.clone();
      let bytes = &mut changed[start..start + encoding.point_bytes()];
      point.serialize_uncompressed(&mut *bytes).unwrap();
      // The field decoder itself permits unchecked off-curve coordinates.
      assert_eq!(
        G1Affine::deserialize_uncompressed_unchecked(&*bytes).unwrap(),
        point,
      );
      assert!(matches!(
        KzgFileSrsV1::open(Cursor::new(changed)),
        Err(KzgError::InvalidG1Power { index: 2 }),
      ));
    }
    let mut changed = original.clone();
    changed[start + G1_BYTES..start + encoding.point_bytes()]
      .copy_from_slice(&Fq::MODULUS.to_bytes_be());
    assert!(KzgFileSrsV1::open(Cursor::new(changed)).is_err());
    let mut changed = original;
    changed[start] |= 0x80;
    assert!(KzgFileSrsV1::open(Cursor::new(changed)).is_err());
  }
}
