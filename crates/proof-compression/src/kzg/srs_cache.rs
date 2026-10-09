//! Bounded I/O for a trusted-local development SRS cache.
use super::Srs;
use ark_bls12_381::{G1Affine, G2Affine};
use ark_serialize::{
  CanonicalDeserialize, CanonicalSerialize, SerializationError,
};
use p3_maybe_rayon::prelude::*;
use std::{
  fs::File,
  io::{BufReader, BufWriter, Read, Write},
  path::Path,
};

pub(super) fn cached(
  max_len: usize,
  seed: &[u8],
  path: &Path,
) -> Result<Srs, SerializationError> {
  assert!(max_len >= 2 && max_len.is_power_of_two());
  let profile = blake3::hash(seed);
  if path.exists() {
    let mut reader = BufReader::with_capacity(1 << 20, File::open(path)?);
    let mut size = [0u8; 8];
    reader.read_exact(&mut size)?;
    let header_len = u64::from_le_bytes(size);
    if header_len > 16384 {
      return Err(SerializationError::InvalidData);
    }
    let mut header = vec![
      0;
      usize::try_from(header_len)
        .map_err(|_error| SerializationError::InvalidData)?
    ];
    reader.read_exact(&mut header)?;
    let mut input = header.as_slice();
    if u64::deserialize_compressed(&mut input)? != 1
      || u64::deserialize_compressed(&mut input)? != max_len as u64
      || <[u8; 32]>::deserialize_compressed(&mut input)? != *profile.as_bytes()
    {
      return Err(SerializationError::InvalidData);
    }
    let g2 = G2Affine::deserialize_compressed(&mut input)?;
    let tau_g2 = G2Affine::deserialize_compressed(&mut input)?;
    let degree_keys: Vec<G2Affine> = Vec::deserialize_compressed(&mut input)?;
    if !input.is_empty() || degree_keys.len() != max_len.ilog2() as usize + 1 {
      return Err(SerializationError::InvalidData);
    }
    let mut hash = blake3::Hasher::new();
    hash.update(&size).update(&header);
    let point_size = G1Affine::identity().uncompressed_size();
    let mut bytes = vec![0u8; (1 << 14) * point_size];
    let mut g1 = vec![G1Affine::identity(); max_len];
    for dst in g1.chunks_mut(1 << 14) {
      let bytes = &mut bytes[..dst.len() * point_size];
      reader.read_exact(bytes)?;
      hash.update(bytes);
      // This is a trusted-local cache of known-trapdoor parameters, not
      // an SRS import. Its checksum is checked before returning points.
      dst.par_iter_mut().zip(bytes.par_chunks(point_size)).try_for_each(
        |(p, b)| {
          *p = G1Affine::deserialize_uncompressed_unchecked(b)?;
          Ok::<_, SerializationError>(())
        },
      )?;
    }
    let mut expected = [0; 32];
    reader.read_exact(&mut expected)?;
    let mut tail = [0];
    if hash.finalize().as_bytes() != &expected || reader.read(&mut tail)? != 0 {
      return Err(SerializationError::InvalidData);
    }
    return Ok(Srs { g1, g2, tau_g2, degree_keys });
  }
  let srs = Srs::unsafe_dev_setup(max_len, seed);
  let temp = path.with_extension(format!("partial-{}", std::process::id()));
  let mut writer = BufWriter::with_capacity(1 << 20, File::create_new(&temp)?);
  let mut header = Vec::new();
  1u64.serialize_compressed(&mut header)?;
  (max_len as u64).serialize_compressed(&mut header)?;
  profile.as_bytes().serialize_compressed(&mut header)?;
  srs.g2.serialize_compressed(&mut header)?;
  srs.tau_g2.serialize_compressed(&mut header)?;
  srs.degree_keys.serialize_compressed(&mut header)?;
  let size = (header.len() as u64).to_le_bytes();
  writer.write_all(&size)?;
  writer.write_all(&header)?;
  let mut hash = blake3::Hasher::new();
  hash.update(&size).update(&header);
  let point_size = G1Affine::identity().uncompressed_size();
  let mut bytes = vec![0u8; (1 << 14) * point_size];
  for src in srs.g1.chunks(1 << 14) {
    let bytes = &mut bytes[..src.len() * point_size];
    bytes
      .par_chunks_mut(point_size)
      .zip(src.par_iter())
      .try_for_each(|(b, p)| p.serialize_uncompressed(b))?;
    writer.write_all(bytes)?;
    hash.update(bytes);
  }
  writer.write_all(hash.finalize().as_bytes())?;
  writer.flush()?;
  drop(writer);
  std::fs::rename(temp, path)?;
  Ok(srs)
}
