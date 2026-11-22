//! Compact constant, resident or checksummed, trusted-local coefficient storage.
use std::{
  borrow::Cow,
  fs::File,
  io::{Read, Seek, SeekFrom},
  ops::Range,
  path::PathBuf,
  sync::{Arc, Mutex},
};
#[cfg(not(feature = "cuda"))]
use std::{
  io::Write,
  path::Path,
  sync::atomic::{AtomicU64, Ordering},
};

use super::curve::Fr;
#[cfg(not(feature = "cuda"))]
use super::{domain::Radix2Coset, field::Scalar};
use crate::pipeline::storage::{fadvise_dontneed, fadvise_sequential};
use ark_ff::{BigInt, PrimeField, Zero};
use ark_serialize::SerializationError;
#[cfg(not(feature = "cuda"))]
use p3_matrix::dense::RowMajorMatrix;
use p3_maybe_rayon::prelude::*;

pub(super) const CHUNK: usize = 1 << 18;
const RAYON_HASH_THRESHOLD: usize = 128 << 10;

#[cfg(not(feature = "cuda"))]
const _: () = {
  assert!(size_of::<Fr>() == size_of::<[u64; 4]>());
  assert!(align_of::<Fr>() == align_of::<[u64; 4]>());
  assert!(std::mem::offset_of!(Fr, 0) == 0);
  assert!(std::mem::offset_of!(BigInt<4>, 0) == 0);
  assert!(size_of::<Scalar>() == size_of::<Fr>());
  assert!(align_of::<Scalar>() == align_of::<Fr>());
};

#[inline]
fn update_hash(hasher: &mut blake3::Hasher, bytes: &[u8]) {
  if bytes.len() >= RAYON_HASH_THRESHOLD {
    hasher.update_rayon(bytes);
  } else {
    hasher.update(bytes);
  }
}

/// An open coefficient file. Temporary spill files unlink themselves on
/// creation (Unix) or remove their path on drop (other targets).
pub(super) struct DiskFile {
  file: File,
  remove_on_drop: Option<PathBuf>,
}

impl DiskFile {
  pub(super) fn persistent(file: File) -> Self {
    fadvise_sequential(&file);
    Self { file, remove_on_drop: None }
  }

  #[cfg(not(feature = "cuda"))]
  pub(super) fn temporary(dir: &Path) -> std::io::Result<Self> {
    static NEXT: AtomicU64 = AtomicU64::new(0);
    std::fs::create_dir_all(dir)?;
    for _ in 0..64 {
      let id = NEXT.fetch_add(1, Ordering::Relaxed);
      let path =
        dir.join(format!(".kzg-spill-{}-{id}.bin", std::process::id()));
      match File::options().create_new(true).read(true).write(true).open(&path)
      {
        Ok(file) => {
          #[cfg(unix)]
          {
            let _ = std::fs::remove_file(&path);
            return Ok(Self { file, remove_on_drop: None });
          }
          #[cfg(not(unix))]
          {
            return Ok(Self { file, remove_on_drop: Some(path) });
          }
        },
        Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {},
        Err(error) => return Err(error),
      }
    }
    Err(std::io::Error::new(
      std::io::ErrorKind::AlreadyExists,
      "failed to create unique KZG spill file",
    ))
  }

  #[cfg(not(feature = "cuda"))]
  pub(super) fn file(&self) -> &File {
    &self.file
  }

  pub(super) fn file_mut(&mut self) -> &mut File {
    &mut self.file
  }
}

impl Drop for DiskFile {
  fn drop(&mut self) {
    if let Some(path) = self.remove_on_drop.take() {
      let _ = std::fs::remove_file(path);
    }
  }
}

/// On-disk scalar encoding for disk-backed columns.
/// Persistent fixed-cache checkpoints always use canonical compressed scalars;
/// ephemeral process-local spill files store raw native Montgomery limbs to
/// skip `into_bigint`/`from_bigint` Montgomery conversions on write and read.
#[derive(Clone, Copy)]
pub(super) enum DiskFormat {
  Canonical,
  #[cfg(not(feature = "cuda"))]
  RawMontgomery,
}

#[cfg(not(feature = "cuda"))]
#[inline]
fn fr_slice_as_bytes(values: &[Fr]) -> &[u8] {
  // SAFETY: Compile-time layout assertions above verify `Fr` has exact size
  // and alignment of `[u64; 4]` with no padding bytes.
  unsafe {
    std::slice::from_raw_parts(
      values.as_ptr().cast::<u8>(),
      size_of_val(values),
    )
  }
}

#[cfg(not(feature = "cuda"))]
#[inline]
fn limbs_slice_as_bytes_mut(values: &mut [[u64; 4]]) -> &mut [u8] {
  // SAFETY: `[u64; 4]` is plain-old-data with no padding bytes or invalid bit
  // patterns; reading arbitrary bytes into it is always sound.
  unsafe {
    std::slice::from_raw_parts_mut(
      values.as_mut_ptr().cast::<u8>(),
      size_of_val(values),
    )
  }
}

/// Ephemeral unlinked process-local spill of a stage-1 trace's natural-domain
/// evaluations in raw Montgomery limb format, consumed once by lookup
/// construction to avoid redundant forward BN254 FFTs and dropped immediately.
#[cfg(not(feature = "cuda"))]
pub(super) struct SpilledEvaluations {
  file: DiskFile,
  domain: Radix2Coset,
  width: usize,
  len: usize,
  digest: blake3::Hash,
}

#[cfg(not(feature = "cuda"))]
impl SpilledEvaluations {
  pub(super) fn spill(
    spill_dir: &Path,
    domain: Radix2Coset,
    matrix: &RowMajorMatrix<Scalar>,
  ) -> std::io::Result<Self> {
    let mut disk = DiskFile::temporary(spill_dir)?;
    let values = &matrix.values;
    let total_bytes = u64::try_from(values.len())
      .ok()
      .and_then(|n| n.checked_mul(32))
      .ok_or_else(|| {
        std::io::Error::new(
          std::io::ErrorKind::InvalidInput,
          "spilled evaluation byte length overflow",
        )
      })?;
    let mut hasher = blake3::Hasher::new();
    // SAFETY: `Scalar` is `#[repr(transparent)]` over `Fr`.
    let frs = unsafe {
      std::slice::from_raw_parts(values.as_ptr().cast::<Fr>(), values.len())
    };
    let mut offset = 0u64;
    for chunk in frs.chunks(CHUNK) {
      let bytes = fr_slice_as_bytes(chunk);
      update_hash(&mut hasher, bytes);
      disk.file_mut().write_all(bytes)?;
      let len = u64::try_from(bytes.len()).expect("chunk fits u64");
      fadvise_dontneed(disk.file(), offset, len);
      offset = offset.saturating_add(len);
    }
    debug_assert_eq!(offset, total_bytes);
    Ok(Self {
      file: disk,
      domain,
      width: matrix.width,
      len: values.len(),
      digest: hasher.finalize(),
    })
  }

  pub(super) fn domain(&self) -> Radix2Coset {
    self.domain
  }

  pub(super) fn load(
    mut self,
  ) -> Result<RowMajorMatrix<Scalar>, SerializationError> {
    let file = self.file.file_mut();
    fadvise_sequential(file);
    file.seek(SeekFrom::Start(0))?;
    let mut out: Vec<Scalar> = Vec::new();
    out
      .try_reserve_exact(self.len)
      .map_err(|_error| SerializationError::InvalidData)?;
    let mut raw = vec![[0u64; 4]; CHUNK.min(self.len)];
    let mut hasher = blake3::Hasher::new();
    let mut offset = 0u64;
    for start in (0..self.len).step_by(CHUNK) {
      let count = CHUNK.min(self.len - start);
      let slice = &mut raw[..count];
      let bytes = limbs_slice_as_bytes_mut(slice);
      file.read_exact(bytes)?;
      update_hash(&mut hasher, bytes);
      let len = u64::try_from(bytes.len()).expect("chunk fits u64");
      fadvise_dontneed(file, offset, len);
      offset = offset.saturating_add(len);
      out.spare_capacity_mut()[start..start + count]
        .par_chunks_mut(2048)
        .zip(slice.par_chunks(2048))
        .try_for_each(|(dst, src)| {
          for (slot, &limbs) in dst.iter_mut().zip(src) {
            let value = BigInt(limbs);
            if value >= Fr::MODULUS {
              return Err(SerializationError::InvalidData);
            }
            slot.write(Scalar(Fr::new_unchecked(value)));
          }
          Ok::<_, SerializationError>(())
        })?;
    }
    if hasher.finalize() != self.digest {
      return Err(SerializationError::InvalidData);
    }
    // SAFETY: Every element in `0..self.len` was initialized in the loop above.
    unsafe { out.set_len(self.len) };
    // `self` drops here, closing the unlinked temp file and releasing disk space.
    Ok(RowMajorMatrix::new(out, self.width))
  }
}

pub(super) enum Column {
  /// A constant polynomial, still bound to its full trace domain.
  Constant {
    value: Fr,
    len: usize,
  },
  Resident {
    values: Arc<Vec<Fr>>,
    range: Range<usize>,
  },
  Disk {
    file: Arc<Mutex<DiskFile>>,
    offset: u64,
    len: usize,
    chunk: usize,
    digest: blake3::Hash,
    format: DiskFormat,
  },
}

impl From<Vec<Fr>> for Column {
  fn from(values: Vec<Fr>) -> Self {
    if values.iter().skip(1).all(Zero::is_zero) {
      return Self::Constant {
        value: values.first().copied().unwrap_or_default(),
        len: values.len(),
      };
    }
    let range = 0..values.len();
    Self::Resident { values: Arc::new(values), range }
  }
}

impl Column {
  /// Host coefficients of a resident column; compact constant and
  /// disk-backed columns return `None` and are read through [`Self::visit`]
  /// or [`Self::load`].
  pub(super) fn resident(&self) -> Option<&[Fr]> {
    match self {
      Self::Resident { values, range } => Some(&values[range.clone()]),
      Self::Constant { .. } | Self::Disk { .. } => None,
    }
  }

  /// Host coefficients without materializing a constant column: a constant
  /// is the one-element slice of its constant term. Disk-backed columns
  /// return `None`.
  #[cfg(feature = "cuda")]
  pub(super) fn host_coefficients(&self) -> Option<&[Fr]> {
    match self {
      Self::Constant { value, .. } => Some(std::slice::from_ref(value)),
      _ => self.resident(),
    }
  }

  pub(super) fn len(&self) -> usize {
    match self {
      Self::Resident { range, .. } => range.len(),
      Self::Constant { len, .. } | Self::Disk { len, .. } => *len,
    }
  }

  pub(super) fn slice(&self, range: Range<usize>) -> Self {
    assert!(range.start <= range.end && range.end <= self.len());
    match self {
      Self::Constant { value, .. } => Self::Constant {
        value: if range.start == 0 && !range.is_empty() {
          *value
        } else {
          Fr::default()
        },
        len: range.len(),
      },
      Self::Resident { values, range: parent } => Self::Resident {
        values: values.clone(),
        range: parent.start + range.start..parent.start + range.end,
      },
      Self::Disk { .. } => {
        unreachable!("quotient slicing precedes checkpointing")
      },
    }
  }

  pub(super) fn index_with_chunk(
    reader: &mut (impl Read + Seek),
    file: Arc<Mutex<DiskFile>>,
    len: usize,
    chunk: usize,
  ) -> Result<Self, SerializationError> {
    assert!(chunk > 0);
    let offset = reader.stream_position()?;
    let mut remaining =
      len.checked_mul(32).ok_or(SerializationError::InvalidData)?;
    let mut bytes = vec![0u8; (chunk * 32).min(remaining)];
    let mut hash = blake3::Hasher::new();
    while remaining != 0 {
      let n = remaining.min(bytes.len());
      reader.read_exact(&mut bytes[..n])?;
      update_hash(&mut hash, &bytes[..n]);
      remaining -= n;
    }
    Ok(Self::Disk {
      file,
      offset,
      len,
      chunk,
      digest: hash.finalize(),
      format: DiskFormat::Canonical,
    })
  }

  /// Construct a disk-backed column from an already-written and hashed span
  /// in a persistent canonical checkpoint file.
  #[cfg(not(feature = "cuda"))]
  pub(super) fn from_disk(
    file: Arc<Mutex<DiskFile>>,
    offset: u64,
    len: usize,
    digest: blake3::Hash,
  ) -> Self {
    Self::Disk {
      file,
      offset,
      len,
      chunk: CHUNK,
      digest,
      format: DiskFormat::Canonical,
    }
  }

  /// Convenience wrapper around [`Self::spill_to_disk_with_chunk`] using the
  /// default [`CHUNK`] size.
  #[cfg(all(test, not(feature = "cuda")))]
  pub(super) fn spill_to_disk(
    file: &Arc<Mutex<DiskFile>>,
    offset: &mut u64,
    coeffs: &[Fr],
  ) -> std::io::Result<Self> {
    Self::spill_to_disk_with_chunk(file, offset, coeffs, CHUNK)
  }

  /// Write non-constant coefficients to an ephemeral spill `file` at `*offset`
  /// in raw Montgomery limb format, hashing them on the fly, and return a
  /// disk-backed [`Column`]. Constant polynomials stay compact in memory
  /// without touching disk.
  #[cfg(not(feature = "cuda"))]
  pub(super) fn spill_to_disk_with_chunk(
    file: &Arc<Mutex<DiskFile>>,
    offset: &mut u64,
    coeffs: &[Fr],
    chunk: usize,
  ) -> std::io::Result<Self> {
    assert!(chunk > 0);
    if coeffs.iter().skip(1).all(Zero::is_zero) {
      return Ok(Self::Constant {
        value: coeffs.first().copied().unwrap_or_default(),
        len: coeffs.len(),
      });
    }
    let start = *offset;
    let byte_len = u64::try_from(coeffs.len())
      .ok()
      .and_then(|n| n.checked_mul(32))
      .ok_or_else(|| {
        std::io::Error::new(
          std::io::ErrorKind::InvalidInput,
          "spilled column byte length overflow",
        )
      })?;
    let mut guard = file.lock().map_err(|_error| {
      std::io::Error::other("spilled column file lock poisoned")
    })?;
    guard.file_mut().seek(SeekFrom::Start(start))?;
    let mut hasher = blake3::Hasher::new();
    let mut pos = start;
    for part in coeffs.chunks(chunk) {
      let bytes = fr_slice_as_bytes(part);
      update_hash(&mut hasher, bytes);
      guard.file_mut().write_all(bytes)?;
      let len = u64::try_from(bytes.len()).expect("chunk fits u64");
      fadvise_dontneed(guard.file(), pos, len);
      pos = pos.saturating_add(len);
    }
    let digest = hasher.finalize();
    drop(guard);
    *offset = start.checked_add(byte_len).ok_or_else(|| {
      std::io::Error::new(
        std::io::ErrorKind::InvalidInput,
        "spilled column file offset overflow",
      )
    })?;
    Ok(Self::Disk {
      file: Arc::clone(file),
      offset: start,
      len: coeffs.len(),
      chunk,
      digest,
      format: DiskFormat::RawMontgomery,
    })
  }

  /// Check the bytes on every access; changing/truncating a checkpoint fails
  /// closed. The file must already be trusted when first indexed.
  pub(super) fn visit(
    &self,
    mut visit: impl FnMut(usize, &[Fr]),
  ) -> Result<(), SerializationError> {
    match self {
      Self::Constant { value, len } => {
        let mut values = vec![Fr::default(); CHUNK.min(*len)];
        for start in (0..*len).step_by(CHUNK) {
          values[0] = if start == 0 { *value } else { Fr::default() };
          visit(start, &values[..CHUNK.min(len - start)]);
        }
      },
      Self::Resident { values, range } => visit(0, &values[range.clone()]),
      Self::Disk { file, offset, len, chunk, digest, format } => {
        let chunk = *chunk;
        let mut guard =
          file.lock().map_err(|_error| SerializationError::InvalidData)?;
        let file = guard.file_mut();
        file.seek(SeekFrom::Start(*offset))?;
        let chunk_elems = chunk.min(*len);
        let mut values = vec![Fr::default(); chunk_elems];
        let mut hash = blake3::Hasher::new();
        let mut pos = *offset;
        match format {
          DiskFormat::Canonical => {
            let mut bytes = vec![0u8; chunk_elems * 32];
            for start in (0..*len).step_by(chunk) {
              let count = chunk.min(len - start);
              let bytes = &mut bytes[..count * 32];
              file.read_exact(bytes)?;
              update_hash(&mut hash, bytes);
              let byte_len =
                u64::try_from(bytes.len()).expect("chunk fits u64");
              fadvise_dontneed(file, pos, byte_len);
              pos = pos.saturating_add(byte_len);
              values[..count]
                .par_chunks_mut(2048)
                .zip(bytes.par_chunks(32 * 2048))
                .try_for_each(|(dst, src)| {
                  for (slot, chunk) in
                    dst.iter_mut().zip(src.as_chunks::<32>().0)
                  {
                    let limbs: [u64; 4] = std::array::from_fn(|i| {
                      u64::from_le_bytes(chunk.as_chunks::<8>().0[i])
                    });
                    *slot = Fr::from_bigint(BigInt(limbs))
                      .ok_or(SerializationError::InvalidData)?;
                  }
                  Ok::<_, SerializationError>(())
                })?;
              visit(start, &values[..count]);
            }
          },
          #[cfg(not(feature = "cuda"))]
          DiskFormat::RawMontgomery => {
            let mut raw = vec![[0u64; 4]; chunk_elems];
            for start in (0..*len).step_by(chunk) {
              let count = chunk.min(len - start);
              let slice = &mut raw[..count];
              let bytes = limbs_slice_as_bytes_mut(slice);
              file.read_exact(bytes)?;
              update_hash(&mut hash, bytes);
              let byte_len =
                u64::try_from(bytes.len()).expect("chunk fits u64");
              fadvise_dontneed(file, pos, byte_len);
              pos = pos.saturating_add(byte_len);
              values[..count]
                .par_chunks_mut(2048)
                .zip(slice.par_chunks(2048))
                .try_for_each(|(dst, src)| {
                  for (slot, &limbs) in dst.iter_mut().zip(src) {
                    let value = BigInt(limbs);
                    if value >= Fr::MODULUS {
                      return Err(SerializationError::InvalidData);
                    }
                    *slot = Fr::new_unchecked(value);
                  }
                  Ok::<_, SerializationError>(())
                })?;
              visit(start, &values[..count]);
            }
          },
        }
        if hash.finalize() != *digest {
          return Err(SerializationError::InvalidData);
        }
      },
    }
    Ok(())
  }

  pub(super) fn load(&self) -> Result<Cow<'_, [Fr]>, SerializationError> {
    if let Self::Resident { values, range } = self {
      return Ok(Cow::Borrowed(&values[range.clone()]));
    }
    let mut values = Vec::with_capacity(self.len());
    self.visit(|_, chunk| values.extend_from_slice(chunk))?;
    Ok(Cow::Owned(values))
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn constant_polynomials_preserve_length_slices_and_chunk_offsets() {
    for len in [0, 1, CHUNK - 1, CHUNK, CHUNK + 3] {
      let mut expected = vec![Fr::default(); len];
      if len != 0 {
        expected[0] = Fr::from(7u8);
      }
      let column = Column::from(expected.clone());
      assert!(matches!(column, Column::Constant { .. }));
      assert_eq!(column.len(), len);
      assert_eq!(column.load().unwrap().as_ref(), expected);
      let mut visited = vec![];
      column
        .visit(|start, values| {
          assert_eq!(start, visited.len());
          visited.extend_from_slice(values);
        })
        .unwrap();
      assert_eq!(visited, expected);
      for range in [0..len, 0..0, len / 2..len, len..len] {
        assert_eq!(
          column.slice(range.clone()).load().unwrap().as_ref(),
          &expected[range]
        );
      }
    }
    assert!(matches!(
      Column::from(vec![Fr::default(), Fr::from(1u8)]),
      Column::Resident { .. }
    ));
  }

  #[cfg(not(feature = "cuda"))]
  #[test]
  fn raw_montgomery_spill_roundtrips_and_detects_corruption() {
    use ark_ff::Field;
    let dir = crate::test_support::TempDir::new("raw-mont-spill");
    let spill_dir = dir.join("spill");
    let file = Arc::new(Mutex::new(DiskFile::temporary(&spill_dir).unwrap()));
    let coeffs: Vec<Fr> = (0..CHUNK + 17)
      .map(|i| Fr::from(u64::try_from(i).unwrap() + 3).square())
      .collect();
    let mut offset = 0u64;
    let col = Column::spill_to_disk(&file, &mut offset, &coeffs).unwrap();
    assert_eq!(offset, u64::try_from(coeffs.len() * 32).unwrap());
    assert_eq!(col.load().unwrap().as_ref(), coeffs.as_slice());

    // Flip a byte in the temp file and verify visit/load fails closed.
    {
      let mut guard = file.lock().unwrap();
      guard.file_mut().seek(SeekFrom::Start(64)).unwrap();
      let mut byte = [0u8; 1];
      guard.file_mut().read_exact(&mut byte).unwrap();
      byte[0] ^= 1;
      guard.file_mut().seek(SeekFrom::Start(64)).unwrap();
      guard.file_mut().write_all(&byte).unwrap();
    }
    assert!(col.load().is_err());

    // Verify SpilledEvaluations roundtrips a multi-column matrix identically.
    let domain = Radix2Coset { log_size: 4, shift: Scalar(Fr::ONE) };
    let matrix = RowMajorMatrix::new(
      (0..16 * 3)
        .map(|i| Scalar(Fr::from(u64::try_from(i * 13 + 7).unwrap())))
        .collect(),
      3,
    );
    let spilled =
      SpilledEvaluations::spill(&spill_dir, domain, &matrix).unwrap();
    assert_eq!(spilled.domain(), domain);
    assert_eq!(spilled.load().unwrap(), matrix);
  }
}
