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
  io::{BufWriter, Write},
  path::Path,
  sync::atomic::{AtomicU64, Ordering},
};

use super::curve::Fr;
use ark_ff::Zero;
use ark_serialize::{CanonicalDeserialize, SerializationError};
use p3_maybe_rayon::prelude::*;

pub(super) const CHUNK: usize = 1 << 16;

/// An open coefficient file. Temporary spill files unlink themselves on
/// creation (Unix) or remove their path on drop (other targets).
pub(super) struct DiskFile {
  file: File,
  remove_on_drop: Option<PathBuf>,
}

impl DiskFile {
  pub(super) fn persistent(file: File) -> Self {
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
      hash.update(&bytes[..n]);
      remaining -= n;
    }
    Ok(Self::Disk { file, offset, len, chunk, digest: hash.finalize() })
  }

  /// Construct a disk-backed column from an already-written and hashed span.
  #[cfg(not(feature = "cuda"))]
  pub(super) fn from_disk(
    file: Arc<Mutex<DiskFile>>,
    offset: u64,
    len: usize,
    digest: blake3::Hash,
  ) -> Self {
    Self::Disk { file, offset, len, chunk: CHUNK, digest }
  }

  /// Write non-constant coefficients to `file` at `*offset`, hashing them on
  /// the fly, and return a disk-backed [`Column`]. Constant polynomials stay
  /// compact in memory without touching disk.
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
    struct HashingWriter<'a, W> {
      inner: &'a mut W,
      hasher: blake3::Hasher,
    }
    impl<W: Write> Write for HashingWriter<'_, W> {
      fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        let n = self.inner.write(buf)?;
        if n >= 128 << 10 {
          self.hasher.update_rayon(&buf[..n]);
        } else {
          self.hasher.update(&buf[..n]);
        }
        Ok(n)
      }
      fn flush(&mut self) -> std::io::Result<()> {
        self.inner.flush()
      }
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
    let mut buffered = BufWriter::with_capacity(1 << 20, guard.file_mut());
    let mut hashing =
      HashingWriter { inner: &mut buffered, hasher: blake3::Hasher::new() };
    super::encoding::write_fields(&mut hashing, coeffs, |v| *v)?;
    let digest = hashing.hasher.finalize();
    buffered.flush()?;
    drop(buffered);
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
      Self::Disk { file, offset, len, chunk, digest } => {
        let chunk = *chunk;
        let mut guard =
          file.lock().map_err(|_error| SerializationError::InvalidData)?;
        let file = guard.file_mut();
        file.seek(SeekFrom::Start(*offset))?;
        let mut bytes = vec![0u8; chunk.min(*len) * 32];
        let mut values = vec![Fr::default(); chunk.min(*len)];
        let mut hash = blake3::Hasher::new();
        for start in (0..*len).step_by(chunk) {
          let count = chunk.min(len - start);
          let bytes = &mut bytes[..count * 32];
          file.read_exact(bytes)?;
          hash.update(bytes);
          values[..count]
            .par_iter_mut()
            .zip(bytes.par_chunks(32))
            .try_for_each(|(dst, src)| {
              *dst = Fr::deserialize_compressed(src)?;
              Ok::<_, SerializationError>(())
            })?;
          visit(start, &values[..count]);
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
}
