//! Resident or checksummed, trusted-local coefficient storage.
use std::{
  borrow::Cow,
  fs::File,
  io::{Read, Seek, SeekFrom},
  ops::Range,
  sync::{Arc, Mutex},
};

use ark_bls12_381::Fr;
use ark_serialize::{CanonicalDeserialize, SerializationError};
use p3_maybe_rayon::prelude::*;

const CHUNK: usize = 1 << 16;

pub(super) enum Column {
  Resident { values: Arc<Vec<Fr>>, range: Range<usize> },
  Disk { file: Arc<Mutex<File>>, offset: u64, len: usize, digest: blake3::Hash },
}

impl From<Vec<Fr>> for Column {
  fn from(values: Vec<Fr>) -> Self {
    let range = 0..values.len();
    Self::Resident { values: Arc::new(values), range }
  }
}

impl Column {
  pub(super) fn len(&self) -> usize {
    match self {
      Self::Resident { range, .. } => range.len(),
      Self::Disk { len, .. } => *len,
    }
  }

  pub(super) fn slice(&self, range: Range<usize>) -> Self {
    match self {
      Self::Resident { values, range: parent } => {
        assert!(range.start <= range.end && range.end <= parent.len());
        Self::Resident {
          values: values.clone(),
          range: parent.start + range.start..parent.start + range.end,
        }
      },
      Self::Disk { .. } => {
        unreachable!("quotient slicing precedes checkpointing")
      },
    }
  }

  pub(super) fn index(
    reader: &mut (impl Read + Seek),
    file: Arc<Mutex<File>>,
    len: usize,
  ) -> Result<Self, SerializationError> {
    let offset = reader.stream_position()?;
    let mut remaining =
      len.checked_mul(32).ok_or(SerializationError::InvalidData)?;
    let mut bytes = vec![0u8; (CHUNK * 32).min(remaining)];
    let mut hash = blake3::Hasher::new();
    while remaining != 0 {
      let n = remaining.min(bytes.len());
      reader.read_exact(&mut bytes[..n])?;
      hash.update(&bytes[..n]);
      remaining -= n;
    }
    Ok(Self::Disk { file, offset, len, digest: hash.finalize() })
  }

  /// Check the bytes on every access; changing/truncating a checkpoint fails
  /// closed. The file must already be trusted when first indexed.
  pub(super) fn visit(
    &self,
    mut visit: impl FnMut(usize, &[Fr]),
  ) -> Result<(), SerializationError> {
    match self {
      Self::Resident { values, range } => visit(0, &values[range.clone()]),
      Self::Disk { file, offset, len, digest } => {
        let mut file =
          file.lock().map_err(|_error| SerializationError::InvalidData)?;
        file.seek(SeekFrom::Start(*offset))?;
        let mut bytes = vec![0u8; CHUNK.min(*len) * 32];
        let mut values = vec![Fr::default(); CHUNK.min(*len)];
        let mut hash = blake3::Hasher::new();
        for start in (0..*len).step_by(CHUNK) {
          let count = CHUNK.min(len - start);
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
