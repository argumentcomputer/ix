//! Compact constant, resident or checksummed, trusted-local coefficient storage.
use std::{
  borrow::Cow,
  fs::File,
  io::{Read, Seek, SeekFrom},
  ops::Range,
  sync::{Arc, Mutex},
};

use ark_bls12_381::Fr;
use ark_ff::Zero;
use ark_serialize::{CanonicalDeserialize, SerializationError};
use p3_maybe_rayon::prelude::*;

const CHUNK: usize = 1 << 16;

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
    file: Arc<Mutex<File>>,
    offset: u64,
    len: usize,
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
      Self::Constant { value, len } => {
        let mut values = vec![Fr::default(); CHUNK.min(*len)];
        for start in (0..*len).step_by(CHUNK) {
          values[0] = if start == 0 { *value } else { Fr::default() };
          visit(start, &values[..CHUNK.min(len - start)]);
        }
      },
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
