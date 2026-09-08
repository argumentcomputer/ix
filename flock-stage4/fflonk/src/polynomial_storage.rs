use ark_bls12_381::Fr;
use ark_ff::{BigInt, PrimeField, Zero};
use std::borrow::Cow;
use std::fmt;
use std::io::{Read, Seek, SeekFrom, Write};
use std::sync::Mutex;

/// Maximum number of field elements in one authenticated polynomial chunk.
pub const FFLONK_POLYNOMIAL_CHUNK_FIELDS: usize = 65_536;
const FIELD_BYTES: usize = 32;
const CHUNK_DOMAIN: &[u8] = b"ix:stage4:fflonk-polynomial-chunk:bls12-381:v1";

/// Read access to a fixed sequence of field elements in ascending index order.
///
/// Implementations must return exactly the requested range, reject out-of-range
/// reads, and keep the sequence fixed for the duration of preprocessing/proving.
/// File-backed keys and prover workspaces authenticate each read against
/// retained hashes of the generated values. `as_slice`, when provided, must
/// expose the same sequence as `read_fields`.
pub trait FflonkPolynomialSourceV1 {
  fn len(&self) -> usize;

  fn is_empty(&self) -> bool {
    self.len() == 0
  }

  fn read_fields(
    &self,
    start: usize,
    output: &mut [Fr],
  ) -> Result<(), FflonkStorageError>;

  fn as_slice(&self) -> Option<&[Fr]> {
    None
  }

  /// One past the last nonzero field, or zero for an all-zero sequence.
  /// A cached value must describe the same fixed sequence as `read_fields`.
  fn nonzero_len(&self) -> Result<usize, FflonkStorageError> {
    if let Some(values) = self.as_slice() {
      return Ok(
        values
          .iter()
          .rposition(|value| !value.is_zero())
          .map_or(0, |index| index + 1),
      );
    }
    let mut values =
      vec![Fr::zero(); self.len().min(FFLONK_POLYNOMIAL_CHUNK_FIELDS)];
    for index in (0..self.len().div_ceil(FFLONK_POLYNOMIAL_CHUNK_FIELDS)).rev()
    {
      let start = index * FFLONK_POLYNOMIAL_CHUNK_FIELDS;
      let count = values.len().min(self.len() - start);
      self.read_fields(start, &mut values[..count])?;
      if let Some(last) =
        values[..count].iter().rposition(|value| !value.is_zero())
      {
        return Ok(start + last + 1);
      }
    }
    Ok(0)
  }
}

impl FflonkPolynomialSourceV1 for [Fr] {
  fn len(&self) -> usize {
    self.len()
  }

  fn read_fields(
    &self,
    start: usize,
    output: &mut [Fr],
  ) -> Result<(), FflonkStorageError> {
    let end = checked_range(self.len(), start, output.len())?;
    output.copy_from_slice(&self[start..end]);
    Ok(())
  }

  fn as_slice(&self) -> Option<&[Fr]> {
    Some(self)
  }
}

impl<T: FflonkPolynomialSourceV1 + ?Sized> FflonkPolynomialSourceV1 for &T {
  fn len(&self) -> usize {
    T::len(self)
  }

  fn read_fields(
    &self,
    start: usize,
    output: &mut [Fr],
  ) -> Result<(), FflonkStorageError> {
    T::read_fields(self, start, output)
  }

  fn as_slice(&self) -> Option<&[Fr]> {
    T::as_slice(self)
  }

  fn nonzero_len(&self) -> Result<usize, FflonkStorageError> {
    T::nonzero_len(self)
  }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FflonkStorageError {
  Io(std::io::ErrorKind),
  Range,
  CountOverflow,
  NonemptyFile,
  ChunkChanged { offset: u64 },
  NoncanonicalField,
  Poisoned,
}

impl fmt::Display for FflonkStorageError {
  fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::Io(kind) => {
        write!(formatter, "FFLONK polynomial I/O failed: {kind}")
      },
      Self::Range => {
        formatter.write_str("FFLONK polynomial read is out of range")
      },
      Self::CountOverflow => {
        formatter.write_str("FFLONK polynomial storage size overflow")
      },
      Self::NonemptyFile => {
        formatter.write_str("FFLONK polynomial scratch file must be empty")
      },
      Self::ChunkChanged { offset } => write!(
        formatter,
        "FFLONK polynomial chunk at byte {offset} changed after generation"
      ),
      Self::NoncanonicalField => formatter
        .write_str("FFLONK polynomial contains a noncanonical field element"),
      Self::Poisoned => {
        formatter.write_str("FFLONK polynomial storage lock was poisoned")
      },
    }
  }
}

impl std::error::Error for FflonkStorageError {}

impl From<std::io::Error> for FflonkStorageError {
  fn from(error: std::io::Error) -> Self {
    Self::Io(error.kind())
  }
}

pub(crate) fn load_polynomial(
  source: &(impl FflonkPolynomialSourceV1 + ?Sized),
) -> Result<Cow<'_, [Fr]>, FflonkStorageError> {
  if let Some(values) = source.as_slice() {
    return Ok(Cow::Borrowed(values));
  }
  let mut values = vec![Fr::zero(); source.len()];
  source.read_fields(0, &mut values)?;
  Ok(Cow::Owned(values))
}

pub(crate) fn for_each_polynomial_chunk(
  source: &(impl FflonkPolynomialSourceV1 + ?Sized),
  mut consume: impl FnMut(usize, &[Fr]),
) -> Result<(), FflonkStorageError> {
  if let Some(values) = source.as_slice() {
    for (index, chunk) in
      values.chunks(FFLONK_POLYNOMIAL_CHUNK_FIELDS).enumerate()
    {
      consume(index * FFLONK_POLYNOMIAL_CHUNK_FIELDS, chunk);
    }
  } else {
    let mut values =
      vec![Fr::zero(); source.len().min(FFLONK_POLYNOMIAL_CHUNK_FIELDS)];
    for start in (0..source.len()).step_by(FFLONK_POLYNOMIAL_CHUNK_FIELDS) {
      let len = values.len().min(source.len() - start);
      source.read_fields(start, &mut values[..len])?;
      consume(start, &values[..len]);
    }
  }
  Ok(())
}

pub(crate) fn evaluate_polynomial_source<const N: usize>(
  source: &(impl FflonkPolynomialSourceV1 + ?Sized),
  points: &[Fr; N],
) -> Result<[Fr; N], FflonkStorageError> {
  let mut output = [Fr::zero(); N];
  let mut consume = |values: &[Fr]| {
    for coefficient in values.iter().rev() {
      for (value, point) in output.iter_mut().zip(points) {
        *value = *value * point + coefficient;
      }
    }
  };
  if let Some(values) = source.as_slice() {
    consume(values);
  } else {
    let mut values =
      vec![Fr::zero(); source.len().min(FFLONK_POLYNOMIAL_CHUNK_FIELDS)];
    for index in
      (0..source.len().div_ceil(FFLONK_POLYNOMIAL_CHUNK_FIELDS)).rev()
    {
      let start = index * FFLONK_POLYNOMIAL_CHUNK_FIELDS;
      let len = values.len().min(source.len() - start);
      source.read_fields(start, &mut values[..len])?;
      consume(&values[..len]);
    }
  }
  Ok(output)
}

#[derive(Debug)]
pub(crate) struct PolynomialFile<R> {
  file: Mutex<R>,
}

#[derive(Debug)]
pub(crate) struct StoredPolynomial {
  offset: u64,
  len: usize,
  nonzero_len: usize,
  end: u64,
  chunk_digests: Vec<[u8; 32]>,
}

impl StoredPolynomial {
  pub(crate) fn nonzero_len(&self) -> usize {
    self.nonzero_len
  }

  pub(crate) fn end(&self) -> u64 {
    self.end
  }

  pub(crate) fn authentication_bytes(&self) -> usize {
    self.chunk_digests.capacity() * 32
  }
}

impl<R: Read + Write + Seek> PolynomialFile<R> {
  pub(crate) fn new(mut file: R) -> Result<Self, FflonkStorageError> {
    if file.seek(SeekFrom::End(0))? != 0 {
      return Err(FflonkStorageError::NonemptyFile);
    }
    Ok(Self { file: Mutex::new(file) })
  }

  // The caller reserves a range that does not overlap any live polynomial.
  // Hashes come from generated bytes before writing, never from the file.
  pub(crate) fn write_polynomial(
    &self,
    offset: u64,
    source: &(impl FflonkPolynomialSourceV1 + ?Sized),
    batch_fields: usize,
  ) -> Result<StoredPolynomial, FflonkStorageError> {
    self.write_generated(offset, source.len(), batch_fields, |start, output| {
      source.read_fields(start, output)
    })
  }

  pub(crate) fn write_generated<E: From<FflonkStorageError>>(
    &self,
    offset: u64,
    len: usize,
    batch_fields: usize,
    mut generate: impl FnMut(usize, &mut [Fr]) -> Result<(), E>,
  ) -> Result<StoredPolynomial, E> {
    if batch_fields == 0
      || !batch_fields.is_multiple_of(FFLONK_POLYNOMIAL_CHUNK_FIELDS)
    {
      return Err(FflonkStorageError::Range.into());
    }
    let end = offset
      .checked_add(field_bytes(len)?)
      .ok_or(FflonkStorageError::CountOverflow)?;
    let mut chunk_digests =
      Vec::with_capacity(len.div_ceil(FFLONK_POLYNOMIAL_CHUNK_FIELDS));
    let mut values = vec![Fr::zero(); len.min(batch_fields)];
    let mut encoded =
      vec![0u8; len.min(FFLONK_POLYNOMIAL_CHUNK_FIELDS) * FIELD_BYTES];
    let mut cursor = offset;
    let mut nonzero_len = 0;
    for start in (0..len).step_by(batch_fields) {
      let count = values.len().min(len - start);
      // The generator may read another polynomial in this file.
      // Never hold the file lock across this call.
      generate(start, &mut values[..count])?;
      if let Some(last) =
        values[..count].iter().rposition(|value| !value.is_zero())
      {
        nonzero_len = start + last + 1;
      }
      for chunk in values[..count].chunks(FFLONK_POLYNOMIAL_CHUNK_FIELDS) {
        let bytes = &mut encoded[..chunk.len() * FIELD_BYTES];
        for (value, record) in
          chunk.iter().zip(bytes.as_chunks_mut::<FIELD_BYTES>().0)
        {
          encode_field(value, record);
        }
        chunk_digests.push(chunk_digest(cursor, bytes));
        self.write_chunk(cursor, bytes)?;
        cursor += bytes.len() as u64;
      }
    }
    self.flush()?;
    debug_assert_eq!(cursor, end);
    Ok(StoredPolynomial { offset, len, nonzero_len, end, chunk_digests })
  }

  fn write_chunk(
    &self,
    offset: u64,
    bytes: &[u8],
  ) -> Result<(), FflonkStorageError> {
    let mut file =
      self.file.lock().map_err(|_| FflonkStorageError::Poisoned)?;
    file.seek(SeekFrom::Start(offset))?;
    file.write_all(bytes)?;
    Ok(())
  }

  fn flush(&self) -> Result<(), FflonkStorageError> {
    self.file.lock().map_err(|_| FflonkStorageError::Poisoned)?.flush()?;
    Ok(())
  }
}

impl<R: Read + Seek> PolynomialFile<R> {
  pub(crate) fn source<'a>(
    &'a self,
    polynomial: &'a StoredPolynomial,
  ) -> impl FflonkPolynomialSourceV1 + 'a {
    StoredPolynomialRef { file: self, polynomial }
  }
}

struct StoredPolynomialRef<'a, R> {
  file: &'a PolynomialFile<R>,
  polynomial: &'a StoredPolynomial,
}

impl<R: Read + Seek> FflonkPolynomialSourceV1 for StoredPolynomialRef<'_, R> {
  fn len(&self) -> usize {
    self.polynomial.len
  }

  fn nonzero_len(&self) -> Result<usize, FflonkStorageError> {
    Ok(self.polynomial.nonzero_len)
  }

  fn read_fields(
    &self,
    start: usize,
    output: &mut [Fr],
  ) -> Result<(), FflonkStorageError> {
    let end = checked_range(self.len(), start, output.len())?;
    if output.is_empty() {
      return Ok(());
    }
    let mut encoded =
      vec![0u8; self.len().min(FFLONK_POLYNOMIAL_CHUNK_FIELDS) * FIELD_BYTES];
    let mut file =
      self.file.file.lock().map_err(|_| FflonkStorageError::Poisoned)?;
    for index in start / FFLONK_POLYNOMIAL_CHUNK_FIELDS
      ..end.div_ceil(FFLONK_POLYNOMIAL_CHUNK_FIELDS)
    {
      let chunk_start = index * FFLONK_POLYNOMIAL_CHUNK_FIELDS;
      let chunk_len =
        FFLONK_POLYNOMIAL_CHUNK_FIELDS.min(self.len() - chunk_start);
      let offset = self.polynomial.offset + field_bytes(chunk_start)?;
      let bytes = &mut encoded[..chunk_len * FIELD_BYTES];
      file.seek(SeekFrom::Start(offset))?;
      file.read_exact(bytes)?;
      if chunk_digest(offset, bytes) != self.polynomial.chunk_digests[index] {
        return Err(FflonkStorageError::ChunkChanged { offset });
      }
      let from = start.max(chunk_start);
      let to = end.min(chunk_start + chunk_len);
      let records = &bytes
        [(from - chunk_start) * FIELD_BYTES..(to - chunk_start) * FIELD_BYTES];
      for (value, record) in output[from - start..to - start]
        .iter_mut()
        .zip(records.as_chunks::<FIELD_BYTES>().0)
      {
        let limbs = core::array::from_fn(|i| {
          u64::from_le_bytes(
            record[i * 8..i * 8 + 8].try_into().expect("eight-byte limb"),
          )
        });
        *value = Fr::from_bigint(BigInt(limbs))
          .ok_or(FflonkStorageError::NoncanonicalField)?;
      }
    }
    Ok(())
  }
}

pub(crate) fn encode_field(value: &Fr, output: &mut [u8; FIELD_BYTES]) {
  for (limb, bytes) in
    value.into_bigint().0.into_iter().zip(output.as_chunks_mut::<8>().0)
  {
    bytes.copy_from_slice(&limb.to_le_bytes());
  }
}

pub(crate) fn checked_range(
  len: usize,
  start: usize,
  count: usize,
) -> Result<usize, FflonkStorageError> {
  start
    .checked_add(count)
    .filter(|end| *end <= len)
    .ok_or(FflonkStorageError::Range)
}

pub(crate) fn field_bytes(count: usize) -> Result<u64, FflonkStorageError> {
  u64::try_from(count)
    .ok()
    .and_then(|count| count.checked_mul(FIELD_BYTES as u64))
    .ok_or(FflonkStorageError::CountOverflow)
}

fn chunk_digest(offset: u64, bytes: &[u8]) -> [u8; 32] {
  let mut hasher = blake3::Hasher::new();
  hasher.update(CHUNK_DOMAIN);
  hasher.update(&offset.to_le_bytes());
  hasher.update(&(bytes.len() as u64).to_le_bytes());
  hasher.update(bytes);
  *hasher.finalize().as_bytes()
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::evaluate_polynomial;
  use ark_ff::Field;
  use std::io::{self, Cursor};

  struct ShortIo {
    bytes: Cursor<Vec<u8>>,
    largest_read: usize,
    largest_write: usize,
    fail_read: bool,
    fail_write: bool,
    fail_flush: bool,
    fail_seek: bool,
  }

  impl ShortIo {
    fn new() -> Self {
      Self {
        bytes: Cursor::new(Vec::new()),
        largest_read: 0,
        largest_write: 0,
        fail_read: false,
        fail_write: false,
        fail_flush: false,
        fail_seek: false,
      }
    }
  }

  impl Read for ShortIo {
    fn read(&mut self, output: &mut [u8]) -> io::Result<usize> {
      if self.fail_read {
        return Err(io::ErrorKind::BrokenPipe.into());
      }
      self.largest_read = self.largest_read.max(output.len());
      let len = output.len().min(4093);
      self.bytes.read(&mut output[..len])
    }
  }

  impl Write for ShortIo {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
      if self.fail_write {
        return Err(io::ErrorKind::WriteZero.into());
      }
      self.largest_write = self.largest_write.max(bytes.len());
      self.bytes.write(&bytes[..bytes.len().min(2053)])
    }
    fn flush(&mut self) -> io::Result<()> {
      if self.fail_flush {
        return Err(io::ErrorKind::BrokenPipe.into());
      }
      Ok(())
    }
  }

  impl Seek for ShortIo {
    fn seek(&mut self, position: SeekFrom) -> io::Result<u64> {
      if self.fail_seek {
        return Err(io::ErrorKind::NotSeekable.into());
      }
      self.bytes.seek(position)
    }
  }

  fn values(len: usize) -> Vec<Fr> {
    (0..len)
      .map(|index| {
        let value = Fr::from(index as u64).square() + Fr::from(19u64);
        if index % 3 == 0 { -value } else { value }
      })
      .collect()
  }

  #[test]
  fn nonzero_length_handles_padding_empty_sources_and_bounded_reverse_reads() {
    struct Opaque<'a> {
      values: &'a [Fr],
      fail: bool,
    }
    impl FflonkPolynomialSourceV1 for Opaque<'_> {
      fn len(&self) -> usize {
        self.values.len()
      }
      fn read_fields(
        &self,
        start: usize,
        output: &mut [Fr],
      ) -> Result<(), FflonkStorageError> {
        assert!(output.len() <= FFLONK_POLYNOMIAL_CHUNK_FIELDS);
        if self.fail {
          return Err(FflonkStorageError::Io(io::ErrorKind::BrokenPipe));
        }
        self.values.read_fields(start, output)
      }
    }
    let mut fields = vec![Fr::zero(); 2 * FFLONK_POLYNOMIAL_CHUNK_FIELDS + 7];
    for live_len in [0, 1, FFLONK_POLYNOMIAL_CHUNK_FIELDS, fields.len()] {
      fields.fill(Fr::zero());
      if live_len != 0 {
        fields[live_len - 1] = Fr::from(19u64);
      }
      let source = Opaque { values: &fields, fail: false };
      assert_eq!(source.nonzero_len().unwrap(), live_len);
      assert_eq!(fields.as_slice().nonzero_len().unwrap(), live_len);
      let file = PolynomialFile::new(Cursor::new(Vec::new())).unwrap();
      let stored = file
        .write_polynomial(0, fields.as_slice(), FFLONK_POLYNOMIAL_CHUNK_FIELDS)
        .unwrap();
      assert_eq!(file.source(&stored).nonzero_len().unwrap(), live_len);
      assert_eq!(file.source(&stored).len(), fields.len());
    }
    assert_eq!(Opaque { values: &[], fail: false }.nonzero_len().unwrap(), 0);
    assert_eq!(
      Opaque { values: &fields, fail: true }.nonzero_len(),
      Err(FflonkStorageError::Io(io::ErrorKind::BrokenPipe))
    );
  }

  #[test]
  fn field_storage_round_trips_partial_chunks_short_io_and_reverse_evaluation()
  {
    let file = PolynomialFile::new(ShortIo::new()).unwrap();
    let values = values(2 * FFLONK_POLYNOMIAL_CHUNK_FIELDS + 3);
    let stored = file
      .write_polynomial(0, values.as_slice(), FFLONK_POLYNOMIAL_CHUNK_FIELDS)
      .unwrap();
    let source = file.source(&stored);
    assert_eq!(stored.end(), (values.len() * 32) as u64);
    assert_eq!(stored.authentication_bytes(), 96);
    assert_eq!(load_polynomial(&source).unwrap().as_ref(), values);
    for (start, count) in [
      (0, 1),
      (1, 17),
      (FFLONK_POLYNOMIAL_CHUNK_FIELDS - 2, 8),
      (values.len() - 3, 3),
      (values.len(), 0),
    ] {
      let mut actual = vec![Fr::zero(); count];
      source.read_fields(start, &mut actual).unwrap();
      assert_eq!(actual, values[start..start + count]);
    }
    assert_eq!(
      source.read_fields(usize::MAX, &mut [Fr::zero()]),
      Err(FflonkStorageError::Range)
    );
    assert_eq!(
      source.read_fields(values.len() + 1, &mut []),
      Err(FflonkStorageError::Range)
    );
    assert_eq!(
      source.read_fields(values.len(), &mut [Fr::zero()]),
      Err(FflonkStorageError::Range)
    );
    let points = [Fr::zero(), Fr::from(1u64), -Fr::from(1u64), Fr::from(23u64)];
    assert_eq!(
      evaluate_polynomial_source(&source, &points).unwrap(),
      points.map(|point| evaluate_polynomial(&values, point))
    );
    let second = file
      .write_polynomial(
        stored.end(),
        &values[..7],
        FFLONK_POLYNOMIAL_CHUNK_FIELDS,
      )
      .unwrap();
    assert_eq!(
      load_polynomial(&file.source(&second)).unwrap().as_ref(),
      &values[..7]
    );
    let io = file.file.lock().unwrap();
    assert!(io.largest_read <= FFLONK_POLYNOMIAL_CHUNK_FIELDS * 32);
    assert!(io.largest_write <= FFLONK_POLYNOMIAL_CHUNK_FIELDS * 32);
    let mut encoded = [0u8; 32];
    encode_field(&values[0], &mut encoded);
    assert_eq!(&io.bytes.get_ref()[..32], &encoded);
  }

  #[test]
  fn partial_reads_authenticate_the_whole_chunk_and_propagate_truncation() {
    let file = PolynomialFile::new(Cursor::new(Vec::new())).unwrap();
    let values = values(FFLONK_POLYNOMIAL_CHUNK_FIELDS + 3);
    let stored = file
      .write_polynomial(0, values.as_slice(), FFLONK_POLYNOMIAL_CHUNK_FIELDS)
      .unwrap();
    let source = file.source(&stored);
    let last_byte_of_first_chunk = FFLONK_POLYNOMIAL_CHUNK_FIELDS * 32 - 1;
    file.file.lock().unwrap().get_mut()[last_byte_of_first_chunk] ^= 1;
    assert_eq!(
      source.read_fields(0, &mut [Fr::zero()]),
      Err(FflonkStorageError::ChunkChanged { offset: 0 })
    );
    file.file.lock().unwrap().get_mut()[last_byte_of_first_chunk] ^= 1;
    let second_chunk = FFLONK_POLYNOMIAL_CHUNK_FIELDS * 32;
    file.file.lock().unwrap().get_mut()[second_chunk] ^= 1;
    let mut first = [Fr::zero()];
    source.read_fields(0, &mut first).unwrap();
    assert_eq!(first[0], values[0]);
    assert_eq!(
      source.read_fields(FFLONK_POLYNOMIAL_CHUNK_FIELDS, &mut first),
      Err(FflonkStorageError::ChunkChanged { offset: second_chunk as u64 })
    );
    file.file.lock().unwrap().get_mut().truncate(second_chunk + 1);
    assert_eq!(
      source.read_fields(FFLONK_POLYNOMIAL_CHUNK_FIELDS, &mut first),
      Err(FflonkStorageError::Io(io::ErrorKind::UnexpectedEof))
    );
  }

  #[test]
  fn empty_polynomials_and_nonempty_storage_have_explicit_boundaries() {
    let file = PolynomialFile::new(Cursor::new(Vec::new())).unwrap();
    let values: [Fr; 0] = [];
    let stored = file
      .write_polynomial(0, values.as_slice(), FFLONK_POLYNOMIAL_CHUNK_FIELDS)
      .unwrap();
    let source = file.source(&stored);
    assert!(source.is_empty());
    assert_eq!(stored.authentication_bytes(), 0);
    assert_eq!(stored.end(), 0);
    source.read_fields(0, &mut []).unwrap();
    assert_eq!(source.read_fields(1, &mut []), Err(FflonkStorageError::Range));
    assert_eq!(
      evaluate_polynomial_source(&source, &[Fr::from(2u64)]).unwrap(),
      [Fr::zero()]
    );
    assert!(matches!(
      PolynomialFile::new(Cursor::new(vec![0u8])),
      Err(FflonkStorageError::NonemptyFile)
    ));
    assert!(matches!(
      file.write_polynomial(
        u64::MAX,
        &[Fr::from(1u64)][..],
        FFLONK_POLYNOMIAL_CHUNK_FIELDS
      ),
      Err(FflonkStorageError::CountOverflow)
    ));
  }

  #[test]
  fn field_storage_preserves_write_flush_read_seek_and_lock_failures() {
    for failure in 0..2 {
      let file = PolynomialFile::new(ShortIo::new()).unwrap();
      {
        let mut io = file.file.lock().unwrap();
        io.fail_write = failure == 0;
        io.fail_flush = failure == 1;
      }
      let kind = if failure == 0 {
        io::ErrorKind::WriteZero
      } else {
        io::ErrorKind::BrokenPipe
      };
      assert!(
        matches!(file.write_polynomial(0, &[Fr::from(1u64)][..], FFLONK_POLYNOMIAL_CHUNK_FIELDS), Err(FflonkStorageError::Io(actual)) if actual == kind)
      );
    }
    let file = PolynomialFile::new(ShortIo::new()).unwrap();
    let stored = file
      .write_polynomial(
        0,
        &[Fr::from(1u64)][..],
        FFLONK_POLYNOMIAL_CHUNK_FIELDS,
      )
      .unwrap();
    file.file.lock().unwrap().fail_read = true;
    assert_eq!(
      file.source(&stored).read_fields(0, &mut [Fr::zero()]),
      Err(FflonkStorageError::Io(io::ErrorKind::BrokenPipe))
    );
    {
      let mut io = file.file.lock().unwrap();
      io.fail_read = false;
      io.fail_seek = true;
    }
    assert_eq!(
      file.source(&stored).read_fields(0, &mut [Fr::zero()]),
      Err(FflonkStorageError::Io(io::ErrorKind::NotSeekable))
    );
    let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
      let _guard = file.file.lock().unwrap();
      panic!("poison the polynomial file lock");
    }));
    assert_eq!(
      file.source(&stored).read_fields(0, &mut [Fr::zero()]),
      Err(FflonkStorageError::Poisoned)
    );
  }
}
