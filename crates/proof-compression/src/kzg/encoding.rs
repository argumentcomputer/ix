//! Bounded parallel conversion of canonical scalar-field streams.

use std::io::{self, Read, Write};

use ark_bls12_381::Fr;
use ark_ff::{BigInt, PrimeField};
use p3_maybe_rayon::prelude::*;

use super::Scalar;

const BLOCK_FIELDS: usize = 1 << 20;
const FIELD_BYTES: usize = 32;

pub(crate) fn write_fields<T: Sync>(
  writer: &mut impl Write,
  values: &[T],
  field: impl Fn(&T) -> Fr + Sync,
) -> io::Result<()> {
  let mut bytes = vec![0; values.len().min(BLOCK_FIELDS) * FIELD_BYTES];
  for values in values.chunks(BLOCK_FIELDS) {
    let bytes = &mut bytes[..values.len() * FIELD_BYTES];
    bytes
      .par_chunks_mut(FIELD_BYTES * 2048)
      .zip(values.par_chunks(2048))
      .for_each(|(bytes, values)| {
        for (bytes, value) in
          bytes.as_chunks_mut::<FIELD_BYTES>().0.iter_mut().zip(values)
        {
          for (out, limb) in bytes
            .as_chunks_mut::<8>()
            .0
            .iter_mut()
            .zip(field(value).into_bigint().0)
          {
            *out = limb.to_le_bytes();
          }
        }
      });
    writer.write_all(bytes)?;
  }
  Ok(())
}

pub(crate) fn read_fields<T: Copy + Send>(
  reader: &mut impl Read,
  count: usize,
  convert: impl Fn(Fr) -> T + Sync + Send,
) -> io::Result<Vec<T>> {
  let mut values: Vec<T> = Vec::new();
  values.try_reserve_exact(count).map_err(io::Error::other)?;
  let mut bytes = vec![0; count.min(BLOCK_FIELDS) * FIELD_BYTES];
  for start in (0..count).step_by(BLOCK_FIELDS) {
    let block = (count - start).min(BLOCK_FIELDS);
    let bytes = &mut bytes[..block * FIELD_BYTES];
    reader.read_exact(bytes)?;
    values.spare_capacity_mut()[start..start + block]
      .par_chunks_mut(2048)
      .zip(bytes.par_chunks(FIELD_BYTES * 2048))
      .try_for_each(|(output, bytes)| {
        for (slot, bytes) in
          output.iter_mut().zip(bytes.as_chunks::<FIELD_BYTES>().0)
        {
          let limbs: [u64; 4] = std::array::from_fn(|i| {
            u64::from_le_bytes(bytes.as_chunks::<8>().0[i])
          });
          let value = Fr::from_bigint(BigInt(limbs)).ok_or_else(|| {
            io::Error::new(
              io::ErrorKind::InvalidData,
              "noncanonical scalar field element",
            )
          })?;
          slot.write(convert(value));
        }
        Ok::<(), io::Error>(())
      })?;
  }
  // All reads and parallel decoders completed successfully. On any error the
  // vector still has length zero, and partially initialized Copy values need
  // no destructors.
  unsafe { values.set_len(count) };
  Ok(values)
}

/// Write canonical 32-byte little-endian scalars without a length prefix.
pub fn write_scalars(
  writer: &mut impl Write,
  values: &[Scalar],
) -> io::Result<()> {
  write_fields(writer, values, |value| value.0)
}

/// Read exactly `count` canonical scalars, rejecting values at least the modulus.
pub fn read_scalars(
  reader: &mut impl Read,
  count: usize,
) -> io::Result<Vec<Scalar>> {
  read_fields(reader, count, Scalar)
}

#[cfg(test)]
mod tests {
  use super::*;
  use ark_ff::Field;
  use ark_serialize::CanonicalSerialize;

  #[test]
  fn field_stream_matches_arkworks_across_blocks() {
    let values: Vec<_> =
      (0..BLOCK_FIELDS + 17).map(|i| Fr::from(i as u64).square()).collect();
    let mut expected = Vec::new();
    for value in &values {
      value.serialize_compressed(&mut expected).unwrap();
    }
    let mut actual = Vec::new();
    write_fields(&mut actual, &values, |value| *value).unwrap();
    assert_eq!(actual, expected);
    let decoded =
      read_fields(&mut actual.as_slice(), values.len(), |value| value).unwrap();
    assert_eq!(decoded, values);
  }

  #[test]
  fn scalar_stream_rejects_invalid_and_truncated_fields() {
    assert!(read_scalars(&mut [255; 32].as_slice(), 1).is_err());
    assert!(read_scalars(&mut [0; 31].as_slice(), 1).is_err());
    assert!(read_scalars(&mut [].as_slice(), 0).unwrap().is_empty());
  }
}
