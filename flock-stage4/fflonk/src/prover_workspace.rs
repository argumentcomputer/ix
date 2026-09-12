//! Polynomial storage and arithmetic for the shared prover schedule.
use crate::polynomial_storage::{
  PolynomialFile, StoredPolynomial, checked_range, field_bytes,
  for_each_polynomial_chunk, load_polynomial,
};
use crate::prover::{
  blind_z, divide_by_xn_minus, poly_add_scaled_source, poly_mul, trim,
};
use crate::{
  FFLONK_POLYNOMIAL_CHUNK_FIELDS, FflonkPolynomialSourceV1, FflonkProverError,
  FflonkStorageError, KzgCommitmentSourceV1, commit_polynomial,
  commit_polynomial_source,
};
use ark_bls12_381::{Fr, G1Affine};
use ark_ff::{Field, One, Zero};
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
use std::collections::BTreeMap;
use std::io::{Read, Seek, Write};
use std::sync::{Arc, Mutex};

type Source<'a> = &'a dyn FflonkPolynomialSourceV1;
type Result<T> = core::result::Result<T, FflonkProverError>;

pub(crate) enum ProverWorkspace<R> {
  Memory,
  File(Arc<ScratchFile<R>>),
}

pub(crate) enum ProverPolynomial<R> {
  Memory(Vec<Fr>),
  File(FilePolynomial<R>),
}

pub(crate) struct ScratchFile<R> {
  file: PolynomialFile<R>,
  space: Mutex<SpaceAllocator>,
}

pub(crate) struct FilePolynomial<R> {
  reservation: Reservation<R>,
  stored: StoredPolynomial,
  len: usize,
}

struct Reservation<R> {
  file: Arc<ScratchFile<R>>,
  offset: u64,
  bytes: u64,
}

impl<R> Drop for Reservation<R> {
  fn drop(&mut self) {
    // A poisoned allocator cannot safely recycle an extent. Future allocation
    // reports the poisoned lock; dropping a handle must not panic or reuse it.
    if let Ok(mut space) = self.file.space.lock() {
      space.release(self.offset, self.bytes);
    }
  }
}

#[derive(Default)]
struct SpaceAllocator {
  end: u64,
  free: BTreeMap<u64, u64>,
}

impl SpaceAllocator {
  fn allocate(
    &mut self,
    bytes: u64,
  ) -> core::result::Result<u64, FflonkStorageError> {
    if bytes == 0 {
      return Ok(0);
    }
    let best = self
      .free
      .iter()
      .filter(|(_, len)| **len >= bytes)
      .min_by_key(|(_, len)| **len)
      .map(|(&offset, &len)| (offset, len));
    if let Some((offset, len)) = best {
      self.free.remove(&offset);
      if len > bytes {
        self.free.insert(offset + bytes, len - bytes);
      }
      return Ok(offset);
    }
    let offset = self.end;
    self.end =
      self.end.checked_add(bytes).ok_or(FflonkStorageError::CountOverflow)?;
    Ok(offset)
  }

  fn release(&mut self, mut offset: u64, mut bytes: u64) {
    if bytes == 0 {
      return;
    }
    if let Some((&previous, &len)) = self.free.range(..offset).next_back()
      && previous + len == offset
    {
      self.free.remove(&previous);
      offset = previous;
      bytes += len;
    }
    if let Some(len) = self.free.remove(&(offset + bytes)) {
      bytes += len;
    }
    if offset + bytes == self.end {
      self.end = offset;
    } else {
      self.free.insert(offset, bytes);
    }
  }
}

impl<R: Read + Seek> FflonkPolynomialSourceV1 for ProverPolynomial<R> {
  fn len(&self) -> usize {
    match self {
      Self::Memory(values) => values.len(),
      Self::File(poly) => poly.len,
    }
  }

  fn read_fields(
    &self,
    start: usize,
    output: &mut [Fr],
  ) -> core::result::Result<(), FflonkStorageError> {
    checked_range(self.len(), start, output.len())?;
    match self {
      Self::Memory(values) => values.as_slice().read_fields(start, output),
      Self::File(poly) => poly
        .reservation
        .file
        .file
        .source(&poly.stored)
        .read_fields(start, output),
    }
  }

  fn as_slice(&self) -> Option<&[Fr]> {
    match self {
      Self::Memory(values) => Some(values),
      Self::File(_) => None,
    }
  }

  fn nonzero_len(&self) -> core::result::Result<usize, FflonkStorageError> {
    match self {
      Self::Memory(values) => values.as_slice().nonzero_len(),
      Self::File(poly) => Ok(poly.stored.nonzero_len().min(poly.len)),
    }
  }
}

impl<R: Read + Write + Seek> ProverWorkspace<R> {
  pub(crate) fn file(storage: R) -> Result<Self> {
    Ok(Self::File(Arc::new(ScratchFile {
      file: PolynomialFile::new(storage)?,
      space: Mutex::new(SpaceAllocator::default()),
    })))
  }

  /// Calls the generator in ascending, bounded, consecutive chunks.
  pub(crate) fn generate(
    &self,
    len: usize,
    coefficients: bool,
    generate: impl FnMut(usize, &mut [Fr]) -> Result<()>,
  ) -> Result<ProverPolynomial<R>> {
    self.generate_with_batch(
      len,
      coefficients,
      FFLONK_POLYNOMIAL_CHUNK_FIELDS,
      generate,
    )
  }

  fn generate_with_batch(
    &self,
    len: usize,
    coefficients: bool,
    batch_fields: usize,
    mut generate: impl FnMut(usize, &mut [Fr]) -> Result<()>,
  ) -> Result<ProverPolynomial<R>> {
    match self {
      Self::Memory => {
        let mut values = vec![Fr::zero(); len];
        for (index, chunk) in values.chunks_mut(batch_fields).enumerate() {
          generate(index * batch_fields, chunk)?;
        }
        if coefficients {
          trim(&mut values);
        }
        Ok(ProverPolynomial::Memory(values))
      },
      Self::File(file) => {
        let bytes = field_bytes(len)?;
        let offset = file
          .space
          .lock()
          .map_err(|_| FflonkStorageError::Poisoned)?
          .allocate(bytes)?;
        // Reserve before writing. An I/O or generator error returns the extent
        // through this guard, without invalidating other live polynomials.
        let reservation = Reservation { file: Arc::clone(file), offset, bytes };
        let stored =
          file.file.write_generated(offset, len, batch_fields, generate)?;
        let len = if coefficients { stored.nonzero_len() } else { len };
        Ok(ProverPolynomial::File(FilePolynomial { reservation, stored, len }))
      },
    }
  }

  pub(crate) fn store_vec(
    &self,
    mut values: Vec<Fr>,
    coefficients: bool,
  ) -> Result<ProverPolynomial<R>> {
    if coefficients {
      trim(&mut values);
    }
    if matches!(self, Self::Memory) {
      return Ok(ProverPolynomial::Memory(values));
    }
    self.generate(values.len(), coefficients, |start, output| {
      output.copy_from_slice(&values[start..start + output.len()]);
      Ok(())
    })
  }

  pub(crate) fn ifft(
    &self,
    source: Source<'_>,
    domain: &Radix2EvaluationDomain<Fr>,
  ) -> Result<ProverPolynomial<R>> {
    self.ifft_vec(load_polynomial(source)?.into_owned(), domain, None)
  }

  pub(crate) fn ifft_owned(
    &self,
    source: ProverPolynomial<R>,
    domain: &Radix2EvaluationDomain<Fr>,
    blinding: [Fr; 3],
  ) -> Result<ProverPolynomial<R>> {
    let values = match source {
      ProverPolynomial::Memory(values) => values,
      other => load_polynomial(&other)?.into_owned(),
    };
    self.ifft_vec(values, domain, Some(blinding))
  }

  pub(crate) fn ifft_vec(
    &self,
    mut values: Vec<Fr>,
    domain: &Radix2EvaluationDomain<Fr>,
    blinding: Option<[Fr; 3]>,
  ) -> Result<ProverPolynomial<R>> {
    if values.len() != domain.size() {
      return Err(FflonkProverError::Shape("IFFT evaluation length"));
    }
    if matches!(self, Self::Memory) {
      domain.ifft_in_place(&mut values);
    } else {
      bounded_fft(&mut values, domain, true);
    }
    if let Some(factors) = blinding {
      values.reserve_exact(factors.len());
      blind_z(&mut values, factors, domain.size())?;
    }
    self.store_vec(values, true)
  }

  pub(crate) fn mul(
    &self,
    left: Source<'_>,
    right: Source<'_>,
  ) -> Result<ProverPolynomial<R>> {
    let left_len = left.nonzero_len()?;
    let right_len = right.nonzero_len()?;
    if left_len == 0 || right_len == 0 {
      return self.store_vec(Vec::new(), true);
    }
    let len = left_len
      .checked_add(right_len - 1)
      .ok_or(FflonkProverError::Shape("polynomial product length overflow"))?;
    let domain = Radix2EvaluationDomain::<Fr>::new(len)
      .ok_or(FflonkProverError::Shape("unsupported product FFT domain"))?;
    if matches!(self, Self::Memory) {
      return Ok(ProverPolynomial::Memory(poly_mul(
        &load_polynomial(left)?,
        &load_polynomial(right)?,
      )));
    }
    let mut values = read_fft_input(left, left_len, domain.size())?;
    bounded_fft(&mut values, &domain, false);
    let left_evaluations = self.store_vec(values, false)?;
    let mut values = read_fft_input(right, right_len, domain.size())?;
    bounded_fft(&mut values, &domain, false);
    for_each_polynomial_chunk(&left_evaluations, |start, chunk| {
      for (value, left) in
        values[start..start + chunk.len()].iter_mut().zip(chunk)
      {
        *value *= left;
      }
    })?;
    drop(left_evaluations);
    bounded_fft(&mut values, &domain, true);
    values.truncate(len);
    self.store_vec(values, true)
  }

  pub(crate) fn sum(
    &self,
    terms: &[(Source<'_>, Fr)],
  ) -> Result<ProverPolynomial<R>> {
    let len = terms
      .iter()
      .filter(|(_, scale)| !scale.is_zero())
      .map(|(source, _)| source.len())
      .max()
      .unwrap_or(0);
    let mut buffer = vec![Fr::zero(); len.min(FFLONK_POLYNOMIAL_CHUNK_FIELDS)];
    self.generate(len, true, |start, output| {
      output.fill(Fr::zero());
      for (source, scale) in terms {
        if scale.is_zero() {
          continue;
        }
        let input = &mut buffer[..output.len()];
        read_padded(*source, start, input)?;
        for (value, input) in output.iter_mut().zip(input) {
          *value += *input * scale;
        }
      }
      Ok(())
    })
  }

  pub(crate) fn add_assign(
    &self,
    output: &mut ProverPolynomial<R>,
    source: Source<'_>,
    scale: Fr,
  ) -> Result<()> {
    match output {
      ProverPolynomial::Memory(values) => {
        poly_add_scaled_source(values, source, scale)?
      },
      _ => *output = self.sum(&[(output, Fr::one()), (source, scale)])?,
    }
    Ok(())
  }

  pub(crate) fn scale(
    &self,
    mut poly: ProverPolynomial<R>,
    scale: Fr,
  ) -> Result<ProverPolynomial<R>> {
    match &mut poly {
      ProverPolynomial::Memory(values) => {
        for value in values.iter_mut() {
          *value *= scale;
        }
        trim(values);
        Ok(poly)
      },
      _ => self.sum(&[(&poly, scale)]),
    }
  }

  pub(crate) fn shift(
    &self,
    source: Source<'_>,
    factor: Fr,
  ) -> Result<ProverPolynomial<R>> {
    self.generate(source.len(), true, |start, output| {
      source.read_fields(start, output)?;
      let mut power = factor.pow([start as u64]);
      for value in output {
        *value *= power;
        power *= factor;
      }
      Ok(())
    })
  }

  pub(crate) fn pack<const N: usize>(
    &self,
    polynomials: [Source<'_>; N],
  ) -> Result<ProverPolynomial<R>> {
    if N == 0 {
      return Err(FflonkProverError::Shape("zero packed polynomial stride"));
    }
    let len = polynomials
      .iter()
      .map(|source| source.len())
      .max()
      .unwrap_or(0)
      .checked_mul(N)
      .ok_or(FflonkProverError::Shape("packed polynomial length overflow"))?;
    // Each batch consumes a complete authenticated chunk from each column,
    // avoiding N re-reads of that chunk as its fields are interleaved.
    let batch_fields = N
      .checked_mul(FFLONK_POLYNOMIAL_CHUNK_FIELDS)
      .ok_or(FflonkProverError::Shape("packed polynomial batch overflow"))?;
    let mut buffer =
      vec![Fr::zero(); (len / N).min(FFLONK_POLYNOMIAL_CHUNK_FIELDS)];
    self.generate_with_batch(len, true, batch_fields, |start, output| {
      let first = start / N;
      let count = (start + output.len()).div_ceil(N) - first;
      for (column, source) in polynomials.iter().enumerate() {
        read_padded(*source, first, &mut buffer[..count])?;
        let initial = (column + N - start % N) % N;
        for index in (initial..output.len()).step_by(N) {
          output[index] = buffer[(start + index) / N - first];
        }
      }
      Ok(())
    })
  }

  pub(crate) fn divide(
    &self,
    polynomial: ProverPolynomial<R>,
    n: usize,
    beta: Fr,
    relation: &'static str,
  ) -> Result<ProverPolynomial<R>> {
    if let ProverPolynomial::Memory(values) = polynomial {
      return self
        .store_vec(divide_by_xn_minus(values, n, beta, relation)?, true);
    }
    if n == 0 {
      return Err(FflonkProverError::Shape("zero-degree divisor"));
    }
    let len = polynomial.nonzero_len()?;
    if len == 0 {
      return self.store_vec(Vec::new(), true);
    }
    if len <= n {
      return Err(FflonkProverError::PolynomialNotDivisible(relation));
    }
    let quotient_len = len - n;
    if beta.is_zero() {
      let mut buffer = vec![Fr::zero(); n.min(FFLONK_POLYNOMIAL_CHUNK_FIELDS)];
      for start in (0..n).step_by(FFLONK_POLYNOMIAL_CHUNK_FIELDS) {
        let count = buffer.len().min(n - start);
        polynomial.read_fields(start, &mut buffer[..count])?;
        if buffer[..count].iter().any(|value| !value.is_zero()) {
          return Err(FflonkProverError::PolynomialNotDivisible(relation));
        }
      }
      return self.generate(quotient_len, true, |start, output| {
        Ok(polynomial.read_fields(start + n, output)?)
      });
    }
    // p_i = q_(i-n) - beta*q_i. Generate ascending coefficients under the
    // zero-remainder assumption, retaining only the last n quotient values.
    // Then check every remaining high coefficient to establish exact division.
    let ring_len = n.min(quotient_len);
    let mut ring = vec![Fr::zero(); ring_len];
    let inverse = beta.inverse().expect("nonzero divisor constant");
    let quotient = self.generate(quotient_len, true, |start, output| {
      polynomial.read_fields(start, output)?;
      for (offset, value) in output.iter_mut().enumerate() {
        let index = start + offset;
        let previous =
          if index >= n { ring[(index - n) % ring_len] } else { Fr::zero() };
        *value = (previous - *value) * inverse;
        ring[index % ring_len] = *value;
      }
      Ok(())
    })?;
    let mut buffer = vec![Fr::zero(); n.min(FFLONK_POLYNOMIAL_CHUNK_FIELDS)];
    for start in (quotient_len..len).step_by(FFLONK_POLYNOMIAL_CHUNK_FIELDS) {
      let count = buffer.len().min(len - start);
      polynomial.read_fields(start, &mut buffer[..count])?;
      for (offset, value) in buffer[..count].iter().enumerate() {
        let index = start + offset;
        let expected =
          if index >= n { ring[(index - n) % ring_len] } else { Fr::zero() };
        if *value != expected {
          return Err(FflonkProverError::PolynomialNotDivisible(relation));
        }
      }
    }
    Ok(quotient)
  }

  /// Consume the large opening inputs, reusing the largest RAM allocation in
  /// memory mode and generating one sequential output in file mode.
  pub(crate) fn opening_combination(
    &self,
    mut parts: [(ProverPolynomial<R>, Fr); 3],
    c0: Source<'_>,
    c0_scale: Fr,
    constant: Fr,
    normalizer: Fr,
  ) -> Result<ProverPolynomial<R>> {
    if matches!(self, Self::File(_)) {
      let constant_poly = [-constant];
      let sum = self.sum(&[
        (&parts[0].0, parts[0].1 * normalizer),
        (&parts[1].0, parts[1].1 * normalizer),
        (&parts[2].0, parts[2].1 * normalizer),
        (c0, c0_scale * normalizer),
        (&constant_poly.as_slice(), normalizer),
      ])?;
      return Ok(sum);
    }
    let largest = parts
      .iter()
      .enumerate()
      .max_by_key(|(_, (poly, _))| match poly {
        ProverPolynomial::Memory(values) => values.capacity(),
        ProverPolynomial::File(_) => 0,
      })
      .map(|(index, _)| index)
      .expect("three polynomials");
    parts.swap(0, largest);
    let mut parts = parts.into_iter();
    let (poly, scale) = parts.next().expect("three polynomials");
    let mut result = self.scale(poly, scale)?;
    for (poly, scale) in parts {
      self.add_assign(&mut result, &poly, scale)?;
    }
    self.add_assign(&mut result, c0, c0_scale)?;
    self.add_assign(&mut result, &[-constant].as_slice(), Fr::one())?;
    self.scale(result, normalizer)
  }

  pub(crate) fn commit(
    &self,
    srs: &(impl KzgCommitmentSourceV1 + ?Sized),
    poly: &ProverPolynomial<R>,
  ) -> Result<G1Affine> {
    Ok(match poly {
      ProverPolynomial::Memory(values) => commit_polynomial(srs, values)?.0,
      ProverPolynomial::File(_) => commit_polynomial_source(srs, poly)?.0,
    })
  }
}

fn read_padded(
  source: Source<'_>,
  start: usize,
  output: &mut [Fr],
) -> core::result::Result<(), FflonkStorageError> {
  output.fill(Fr::zero());
  let count = output.len().min(source.len().saturating_sub(start));
  if count != 0 {
    source.read_fields(start, &mut output[..count])?;
  }
  Ok(())
}

fn read_fft_input(
  source: Source<'_>,
  len: usize,
  domain_size: usize,
) -> Result<Vec<Fr>> {
  let mut values = Vec::with_capacity(domain_size);
  values.resize(len, Fr::zero());
  source.read_fields(0, &mut values)?;
  Ok(values)
}

/// Radix-2 DIT with bit reversal and a bounded twiddle cache. Arkworks' FFT
/// retains a domain/2 roots table; here at most one authenticated-chunk-sized
/// roots tile coexists with the single transform buffer. All domains used by
/// this prover are unshifted roots-of-unity domains.
fn bounded_fft(
  values: &mut Vec<Fr>,
  domain: &Radix2EvaluationDomain<Fr>,
  inverse: bool,
) {
  let size = domain.size();
  debug_assert_eq!(domain.coset_offset(), Fr::one());
  values.resize(size, Fr::zero());
  let log_size = size.trailing_zeros();
  if log_size == 0 {
    return;
  }
  for index in 0..size {
    let reversed = index.reverse_bits() >> (usize::BITS - log_size);
    if index < reversed {
      values.swap(index, reversed);
    }
  }
  let root = if inverse { domain.group_gen_inv() } else { domain.group_gen() };
  let mut roots =
    vec![Fr::zero(); (size / 2).min(FFLONK_POLYNOMIAL_CHUNK_FIELDS)];
  for stage in 1..=log_size {
    let width = 1usize << stage;
    let half = width / 2;
    let step = root.pow([(size / width) as u64]);
    let mut power = Fr::one();
    for start in (0..half).step_by(FFLONK_POLYNOMIAL_CHUNK_FIELDS) {
      let count = roots.len().min(half - start);
      for root in &mut roots[..count] {
        *root = power;
        power *= step;
      }
      for block in values.chunks_exact_mut(width) {
        let (low, high) = block.split_at_mut(half);
        for ((low, high), root) in low[start..start + count]
          .iter_mut()
          .zip(&mut high[start..start + count])
          .zip(&roots[..count])
        {
          let product = *high * root;
          let original = *low;
          *low = original + product;
          *high = original - product;
        }
      }
    }
  }
  if inverse {
    for value in values {
      *value *= domain.size_inv();
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use std::io::{self, Cursor, SeekFrom};

  fn workspace() -> ProverWorkspace<Cursor<Vec<u8>>> {
    ProverWorkspace::file(Cursor::new(Vec::new())).unwrap()
  }

  fn values(len: usize) -> Vec<Fr> {
    (0..len)
      .map(|index| Fr::from(index as u64 + 3).square() - Fr::from(23u64))
      .collect()
  }

  fn read<R: Read + Seek>(poly: &ProverPolynomial<R>) -> Vec<Fr> {
    load_polynomial(poly).unwrap().into_owned()
  }

  #[test]
  fn tiled_fft_matches_arkworks_in_both_directions_and_across_root_tiles() {
    for size in [1, 2, 4, 8, 64, 131_072, 262_144] {
      let domain = Radix2EvaluationDomain::<Fr>::new(size).unwrap();
      let input = values(if size > 8 { size / 3 + 1 } else { size });
      let expected = domain.fft(&input);
      let mut actual = input;
      bounded_fft(&mut actual, &domain, false);
      assert_eq!(actual, expected, "forward FFT size {size}");
      let expected = domain.ifft(&actual);
      bounded_fft(&mut actual, &domain, true);
      assert_eq!(actual, expected, "inverse FFT size {size}");
    }
  }

  #[test]
  fn file_arithmetic_matches_independent_polynomial_identities() {
    let ws = workspace();
    for (left_len, right_len) in [(0, 0), (0, 7), (1, 1), (9, 12), (33, 65)] {
      let mut left = values(left_len);
      let mut right = values(right_len);
      left.resize(left_len + 3, Fr::zero());
      right.resize(right_len + 5, Fr::zero());
      let a = ws.store_vec(left.clone(), false).unwrap();
      let b = ws.store_vec(right.clone(), false).unwrap();
      assert_eq!(read(&ws.mul(&a, &b).unwrap()), poly_mul(&left, &right));
      let scaled =
        ws.sum(&[(&a, Fr::from(3u64)), (&b, -Fr::from(5u64))]).unwrap();
      let shift = ws.shift(&a, Fr::from(7u64)).unwrap();
      for point in [Fr::zero(), Fr::one(), Fr::from(19u64)] {
        assert_eq!(
          crate::evaluate_polynomial(&read(&scaled), point),
          crate::evaluate_polynomial(&left, point) * Fr::from(3u64)
            - crate::evaluate_polynomial(&right, point) * Fr::from(5u64)
        );
        assert_eq!(
          crate::evaluate_polynomial(&read(&shift), point),
          crate::evaluate_polynomial(&left, point * Fr::from(7u64))
        );
      }
    }
    let zero = ws.store_vec(vec![Fr::zero(); 11], true).unwrap();
    assert_eq!(zero.len(), 0);
    assert!(zero.as_slice().is_none());
    assert_eq!(zero.read_fields(1, &mut []), Err(FflonkStorageError::Range));
  }

  #[test]
  fn streamed_packing_preserves_interleaving_across_partial_chunks() {
    let ws = workspace();
    let mut a = values(FFLONK_POLYNOMIAL_CHUNK_FIELDS + 9);
    a.resize(a.len() + 3, Fr::zero());
    let b = values(19);
    let c = values(FFLONK_POLYNOMIAL_CHUNK_FIELDS - 5);
    let inputs = [a, b, c];
    let stored = inputs
      .each_ref()
      .map(|values| ws.store_vec(values.clone(), false).unwrap());
    let actual = read(&ws.pack([&stored[0], &stored[1], &stored[2]]).unwrap());
    let mut expected =
      vec![Fr::zero(); inputs.iter().map(Vec::len).max().unwrap() * 3];
    for (column, input) in inputs.iter().enumerate() {
      for (row, value) in input.iter().enumerate() {
        expected[row * 3 + column] = *value;
      }
    }
    trim(&mut expected);
    assert_eq!(actual, expected);
  }

  #[test]
  fn streamed_exact_division_checks_every_remainder_and_short_quotients() {
    let ws = workspace();
    for quotient_len in [0, 1, 2, 7, 31, FFLONK_POLYNOMIAL_CHUNK_FIELDS + 7] {
      let quotient = values(quotient_len);
      for n in [1, 3, 4, 8, 32, FFLONK_POLYNOMIAL_CHUNK_FIELDS + 3] {
        for beta in [Fr::zero(), Fr::one(), -Fr::one(), Fr::from(13u64)] {
          let mut product = vec![Fr::zero(); quotient.len() + n];
          for (degree, coefficient) in quotient.iter().enumerate() {
            product[degree + n] += coefficient;
            product[degree] -= beta * coefficient;
          }
          product.resize(product.len() + 3, Fr::zero());
          let actual = ws
            .divide(
              ws.store_vec(product.clone(), true).unwrap(),
              n,
              beta,
              "division fixture",
            )
            .unwrap();
          assert_eq!(
            read(&actual),
            quotient,
            "n={n}, quotient_len={quotient_len}"
          );
          // Mutations at both ends test the ascending recurrence and its final
          // high-coefficient check. X^n divides high-only changes, so test
          // remainder positions explicitly for beta=0.
          for index in [0, n - 1] {
            product[index] += Fr::one();
            assert!(matches!(
              ws.divide(
                ws.store_vec(product.clone(), true).unwrap(),
                n,
                beta,
                "division fixture"
              ),
              Err(FflonkProverError::PolynomialNotDivisible(
                "division fixture"
              ))
            ));
            product[index] -= Fr::one();
          }
          if !beta.is_zero() && quotient_len != 0 {
            let index = quotient_len + n - 1;
            product[index] += Fr::one();
            assert!(matches!(
              ws.divide(
                ws.store_vec(product, true).unwrap(),
                n,
                beta,
                "division fixture"
              ),
              Err(FflonkProverError::PolynomialNotDivisible(
                "division fixture"
              ))
            ));
          }
        }
      }
    }
    assert!(matches!(
      ws.divide(ws.store_vec(Vec::new(), true).unwrap(), 0, Fr::one(), "zero"),
      Err(FflonkProverError::Shape(_))
    ));
    for n in [1, 3, 8] {
      assert!(matches!(
        ws.divide(
          ws.store_vec(vec![Fr::one(); n], true).unwrap(),
          n,
          Fr::one(),
          "low degree"
        ),
        Err(FflonkProverError::PolynomialNotDivisible("low degree"))
      ));
    }
  }

  #[test]
  fn extent_allocator_reuses_best_fit_coalesces_and_checks_overflow() {
    let mut space = SpaceAllocator::default();
    assert_eq!(space.allocate(16).unwrap(), 0);
    assert_eq!(space.allocate(8).unwrap(), 16);
    assert_eq!(space.allocate(32).unwrap(), 24);
    assert_eq!(space.allocate(8).unwrap(), 56);
    space.release(0, 16);
    space.release(24, 32);
    assert_eq!(space.allocate(12).unwrap(), 0);
    assert_eq!(space.allocate(4).unwrap(), 12);
    space.release(12, 4);
    space.release(0, 12);
    space.release(16, 8);
    assert_eq!(space.free.get(&0), Some(&56));
    assert_eq!(space.allocate(48).unwrap(), 0);
    space.release(0, 48);
    space.release(56, 8);
    assert_eq!(space.end, 0);
    assert!(space.free.is_empty());
    assert_eq!(space.allocate(u64::MAX).unwrap(), 0);
    assert_eq!(space.allocate(1), Err(FflonkStorageError::CountOverflow));
    assert_eq!(space.end, u64::MAX);
  }

  struct SharedIo {
    bytes: Arc<Mutex<Cursor<Vec<u8>>>>,
    failure: Arc<Mutex<Option<&'static str>>>,
  }

  impl Read for SharedIo {
    fn read(&mut self, output: &mut [u8]) -> io::Result<usize> {
      if *self.failure.lock().unwrap() == Some("read") {
        return Err(io::ErrorKind::BrokenPipe.into());
      }
      let count = output.len().min(4093);
      self.bytes.lock().unwrap().read(&mut output[..count])
    }
  }
  impl Write for SharedIo {
    fn write(&mut self, input: &[u8]) -> io::Result<usize> {
      if *self.failure.lock().unwrap() == Some("write") {
        return Err(io::ErrorKind::WriteZero.into());
      }
      self.bytes.lock().unwrap().write(&input[..input.len().min(2053)])
    }
    fn flush(&mut self) -> io::Result<()> {
      if *self.failure.lock().unwrap() == Some("flush") {
        return Err(io::ErrorKind::BrokenPipe.into());
      }
      Ok(())
    }
  }
  impl Seek for SharedIo {
    fn seek(&mut self, position: SeekFrom) -> io::Result<u64> {
      if *self.failure.lock().unwrap() == Some("seek") {
        return Err(io::ErrorKind::NotSeekable.into());
      }
      self.bytes.lock().unwrap().seek(position)
    }
  }

  #[test]
  fn extent_reuse_and_failed_generation_preserve_live_authenticated_polynomials()
   {
    let bytes = Arc::new(Mutex::new(Cursor::new(Vec::new())));
    let failure = Arc::new(Mutex::new(None));
    let ws = ProverWorkspace::file(SharedIo {
      bytes: Arc::clone(&bytes),
      failure: Arc::clone(&failure),
    })
    .unwrap();
    let keep = values(21);
    let live = ws.store_vec(keep.clone(), true).unwrap();
    assert!(matches!(
      ws.generate(FFLONK_POLYNOMIAL_CHUNK_FIELDS + 1, true, |start, output| {
        if start != 0 {
          return Err(FflonkProverError::SingularChallenge("late generator"));
        }
        output.fill(Fr::one());
        Ok(())
      }),
      Err(FflonkProverError::SingularChallenge("late generator"))
    ));
    assert_eq!(read(&live), keep);
    for reason in ["write", "flush", "seek"] {
      *failure.lock().unwrap() = Some(reason);
      assert!(matches!(
        ws.store_vec(values(13), true),
        Err(FflonkProverError::Storage(FflonkStorageError::Io(_)))
      ));
      *failure.lock().unwrap() = None;
      assert_eq!(read(&live), keep);
    }
    assert!(matches!(
      ws.generate(19, true, |_, _| Err(FflonkProverError::SingularChallenge(
        "generator"
      ))),
      Err(FflonkProverError::SingularChallenge("generator"))
    ));
    // The failed reservations and every dropped temporary must be reusable.
    let high_water;
    {
      let temporary = ws.store_vec(values(29), true).unwrap();
      assert_eq!(read(&temporary), values(29));
      high_water = bytes.lock().unwrap().get_ref().len();
    }
    for _ in 0..20 {
      let temporary = ws.store_vec(values(29), true).unwrap();
      assert_eq!(read(&temporary), values(29));
      assert_eq!(read(&live), keep);
      assert_eq!(bytes.lock().unwrap().get_ref().len(), high_water);
    }
    *failure.lock().unwrap() = Some("read");
    assert_eq!(
      live.read_fields(0, &mut [Fr::zero()]),
      Err(FflonkStorageError::Io(io::ErrorKind::BrokenPipe))
    );
    *failure.lock().unwrap() = None;
    bytes.lock().unwrap().get_mut()[20 * 32 + 31] ^= 1;
    assert!(matches!(
      live.read_fields(0, &mut [Fr::zero()]),
      Err(FflonkStorageError::ChunkChanged { offset: 0 })
    ));
    bytes.lock().unwrap().get_mut()[20 * 32 + 31] ^= 1;
    bytes.lock().unwrap().get_mut().truncate(1);
    assert_eq!(
      live.read_fields(0, &mut [Fr::zero()]),
      Err(FflonkStorageError::Io(io::ErrorKind::UnexpectedEof))
    );
  }

  #[test]
  fn workspace_rejects_nonempty_storage_and_poisoned_extent_allocator() {
    assert!(matches!(
      ProverWorkspace::file(Cursor::new(vec![0u8])),
      Err(FflonkProverError::Storage(FflonkStorageError::NonemptyFile))
    ));
    let ws = workspace();
    let live = ws.store_vec(values(8), true).unwrap();
    let ProverWorkspace::File(file) = &ws else { unreachable!() };
    let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
      let _guard = file.space.lock().unwrap();
      panic!("poison the extent allocator");
    }));
    assert!(matches!(
      ws.store_vec(values(8), true),
      Err(FflonkProverError::Storage(FflonkStorageError::Poisoned))
    ));
    assert_eq!(read(&live), values(8));
    drop(live);
  }
}
