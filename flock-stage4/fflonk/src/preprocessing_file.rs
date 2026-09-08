use crate::polynomial_storage::{
  PolynomialFile, StoredPolynomial, for_each_polynomial_chunk,
};
use crate::preprocessing::{
  hash_field_values, hash_fields, preprocessing_domain, preprocessing_hasher,
  sealed,
};
use crate::{
  FFLONK_POLYNOMIAL_CHUNK_FIELDS, FflonkFixedPolynomialV1,
  FflonkPolynomialSourceV1, FflonkPreprocessingError, FflonkProvingKeyV1,
  FflonkStorageError, FflonkVerificationKeyV1, KzgCommitmentSourceV1,
  KzgCommitmentV1, PlonkArithmetizationV1, commit_polynomial_source,
};
use ark_bls12_381::Fr;
use ark_ff::{FftField, Field, Zero};
use ark_poly::EvaluationDomain;
use std::io::{Read, Seek, Write};

/// A proving key with authenticated polynomials in caller-owned scratch storage.
///
/// Use `R = std::fs::File` for disk storage. The key retains its arithmetization,
/// verification metadata, and chunk hashes, while its eight coefficient
/// polynomials, three sigma evaluation columns, and packed C0 live in the file.
/// The file contains canonical 32-byte little-endian fields and costs `19*n*32`
/// bytes. It is scratch storage: reopening the raw file does not reconstruct a
/// trusted key, and the authentication metadata is never loaded from the file.
///
/// Reads authenticate whole chunks against the values computed during
/// preprocessing, including when only part of a chunk is requested. A caller's
/// reader may own additional buffers; reads on one key are serialized by a mutex.
#[derive(Debug)]
pub struct FflonkFilePreprocessedCircuitV1<R> {
  arithmetization: PlonkArithmetizationV1,
  file: PolynomialFile<R>,
  coefficients: [StoredPolynomial; 8],
  sigma_evaluations: [StoredPolynomial; 3],
  c0: StoredPolynomial,
  verification_key: FflonkVerificationKeyV1,
  required_srs_degree: u64,
  digest: [u8; 32],
}

impl<R> FflonkFilePreprocessedCircuitV1<R> {
  pub fn arithmetization(&self) -> &PlonkArithmetizationV1 {
    &self.arithmetization
  }
  pub const fn verification_key(&self) -> FflonkVerificationKeyV1 {
    self.verification_key
  }
  pub const fn c0_commitment(&self) -> KzgCommitmentV1 {
    KzgCommitmentV1(self.verification_key.c0())
  }
  pub const fn required_srs_degree(&self) -> u64 {
    self.required_srs_degree
  }
  pub const fn digest(&self) -> [u8; 32] {
    self.digest
  }

  /// Exact scratch payload bytes, excluding filesystem metadata and cache.
  pub fn storage_bytes(&self) -> u64 {
    self.c0.end()
  }

  /// Requested heap bytes in the retained chunk hashes, excluding the reader,
  /// arithmetization, and fixed-size key metadata.
  pub fn authentication_bytes(&self) -> usize {
    self
      .coefficients
      .iter()
      .chain(&self.sigma_evaluations)
      .chain([&self.c0])
      .map(StoredPolynomial::authentication_bytes)
      .sum()
  }
}

impl<R> sealed::Sealed for FflonkFilePreprocessedCircuitV1<R> {}

impl<R: Read + Seek> FflonkProvingKeyV1 for FflonkFilePreprocessedCircuitV1<R> {
  fn arithmetization(&self) -> &PlonkArithmetizationV1 {
    self.arithmetization()
  }
  fn verification_key(&self) -> FflonkVerificationKeyV1 {
    self.verification_key()
  }
  fn required_srs_degree(&self) -> u64 {
    self.required_srs_degree()
  }
  fn digest(&self) -> [u8; 32] {
    self.digest()
  }
  fn coefficient_source(
    &self,
    polynomial: FflonkFixedPolynomialV1,
  ) -> impl FflonkPolynomialSourceV1 + '_ {
    self.file.source(&self.coefficients[polynomial.index()])
  }
  fn sigma_sources(&self) -> [impl FflonkPolynomialSourceV1 + '_; 3] {
    core::array::from_fn(|column| {
      self.file.source(&self.sigma_evaluations[column])
    })
  }
  fn c0_source(&self) -> impl FflonkPolynomialSourceV1 + '_ {
    self.file.source(&self.c0)
  }
}

/// Preprocess directly into an empty, readable/writable/seekable scratch file.
///
/// This never constructs the materialized key. Each selector needs one size-n
/// in-place IFFT buffer. Sigma construction additionally retains n omega powers;
/// C0 packing uses bounded chunks, and its KZG commitment streams from storage.
/// The arithmetization and FFT workspaces remain in memory. The caller controls
/// file creation, cleanup, and durability; errors may leave partial scratch data.
pub fn preprocess_fflonk_to_file<R: Read + Write + Seek>(
  srs: &(impl KzgCommitmentSourceV1 + ?Sized),
  arithmetization: PlonkArithmetizationV1,
  storage: R,
) -> Result<FflonkFilePreprocessedCircuitV1<R>, FflonkPreprocessingError> {
  let (domain, required_srs_degree) =
    preprocessing_domain(srs, &arithmetization)?;
  let n = domain.size();
  let c0_len =
    n.checked_mul(8).ok_or(FflonkPreprocessingError::CountOverflow)?;
  let file = PolynomialFile::new(storage)?;
  let mut offset = 0;
  let mut coefficients = Vec::with_capacity(8);
  let mut sigma_evaluations = Vec::with_capacity(3);
  let mut hasher =
    preprocessing_hasher(&arithmetization, srs.digest(), required_srs_degree);
  for id in &FflonkFixedPolynomialV1::ALL[..5] {
    let mut values: Vec<Fr> = arithmetization
      .gates()
      .iter()
      .map(|gate| match id {
        FflonkFixedPolynomialV1::Ql => gate.ql,
        FflonkFixedPolynomialV1::Qr => gate.qr,
        FflonkFixedPolynomialV1::Qm => gate.qm,
        FflonkFixedPolynomialV1::Qo => gate.qo,
        FflonkFixedPolynomialV1::Qc => gate.qc,
        _ => unreachable!("five selectors"),
      })
      .collect();
    domain.ifft_in_place(&mut values);
    hash_fields(&mut hasher, &values);
    let stored = file.write_polynomial(
      offset,
      values.as_slice(),
      FFLONK_POLYNOMIAL_CHUNK_FIELDS,
    )?;
    offset = stored.end();
    coefficients.push(stored);
  }
  let k1 = Fr::GENERATOR;
  let k2 = k1.square();
  let cosets = [Fr::ONE, k1, k2];
  let omega_powers: Vec<Fr> = domain.elements().collect();
  for targets in arithmetization.sigma() {
    let mut values = Vec::with_capacity(n);
    for target in targets {
      let row = usize::try_from(target.row)
        .map_err(|_| FflonkPreprocessingError::CountOverflow)?;
      let omega =
        omega_powers.get(row).ok_or(FflonkPreprocessingError::CountOverflow)?;
      let coset = cosets
        .get(usize::from(target.column))
        .ok_or(FflonkPreprocessingError::CountOverflow)?;
      values.push(*omega * coset);
    }
    if values.len() != n {
      return Err(FflonkPreprocessingError::CountOverflow);
    }
    let stored = file.write_polynomial(
      offset,
      values.as_slice(),
      FFLONK_POLYNOMIAL_CHUNK_FIELDS,
    )?;
    offset = stored.end();
    sigma_evaluations.push(stored);
    domain.ifft_in_place(&mut values);
    hash_fields(&mut hasher, &values);
    let stored = file.write_polynomial(
      offset,
      values.as_slice(),
      FFLONK_POLYNOMIAL_CHUNK_FIELDS,
    )?;
    offset = stored.end();
    coefficients.push(stored);
  }
  drop(omega_powers);
  let coefficients: [StoredPolynomial; 8] = coefficients
    .try_into()
    .map_err(|_| FflonkPreprocessingError::CountOverflow)?;
  let sigma_evaluations = sigma_evaluations
    .try_into()
    .map_err(|_| FflonkPreprocessingError::CountOverflow)?;
  let c0 = file.write_polynomial(
    offset,
    &InterleavedC0 { file: &file, coefficients: &coefficients, len: c0_len },
    8 * FFLONK_POLYNOMIAL_CHUNK_FIELDS,
  )?;
  let c0_source = file.source(&c0);
  let c0_commitment = commit_polynomial_source(srs, &c0_source)?;
  hasher.update(&(c0_len as u64).to_le_bytes());
  for_each_polynomial_chunk(&c0_source, |_, values| {
    hash_field_values(&mut hasher, values)
  })?;
  drop(c0_source);
  let verification_key = FflonkVerificationKeyV1::new(
    usize::try_from(arithmetization.census().public_input_rows)
      .map_err(|_| FflonkPreprocessingError::CountOverflow)?,
    arithmetization.census().domain_size,
    k1,
    k2,
    c0_commitment.0,
    srs.verifier_key(),
  )?;
  Ok(FflonkFilePreprocessedCircuitV1 {
    arithmetization,
    file,
    coefficients,
    sigma_evaluations,
    c0,
    verification_key,
    required_srs_degree,
    digest: *hasher.finalize().as_bytes(),
  })
}

struct InterleavedC0<'a, R> {
  file: &'a PolynomialFile<R>,
  coefficients: &'a [StoredPolynomial; 8],
  len: usize,
}

impl<R: Read + Seek> FflonkPolynomialSourceV1 for InterleavedC0<'_, R> {
  fn len(&self) -> usize {
    self.len
  }
  fn read_fields(
    &self,
    start: usize,
    output: &mut [Fr],
  ) -> Result<(), FflonkStorageError> {
    let end = start
      .checked_add(output.len())
      .filter(|end| *end <= self.len)
      .ok_or(FflonkStorageError::Range)?;
    if output.is_empty() {
      return Ok(());
    }
    let first_row = start / 8;
    let mut column = vec![Fr::zero(); end.div_ceil(8) - first_row];
    for (slot, id) in FflonkFixedPolynomialV1::C0_ORDER.into_iter().enumerate()
    {
      self
        .file
        .source(&self.coefficients[id.index()])
        .read_fields(first_row, &mut column)?;
      for (row, value) in column.iter().enumerate() {
        let index = 8 * (first_row + row) + slot;
        if (start..end).contains(&index) {
          output[index - start] = *value;
        }
      }
    }
    Ok(())
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::polynomial_storage::load_polynomial;
  use crate::{
    FflonkBlindingV1, FflonkProverError, KzgError, KzgUniversalSrsV1,
    arithmetize_r1cs, preprocess_fflonk, prove_fflonk,
    required_fflonk_srs_degree, verify_fflonk,
  };
  use ark_bls12_381::{G1Affine, G2Affine};
  use ark_ec::{AffineRepr, CurveGroup};
  use ark_ff::PrimeField;
  use ix_terminal_circuit::{
    CanonicalR1csV1, ConstraintPhase, LinearCombination, R1csBuilder, Witness,
  };
  use std::io::{Cursor, SeekFrom};

  fn fixture(count: u64) -> (CanonicalR1csV1, Witness) {
    let mut builder = R1csBuilder::new();
    let public = builder.alloc_public(Fr::from(3u64)).unwrap();
    for i in 0..count {
      let value = Fr::from(i + 5);
      let private = builder.alloc_private(value).unwrap();
      let product = builder
        .alloc_private(Fr::from(9u64) * (Fr::from(3u64) * value - Fr::ONE))
        .unwrap();
      builder.enforce(
        ConstraintPhase::Statement,
        LinearCombination::from_constant(Fr::from(3u64))
          .term(public, Fr::from(2u64)),
        LinearCombination::from_constant(-Fr::ONE)
          .term(private, Fr::from(3u64)),
        LinearCombination::from_variable(product),
      );
    }
    builder.finish().unwrap()
  }

  fn test_srs(degree: usize, tau: Fr) -> KzgUniversalSrsV1 {
    let mut scalar = Fr::ONE;
    let powers = (0..=degree)
      .map(|_| {
        let point =
          G1Affine::generator().mul_bigint(scalar.into_bigint()).into_affine();
        scalar *= tau;
        point
      })
      .collect();
    KzgUniversalSrsV1::new(
      powers,
      G2Affine::generator(),
      G2Affine::generator().mul_bigint(tau.into_bigint()).into_affine(),
    )
    .unwrap()
  }

  #[test]
  fn disk_key_polynomials_digest_and_proof_match_materialized_preprocessing() {
    for count in [1, 5] {
      let (r1cs, witness) = fixture(count);
      let arithmetization = arithmetize_r1cs(&r1cs).unwrap();
      let n = arithmetization.census().domain_size;
      let srs = test_srs(
        usize::try_from(required_fflonk_srs_degree(n).unwrap()).unwrap(),
        Fr::from(23u64),
      );
      let memory = preprocess_fflonk(&srs, arithmetization.clone()).unwrap();
      let file = preprocess_fflonk_to_file(
        &srs,
        arithmetization,
        Cursor::new(Vec::new()),
      )
      .unwrap();
      assert_eq!(file.digest(), memory.digest());
      assert_eq!(file.verification_key(), memory.verification_key());
      assert_eq!(file.c0_commitment(), memory.c0_commitment());
      assert_eq!(file.required_srs_degree(), memory.required_srs_degree());
      assert_eq!(file.arithmetization(), memory.arithmetization());
      assert_eq!(file.storage_bytes(), 19 * n * 32);
      assert_eq!(file.authentication_bytes(), 12 * 32);
      for id in FflonkFixedPolynomialV1::ALL {
        assert_eq!(
          load_polynomial(&file.coefficient_source(id)).unwrap(),
          load_polynomial(&memory.coefficient_source(id)).unwrap()
        );
      }
      for (actual, expected) in
        file.sigma_sources().iter().zip(memory.sigma_sources())
      {
        assert_eq!(
          load_polynomial(actual).unwrap(),
          load_polynomial(&expected).unwrap()
        );
      }
      let c0 = load_polynomial(&file.c0_source()).unwrap().into_owned();
      assert_eq!(c0, memory.c0_coefficients());
      let interleaved = InterleavedC0 {
        file: &file.file,
        coefficients: &file.coefficients,
        len: c0.len(),
      };
      for start in [0, 1, 7, 8, c0.len() - 9] {
        let mut values = [Fr::zero(); 9];
        interleaved.read_fields(start, &mut values).unwrap();
        assert_eq!(&values, &c0[start..start + 9]);
      }
      for blinding in [
        FflonkBlindingV1::default(),
        FflonkBlindingV1 {
          wire_evaluations: core::array::from_fn(|i| Fr::from(i as u64 + 31)),
          z_coefficients: [Fr::from(41u64), Fr::from(43u64), Fr::from(47u64)],
        },
      ] {
        let expected =
          prove_fflonk(&srs, &memory, &r1cs, &witness, blinding).unwrap();
        let actual =
          prove_fflonk(&srs, &file, &r1cs, &witness, blinding).unwrap();
        assert_eq!(actual.proof.to_bytes(), expected.proof.to_bytes());
        assert_eq!(actual.public_inputs, expected.public_inputs);
        assert_eq!(
          verify_fflonk(
            &file.verification_key(),
            &actual.proof,
            &actual.public_inputs
          ),
          Ok(true)
        );
      }
    }
  }

  #[test]
  fn c0_packing_crosses_source_and_output_chunk_boundaries() {
    use crate::polynomial_storage::evaluate_polynomial_source;
    let n = FFLONK_POLYNOMIAL_CHUNK_FIELDS + 3;
    let file = PolynomialFile::new(Cursor::new(Vec::new())).unwrap();
    let mut offset = 0;
    let coefficients: [_; 8] = core::array::from_fn(|column| {
      let values = (0..n)
        .map(|row| Fr::from((11 * row + column + 1) as u64))
        .collect::<Vec<_>>();
      let stored = file
        .write_polynomial(
          offset,
          values.as_slice(),
          FFLONK_POLYNOMIAL_CHUNK_FIELDS,
        )
        .unwrap();
      offset = stored.end();
      stored
    });
    let interleaved =
      InterleavedC0 { file: &file, coefficients: &coefficients, len: 8 * n };
    let c0 = file
      .write_polynomial(
        offset,
        &interleaved,
        8 * FFLONK_POLYNOMIAL_CHUNK_FIELDS,
      )
      .unwrap();
    let source = file.source(&c0);
    for start in [
      0,
      FFLONK_POLYNOMIAL_CHUNK_FIELDS - 3,
      8 * FFLONK_POLYNOMIAL_CHUNK_FIELDS - 3,
      8 * n - 9,
    ] {
      let mut values = [Fr::zero(); 9];
      source.read_fields(start, &mut values).unwrap();
      for (i, value) in values.into_iter().enumerate() {
        let degree = start + i;
        let column = FflonkFixedPolynomialV1::C0_ORDER[degree % 8].index();
        assert_eq!(value, Fr::from((11 * (degree / 8) + column + 1) as u64));
      }
    }
    let point = Fr::from(19u64);
    let x8 = point.pow([8]);
    let mut expected = Fr::zero();
    let mut power = Fr::ONE;
    for id in FflonkFixedPolynomialV1::C0_ORDER {
      let at_x8 = (0..n).rev().fold(Fr::zero(), |value, row| {
        value * x8 + Fr::from((11 * row + id.index() + 1) as u64)
      });
      expected += power * at_x8;
      power *= point;
    }
    assert_eq!(
      evaluate_polynomial_source(&source, &[point]).unwrap(),
      [expected]
    );
  }

  #[test]
  fn file_key_rejects_wrong_srs_and_nonempty_scratch_storage() {
    let (r1cs, witness) = fixture(1);
    let arithmetization = arithmetize_r1cs(&r1cs).unwrap();
    let degree = usize::try_from(
      required_fflonk_srs_degree(arithmetization.census().domain_size).unwrap(),
    )
    .unwrap();
    let srs = test_srs(degree, Fr::from(23u64));
    assert!(matches!(
      preprocess_fflonk_to_file(
        &srs,
        arithmetization.clone(),
        Cursor::new(vec![1])
      ),
      Err(FflonkPreprocessingError::Storage(FflonkStorageError::NonemptyFile))
    ));
    let short_srs = test_srs(degree - 1, Fr::from(23u64));
    assert!(matches!(
      preprocess_fflonk_to_file(
        &short_srs,
        arithmetization.clone(),
        Cursor::new(Vec::new())
      ),
      Err(FflonkPreprocessingError::Srs(KzgError::DegreeTooLarge { .. }))
    ));
    let file =
      preprocess_fflonk_to_file(&srs, arithmetization, Cursor::new(Vec::new()))
        .unwrap();
    let other_srs = test_srs(degree, Fr::from(29u64));
    assert_eq!(
      prove_fflonk(
        &other_srs,
        &file,
        &r1cs,
        &witness,
        FflonkBlindingV1::default()
      ),
      Err(FflonkProverError::SrsMismatch)
    );
  }

  #[test]
  fn external_file_changes_are_rejected_in_early_and_late_proof_rounds() {
    use std::sync::atomic::{AtomicU64, Ordering};
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let path = std::env::temp_dir().join(format!(
      "ix-fflonk-key-test-{}-{}.bin",
      std::process::id(),
      NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    struct Cleanup(std::path::PathBuf);
    impl Drop for Cleanup {
      fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
      }
    }
    let cleanup = Cleanup(path);
    let storage = std::fs::OpenOptions::new()
      .read(true)
      .write(true)
      .create_new(true)
      .open(&cleanup.0)
      .unwrap();
    let (r1cs, witness) = fixture(1);
    let arithmetization = arithmetize_r1cs(&r1cs).unwrap();
    let n = arithmetization.census().domain_size;
    let srs = test_srs(
      usize::try_from(required_fflonk_srs_degree(n).unwrap()).unwrap(),
      Fr::from(23u64),
    );
    let key =
      preprocess_fflonk_to_file(&srs, arithmetization, storage).unwrap();
    let mut writer = std::fs::OpenOptions::new()
      .read(true)
      .write(true)
      .open(&cleanup.0)
      .unwrap();
    // QL is read in round 1, sigma evaluations in round 2, and C0 in round 4.
    for offset in [0, 5 * n * 32, 11 * n * 32] {
      writer.seek(SeekFrom::Start(offset)).unwrap();
      let mut original = [0u8; 1];
      writer.read_exact(&mut original).unwrap();
      writer.seek(SeekFrom::Start(offset)).unwrap();
      writer.write_all(&[original[0] ^ 1]).unwrap();
      writer.flush().unwrap();
      assert_eq!(
        prove_fflonk(&srs, &key, &r1cs, &witness, FflonkBlindingV1::default()),
        Err(FflonkProverError::Storage(FflonkStorageError::ChunkChanged {
          offset
        }))
      );
      writer.seek(SeekFrom::Start(offset)).unwrap();
      writer.write_all(&original).unwrap();
      writer.flush().unwrap();
    }
    let output =
      prove_fflonk(&srs, &key, &r1cs, &witness, FflonkBlindingV1::default())
        .unwrap();
    assert_eq!(
      verify_fflonk(
        &key.verification_key(),
        &output.proof,
        &output.public_inputs
      ),
      Ok(true)
    );
  }
}
