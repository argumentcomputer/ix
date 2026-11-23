//! Monomial-basis KZG implementing [`Pcs`] for BN254 and BLS12-381.
//!
//! Each column has one G1 commitment under the declared full public degree.
//! Domain sizes describe trace geometry; the public setup supplies the global
//! polynomial degree allowance used by the enclosing constraint argument.
//! Openings at each point are folded with a
//! transcript challenge, producing one witness commitment per distinct point.
//! A second challenge batches their pairing equations.
//!
//! Quotients use coefficient slices: `Q(X) = Σₖ X^{k·n}·cₖ(X)`.
//! Coset FFTs evaluate stored coefficients on the quotient domain;
//! [`Pcs::max_quotient_degree`] bounds this evaluation budget. Requested
//! evaluation domains must be at least as large as the committed trace;
//! smaller-domain coefficient folding is unsupported.
//!
//! With the `cuda` feature, resident columns of sufficient size run their
//! transforms, commitments, evaluations and opening divisions on the
//! selected devices, retaining device copies within the residency budget.
//! Only shapes below the device thresholds and disk-backed columns use the
//! host implementation; a device that cannot admit an operation is an error.
//! The proof bytes do not depend on the path taken.

use std::sync::Arc;

use super::curve::{
  Bn254, G1AffineOf, G1ProjectiveOf, KzgCurve, read_g1_compressed_for,
};
use ark_ec::{CurveGroup, VariableBaseMSM, pairing::Pairing};
use ark_ff::{Field as ArkField, Zero};
use ark_poly::{
  EvaluationDomain as ArkEvaluationDomain, Radix2EvaluationDomain,
};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use p3_maybe_rayon::prelude::*;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use multi_stark::traits::EvaluationDomain;
use multi_stark::traits::OpenedValues;
use multi_stark::traits::OpeningRounds;
use multi_stark::traits::Pcs;
use multi_stark::traits::Transcript;
use multi_stark::traits::TwoAdicField;
use multi_stark::traits::VerifyRounds;

#[cfg(not(feature = "cuda"))]
use super::coefficients::SpilledEvaluations;
use super::coefficients::{Column, DiskFile};
#[cfg(feature = "cuda")]
use super::cuda;
use super::domain::Radix2Coset;
use super::field::CurveScalar;
use super::srs::Srs;
use super::transcript::KzgTranscript;

/// Per-matrix column commitments.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KzgCommitment<C: KzgCurve = Bn254>(pub Vec<Vec<G1AffineOf<C>>>);

/// One opening proof: one witness point per distinct opening point, in
/// transcript (first-appearance) order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KzgProof<C: KzgCurve = Bn254>(pub Vec<G1AffineOf<C>>);

impl<C: KzgCurve> Serialize for KzgCommitment<C> {
  fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
    let mut bytes = Vec::new();
    self
      .0
      .serialize_compressed(&mut bytes)
      .map_err(serde::ser::Error::custom)?;
    bytes.serialize(serializer)
  }
}

impl<'de, C: KzgCurve> Deserialize<'de> for KzgCommitment<C> {
  fn deserialize<D: Deserializer<'de>>(
    deserializer: D,
  ) -> Result<Self, D::Error> {
    let bytes = Vec::<u8>::deserialize(deserializer)?;
    decode_commitment::<C>(&bytes).map_err(serde::de::Error::custom)
  }
}

fn decode_commitment<C: KzgCurve>(
  mut input: &[u8],
) -> Result<KzgCommitment<C>, ark_serialize::SerializationError> {
  use ark_serialize::SerializationError;
  fn count(
    input: &mut &[u8],
    element_bytes: usize,
  ) -> Result<usize, SerializationError> {
    let count = usize::try_from(u64::deserialize_compressed(&mut *input)?)
      .map_err(|_error| SerializationError::InvalidData)?;
    if count > input.len() / element_bytes {
      return Err(SerializationError::InvalidData);
    }
    Ok(count)
  }
  let rows = count(&mut input, 8)?;
  let mut matrices = Vec::with_capacity(rows);
  for _ in 0..rows {
    let width = count(&mut input, C::G1_COMPRESSED_BYTES)?;
    let mut points = Vec::with_capacity(width);
    for _ in 0..width {
      points.push(read_g1_compressed_for::<C>(&mut input)?);
    }
    matrices.push(points);
  }
  if !input.is_empty() {
    return Err(SerializationError::InvalidData);
  }
  Ok(KzgCommitment(matrices))
}

// The shared PCS interface requires serde, but KZG proof transport requires
// the authenticated shape supplied to FixedProofCodec.
impl<C: KzgCurve> Serialize for KzgProof<C> {
  fn serialize<S: Serializer>(
    &self,
    _serializer: S,
  ) -> Result<S::Ok, S::Error> {
    Err(serde::ser::Error::custom("KZG proofs require FixedProofCodec"))
  }
}

impl<'de, C: KzgCurve> Deserialize<'de> for KzgProof<C> {
  fn deserialize<D: Deserializer<'de>>(
    _deserializer: D,
  ) -> Result<Self, D::Error> {
    Err(serde::de::Error::custom("KZG proofs require FixedProofCodec"))
  }
}

/// A committed matrix on the prover side: its domain and each column
/// polynomial in coefficient form (length = domain size).
pub struct CommittedMatrix<C: KzgCurve = Bn254> {
  pub(crate) domain: Radix2Coset<C>,
  columns: Vec<Column<C>>,
  /// Compact constant columns and resident columns whose coefficients above
  /// the constant term are zero. Disk-backed columns are never flagged; the
  /// flag is an optimization.
  constants: Vec<bool>,
  /// Optional one-shot spill of natural-domain stage-1 evaluations so
  /// `host_lookup_part` can reload them sequentially instead of running
  /// redundant forward FFTs.
  #[cfg(not(feature = "cuda"))]
  spilled_evaluations: std::sync::Mutex<Option<SpilledEvaluations<C>>>,
  #[cfg(feature = "cuda")]
  resident: std::sync::OnceLock<Vec<Option<Arc<cuda::ResidentPolynomial<C>>>>>,
}

impl<C: KzgCurve> CommittedMatrix<C> {
  /// Evaluation domain represented by the stored coefficient columns.
  pub fn domain(&self) -> Radix2Coset<C> {
    self.domain
  }

  /// Number of polynomial columns.
  pub fn width(&self) -> usize {
    self.columns.len()
  }

  /// Coefficient columns, in matrix column order.
  pub(super) fn coefficient_columns(&self) -> &[Column<C>] {
    &self.columns
  }

  pub(super) fn new(domain: Radix2Coset<C>, columns: Vec<Column<C>>) -> Self {
    let constants = columns
      .par_iter()
      .map(|column| {
        matches!(column, Column::Constant { .. })
          || column
            .resident()
            .is_some_and(|values| values.iter().skip(1).all(Zero::is_zero))
      })
      .collect();
    Self {
      domain,
      columns,
      constants,
      #[cfg(not(feature = "cuda"))]
      spilled_evaluations: std::sync::Mutex::new(None),
      #[cfg(feature = "cuda")]
      resident: Default::default(),
    }
  }

  /// Consume and reload spilled natural-domain evaluations once, immediately
  /// closing and releasing the unlinked temporary spill file.
  #[cfg(not(feature = "cuda"))]
  #[allow(dead_code)]
  pub(super) fn take_spilled_evaluations(
    &self,
    domain: Radix2Coset<C>,
  ) -> Option<RowMajorMatrix<CurveScalar<C>>> {
    let mut guard = self.spilled_evaluations.lock().ok()?;
    if guard.as_ref().is_none_or(|spilled| spilled.domain() != domain) {
      return None;
    }
    let spilled = guard.take()?;
    drop(guard);
    Some(spilled.load().expect("spilled natural-domain evaluations"))
  }

  fn constant_columns(&self) -> &[bool] {
    &self.constants
  }

  /// Every column as a host slice with its current device residency and
  /// constant flag, or `None` when a column is disk-backed. A compact
  /// constant column is the one-element slice of its constant term; device
  /// consumers read only that term or zero-pad it to the trace length.
  /// Residency is reported, not created; see [`Self::resident_columns`].
  #[cfg(feature = "cuda")]
  pub(super) fn cuda_columns(
    &self,
  ) -> Option<Vec<(&[C::Fr], Option<&cuda::ResidentPolynomial<C>>, bool)>> {
    let resident = self.resident.get();
    self
      .columns
      .iter()
      .enumerate()
      .zip(&self.constants)
      .map(|((index, column), &constant)| {
        Some((
          column.host_coefficients()?,
          resident.and_then(|columns| columns[index].as_deref()),
          constant,
        ))
      })
      .collect()
  }

  /// Device copies of the non-constant resident columns, uploaded on first
  /// use within the residency budget. Disk-backed columns stay host-only.
  #[cfg(feature = "cuda")]
  pub(super) fn resident_columns(
    &self,
  ) -> &[Option<Arc<cuda::ResidentPolynomial<C>>>] {
    self.resident.get_or_init(|| {
      // A OnceLock initializer must not run Rayon work that can reenter it.
      self
        .columns
        .iter()
        .zip(&self.constants)
        .map(|(column, &constant)| {
          if constant {
            None
          } else {
            column.resident().and_then(cuda::retain::<C>)
          }
        })
        .collect()
    })
  }
}

/// Prover-side retained data for one commitment round.
pub struct KzgProverData<C: KzgCurve = Bn254> {
  commitment: KzgCommitment<C>,
  pub matrices: Vec<CommittedMatrix<C>>,
}

impl<C: KzgCurve> KzgProverData<C> {
  #[cfg(all(test, feature = "cuda"))]
  pub(super) fn coefficient_fixture(
    domain: Radix2Coset<C>,
    columns: Vec<Vec<C::Fr>>,
  ) -> Self {
    Self {
      commitment: KzgCommitment(vec![vec![]]),
      matrices: vec![CommittedMatrix::new(
        domain,
        columns.into_iter().map(Column::from).collect(),
      )],
    }
  }

  /// Save a local prover checkpoint. This is not a verifier-key format.
  pub fn write_checkpoint(
    &self,
    mut out: impl std::io::Write,
  ) -> Result<(), ark_serialize::SerializationError> {
    out.write_all(C::CHECKPOINT_MAGIC)?;
    self.commitment.0.serialize_compressed(&mut out)?;
    (self.matrices.len() as u64).serialize_compressed(&mut out)?;
    for matrix in &self.matrices {
      (matrix.domain.log_size as u64).serialize_compressed(&mut out)?;
      matrix.domain.shift.0.serialize_compressed(&mut out)?;
      (matrix.columns.len() as u64).serialize_compressed(&mut out)?;
      for column in &matrix.columns {
        (column.len() as u64).serialize_compressed(&mut out)?;
        let mut result = Ok(());
        column.visit(|_, values| {
          if result.is_err() {
            return;
          }
          result =
            super::encoding::write_fields::<C, _>(&mut out, values, |value| {
              *value
            })
            .map_err(ark_serialize::SerializationError::from);
        })?;
        result?;
      }
    }
    Ok(())
  }

  /// Load a trusted, locally produced prover checkpoint.
  pub fn read_checkpoint(
    mut input: impl std::io::Read,
  ) -> Result<Self, ark_serialize::SerializationError> {
    let mut magic = [0; 8];
    input.read_exact(&mut magic)?;
    if &magic != C::CHECKPOINT_MAGIC {
      return Err(ark_serialize::SerializationError::InvalidData);
    }
    let commitment = KzgCommitment(Vec::deserialize_compressed(&mut input)?);
    let count = usize::try_from(u64::deserialize_compressed(&mut input)?)
      .map_err(|_error| ark_serialize::SerializationError::InvalidData)?;
    if count != commitment.0.len() {
      return Err(ark_serialize::SerializationError::InvalidData);
    }
    let mut matrices = Vec::with_capacity(count);
    for i in 0..count {
      let log_size = usize::try_from(u64::deserialize_compressed(&mut input)?)
        .map_err(|_error| ark_serialize::SerializationError::InvalidData)?;
      if log_size > CurveScalar::<C>::TWO_ADICITY {
        return Err(ark_serialize::SerializationError::InvalidData);
      }
      let shift = CurveScalar(C::Fr::deserialize_compressed(&mut input)?);
      let width = usize::try_from(u64::deserialize_compressed(&mut input)?)
        .map_err(|_error| ark_serialize::SerializationError::InvalidData)?;
      if width != commitment.0[i].len() {
        return Err(ark_serialize::SerializationError::InvalidData);
      }
      let mut columns = Vec::with_capacity(width);
      for _ in 0..width {
        let len = u64::deserialize_compressed(&mut input)?;
        if len != 1u64 << log_size {
          return Err(ark_serialize::SerializationError::InvalidData);
        }
        columns.push(
          super::encoding::read_fields::<C, _>(
            &mut input,
            1usize << log_size,
            |v| v,
          )
          .map_err(ark_serialize::SerializationError::from)?,
        );
      }
      matrices.push(CommittedMatrix::new(
        Radix2Coset { log_size, shift },
        columns.into_iter().map(Column::from).collect(),
      ));
    }
    let mut tail = [0];
    if input.read(&mut tail)? != 0 {
      return Err(ark_serialize::SerializationError::InvalidData);
    }
    Ok(Self { commitment, matrices })
  }

  /// Index an existing trusted local checkpoint without retaining its columns.
  /// Each later read checks canonical scalars and the digest recorded here.
  pub fn read_checkpoint_file(
    path: impl AsRef<std::path::Path>,
  ) -> Result<Self, ark_serialize::SerializationError> {
    Self::read_checkpoint_file_with_chunk(path, super::coefficients::CHUNK)
  }

  fn read_checkpoint_file_with_chunk(
    path: impl AsRef<std::path::Path>,
    chunk: usize,
  ) -> Result<Self, ark_serialize::SerializationError> {
    use ark_serialize::SerializationError;
    use std::{
      fs::File,
      io::{BufReader, Read},
      sync::Mutex,
    };
    let file = Arc::new(Mutex::new(DiskFile::persistent(File::open(path)?)));
    let mut guard =
      file.lock().map_err(|_error| SerializationError::InvalidData)?;
    let mut reader = BufReader::with_capacity(1 << 20, guard.file_mut());
    let mut magic = [0; 8];
    reader.read_exact(&mut magic)?;
    if &magic != C::CHECKPOINT_MAGIC {
      return Err(SerializationError::InvalidData);
    }
    let commitment = KzgCommitment(Vec::deserialize_compressed(&mut reader)?);
    let count = usize::try_from(u64::deserialize_compressed(&mut reader)?)
      .map_err(|_error| SerializationError::InvalidData)?;
    if count != commitment.0.len() {
      return Err(SerializationError::InvalidData);
    }
    let mut matrices = Vec::with_capacity(count);
    for i in 0..count {
      let log = u64::deserialize_compressed(&mut reader)?;
      if log > CurveScalar::<C>::TWO_ADICITY as u64 {
        return Err(SerializationError::InvalidData);
      }
      let log_size = usize::try_from(log)
        .map_err(|_error| SerializationError::InvalidData)?;
      let shift = CurveScalar(C::Fr::deserialize_compressed(&mut reader)?);
      let width = u64::deserialize_compressed(&mut reader)?;
      if width != commitment.0[i].len() as u64 {
        return Err(SerializationError::InvalidData);
      }
      let mut columns = Vec::with_capacity(commitment.0[i].len());
      for _ in 0..width {
        let len = u64::deserialize_compressed(&mut reader)?;
        if len != 1u64 << log {
          return Err(SerializationError::InvalidData);
        }
        columns.push(Column::index_with_chunk(
          &mut reader,
          file.clone(),
          1usize << log_size,
          chunk,
        )?);
      }
      matrices
        .push(CommittedMatrix::new(Radix2Coset { log_size, shift }, columns));
    }
    let mut tail = [0];
    if reader.read(&mut tail)? != 0 {
      return Err(SerializationError::InvalidData);
    }
    crate::pipeline::storage::fadvise_dontneed(reader.get_ref(), 0, 0);
    Ok(Self { commitment, matrices })
  }

  /// Combine independently committed matrices in canonical circuit order.
  pub fn concatenate(
    parts: impl IntoIterator<Item = Self>,
  ) -> (KzgCommitment<C>, Self) {
    let mut commitment = KzgCommitment(vec![]);
    let mut matrices = Vec::new();
    for mut part in parts {
      commitment.0.append(&mut part.commitment.0);
      matrices.append(&mut part.matrices);
    }
    (commitment.clone(), Self { commitment, matrices })
  }
}

/// Prover data that keeps each committed matrix as coefficient columns, so
/// lookup and quotient constructions can read committed rounds directly.
pub(crate) trait CoefficientData<C: KzgCurve = Bn254>: Sync {
  fn matrix(&self, index: usize) -> Option<&CommittedMatrix<C>>;
}

impl<C: KzgCurve> CoefficientData<C> for KzgProverData<C> {
  fn matrix(&self, index: usize) -> Option<&CommittedMatrix<C>> {
    self.matrices.get(index)
  }
}

/// A configuration over curve scalars whose PCS retains coefficient columns.
pub(crate) trait CoefficientConfig<C: KzgCurve = Bn254>:
  multi_stark::config::ProofConfig<
    Challenge = CurveScalar<C>,
    Pcs: Pcs<
      F = CurveScalar<C>,
      Domain = Radix2Coset<C>,
      ProverData: CoefficientData<C>,
    >,
  >
{
}

impl<C: KzgCurve, SC> CoefficientConfig<C> for SC where
  SC: multi_stark::config::ProofConfig<
      Challenge = CurveScalar<C>,
      Pcs: Pcs<
        F = CurveScalar<C>,
        Domain = Radix2Coset<C>,
        ProverData: CoefficientData<C>,
      >,
    >
{
}

#[derive(Debug)]
pub enum KzgError {
  /// Commitment/opened-value dimensions disagree with the rounds.
  ShapeMismatch,
  /// The batched pairing equation does not hold.
  PairingCheckFailed,
  /// A commitment or witness point is off the curve or outside the subgroup.
  InvalidPoint,
}

/// See the module docs.
#[derive(Clone)]
pub struct KzgPcs<C: KzgCurve = Bn254> {
  srs: Option<Arc<Srs<C>>>,
  #[cfg(feature = "cuda")]
  srs_owner: Option<Arc<cuda::srs_residency::Owner<C>>>,
  verifier: super::VerifierParams<C>,
  max_quotient_degree: usize,
}

impl<C: KzgCurve> KzgPcs<C> {
  /// The public anchors every proof of this configuration is bound to.
  pub fn verifier_params(&self) -> &super::VerifierParams<C> {
    &self.verifier
  }

  /// Loaded proving powers, independent of the public trace capacity.
  /// Verifier-only configurations do not carry proving powers.
  pub fn proving_capacity(&self) -> Option<usize> {
    self.srs.as_ref().map(|srs| srs.max_len())
  }

  /// The public setup these parameters commit to.
  pub fn public_setup(&self) -> super::PublicSetup {
    self.verifier.public_setup()
  }

  pub(super) fn evaluate_columns(
    &self,
    data: &KzgProverData<C>,
    idx: usize,
    domain: Radix2Coset<C>,
    selected: &[usize],
  ) -> RowMajorMatrix<CurveScalar<C>> {
    self.evaluate_matrix_columns(&data.matrices[idx], domain, selected)
  }

  pub(super) fn evaluate_matrix_columns(
    &self,
    matrix: &CommittedMatrix<C>,
    domain: Radix2Coset<C>,
    selected: &[usize],
  ) -> RowMajorMatrix<CurveScalar<C>> {
    assert!(
      domain.size() >= matrix.domain.size(),
      "evaluation domain ({}) is smaller than the committed trace ({})",
      domain.size(),
      matrix.domain.size()
    );
    assert!(
      domain.size() <= matrix.domain.size() * self.max_quotient_degree,
      "requested domain ({}) exceeds the coset-FFT budget ({}x trace); \
             raise max_quotient_degree if this cost is intended",
      domain.size(),
      self.max_quotient_degree
    );
    #[cfg(feature = "cuda")]
    if domain.size() >= 1 << 10
      && let Some(views) = matrix.cuda_columns()
    {
      return Self::evaluate_columns_on_device(
        matrix,
        &views,
        domain,
        selected,
        1 << 30,
      );
    }
    #[cfg(feature = "cuda")]
    tracing::debug!(
      curve = C::NAME,
      rows = domain.size(),
      columns = selected.len(),
      reason = "small domain or disk-backed columns",
      "KZG FFT using CPU evaluation"
    );
    let ark = Self::ark_domain(domain);
    let width = selected.len();
    let height = domain.size();
    let mut values = vec![CurveScalar(C::FR_ZERO); width * height];
    let pairs = width / 2;
    for i in 0..pairs {
      let columns = super::fft_batch::evaluate::<C>(
        &[
          &matrix.columns[selected[2 * i]],
          &matrix.columns[selected[2 * i + 1]],
        ],
        ark,
      );
      values.par_chunks_mut(width).zip(columns).for_each(|(row, value)| {
        row[2 * i] = CurveScalar(value.0[0]);
        row[2 * i + 1] = CurveScalar(value.0[1]);
      });
    }
    if let Some(coefficients) =
      selected.get(pairs * 2).map(|&i| &matrix.columns[i])
    {
      let column = match coefficients {
        Column::Constant { value, .. } => vec![*value; height],
        _ => {
          let coefficients =
            coefficients.load().expect("coefficient checkpoint");
          if coefficients.iter().skip(1).all(Zero::is_zero) {
            vec![coefficients.first().copied().unwrap_or(C::FR_ZERO); height]
          } else {
            let mut values = coefficients.into_owned();
            ark.fft_in_place(&mut values);
            values
          }
        },
      };
      values
        .par_chunks_mut(width)
        .zip(column)
        .for_each(|(row, value)| row[pairs * 2] = CurveScalar(value));
    }
    RowMajorMatrix::new(values, width)
  }

  /// Coset-evaluate the selected columns through device FFT queues. The
  /// destination holds the full matrix; simultaneous FFT outputs are bounded
  /// by `scratch_bytes`, or one column when a column exceeds that budget.
  #[cfg(feature = "cuda")]
  fn evaluate_columns_on_device(
    matrix: &CommittedMatrix<C>,
    views: &[(&[C::Fr], Option<&cuda::ResidentPolynomial<C>>, bool)],
    domain: Radix2Coset<C>,
    selected: &[usize],
    scratch_bytes: usize,
  ) -> RowMajorMatrix<CurveScalar<C>> {
    let _profile =
      cuda::ProfileRange::<C>::new(c"kzg/evaluation-reconstruction");
    let started = std::time::Instant::now();
    let constants = matrix.constant_columns();
    let width = selected.len();
    let height = domain.size();
    let mut values = generate_buffer(width * height, |index| {
      let column = selected[index % width];
      if constants[column] {
        CurveScalar(views[column].0[0])
      } else {
        CurveScalar(C::FR_ZERO)
      }
    });
    let active: Vec<_> =
      (0..width).filter(|&position| !constants[selected[position]]).collect();
    let batch_columns = (scratch_bytes / (height * size_of::<C::Fr>())).max(1);
    let residents = matrix.resident_columns();
    for batch in active.chunks(batch_columns) {
      let inputs: Vec<_> = batch
        .iter()
        .map(|&position| {
          let column = selected[position];
          (views[column].0, residents[column].as_deref())
        })
        .collect();
      let transformed =
        cuda::fft_columns::<C>(&inputs, domain.log_size, false, domain.shift.0);
      values.par_chunks_mut(width * (1 << 12)).enumerate().for_each(
        |(tile, rows)| {
          for (offset, row) in rows.chunks_mut(width).enumerate() {
            let index = tile * (1 << 12) + offset;
            for (&position, evaluations) in batch.iter().zip(&transformed) {
              row[position] = CurveScalar(evaluations[index]);
            }
          }
        },
      );
    }
    tracing::info!(
      curve = C::NAME,
      width,
      height,
      batch_columns,
      seconds = started.elapsed().as_secs_f64(),
      "KZG evaluation reconstruction"
    );
    RowMajorMatrix::new(values, width)
  }

  pub fn new(srs: Arc<Srs<C>>, max_quotient_degree: usize) -> Self {
    let max_trace_len = srs.max_len();
    Self::with_max_trace_len(srs, max_trace_len, max_quotient_degree)
  }

  pub fn with_max_trace_len(
    srs: Arc<Srs<C>>,
    max_trace_len: usize,
    max_quotient_degree: usize,
  ) -> Self {
    let verifier =
      super::VerifierParams::with_max_trace_len(&srs, max_trace_len);
    Self::validate_quotient_domain(&verifier, max_quotient_degree);
    Self {
      #[cfg(feature = "cuda")]
      srs_owner: Some(cuda::srs_residency::Owner::new(Arc::clone(&srs))),
      srs: Some(srs),
      verifier,
      max_quotient_degree,
    }
  }

  pub fn verifier_only(
    verifier: super::VerifierParams<C>,
    max_quotient_degree: usize,
  ) -> Self {
    Self::validate_quotient_domain(&verifier, max_quotient_degree);
    Self {
      srs: None,
      #[cfg(feature = "cuda")]
      srs_owner: None,
      verifier,
      max_quotient_degree,
    }
  }

  fn validate_quotient_domain(
    verifier: &super::VerifierParams<C>,
    max_quotient_degree: usize,
  ) {
    assert!(max_quotient_degree.is_power_of_two());
    assert!(
      verifier.max_trace_len().ilog2() + max_quotient_degree.ilog2()
        <= <C::Fr as ark_ff::FftField>::TWO_ADICITY,
      "trace and quotient domains exceed scalar two-adicity"
    );
  }

  pub(super) fn prover_srs(&self) -> &Srs<C> {
    self.srs.as_deref().expect("proving requires the full SRS")
  }

  #[cfg(feature = "cuda")]
  fn srs_owner(&self) -> &Arc<cuda::srs_residency::Owner<C>> {
    self.srs_owner.as_ref().expect("proving requires the full SRS")
  }

  /// Device-generated coefficient columns of one trace-sized matrix.
  #[cfg(feature = "cuda")]
  pub(super) fn coefficient_matrix(
    &self,
    trace_log_size: usize,
    columns: Vec<Vec<C::Fr>>,
  ) -> CommittedMatrix<C> {
    let n = 1usize
      .checked_shl(u32::try_from(trace_log_size).expect("trace log size"))
      .unwrap();
    assert!(
      n <= self.verifier.max_trace_len() && n <= self.prover_srs().max_len()
    );
    assert!(!columns.is_empty());
    assert!(columns.iter().all(|column| column.len() == n));
    CommittedMatrix::new(
      Radix2Coset {
        log_size: trace_log_size,
        shift: multi_stark::traits::Algebra::<CurveScalar<C>>::ONE,
      },
      columns.into_iter().map(Column::from).collect(),
    )
  }

  /// Commit one coefficient matrix as a single-matrix round.
  pub(super) fn commit_matrix(
    &self,
    matrix: CommittedMatrix<C>,
  ) -> KzgProverData<C> {
    let commitment = KzgCommitment(vec![self.commit_matrix_columns(&matrix)]);
    KzgProverData { commitment, matrices: vec![matrix] }
  }

  /// Interpolate quotient evaluations over `quotient_domain` and split
  /// `Q(X) = Σₖ X^{k·n}·cₖ(X)` into trace-sized slices: slice k of
  /// coordinate d is column `k·D + d`, the order the verifier's
  /// ζ-recombination reads.
  pub(super) fn interpolate_quotient(
    quotient_domain: Radix2Coset<C>,
    evaluations: RowMajorMatrix<CurveScalar<C>>,
    quotient_degree: usize,
  ) -> CommittedMatrix<C> {
    let big = quotient_domain.size();
    assert!(quotient_degree != 0 && big.is_multiple_of(quotient_degree));
    let n = big / quotient_degree;
    let coefficients =
      Self::interpolate_columns(quotient_domain, evaluations).columns;
    let columns = (0..quotient_degree)
      .flat_map(|k| {
        coefficients.iter().map(move |c| c.slice(k * n..(k + 1) * n))
      })
      .collect();
    CommittedMatrix::new(
      Radix2Coset {
        log_size: p3_util::log2_strict_usize(n),
        shift: multi_stark::traits::Algebra::<CurveScalar<C>>::ONE,
      },
      columns,
    )
  }

  /// The arkworks FFT domain realizing one of ours.
  fn ark_domain(domain: Radix2Coset<C>) -> Radix2EvaluationDomain<C::Fr> {
    let base = Radix2EvaluationDomain::new(domain.size())
      .expect("size within Fr two-adicity");
    if domain.shift == multi_stark::traits::Algebra::<CurveScalar<C>>::ONE {
      base
    } else {
      base.get_coset(domain.shift.0).expect("nonzero coset shift")
    }
  }

  fn commit_matrix_columns(
    &self,
    matrix: &CommittedMatrix<C>,
  ) -> Vec<G1AffineOf<C>> {
    #[cfg(feature = "cuda")]
    if matrix.domain.size() >= 1 << 12
      && let Some(views) = matrix.cuda_columns()
    {
      let count = matrix.domain.size();
      assert!(
        count <= self.verifier.max_trace_len()
          && count <= self.prover_srs().max_len(),
        "polynomial length {count} exceeds the trace cap or loaded SRS"
      );
      let constants = matrix.constant_columns();
      let mut commits = vec![G1ProjectiveOf::<C>::zero(); views.len()];
      let active: Vec<_> =
        (0..views.len()).filter(|&i| !constants[i]).collect();
      for (i, (column, _, _)) in views.iter().enumerate() {
        if constants[i] {
          commits[i] = self.prover_srs().g1[0] * column[0];
        }
      }
      if !active.is_empty() {
        // Residency is retained from 2^16 rows, where repeated device use
        // amortizes the upload; smaller columns are streamed from the host.
        let residents = (count >= 1 << 16).then(|| matrix.resident_columns());
        let inputs: Vec<_> = active
          .iter()
          .map(|&i| (views[i].0, residents.and_then(|r| r[i].as_deref())))
          .collect();
        let started = std::time::Instant::now();
        let points = if cuda::srs_residency::enabled() {
          cuda::srs_residency::msm_columns::<C>(self.srs_owner(), 0, &inputs)
        } else {
          cuda::msm_columns_resident::<C>(
            &self.prover_srs().g1[..count],
            &inputs,
          )
        };
        for (i, point) in active.into_iter().zip(points) {
          commits[i] = point;
        }
        tracing::debug!(
          curve = C::NAME,
          count,
          columns = inputs.len(),
          seconds = started.elapsed().as_secs_f64(),
          "KZG column MSMs"
        );
      }
      return G1ProjectiveOf::<C>::normalize_batch(&commits);
    }
    let commits: Vec<G1ProjectiveOf<C>> =
      matrix.columns.iter().map(|c| self.commit_column(c)).collect();
    G1ProjectiveOf::<C>::normalize_batch(&commits)
  }

  /// Commit one column. A constant column is a multiple of the first power,
  /// so its coefficients are never materialized.
  fn commit_column(&self, column: &Column<C>) -> G1ProjectiveOf<C> {
    match column {
      Column::Constant { value, len } => {
        assert!(
          *len <= self.verifier.max_trace_len(),
          "polynomial length {len} exceeds the trace cap ({})",
          self.verifier.max_trace_len()
        );
        self.prover_srs().g1[0] * value
      },
      _ => self.msm(&column.load().expect("coefficient checkpoint")),
    }
  }

  pub(super) fn msm(&self, coeffs: &[C::Fr]) -> G1ProjectiveOf<C> {
    // Bound digit/bucket scratch and expose point-range parallelism in
    // addition to the MSM implementation's small number of scalar windows.
    const CHUNK: usize = 1 << 18;
    self.msm_with_chunk(coeffs, CHUNK)
  }

  fn msm_with_chunk(
    &self,
    coeffs: &[C::Fr],
    chunk: usize,
  ) -> G1ProjectiveOf<C> {
    assert!(chunk > 0);
    assert!(
      coeffs.len() <= self.verifier.max_trace_len(),
      "polynomial length {} exceeds the trace cap ({})",
      coeffs.len(),
      self.verifier.max_trace_len()
    );
    if coeffs.is_empty() {
      return G1ProjectiveOf::<C>::zero();
    }
    assert!(
      coeffs.len() <= self.prover_srs().max_len(),
      "proving requires the complete coefficient prefix"
    );
    if coeffs.iter().skip(1).all(Zero::is_zero) {
      #[cfg(feature = "cuda")]
      tracing::debug!(
        curve = C::NAME,
        reason = "constant polynomial",
        "KZG commitment using CPU arithmetic"
      );
      return self.prover_srs().g1[0]
        * coeffs.first().copied().unwrap_or(C::FR_ZERO);
    }
    #[cfg(feature = "cuda")]
    if coeffs.len() >= 1 << 12 {
      if cuda::srs_residency::enabled() {
        return cuda::srs_residency::msm_columns::<C>(
          self.srs_owner(),
          0,
          &[(coeffs, None)],
        )[0];
      }
      return cuda::msm::<C>(&self.prover_srs().g1[..coeffs.len()], coeffs);
    }
    #[cfg(feature = "cuda")]
    tracing::debug!(
      curve = C::NAME,
      points = coeffs.len(),
      reason = "small MSM",
      "KZG commitment using CPU MSM"
    );
    C::cpu_msm(&self.prover_srs().g1[..coeffs.len()], coeffs)
  }

  /// Commit a single constant column without allocating evaluation or
  /// coefficient buffers.
  #[allow(dead_code)]
  pub(super) fn commit_constant_column(
    &self,
    domain: Radix2Coset<C>,
    value: C::Fr,
  ) -> KzgProverData<C> {
    let column = Column::Constant { value, len: domain.size() };
    let point = self.commit_column(&column).into_affine();
    let commitment = KzgCommitment(vec![vec![point]]);
    KzgProverData {
      commitment,
      matrices: vec![CommittedMatrix::new(domain, vec![column])],
    }
  }

  /// Extract `column` from a row-major `matrix` into `dst` in a single
  /// parallel pass, returning `Some(constant)` when every row equals the
  /// first row so callers can skip IFFT/MSM without a second strided scan.
  #[cfg(not(feature = "cuda"))]
  fn extract_column_into(
    matrix: &RowMajorMatrix<CurveScalar<C>>,
    column: usize,
    dst: &mut Vec<C::Fr>,
  ) -> Option<C::Fr> {
    let height = matrix.height();
    let width = matrix.width();
    let first = matrix.values[column].0;
    if dst.len() != height {
      *dst = generate_buffer(height, |_| C::FR_ZERO);
    }
    let is_constant = dst
      .par_chunks_mut(1 << 14)
      .enumerate()
      .map(|(tile, chunk)| {
        let base = tile << 14;
        let mut all_equal = true;
        for (offset, slot) in chunk.iter_mut().enumerate() {
          let value = matrix.values[(base + offset) * width + column].0;
          *slot = value;
          all_equal &= value == first;
        }
        all_equal
      })
      .reduce(|| true, |a, b| a && b);
    is_constant.then_some(first)
  }

  /// Stream-commit each column of `matrix` over `domain`, returning only the
  /// normalized KZG commitments without keeping all column vectors resident.
  #[cfg(not(feature = "cuda"))]
  pub(crate) fn commit_matrix_commitment_only(
    &self,
    domain: Radix2Coset<C>,
    matrix: RowMajorMatrix<CurveScalar<C>>,
  ) -> KzgCommitment<C> {
    assert_eq!(matrix.height(), domain.size(), "matrix height != domain size");
    let width = matrix.width();
    let height = domain.size();
    let ark = Self::ark_domain(domain);
    let mut commits = Vec::with_capacity(width);
    if width == 1 {
      let first = matrix.values[0].0;
      if matrix.values.par_iter().all(|v| v.0 == first) {
        drop(matrix);
        commits.push(
          self.commit_column(&Column::Constant { value: first, len: height }),
        );
      } else {
        let mut coeffs: Vec<C::Fr> =
          matrix.values.into_iter().map(|v| v.0).collect();
        ark.ifft_in_place(&mut coeffs);
        commits.push(self.msm(&coeffs));
      }
    } else {
      let mut coeffs = Vec::new();
      for column in 0..width {
        if let Some(value) =
          Self::extract_column_into(&matrix, column, &mut coeffs)
        {
          commits
            .push(self.commit_column(&Column::Constant { value, len: height }));
        } else {
          ark.ifft_in_place(&mut coeffs);
          commits.push(self.msm(&coeffs));
        }
      }
      drop(coeffs);
      drop(matrix);
    }
    KzgCommitment(vec![G1ProjectiveOf::<C>::normalize_batch(&commits)])
  }

  /// Stream-commit `matrix` one column at a time directly into a checkpoint
  /// file in the exact [`KzgProverData::write_checkpoint`] format, avoiding a
  /// full transposed copy in memory and avoiding re-reading the written file
  /// to compute per-column digests.
  #[cfg(not(feature = "cuda"))]
  pub(crate) fn commit_matrix_to_checkpoint(
    &self,
    domain: Radix2Coset<C>,
    matrix: RowMajorMatrix<CurveScalar<C>>,
    temp_path: &std::path::Path,
  ) -> Result<
    (KzgCommitment<C>, Vec<StreamedColumn<C>>),
    ark_serialize::SerializationError,
  > {
    use std::{
      fs::File,
      io::{BufWriter, Seek, SeekFrom, Write},
    };
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

    assert_eq!(matrix.height(), domain.size(), "matrix height != domain size");
    let width = matrix.width();
    let height = domain.size();
    let encode_header = |commitment: &KzgCommitment<C>| -> Result<
      Vec<u8>,
      ark_serialize::SerializationError,
    > {
      let mut header = Vec::new();
      header.extend_from_slice(C::CHECKPOINT_MAGIC);
      commitment.0.serialize_compressed(&mut header)?;
      1u64.serialize_compressed(&mut header)?;
      (domain.log_size as u64).serialize_compressed(&mut header)?;
      domain.shift.0.serialize_compressed(&mut header)?;
      (width as u64).serialize_compressed(&mut header)?;
      Ok(header)
    };

    let placeholder =
      KzgCommitment::<C>(vec![vec![G1AffineOf::<C>::default(); width]]);
    let placeholder_header = encode_header(&placeholder)?;
    let mut writer =
      BufWriter::with_capacity(1 << 20, File::create(temp_path)?);
    writer.write_all(&placeholder_header)?;
    let mut file_offset = u64::try_from(placeholder_header.len())
      .map_err(|_error| ark_serialize::SerializationError::InvalidData)?;
    let column_bytes = u64::try_from(height)
      .ok()
      .and_then(|h| h.checked_mul(32))
      .ok_or(ark_serialize::SerializationError::InvalidData)?;

    let ark = Self::ark_domain(domain);
    let mut commits = Vec::with_capacity(width);
    let mut columns = Vec::with_capacity(width);

    let write_constant =
      |writer: &mut BufWriter<File>,
       value: C::Fr,
       file_offset: &mut u64|
       -> Result<StreamedColumn<C>, ark_serialize::SerializationError> {
        (height as u64).serialize_compressed(&mut *writer)?;
        *file_offset += 8;
        let column = Column::<C>::Constant { value, len: height };
        let mut result = Ok(());
        column.visit(|_, values| {
          if result.is_err() {
            return;
          }
          result =
            super::encoding::write_fields::<C, _>(&mut *writer, values, |v| *v)
              .map_err(ark_serialize::SerializationError::from);
        })?;
        result?;
        *file_offset += column_bytes;
        Ok(StreamedColumn::Constant(value))
      };

    let write_dense =
      |writer: &mut BufWriter<File>,
       coeffs: &[C::Fr],
       file_offset: &mut u64|
       -> Result<StreamedColumn<C>, ark_serialize::SerializationError> {
        (height as u64).serialize_compressed(&mut *writer)?;
        *file_offset += 8;
        let offset = *file_offset;
        let mut hashing =
          HashingWriter { inner: writer, hasher: blake3::Hasher::new() };
        super::encoding::write_fields::<C, _>(&mut hashing, coeffs, |v| *v)?;
        let digest = hashing.hasher.finalize();
        *file_offset += column_bytes;
        Ok(StreamedColumn::Disk { offset, digest })
      };

    if width == 1 {
      let first = matrix.values[0].0;
      if matrix.values.par_iter().all(|v| v.0 == first) {
        drop(matrix);
        commits.push(
          self.commit_column(&Column::Constant { value: first, len: height }),
        );
        columns.push(write_constant(&mut writer, first, &mut file_offset)?);
      } else {
        let mut coeffs: Vec<C::Fr> =
          matrix.values.into_iter().map(|v| v.0).collect();
        ark.ifft_in_place(&mut coeffs);
        commits.push(self.msm(&coeffs));
        columns.push(write_dense(&mut writer, &coeffs, &mut file_offset)?);
      }
    } else {
      let mut coeffs = Vec::new();
      for column in 0..width {
        if let Some(value) =
          Self::extract_column_into(&matrix, column, &mut coeffs)
        {
          commits
            .push(self.commit_column(&Column::Constant { value, len: height }));
          columns.push(write_constant(&mut writer, value, &mut file_offset)?);
        } else {
          ark.ifft_in_place(&mut coeffs);
          commits.push(self.msm(&coeffs));
          columns.push(write_dense(&mut writer, &coeffs, &mut file_offset)?);
        }
      }
      drop(coeffs);
      drop(matrix);
    }

    let commitment =
      KzgCommitment(vec![G1ProjectiveOf::<C>::normalize_batch(&commits)]);
    let real_header = encode_header(&commitment)?;
    assert_eq!(
      real_header.len(),
      placeholder_header.len(),
      "checkpoint header length changed after commitment"
    );
    writer.flush()?;
    let mut file = writer.into_inner().map_err(|error| {
      ark_serialize::SerializationError::from(error.into_error())
    })?;
    file.seek(SeekFrom::Start(0))?;
    file.write_all(&real_header)?;
    file.flush()?;
    Ok((commitment, columns))
  }

  /// Open a persisted streamed checkpoint without re-reading its coefficient
  /// payload to recompute column digests.
  #[cfg(not(feature = "cuda"))]
  pub(crate) fn open_streamed_checkpoint(
    path: &std::path::Path,
    domain: Radix2Coset<C>,
    commitment: KzgCommitment<C>,
    columns: Vec<StreamedColumn<C>>,
  ) -> std::io::Result<KzgProverData<C>> {
    let height = domain.size();
    let needs_file = columns
      .iter()
      .any(|column| matches!(column, StreamedColumn::Disk { .. }));
    let file = if needs_file {
      Some(Arc::new(std::sync::Mutex::new(DiskFile::persistent(
        std::fs::File::open(path)?,
      ))))
    } else {
      None
    };
    let columns = columns
      .into_iter()
      .map(|column| match column {
        StreamedColumn::Constant(value) => {
          Column::Constant { value, len: height }
        },
        StreamedColumn::Disk { offset, digest } => Column::from_disk(
          Arc::clone(file.as_ref().expect("file opened for disk columns")),
          offset,
          height,
          digest,
        ),
      })
      .collect();
    Ok(KzgProverData {
      commitment,
      matrices: vec![CommittedMatrix::new(domain, columns)],
    })
  }

  /// Stream-commit `matrix` one column at a time on CPU and spill non-constant
  /// coefficient columns to a temporary disk file in `spill_dir`.
  #[cfg(not(feature = "cuda"))]
  pub(crate) fn commit_matrix_spilled(
    &self,
    domain: Radix2Coset<C>,
    matrix: RowMajorMatrix<CurveScalar<C>>,
    spill_dir: &std::path::Path,
  ) -> std::io::Result<(KzgCommitment<C>, KzgProverData<C>)> {
    self.commit_matrix_spilled_with_options(
      domain,
      matrix,
      spill_dir,
      super::coefficients::CHUNK,
      false,
    )
  }

  #[cfg(not(feature = "cuda"))]
  #[allow(dead_code)]
  pub(super) fn commit_matrix_spilled_with_chunk(
    &self,
    domain: Radix2Coset<C>,
    matrix: RowMajorMatrix<CurveScalar<C>>,
    spill_dir: &std::path::Path,
    chunk: usize,
  ) -> std::io::Result<(KzgCommitment<C>, KzgProverData<C>)> {
    self.commit_matrix_spilled_with_options(
      domain, matrix, spill_dir, chunk, false,
    )
  }

  /// Like [`Self::commit_matrix_spilled`], optionally spilling the input
  /// natural-domain evaluations to a temporary raw-Montgomery file when
  /// `retain_evaluations` is true and at least one column is non-constant, so
  /// lookup construction can reload them without redundant forward FFTs.
  #[cfg(not(feature = "cuda"))]
  pub(crate) fn commit_matrix_spilled_with_evaluations(
    &self,
    domain: Radix2Coset<C>,
    matrix: RowMajorMatrix<CurveScalar<C>>,
    spill_dir: &std::path::Path,
    retain_evaluations: bool,
  ) -> std::io::Result<(KzgCommitment<C>, KzgProverData<C>)> {
    self.commit_matrix_spilled_with_options(
      domain,
      matrix,
      spill_dir,
      super::coefficients::CHUNK,
      retain_evaluations,
    )
  }

  #[cfg(not(feature = "cuda"))]
  fn commit_matrix_spilled_with_options(
    &self,
    domain: Radix2Coset<C>,
    matrix: RowMajorMatrix<CurveScalar<C>>,
    spill_dir: &std::path::Path,
    chunk: usize,
    retain_evaluations: bool,
  ) -> std::io::Result<(KzgCommitment<C>, KzgProverData<C>)> {
    assert_eq!(matrix.height(), domain.size(), "matrix height != domain size");
    let width = matrix.width();
    let height = domain.size();
    let ark = Self::ark_domain(domain);
    let mut commits = Vec::with_capacity(width);
    let mut columns = Vec::with_capacity(width);
    let mut spill_file: Option<Arc<std::sync::Mutex<DiskFile>>> = None;
    let mut spill_offset = 0u64;
    let mut spilled_evaluations: Option<SpilledEvaluations<C>> = None;

    let mut spill_column = |coeffs: &[C::Fr]| -> std::io::Result<Column<C>> {
      if coeffs.iter().skip(1).all(Zero::is_zero) {
        return Ok(Column::Constant {
          value: coeffs.first().copied().unwrap_or_default(),
          len: coeffs.len(),
        });
      }
      let file = match &spill_file {
        Some(file) => file,
        None => {
          let created =
            Arc::new(std::sync::Mutex::new(DiskFile::temporary(spill_dir)?));
          spill_file.insert(created)
        },
      };
      Column::spill_to_disk_with_chunk(file, &mut spill_offset, coeffs, chunk)
    };

    if width == 1 {
      let first = matrix.values[0].0;
      if matrix.values.par_iter().all(|v| v.0 == first) {
        drop(matrix);
        let col = Column::Constant { value: first, len: height };
        commits.push(self.commit_column(&col));
        columns.push(col);
      } else {
        if retain_evaluations {
          spilled_evaluations =
            Some(SpilledEvaluations::spill(spill_dir, domain, &matrix)?);
        }
        let mut coeffs: Vec<C::Fr> =
          matrix.values.into_iter().map(|v| v.0).collect();
        ark.ifft_in_place(&mut coeffs);
        commits.push(self.msm(&coeffs));
        columns.push(spill_column(&coeffs)?);
      }
    } else {
      let mut coeffs = Vec::new();
      let mut any_non_constant = false;
      for column in 0..width {
        if let Some(value) =
          Self::extract_column_into(&matrix, column, &mut coeffs)
        {
          let col = Column::Constant { value, len: height };
          commits.push(self.commit_column(&col));
          columns.push(col);
        } else {
          any_non_constant = true;
          ark.ifft_in_place(&mut coeffs);
          commits.push(self.msm(&coeffs));
          columns.push(spill_column(&coeffs)?);
        }
      }
      drop(coeffs);
      if retain_evaluations && any_non_constant {
        spilled_evaluations =
          Some(SpilledEvaluations::spill(spill_dir, domain, &matrix)?);
      }
      drop(matrix);
    }

    let commitment =
      KzgCommitment(vec![G1ProjectiveOf::<C>::normalize_batch(&commits)]);
    let mut committed = CommittedMatrix::new(domain, columns);
    committed.spilled_evaluations = std::sync::Mutex::new(spilled_evaluations);
    let data = KzgProverData {
      commitment: commitment.clone(),
      matrices: vec![committed],
    };
    Ok((commitment, data))
  }

  /// Interpolate, slice, commit and spill a quotient polynomial to a temporary
  /// disk file in `spill_dir`, dropping the resident coefficients immediately.
  #[cfg(not(feature = "cuda"))]
  #[allow(dead_code)]
  pub(super) fn commit_quotient_spilled_with_chunk(
    &self,
    quotient_domain: Radix2Coset<C>,
    evaluations: RowMajorMatrix<CurveScalar<C>>,
    quotient_degree: usize,
    spill_dir: &std::path::Path,
    chunk: usize,
  ) -> std::io::Result<(KzgCommitment<C>, KzgProverData<C>)> {
    let big = quotient_domain.size();
    debug_assert_eq!(big % quotient_degree, 0);
    let n = big / quotient_degree;
    let coefficient_columns =
      Self::interpolate_columns(quotient_domain, evaluations).columns;
    let mut spill_file: Option<Arc<std::sync::Mutex<DiskFile>>> = None;
    let mut spill_offset = 0u64;
    let mut commits =
      Vec::with_capacity(quotient_degree * coefficient_columns.len());
    let mut columns =
      Vec::with_capacity(quotient_degree * coefficient_columns.len());
    for k in 0..quotient_degree {
      let range = k * n..(k + 1) * n;
      for c in &coefficient_columns {
        let sliced = c.slice(range.clone());
        match &sliced {
          Column::Constant { .. } => {
            commits.push(self.commit_column(&sliced));
            columns.push(sliced);
          },
          Column::Resident { values, range } => {
            let coeffs = &values[range.clone()];
            commits.push(self.msm(coeffs));
            if coeffs.iter().skip(1).all(Zero::is_zero) {
              columns.push(Column::Constant {
                value: coeffs.first().copied().unwrap_or_default(),
                len: coeffs.len(),
              });
            } else {
              let file = match &spill_file {
                Some(file) => file,
                None => {
                  let created = Arc::new(std::sync::Mutex::new(
                    DiskFile::temporary(spill_dir)?,
                  ));
                  spill_file.insert(created)
                },
              };
              columns.push(Column::spill_to_disk_with_chunk(
                file,
                &mut spill_offset,
                coeffs,
                chunk,
              )?);
            }
          },
          Column::Disk { .. } => {
            unreachable!("quotient slicing precedes spilling")
          },
        }
      }
    }
    drop(coefficient_columns);
    let commitment =
      KzgCommitment(vec![G1ProjectiveOf::<C>::normalize_batch(&commits)]);
    let matrix = CommittedMatrix::new(
      Radix2Coset {
        log_size: p3_util::log2_strict_usize(n),
        shift: multi_stark::traits::Algebra::<CurveScalar<C>>::ONE,
      },
      columns,
    );
    let data =
      KzgProverData { commitment: commitment.clone(), matrices: vec![matrix] };
    Ok((commitment, data))
  }

  /// Interpolate each column of `matrix` over `domain`.
  pub(super) fn interpolate_columns(
    domain: Radix2Coset<C>,
    matrix: RowMajorMatrix<CurveScalar<C>>,
  ) -> CommittedMatrix<C> {
    assert_eq!(matrix.height(), domain.size(), "matrix height != domain size");
    let width = matrix.width();
    let height = domain.size();
    let mut constants = vec![false; width];
    let mut output: Vec<Option<Column<C>>> = (0..width).map(|_| None).collect();
    let mut active = Vec::new();
    let mut inputs = Vec::new();
    if width == 1 {
      let first = matrix.values[0].0;
      if matrix.values.par_iter().all(|v| v.0 == first) {
        drop(matrix);
        constants[0] = true;
        output[0] = Some(Column::Constant { value: first, len: height });
      } else {
        // The consuming map reuses the transparent scalar vector's allocation.
        active.push(0);
        inputs.push(matrix.values.into_iter().map(|v| v.0).collect());
      }
    } else {
      let extracted: Vec<Result<Vec<C::Fr>, C::Fr>> = (0..width)
        .into_par_iter()
        .map(|column| {
          let first = matrix.values[column].0;
          let is_constant = (1..height)
            .all(|row| matrix.values[row * width + column].0 == first);
          if is_constant {
            Err(first)
          } else {
            Ok(generate_buffer(height, |row| {
              matrix.values[row * width + column].0
            }))
          }
        })
        .collect();
      drop(matrix);
      for (i, col) in extracted.into_iter().enumerate() {
        match col {
          Err(value) => {
            constants[i] = true;
            output[i] = Some(Column::Constant { value, len: height });
          },
          Ok(values) => {
            active.push(i);
            inputs.push(values);
          },
        }
      }
    }
    #[cfg(feature = "cuda")]
    let resident = std::sync::OnceLock::new();
    #[cfg(feature = "cuda")]
    let interpolated = if domain.size() >= 1 << 10 {
      let (columns, residents) =
        cuda::interpolate_columns::<C>(inputs, domain.log_size, domain.shift.0);
      let mut all_residents = vec![None; width];
      for (&i, resident) in active.iter().zip(residents) {
        all_residents[i] = resident;
      }
      let _ = resident.set(all_residents);
      columns
    } else {
      tracing::debug!(
        curve = C::NAME,
        rows = domain.size(),
        columns = inputs.len(),
        reason = "small domain",
        "KZG interpolation using CPU FFT"
      );
      Self::interpolate_on_host(domain, inputs)
    };
    #[cfg(not(feature = "cuda"))]
    let interpolated = Self::interpolate_on_host(domain, inputs);
    for (i, column) in active.into_iter().zip(interpolated) {
      output[i] = Some(Column::from(column));
    }
    CommittedMatrix {
      domain,
      columns: output
        .into_iter()
        .map(|column| column.expect("every column is interpolated"))
        .collect(),
      constants,
      #[cfg(not(feature = "cuda"))]
      spilled_evaluations: std::sync::Mutex::new(None),
      #[cfg(feature = "cuda")]
      resident,
    }
  }

  fn interpolate_on_host(
    domain: Radix2Coset<C>,
    mut columns: Vec<Vec<C::Fr>>,
  ) -> Vec<Vec<C::Fr>> {
    let ark = Self::ark_domain(domain);
    // Large arkworks IFFTs already parallelize across Rayon threads; running
    // one column at a time bounds peak scratch memory and improves cache reuse.
    if domain.size() >= 1 << 16 {
      for col in &mut columns {
        ark.ifft_in_place(col);
      }
    } else {
      columns.par_iter_mut().for_each(|col| {
        ark.ifft_in_place(col);
      });
    }
    columns
  }
}

/// Column metadata recorded while streaming a matrix into a checkpoint file.
#[cfg(not(feature = "cuda"))]
pub(crate) enum StreamedColumn<C: KzgCurve = Bn254> {
  Constant(C::Fr),
  Disk { offset: u64, digest: blake3::Hash },
}

impl<C: KzgCurve> Pcs for KzgPcs<C> {
  type F = CurveScalar<C>;
  type Challenge = CurveScalar<C>;
  type Domain = Radix2Coset<C>;
  type Challenger = KzgTranscript<C>;
  type Commitment = KzgCommitment<C>;
  type ProverData = KzgProverData<C>;
  type Proof = KzgProof<C>;
  type Error = KzgError;
  type Evaluations<'a> = RowMajorMatrix<CurveScalar<C>>;

  fn natural_domain_for_degree(&self, degree: usize) -> Radix2Coset<C> {
    Radix2Coset {
      log_size: p3_util::log2_strict_usize(degree),
      shift: multi_stark::traits::Algebra::<CurveScalar<C>>::ONE,
    }
  }

  fn max_quotient_degree(&self) -> usize {
    self.max_quotient_degree
  }

  fn commit(
    &self,
    evaluations: Vec<(Radix2Coset<C>, RowMajorMatrix<CurveScalar<C>>)>,
  ) -> (KzgCommitment<C>, KzgProverData<C>) {
    let matrices: Vec<CommittedMatrix<C>> = evaluations
      .into_iter()
      .map(|(domain, matrix)| Self::interpolate_columns(domain, matrix))
      .collect();
    let commitment = KzgCommitment(
      matrices.iter().map(|m| self.commit_matrix_columns(m)).collect(),
    );
    (commitment.clone(), KzgProverData { matrices, commitment })
  }

  fn commit_quotient(
    &self,
    quotients: Vec<(Radix2Coset<C>, RowMajorMatrix<CurveScalar<C>>, usize)>,
  ) -> (KzgCommitment<C>, KzgProverData<C>) {
    let matrices: Vec<CommittedMatrix<C>> = quotients
      .into_iter()
      .map(|(quotient_domain, evaluations, quotient_degree)| {
        Self::interpolate_quotient(
          quotient_domain,
          evaluations,
          quotient_degree,
        )
      })
      .collect();
    let commitment = KzgCommitment(
      matrices.iter().map(|m| self.commit_matrix_columns(m)).collect(),
    );
    (commitment.clone(), KzgProverData { matrices, commitment })
  }

  fn get_evaluations_on_domain(
    &self,
    data: &KzgProverData<C>,
    idx: usize,
    domain: Radix2Coset<C>,
  ) -> RowMajorMatrix<CurveScalar<C>> {
    self.evaluate_columns(
      data,
      idx,
      domain,
      &(0..data.matrices[idx].columns.len()).collect::<Vec<_>>(),
    )
  }

  fn open(
    &self,
    rounds: OpeningRounds<'_, KzgProverData<C>, CurveScalar<C>>,
    challenger: &mut KzgTranscript<C>,
  ) -> (OpenedValues<CurveScalar<C>>, KzgProof<C>) {
    for (data, _) in &rounds {
      challenger.observe_commitment(data.commitment.clone());
      for m in &data.matrices {
        challenger.observe_canonical(&(m.domain.log_size as u64));
      }
    }
    // Pass 1: evaluate everything, observing values in traversal
    // order, and batch (polynomial, value) pairs per distinct point.
    struct PointBatch<'a, C: KzgCurve> {
      z: C::Fr,
      entries: Vec<(&'a Column<C>, C::Fr)>,
    }
    let mut batches: Vec<PointBatch<'_, C>> = Vec::new();
    let mut opened: OpenedValues<CurveScalar<C>> = Vec::new();
    for (data, points_per_matrix) in &rounds {
      debug_assert_eq!(data.matrices.len(), points_per_matrix.len());
      let mut round_values = Vec::new();
      for (index, (matrix, points)) in
        data.matrices.iter().zip(points_per_matrix).enumerate()
      {
        if !points.is_empty() {
          assert_eq!(
            matrix.columns.len(),
            data.commitment.0[index].len(),
            "missing polynomial data for requested openings"
          );
        }
        let mut matrix_values =
          vec![
            vec![CurveScalar(C::FR_ZERO); matrix.columns.len()];
            points.len()
          ];
        if !points.is_empty() {
          let zs: Vec<_> = points.iter().map(|z| z.0).collect();
          let constants = matrix.constant_columns();
          #[cfg(feature = "cuda")]
          let views = matrix.cuda_columns();
          #[cfg(feature = "cuda")]
          let residents = views.as_ref().map(|_| matrix.resident_columns());
          for (column_index, column) in matrix.columns.iter().enumerate() {
            if constants[column_index] {
              let value = match column {
                Column::Constant { value, .. } => *value,
                _ => column
                  .resident()
                  .and_then(|values| values.first().copied())
                  .unwrap_or(C::FR_ZERO),
              };
              for row in &mut matrix_values {
                row[column_index] = CurveScalar(value);
              }
              continue;
            }
            #[cfg(feature = "cuda")]
            if let Some(views) = &views
              && views[column_index].0.len() >= 1 << 12
            {
              let values = cuda::evaluate_resident::<C>(
                views[column_index].0,
                residents.and_then(|r| r[column_index].as_deref()),
                &zs,
              );
              for (row, value) in matrix_values.iter_mut().zip(values) {
                row[column_index] = CurveScalar(value);
              }
              continue;
            }
            #[cfg(feature = "cuda")]
            tracing::debug!(
              curve = C::NAME,
              column = column_index,
              elements = column.len(),
              reason = "small or disk-backed polynomial",
              "KZG opening using CPU evaluation"
            );
            // Decode a disk column once for all requested points.
            column
              .visit(|start, chunk| {
                for (&z, row) in zs.iter().zip(&mut matrix_values) {
                  row[column_index].0 +=
                    eval_poly::<C>(chunk, z) * z.pow([start as u64]);
                }
              })
              .expect("coefficient checkpoint");
          }
        }
        for (&z, row) in points.iter().zip(&matrix_values) {
          for &value in row {
            challenger.observe_challenge(value);
          }
          let batch = match batches.iter().position(|b| b.z == z.0) {
            Some(i) => &mut batches[i],
            None => {
              batches.push(PointBatch { z: z.0, entries: Vec::new() });
              batches.last_mut().expect("just pushed")
            },
          };
          for (column, value) in matrix.columns.iter().zip(row) {
            batch.entries.push((column, value.0));
          }
        }
        round_values.push(matrix_values);
      }
      opened.push(round_values);
    }

    let v = challenger.sample_challenge().0;

    // Fold two points per scan, bounding scratch to two polynomials.
    let mut witnesses = Vec::with_capacity(batches.len());
    for group in batches.chunks(2) {
      let mut combined: Vec<Vec<C::Fr>> = group
        .iter()
        .map(|batch| {
          vec![
            C::FR_ZERO;
            batch.entries.iter().map(|(c, _)| c.len()).max().unwrap_or(0)
          ]
        })
        .collect();
      let mut columns: Vec<(&Column<C>, [C::Fr; 2])> = Vec::new();
      let mut indices = std::collections::HashMap::new();
      for (batch_index, batch) in group.iter().enumerate() {
        let mut power = C::FR_ONE;
        for (column, _) in &batch.entries {
          let index =
            *indices.entry(std::ptr::from_ref(*column)).or_insert_with(|| {
              columns.push((column, [C::FR_ZERO; 2]));
              columns.len() - 1
            });
          columns[index].1[batch_index] += power;
          power *= v;
        }
      }
      for (column, weights) in columns {
        if let Column::Constant { value, .. } = column {
          for (dst, weight) in combined.iter_mut().zip(weights) {
            if let Some(first) = dst.first_mut() {
              *first += *value * weight;
            }
          }
          continue;
        }
        column
          .visit(|start, chunk| {
            if let [a, b] = combined.as_mut_slice()
              && weights[0] != C::FR_ZERO
              && weights[1] != C::FR_ZERO
            {
              a[start..start + chunk.len()]
                .par_iter_mut()
                .zip(&mut b[start..start + chunk.len()])
                .zip(chunk)
                .for_each(|((a, b), c)| {
                  *a += weights[0] * c;
                  *b += weights[1] * c;
                });
            } else {
              for (dst, weight) in combined.iter_mut().zip(weights) {
                if weight != C::FR_ZERO {
                  dst[start..start + chunk.len()]
                    .par_iter_mut()
                    .zip(chunk)
                    .for_each(|(a, c)| *a += weight * c);
                }
              }
            }
          })
          .expect("coefficient checkpoint");
      }
      for (batch, values) in group.iter().zip(combined) {
        // Subtracting claimed values only changes the remainder.
        witnesses.push(self.witness(values, batch.z));
      }
    }
    let witnesses = G1ProjectiveOf::<C>::normalize_batch(&witnesses);
    for w in &witnesses {
      challenger.observe_canonical(w);
    }
    // Mirror the verifier's cross-point batching sample to keep the
    // transcripts in lockstep (the prover has no use for r).
    let _r = challenger.sample_challenge();

    (opened, KzgProof(witnesses))
  }

  fn verify(
    &self,
    rounds: VerifyRounds<KzgCommitment<C>, Radix2Coset<C>, CurveScalar<C>>,
    proof: &KzgProof<C>,
    challenger: &mut KzgTranscript<C>,
  ) -> Result<(), KzgError> {
    // Serde-decoded points were validated; in-memory callers may not be.
    let points: Vec<_> = rounds
      .iter()
      .flat_map(|(commitment, _)| commitment.0.iter().flatten())
      .chain(&proof.0)
      .collect();
    if points.par_iter().any(|point| {
      !point.is_on_curve() || !point.is_in_correct_subgroup_assuming_on_curve()
    }) {
      return Err(KzgError::InvalidPoint);
    }
    for (commitment, matrices) in &rounds {
      challenger.observe_commitment(commitment.clone());
      for (domain, _) in matrices {
        challenger.observe_canonical(&(domain.log_size as u64));
      }
    }
    for (commitment, matrices) in &rounds {
      if commitment.0.len() != matrices.len()
        || matrices.iter().any(|(domain, _)| {
          domain.log_size > self.verifier.max_trace_len().ilog2() as usize
        })
      {
        return Err(KzgError::ShapeMismatch);
      }
    }
    // Mirror `open`'s traversal exactly: observe claimed values and
    // batch (commitment, value) pairs per distinct point.
    struct PointBatch<C: KzgCurve> {
      z: C::Fr,
      commitments: Vec<G1AffineOf<C>>,
      values: Vec<C::Fr>,
    }
    let mut batches: Vec<PointBatch<C>> = Vec::new();
    for (commitment, matrices) in &rounds {
      if commitment.0.len() != matrices.len() {
        return Err(KzgError::ShapeMismatch);
      }
      for (column_commits, (_domain, openings)) in
        commitment.0.iter().zip(matrices)
      {
        for (z, values) in openings {
          if values.len() != column_commits.len() {
            return Err(KzgError::ShapeMismatch);
          }
          for &value in values {
            challenger.observe_challenge(value);
          }
          let batch = match batches.iter().position(|b| b.z == z.0) {
            Some(i) => &mut batches[i],
            None => {
              batches.push(PointBatch {
                z: z.0,
                commitments: Vec::new(),
                values: Vec::new(),
              });
              batches.last_mut().expect("just pushed")
            },
          };
          batch.commitments.extend_from_slice(column_commits);
          batch.values.extend(values.iter().map(|value| value.0));
        }
      }
    }
    if proof.0.len() != batches.len() {
      return Err(KzgError::ShapeMismatch);
    }

    let v = challenger.sample_challenge().0;
    for w in &proof.0 {
      challenger.observe_canonical(w);
    }
    let r = challenger.sample_challenge().0;

    // Per point z (with witness W and v-powers u):
    //   e(C_z − y_z·G + z·W, H) = e(W, τH)
    // where C_z = Σ uᵢ·Cᵢ and y_z = Σ uᵢ·yᵢ. Cross-batched over
    // points with powers of r into one 2-pairing product.
    let g = G1ProjectiveOf::<C>::from(self.verifier.g1[0]);
    let mut lhs = G1ProjectiveOf::<C>::zero();
    let mut rhs = G1ProjectiveOf::<C>::zero();
    let mut r_power = C::FR_ONE;
    for (batch, &witness) in batches.iter().zip(&proof.0) {
      let mut v_powers = Vec::with_capacity(batch.values.len());
      let mut power = C::FR_ONE;
      let mut y = C::FR_ZERO;
      for &value in &batch.values {
        v_powers.push(power);
        y += power * value;
        power *= v;
      }
      let c = G1ProjectiveOf::<C>::msm(&batch.commitments, &v_powers)
        .expect("equal lengths");
      lhs += (c - g * y + witness * batch.z) * r_power;
      rhs += witness * r_power;
      r_power *= r;
    }
    let check = C::PairingCurve::multi_pairing(
      [lhs.into_affine(), (-rhs).into_affine()],
      [self.verifier.g2, self.verifier.tau_g2],
    );
    if check.is_zero() { Ok(()) } else { Err(KzgError::PairingCheckFailed) }
  }
}

impl<C: KzgCurve> KzgPcs<C> {
  /// The witness commitment `[(p(X) − p(z)) / (X − z)]·G` of one folded
  /// opening polynomial.
  pub(super) fn witness(
    &self,
    combined: Vec<C::Fr>,
    z: C::Fr,
  ) -> G1ProjectiveOf<C> {
    #[cfg(feature = "cuda")]
    if combined.len() >= 1 << 16 {
      let witness = if cuda::srs_residency::enabled() {
        cuda::srs_residency::single_device_opening::<C>(
          self.srs_owner(),
          &combined,
          z,
        )
      } else {
        cuda::single_device_opening::<C>(
          &self.prover_srs().g1[..combined.len() - 1],
          &combined,
          z,
        )
      };
      if let Some(witness) = witness {
        return witness;
      }
    }
    self.msm(&divide_by_linear::<C>(combined, z))
  }
}

const POLYNOMIAL_BLOCK: usize = 1 << 12;

fn eval_poly_serial<C: KzgCurve>(coeffs: &[C::Fr], z: C::Fr) -> C::Fr {
  coeffs.iter().rev().fold(C::FR_ZERO, |acc, c| acc * z + c)
}

/// Evaluate coefficient blocks independently, then fold at z^block_size.
pub(super) fn eval_poly<C: KzgCurve>(coeffs: &[C::Fr], z: C::Fr) -> C::Fr {
  if coeffs.len() <= POLYNOMIAL_BLOCK {
    return eval_poly_serial::<C>(coeffs, z);
  }
  let blocks: Vec<_> = coeffs
    .par_chunks(POLYNOMIAL_BLOCK)
    .map(|block| eval_poly_serial::<C>(block, z))
    .collect();
  eval_poly_serial::<C>(&blocks, z.pow([POLYNOMIAL_BLOCK as u64]))
}

/// `⌊p / (X − z)⌋`, on the device for large polynomials.
fn divide_by_linear<C: KzgCurve>(p: Vec<C::Fr>, z: C::Fr) -> Vec<C::Fr> {
  if p.len() <= 1 {
    return Vec::new();
  }
  #[cfg(feature = "cuda")]
  if p.len() >= 1 << 16 {
    return cuda::divide::<C>(&p, z);
  }
  #[cfg(feature = "cuda")]
  tracing::debug!(
    curve = C::NAME,
    elements = p.len(),
    reason = "small polynomial",
    "KZG opening using CPU division"
  );
  divide_by_linear_host::<C>(p, z)
}

/// Synthetic division on the host, reusing the input allocation. Block
/// boundary carries are suffix evaluations; the second pass runs
/// independently in each block. Callers dividing many polynomials use it
/// directly to avoid one device round trip per polynomial.
pub(super) fn divide_by_linear_host<C: KzgCurve>(
  mut p: Vec<C::Fr>,
  z: C::Fr,
) -> Vec<C::Fr> {
  if p.len() <= 1 {
    return Vec::new();
  }
  let n = p.len() - 1;
  if n <= POLYNOMIAL_BLOCK {
    let mut carry = C::FR_ZERO;
    for value in p[1..].iter_mut().rev() {
      carry = *value + z * carry;
      *value = carry;
    }
  } else {
    let mut boundaries: Vec<_> = p[1..]
      .par_chunks(POLYNOMIAL_BLOCK)
      .map(|block| eval_poly_serial::<C>(block, z))
      .collect();
    let full_power = z.pow([POLYNOMIAL_BLOCK as u64]);
    let mut carry = C::FR_ZERO;
    for (i, boundary) in boundaries.iter_mut().enumerate().rev() {
      let size = (n - i * POLYNOMIAL_BLOCK).min(POLYNOMIAL_BLOCK);
      let power = if size == POLYNOMIAL_BLOCK {
        full_power
      } else {
        z.pow([size as u64])
      };
      let local = *boundary;
      *boundary = carry;
      carry = local + power * carry;
    }
    p[1..].par_chunks_mut(POLYNOMIAL_BLOCK).zip(boundaries).for_each(
      |(block, mut carry)| {
        for value in block.iter_mut().rev() {
          carry = *value + z * carry;
          *value = carry;
        }
      },
    );
  }
  p.copy_within(1.., 0);
  p.truncate(n);
  p
}

/// Parallel first-touch initialization of a large field buffer.
pub(super) fn generate_buffer<T: Copy + Send>(
  len: usize,
  value: impl Fn(usize) -> T + Sync,
) -> Vec<T> {
  let mut output: Vec<T> = Vec::with_capacity(len);
  output.spare_capacity_mut()[..len]
    .par_chunks_mut(1 << 14)
    .enumerate()
    .for_each(|(tile, chunk)| {
      for (offset, slot) in chunk.iter_mut().enumerate() {
        slot.write(value((tile << 14) + offset));
      }
    });
  // Every slot is initialized after the parallel iterator joins. T is Copy,
  // so a panic during initialization cannot leak partially constructed values.
  unsafe { output.set_len(len) };
  output
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::kzg::curve::Bls12381;
  use multi_stark::traits::Algebra;
  use multi_stark::traits::Field;

  fn check_pcs_suite<C: KzgCurve>() {
    if let Some(max_domain) =
      1usize.checked_shl(u32::try_from(CurveScalar::<C>::TWO_ADICITY).unwrap())
    {
      let anchors =
        Srs::<C>::unsafe_dev_setup_prefix(2, max_domain - 1, b"domain-cap");
      let params = super::super::VerifierParams::<C>::with_max_trace_len(
        &anchors,
        max_domain / 2,
      );
      KzgPcs::<C>::verifier_only(params.clone(), 2);
      for degree in [0, 3, 4] {
        assert!(
          std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            KzgPcs::<C>::verifier_only(params.clone(), degree)
          }))
          .is_err()
        );
      }
      let params = super::super::VerifierParams::<C>::with_max_trace_len(
        &anchors, max_domain,
      );
      KzgPcs::<C>::verifier_only(params.clone(), 1);
      assert!(
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
          KzgPcs::<C>::verifier_only(params.clone(), 2)
        }))
        .is_err()
      );
      assert!(
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
          KzgPcs::<C>::with_max_trace_len(Arc::new(anchors), max_domain, 2)
        }))
        .is_err()
      );
    }

    let pcs = KzgPcs::<C>::new(
      Arc::new(Srs::<C>::unsafe_dev_setup(4, b"checkpoint-magic")),
      2,
    );
    let domain = pcs.natural_domain_for_degree(4);
    let (commitment, data) = pcs.commit(vec![(
      domain,
      RowMajorMatrix::new_col(vec![CurveScalar::<C>::ONE; 4]),
    )]);
    let mut bytes = Vec::new();
    data.write_checkpoint(&mut bytes).unwrap();
    let decoded =
      KzgProverData::<C>::read_checkpoint(bytes.as_slice()).unwrap();
    assert_eq!(decoded.commitment, commitment);

    let mut wrong_magic = bytes.clone();
    wrong_magic[7] ^= 1;
    assert!(
      KzgProverData::<C>::read_checkpoint(wrong_magic.as_slice()).is_err()
    );

    let log_offset = 8 + commitment.0.compressed_size() + 8;
    bytes[log_offset..log_offset + 8].copy_from_slice(
      &(CurveScalar::<C>::TWO_ADICITY as u64 + 1).to_le_bytes(),
    );
    assert!(KzgProverData::<C>::read_checkpoint(bytes.as_slice()).is_err());

    assert!(decode_commitment::<C>(&[255; 8]).is_err());
    let mut nested = 1u64.to_le_bytes().to_vec();
    nested.extend([255; 8]);
    assert!(decode_commitment::<C>(&nested).is_err());
    let commitment =
      KzgCommitment::<C>(vec![vec![G1AffineOf::<C>::default()], vec![]]);
    let mut bytes = Vec::new();
    commitment.0.serialize_compressed(&mut bytes).unwrap();
    assert_eq!(decode_commitment::<C>(&bytes).unwrap(), commitment);
    for end in 0..bytes.len() {
      assert!(decode_commitment::<C>(&bytes[..end]).is_err());
    }
    bytes.push(0);
    assert!(decode_commitment::<C>(&bytes).is_err());

    let config = bincode::config::standard();
    assert!(
      bincode::serde::encode_to_vec(KzgProof::<C>(vec![]), config).is_err()
    );
    assert!(
      bincode::serde::decode_from_slice::<KzgProof<C>, _>(&[255; 8], config)
        .is_err()
    );

    let pcs = KzgPcs::<C>::new(
      Arc::new(Srs::<C>::unsafe_dev_setup(32, b"constant-columns")),
      2,
    );
    let domain = pcs.natural_domain_for_degree(16);
    let (commitment, compact) = pcs.commit(vec![(
      domain,
      RowMajorMatrix::new(
        (0..16)
          .flat_map(|_| {
            [
              CurveScalar::<C>::ZERO,
              CurveScalar::<C>::from_u8(7),
              CurveScalar::<C>::ONE,
            ]
          })
          .collect(),
        3,
      ),
    )]);
    assert!(
      compact.matrices[0]
        .columns
        .iter()
        .all(|c| matches!(c, Column::Constant { .. }))
    );
    let z = CurveScalar::<C>::from_u8(19);
    let (values, proof) = pcs.open(
      vec![(&compact, vec![vec![z]])],
      &mut KzgTranscript::<C>::default(),
    );
    let verifier = KzgPcs::<C>::verifier_only(pcs.verifier.clone(), 2);
    verifier
      .verify(
        vec![(commitment, vec![(domain, vec![(z, values[0][0][0].clone())])])],
        &proof,
        &mut KzgTranscript::<C>::default(),
      )
      .unwrap();

    let pcs = KzgPcs::<C>::new(
      Arc::new(Srs::<C>::unsafe_dev_setup(256, b"chunked-msm")),
      4,
    );
    let mut value = C::Fr::from(17u64);
    let coefficients: Vec<_> = (0..(9 * 16 + 3))
      .map(|_| {
        value = value.square() + C::FR_ONE;
        value
      })
      .collect();
    let expected = G1ProjectiveOf::<C>::msm(
      &pcs.prover_srs().g1[..coefficients.len()],
      &coefficients,
    )
    .unwrap();
    assert_eq!(pcs.msm_with_chunk(&coefficients, 16), expected);
    assert_eq!(pcs.msm(&coefficients), expected);
  }

  #[test]
  fn kzg_pcs_suite_passes_for_both_curves() {
    check_pcs_suite::<Bn254>();
    check_pcs_suite::<Bls12381>();
  }

  #[test]
  fn disk_coefficients_match_resident_and_detect_changes() {
    use crate::kzg::field::Scalar;
    use std::io::{Seek, SeekFrom, Write};
    let directory = crate::test_support::TempDir::new("kzg-columns");
    let path = directory.join("columns.bin");
    let mut file = std::fs::File::create_new(&path).unwrap();
    let pcs = KzgPcs::<Bn254>::new(
      Arc::new(Srs::<Bn254>::unsafe_dev_setup(1 << 9, b"disk-columns")),
      2,
    );
    let domain = pcs.natural_domain_for_degree(1 << 9);
    let (_, resident) = pcs.commit(vec![(
      domain,
      RowMajorMatrix::new_col(
        (0..domain.size()).map(Scalar::from_usize).collect(),
      ),
    )]);
    let mut bytes = Vec::new();
    resident.write_checkpoint(&mut bytes).unwrap();
    file.write_all(&bytes).unwrap();
    let disk =
      KzgProverData::<Bn254>::read_checkpoint_file_with_chunk(&path, 1 << 7)
        .unwrap();
    let mut roundtrip = Vec::new();
    disk.write_checkpoint(&mut roundtrip).unwrap();
    assert_eq!(bytes, roundtrip);
    for shift in [Scalar::ONE, Scalar::from_u8(7)] {
      let coset = Radix2Coset { shift, ..domain };
      assert_eq!(
        pcs.get_evaluations_on_domain(&disk, 0, coset),
        pcs.get_evaluations_on_domain(&resident, 0, coset)
      );
    }
    let points = vec![vec![
      Scalar::from_u8(13),
      Scalar::from_u8(19),
      Scalar::from_u8(13),
      Scalar::from_u8(23),
      Scalar::from_u8(29),
    ]];
    let expected = pcs.open(
      vec![(&resident, points.clone())],
      &mut KzgTranscript::<Bn254>::default(),
    );
    let actual = pcs.open(
      vec![(&disk, points.clone())],
      &mut KzgTranscript::<Bn254>::default(),
    );
    pcs
      .verify(
        vec![(
          resident.commitment.clone(),
          vec![(
            domain,
            points[0].iter().copied().zip(actual.0[0][0].clone()).collect(),
          )],
        )],
        &actual.1,
        &mut KzgTranscript::<Bn254>::default(),
      )
      .unwrap();
    assert_eq!(actual, expected);
    file.seek(SeekFrom::End(-32)).unwrap();
    file.write_all(&[0; 32]).unwrap();
    assert!(disk.matrices[0].columns[0].load().is_err());
    file.set_len(0).unwrap();
    assert!(disk.matrices[0].columns[0].load().is_err());
    assert!(KzgProverData::<Bn254>::read_checkpoint_file(&path).is_err());
  }

  #[test]
  fn blocked_opening_arithmetic_matches_horner_and_synthetic_division() {
    for n in [
      0,
      1,
      2,
      POLYNOMIAL_BLOCK,
      POLYNOMIAL_BLOCK + 1,
      2 * POLYNOMIAL_BLOCK + 3,
    ] {
      let p: Vec<_> =
        (0..n).map(|i| ark_bls12_381::Fr::from((i * i + 7) as u64)).collect();
      for z in [
        Bls12381::FR_ZERO,
        Bls12381::FR_ONE,
        -Bls12381::FR_ONE,
        ark_bls12_381::Fr::from(13u64),
      ] {
        assert_eq!(
          eval_poly::<Bls12381>(&p, z),
          eval_poly_serial::<Bls12381>(&p, z)
        );
        let mut expected = vec![Bls12381::FR_ZERO; n.saturating_sub(1)];
        let mut carry = Bls12381::FR_ZERO;
        for j in (1..n).rev() {
          carry = p[j] + z * carry;
          expected[j - 1] = carry;
        }
        assert_eq!(divide_by_linear::<Bls12381>(p.clone(), z), expected);
      }
    }
  }
}

#[cfg(test)]
#[path = "pcs/public_degree_tests.rs"]
mod public_degree_tests;
