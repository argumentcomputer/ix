//! Monomial-basis KZG over BLS12-381 implementing [`Pcs`].
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
//! [`Pcs::max_quotient_degree`] bounds this evaluation budget.
//!
//! With the `cuda` feature, resident columns of sufficient size run their
//! transforms, commitments, evaluations and opening divisions on the
//! selected devices, retaining device copies within the residency budget.
//! Only shapes below the device thresholds and disk-backed columns use the
//! host implementation; a device that cannot admit an operation is an error.
//! The proof bytes do not depend on the path taken.

use std::sync::Arc;

use ark_bls12_381::{Bls12_381, Fr, G1Affine, G1Projective};
use ark_ec::{CurveGroup, VariableBaseMSM, pairing::Pairing};
use ark_ff::{AdditiveGroup, Field as ArkField, Zero};
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
use multi_stark::traits::VerifyRounds;

use super::coefficients::Column;
#[cfg(feature = "cuda")]
use super::cuda;
use super::domain::Radix2Coset;
use super::field::Scalar;
use super::srs::Srs;
use super::transcript::Blake3Transcript;

/// Per-matrix column commitments.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KzgCommitment(pub Vec<Vec<G1Affine>>);

/// One opening proof: one witness point per distinct opening point, in
/// transcript (first-appearance) order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KzgProof(pub Vec<G1Affine>);

/// Serde via the arkworks canonical (compressed, validated) encoding.
macro_rules! serde_via_canonical {
  ($t:ty, $inner:ty) => {
    impl Serialize for $t {
      fn serialize<S: Serializer>(
        &self,
        serializer: S,
      ) -> Result<S::Ok, S::Error> {
        let mut bytes = Vec::new();
        self
          .0
          .serialize_compressed(&mut bytes)
          .map_err(serde::ser::Error::custom)?;
        bytes.serialize(serializer)
      }
    }
    impl<'de> Deserialize<'de> for $t {
      fn deserialize<D: Deserializer<'de>>(
        deserializer: D,
      ) -> Result<Self, D::Error> {
        let bytes = Vec::<u8>::deserialize(deserializer)?;
        let mut input = bytes.as_slice();
        let value = <$inner>::deserialize_compressed(&mut input)
          .map_err(serde::de::Error::custom)?;
        if !input.is_empty() {
          return Err(serde::de::Error::custom("trailing proof bytes"));
        }
        Ok(Self(value))
      }
    }
  };
}
serde_via_canonical!(KzgCommitment, Vec<Vec<G1Affine>>);
serde_via_canonical!(KzgProof, Vec<G1Affine>);

/// A committed matrix on the prover side: its domain and each column
/// polynomial in coefficient form (length = domain size).
pub struct CommittedMatrix {
  pub(crate) domain: Radix2Coset,
  columns: Vec<Column>,
  /// Resident columns whose coefficients above the constant term are zero.
  /// Disk-backed columns are never flagged; the flag is an optimization.
  constants: Vec<bool>,
  #[cfg(feature = "cuda")]
  resident: std::sync::OnceLock<Vec<Option<Arc<cuda::ResidentPolynomial>>>>,
}

impl CommittedMatrix {
  /// Evaluation domain represented by the stored coefficient columns.
  pub fn domain(&self) -> Radix2Coset {
    self.domain
  }

  /// Number of polynomial columns.
  pub fn width(&self) -> usize {
    self.columns.len()
  }

  fn new(domain: Radix2Coset, columns: Vec<Column>) -> Self {
    let constants = columns
      .par_iter()
      .map(|column| {
        column
          .resident()
          .is_some_and(|values| values.iter().skip(1).all(Zero::is_zero))
      })
      .collect();
    Self {
      domain,
      columns,
      constants,
      #[cfg(feature = "cuda")]
      resident: Default::default(),
    }
  }

  fn constant_columns(&self) -> &[bool] {
    &self.constants
  }

  /// Every column as a host slice with its current device residency and
  /// constant flag, or `None` when a column is disk-backed. Residency is
  /// reported, not created; see [`Self::resident_columns`].
  #[cfg(feature = "cuda")]
  pub(super) fn cuda_columns(
    &self,
  ) -> Option<Vec<(&[Fr], Option<&cuda::ResidentPolynomial>, bool)>> {
    let resident = self.resident.get();
    self
      .columns
      .iter()
      .enumerate()
      .zip(&self.constants)
      .map(|((index, column), &constant)| {
        Some((
          column.resident()?,
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
  ) -> &[Option<Arc<cuda::ResidentPolynomial>>] {
    self.resident.get_or_init(|| {
      // A OnceLock initializer must not run Rayon work that can reenter it.
      self
        .columns
        .iter()
        .zip(&self.constants)
        .map(|(column, &constant)| {
          if constant { None } else { column.resident().and_then(cuda::retain) }
        })
        .collect()
    })
  }
}

/// Prover-side retained data for one commitment round.
pub struct KzgProverData {
  commitment: KzgCommitment,
  pub matrices: Vec<CommittedMatrix>,
}

impl KzgProverData {
  /// Detach device coefficients while retaining the host key and commitment.
  /// Later GPU operations may hydrate the same immutable coefficients again.
  /// Drop all other request data before releasing the backend's idle memory.
  pub fn release_device_residency(&mut self) {
    #[cfg(feature = "cuda")]
    for matrix in &mut self.matrices {
      drop(matrix.resident.take());
    }
  }

  #[cfg(all(test, feature = "cuda"))]
  pub(super) fn coefficient_fixture(
    domain: Radix2Coset,
    columns: Vec<Vec<Fr>>,
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
    out.write_all(b"IXKZGCP4")?;
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
            super::encoding::write_fields(&mut out, values, |value| *value)
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
    if &magic != b"IXKZGCP4" {
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
      if log_size > 32 {
        return Err(ark_serialize::SerializationError::InvalidData);
      }
      let shift = Scalar(Fr::deserialize_compressed(&mut input)?);
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
          super::encoding::read_fields(&mut input, 1usize << log_size, |v| v)
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
    use ark_serialize::SerializationError;
    use std::{
      fs::File,
      io::{BufReader, Read},
      sync::Mutex,
    };
    let file = Arc::new(Mutex::new(File::open(path)?));
    let mut guard =
      file.lock().map_err(|_error| SerializationError::InvalidData)?;
    let mut reader = BufReader::with_capacity(1 << 20, &mut *guard);
    let mut magic = [0; 8];
    reader.read_exact(&mut magic)?;
    if &magic != b"IXKZGCP4" {
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
      if log > 32 {
        return Err(SerializationError::InvalidData);
      }
      let log_size = usize::try_from(log)
        .map_err(|_error| SerializationError::InvalidData)?;
      let shift = Scalar(Fr::deserialize_compressed(&mut reader)?);
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
        columns.push(Column::index(
          &mut reader,
          file.clone(),
          1usize << log_size,
        )?);
      }
      matrices
        .push(CommittedMatrix::new(Radix2Coset { log_size, shift }, columns));
    }
    let mut tail = [0];
    if reader.read(&mut tail)? != 0 {
      return Err(SerializationError::InvalidData);
    }
    Ok(Self { commitment, matrices })
  }

  /// Combine independently committed matrices in canonical circuit order.
  pub fn concatenate(
    parts: impl IntoIterator<Item = Self>,
  ) -> (KzgCommitment, Self) {
    let mut commitment = KzgCommitment(vec![]);
    let mut matrices = Vec::new();
    for mut part in parts {
      commitment.0.append(&mut part.commitment.0);
      matrices.append(&mut part.matrices);
    }
    (commitment.clone(), Self { commitment, matrices })
  }
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

/// Device memory at a synchronized idle boundary. Current and default pool
/// counters refer to the same pages when `current_pool_is_default` is true.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize)]
pub struct KzgDeviceMemorySnapshot {
  pub driver_free_bytes: u64,
  pub total_bytes: u64,
  pub current_pool_reserved_bytes: u64,
  pub current_pool_used_bytes: u64,
  pub default_pool_reserved_bytes: u64,
  pub default_pool_used_bytes: u64,
  pub current_pool_is_default: bool,
  /// Includes reserved coefficient capacity of operations waiting for a lease.
  pub resident_coefficient_bytes: usize,
  pub srs_point_bytes: usize,
  pub msm_workspace_bytes: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct KzgDeviceMemoryRelease {
  pub device: i32,
  pub before: KzgDeviceMemorySnapshot,
  pub after: KzgDeviceMemorySnapshot,
  pub released_srs_point_bytes: usize,
  pub released_msm_workspace_bytes: usize,
}

/// CPU execution and a CUDA backend with no initialized devices have no
/// device reports. `quiesced` confirms an actual synchronized release on
/// every selected device; live NTT tables, contexts, and other owners'
/// allocations remain valid.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize)]
pub struct KzgIdleMemoryRelease {
  pub cuda_enabled: bool,
  pub initialized: bool,
  pub quiesced: bool,
  pub devices: Vec<KzgDeviceMemoryRelease>,
}

/// See the module docs.
#[derive(Clone)]
pub struct KzgPcs {
  srs: Option<Arc<Srs>>,
  #[cfg(feature = "cuda")]
  srs_owner: Option<Arc<cuda::srs_cache::Owner>>,
  verifier: super::VerifierParams,
  max_quotient_degree: usize,
}

impl KzgPcs {
  /// The public anchors every proof of this configuration is bound to.
  pub fn verifier_params(&self) -> &super::VerifierParams {
    &self.verifier
  }

  /// The public setup these parameters commit to.
  pub fn public_setup(&self) -> super::PublicSetup {
    self.verifier.public_setup()
  }

  pub(super) fn evaluate_columns(
    &self,
    data: &KzgProverData,
    idx: usize,
    domain: Radix2Coset,
    selected: &[usize],
  ) -> RowMajorMatrix<Scalar> {
    let matrix = &data.matrices[idx];
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
    let ark = Self::ark_domain(domain);
    let width = selected.len();
    let height = domain.size();
    let mut values = vec![Scalar(Fr::ZERO); width * height];
    let pairs = width / 2;
    for i in 0..pairs {
      let columns = super::fft_batch::evaluate(
        &[
          &matrix.columns[selected[2 * i]],
          &matrix.columns[selected[2 * i + 1]],
        ],
        ark,
      );
      values.par_chunks_mut(width).zip(columns).for_each(|(row, value)| {
        row[2 * i] = Scalar(value.0[0]);
        row[2 * i + 1] = Scalar(value.0[1]);
      });
    }
    if let Some(coefficients) =
      selected.get(pairs * 2).map(|&i| &matrix.columns[i])
    {
      let coefficients = coefficients.load().expect("coefficient checkpoint");
      let column = if coefficients.iter().skip(1).all(Zero::is_zero) {
        vec![coefficients.first().copied().unwrap_or(Fr::ZERO); height]
      } else {
        let mut values = coefficients.into_owned();
        ark.fft_in_place(&mut values);
        values
      };
      values
        .par_chunks_mut(width)
        .zip(column)
        .for_each(|(row, value)| row[pairs * 2] = Scalar(value));
    }
    RowMajorMatrix::new(values, width)
  }

  /// Coset-evaluate the selected columns through device FFT queues. The
  /// destination holds the full matrix; simultaneous FFT outputs are bounded
  /// by `scratch_bytes`, or one column when a column exceeds that budget.
  #[cfg(feature = "cuda")]
  fn evaluate_columns_on_device(
    matrix: &CommittedMatrix,
    views: &[(&[Fr], Option<&cuda::ResidentPolynomial>, bool)],
    domain: Radix2Coset,
    selected: &[usize],
    scratch_bytes: usize,
  ) -> RowMajorMatrix<Scalar> {
    let _profile = cuda::ProfileRange::new(c"kzg/evaluation-reconstruction");
    let started = std::time::Instant::now();
    let constants = matrix.constant_columns();
    let width = selected.len();
    let height = domain.size();
    let mut values = super::buffer::generate(width * height, |index| {
      let column = selected[index % width];
      if constants[column] {
        Scalar(views[column].0[0])
      } else {
        Scalar(Fr::ZERO)
      }
    });
    let active: Vec<_> =
      (0..width).filter(|&position| !constants[selected[position]]).collect();
    let batch_columns = (scratch_bytes / (height * size_of::<Fr>())).max(1);
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
        cuda::fft_columns(&inputs, domain.log_size, false, domain.shift.0);
      values.par_chunks_mut(width * (1 << 12)).enumerate().for_each(
        |(tile, rows)| {
          for (offset, row) in rows.chunks_mut(width).enumerate() {
            let index = tile * (1 << 12) + offset;
            for (&position, evaluations) in batch.iter().zip(&transformed) {
              row[position] = Scalar(evaluations[index]);
            }
          }
        },
      );
    }
    tracing::info!(
      width,
      height,
      batch_columns,
      seconds = started.elapsed().as_secs_f64(),
      "KZG evaluation reconstruction"
    );
    RowMajorMatrix::new(values, width)
  }

  pub fn new(srs: Arc<Srs>, max_quotient_degree: usize) -> Self {
    let max_trace_len = srs.max_len();
    Self::with_max_trace_len(srs, max_trace_len, max_quotient_degree)
  }

  pub fn with_max_trace_len(
    srs: Arc<Srs>,
    max_trace_len: usize,
    max_quotient_degree: usize,
  ) -> Self {
    let verifier =
      super::VerifierParams::with_max_trace_len(&srs, max_trace_len);
    Self {
      #[cfg(feature = "cuda")]
      srs_owner: Some(cuda::srs_cache::Owner::new(Arc::clone(&srs))),
      srs: Some(srs),
      verifier,
      max_quotient_degree,
    }
  }

  pub fn verifier_only(
    verifier: super::VerifierParams,
    max_quotient_degree: usize,
  ) -> Self {
    Self {
      srs: None,
      #[cfg(feature = "cuda")]
      srs_owner: None,
      verifier,
      max_quotient_degree,
    }
  }

  /// Evict process-wide KZG SRS caches and trim unused CUDA pool pages
  /// without resetting devices. Release retained prover-data residency and
  /// drop request temporaries first. Callers must stop submitting work to
  /// keep devices idle after this method returns; concurrent submissions
  /// wait for its leases.
  pub fn release_idle_device_memory() -> KzgIdleMemoryRelease {
    #[cfg(feature = "cuda")]
    {
      cuda::release_idle_device_memory()
    }
    #[cfg(not(feature = "cuda"))]
    {
      KzgIdleMemoryRelease::default()
    }
  }

  fn prover_srs(&self) -> &Srs {
    self.srs.as_deref().expect("proving requires the full SRS")
  }

  #[cfg(feature = "cuda")]
  fn srs_owner(&self) -> &Arc<cuda::srs_cache::Owner> {
    self.srs_owner.as_ref().expect("proving requires the full SRS")
  }

  /// Commit device-generated coefficient columns of one trace-sized matrix.
  #[cfg(feature = "cuda")]
  pub(super) fn commit_trace_coefficients(
    &self,
    trace_log_size: usize,
    columns: Vec<Vec<Fr>>,
  ) -> KzgProverData {
    let n = 1usize
      .checked_shl(u32::try_from(trace_log_size).expect("trace log size"))
      .unwrap();
    assert!(
      n <= self.verifier.max_trace_len() && n <= self.prover_srs().max_len()
    );
    assert!(!columns.is_empty());
    assert!(columns.iter().all(|column| column.len() == n));
    let matrix = CommittedMatrix::new(
      Radix2Coset {
        log_size: trace_log_size,
        shift: multi_stark::traits::Algebra::<Scalar>::ONE,
      },
      columns.into_iter().map(Column::from).collect(),
    );
    let commitments = self.commit_matrix_columns(&matrix);
    KzgProverData {
      commitment: KzgCommitment(vec![commitments]),
      matrices: vec![matrix],
    }
  }

  #[cfg(feature = "cuda")]
  pub(super) fn commit_quotient_coefficients(
    &self,
    trace_log_size: usize,
    columns: Vec<Vec<Fr>>,
  ) -> KzgProverData {
    assert!(!columns.is_empty() && columns.len() <= self.max_quotient_degree);
    self.commit_trace_coefficients(trace_log_size, columns)
  }

  /// The arkworks FFT domain realizing one of ours.
  fn ark_domain(domain: Radix2Coset) -> Radix2EvaluationDomain<Fr> {
    let base = Radix2EvaluationDomain::new(domain.size())
      .expect("size within Fr two-adicity");
    if domain.shift == multi_stark::traits::Algebra::<Scalar>::ONE {
      base
    } else {
      base.get_coset(domain.shift.0).expect("nonzero coset shift")
    }
  }

  fn commit_matrix_columns(&self, matrix: &CommittedMatrix) -> Vec<G1Affine> {
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
      let mut commits = vec![G1Projective::zero(); views.len()];
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
        let points = if cuda::srs_cache::enabled() {
          cuda::srs_cache::msm_columns(self.srs_owner(), 0, &inputs)
        } else {
          cuda::msm_columns_resident(&self.prover_srs().g1[..count], &inputs)
        };
        for (i, point) in active.into_iter().zip(points) {
          commits[i] = point;
        }
        tracing::debug!(
          count,
          columns = inputs.len(),
          seconds = started.elapsed().as_secs_f64(),
          "KZG column MSMs"
        );
      }
      return G1Projective::normalize_batch(&commits);
    }
    let commits: Vec<G1Projective> = matrix
      .columns
      .iter()
      .map(|c| self.msm(&c.load().expect("coefficient checkpoint")))
      .collect();
    G1Projective::normalize_batch(&commits)
  }

  fn msm(&self, coeffs: &[Fr]) -> G1Projective {
    assert!(
      coeffs.len() <= self.verifier.max_trace_len(),
      "polynomial length {} exceeds the trace cap ({})",
      coeffs.len(),
      self.verifier.max_trace_len()
    );
    if coeffs.is_empty() {
      return G1Projective::zero();
    }
    assert!(
      coeffs.len() <= self.prover_srs().max_len(),
      "proving requires the complete coefficient prefix"
    );
    if coeffs.iter().skip(1).all(Zero::is_zero) {
      return self.prover_srs().g1[0]
        * coeffs.first().copied().unwrap_or(Fr::ZERO);
    }
    #[cfg(feature = "cuda")]
    if coeffs.len() >= 1 << 12 {
      if cuda::srs_cache::enabled() {
        return cuda::srs_cache::msm_columns(
          self.srs_owner(),
          0,
          &[(coeffs, None)],
        )[0];
      }
      return cuda::msm(&self.prover_srs().g1[..coeffs.len()], coeffs);
    }
    // Bound digit/bucket scratch and expose point-range parallelism in
    // addition to the MSM implementation's small number of scalar windows.
    const CHUNK: usize = 1 << 18;
    let concurrency = current_num_threads().div_ceil(8).min(4);
    let mut result = G1Projective::zero();
    for (batch, values) in coeffs.chunks(CHUNK * concurrency).enumerate() {
      let partial: G1Projective = values
        .par_chunks(CHUNK)
        .enumerate()
        .map(|(i, scalars)| {
          let start = batch * CHUNK * concurrency + i * CHUNK;
          G1Projective::msm(
            &self.prover_srs().g1[start..start + scalars.len()],
            scalars,
          )
          .expect("equal lengths")
        })
        .sum();
      result += partial;
    }
    result
  }

  /// Interpolate each column of `matrix` over `domain`.
  fn interpolate_columns(
    domain: Radix2Coset,
    matrix: RowMajorMatrix<Scalar>,
  ) -> CommittedMatrix {
    assert_eq!(matrix.height(), domain.size(), "matrix height != domain size");
    let width = matrix.width();
    let evals: Vec<Vec<Fr>> = if width == 1 {
      // The consuming map reuses the transparent scalar vector's allocation.
      vec![matrix.values.into_iter().map(|v| v.0).collect()]
    } else {
      (0..width)
        .into_par_iter()
        .map(|column| {
          super::buffer::generate(matrix.height(), |row| {
            matrix.values[row * width + column].0
          })
        })
        .collect()
    };
    let mut constants = vec![false; width];
    let mut output: Vec<Vec<Fr>> = vec![Vec::new(); width];
    let mut active = Vec::new();
    let mut inputs = Vec::new();
    for (i, mut col) in evals.into_iter().enumerate() {
      let first = col[0];
      if col.iter().all(|&v| v == first) {
        constants[i] = true;
        col.fill(Fr::ZERO);
        col[0] = first;
        output[i] = col;
      } else {
        active.push(i);
        inputs.push(col);
      }
    }
    #[cfg(feature = "cuda")]
    let resident = std::sync::OnceLock::new();
    #[cfg(feature = "cuda")]
    let interpolated = if domain.size() >= 1 << 10 {
      let (columns, residents) =
        cuda::interpolate_columns(inputs, domain.log_size, domain.shift.0);
      let mut all_residents = vec![None; width];
      for (&i, resident) in active.iter().zip(residents) {
        all_residents[i] = resident;
      }
      let _ = resident.set(all_residents);
      columns
    } else {
      Self::interpolate_on_host(domain, inputs)
    };
    #[cfg(not(feature = "cuda"))]
    let interpolated = Self::interpolate_on_host(domain, inputs);
    for (i, column) in active.into_iter().zip(interpolated) {
      output[i] = column;
    }
    CommittedMatrix {
      domain,
      columns: output.into_iter().map(Column::from).collect(),
      constants,
      #[cfg(feature = "cuda")]
      resident,
    }
  }

  fn interpolate_on_host(
    domain: Radix2Coset,
    columns: Vec<Vec<Fr>>,
  ) -> Vec<Vec<Fr>> {
    let ark = Self::ark_domain(domain);
    columns
      .into_par_iter()
      .map(|mut col| {
        ark.ifft_in_place(&mut col);
        col
      })
      .collect()
  }
}

impl Pcs for KzgPcs {
  type F = Scalar;
  type Challenge = Scalar;
  type Domain = Radix2Coset;
  type Challenger = Blake3Transcript;
  type Commitment = KzgCommitment;
  type ProverData = KzgProverData;
  type Proof = KzgProof;
  type Error = KzgError;
  type Evaluations<'a> = RowMajorMatrix<Scalar>;

  fn natural_domain_for_degree(&self, degree: usize) -> Radix2Coset {
    Radix2Coset {
      log_size: p3_util::log2_strict_usize(degree),
      shift: multi_stark::traits::Algebra::<Scalar>::ONE,
    }
  }

  fn max_quotient_degree(&self) -> usize {
    self.max_quotient_degree
  }

  fn commit(
    &self,
    evaluations: Vec<(Radix2Coset, RowMajorMatrix<Scalar>)>,
  ) -> (KzgCommitment, KzgProverData) {
    let matrices: Vec<CommittedMatrix> = evaluations
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
    quotients: Vec<(Radix2Coset, RowMajorMatrix<Scalar>, usize)>,
  ) -> (KzgCommitment, KzgProverData) {
    let matrices: Vec<CommittedMatrix> = quotients
      .into_iter()
      .map(|(quotient_domain, evaluations, quotient_degree)| {
        let big = quotient_domain.size();
        debug_assert_eq!(big % quotient_degree, 0);
        let n = big / quotient_degree;
        let coefficient_columns =
          Self::interpolate_columns(quotient_domain, evaluations).columns;
        // Slice `Q(X) = Σₖ X^{k·n}·cₖ(X)`: slice k of coordinate d
        // is coefficient range [k·n, (k+1)·n), laid out as column
        // `k·D + d` — the order the verifier's ζ-recombination
        // reads.
        let columns: Vec<Column> = (0..quotient_degree)
          .flat_map(|k| {
            coefficient_columns.iter().map(move |c| c.slice(k * n..(k + 1) * n))
          })
          .collect();
        CommittedMatrix::new(
          Radix2Coset {
            log_size: p3_util::log2_strict_usize(n),
            shift: multi_stark::traits::Algebra::<Scalar>::ONE,
          },
          columns,
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
    data: &KzgProverData,
    idx: usize,
    domain: Radix2Coset,
  ) -> RowMajorMatrix<Scalar> {
    self.evaluate_columns(
      data,
      idx,
      domain,
      &(0..data.matrices[idx].columns.len()).collect::<Vec<_>>(),
    )
  }

  fn open(
    &self,
    rounds: OpeningRounds<'_, KzgProverData, Scalar>,
    challenger: &mut Blake3Transcript,
  ) -> (OpenedValues<Scalar>, KzgProof) {
    for (data, _) in &rounds {
      challenger.observe_commitment(data.commitment.clone());
      for m in &data.matrices {
        challenger.observe_canonical(&(m.domain.log_size as u64));
      }
    }
    // Pass 1: evaluate everything, observing values in traversal
    // order, and batch (polynomial, value) pairs per distinct point.
    struct PointBatch<'a> {
      z: Fr,
      entries: Vec<(&'a Column, Fr)>,
    }
    let mut batches: Vec<PointBatch<'_>> = Vec::new();
    let mut opened: OpenedValues<Scalar> = Vec::new();
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
          vec![vec![Scalar(Fr::ZERO); matrix.columns.len()]; points.len()];
        if !points.is_empty() {
          let zs: Vec<_> = points.iter().map(|z| z.0).collect();
          let constants = matrix.constant_columns();
          #[cfg(feature = "cuda")]
          let views = matrix.cuda_columns();
          #[cfg(feature = "cuda")]
          let residents = views.as_ref().map(|_| matrix.resident_columns());
          for (column_index, column) in matrix.columns.iter().enumerate() {
            if constants[column_index] {
              let value = column
                .resident()
                .and_then(|values| values.first().copied())
                .unwrap_or(Fr::ZERO);
              for row in &mut matrix_values {
                row[column_index] = Scalar(value);
              }
              continue;
            }
            #[cfg(feature = "cuda")]
            if let Some(views) = &views
              && views[column_index].0.len() >= 1 << 12
            {
              let values = cuda::evaluate_resident(
                views[column_index].0,
                residents.and_then(|r| r[column_index].as_deref()),
                &zs,
              );
              for (row, value) in matrix_values.iter_mut().zip(values) {
                row[column_index] = Scalar(value);
              }
              continue;
            }
            // Decode a disk column once for all requested points.
            column
              .visit(|start, chunk| {
                for (&z, row) in zs.iter().zip(&mut matrix_values) {
                  row[column_index].0 +=
                    eval_poly(chunk, z) * z.pow([start as u64]);
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
      let mut combined: Vec<Vec<Fr>> = group
        .iter()
        .map(|batch| {
          vec![
            Fr::ZERO;
            batch.entries.iter().map(|(c, _)| c.len()).max().unwrap_or(0)
          ]
        })
        .collect();
      let mut columns: Vec<(&Column, [Fr; 2])> = Vec::new();
      let mut indices = std::collections::HashMap::new();
      for (batch_index, batch) in group.iter().enumerate() {
        let mut power = Fr::ONE;
        for (column, _) in &batch.entries {
          let index =
            *indices.entry(std::ptr::from_ref(*column)).or_insert_with(|| {
              columns.push((column, [Fr::ZERO; 2]));
              columns.len() - 1
            });
          columns[index].1[batch_index] += power;
          power *= v;
        }
      }
      for (column, weights) in columns {
        column
          .visit(|start, chunk| {
            if let [a, b] = combined.as_mut_slice()
              && weights[0] != Fr::ZERO
              && weights[1] != Fr::ZERO
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
                if weight != Fr::ZERO {
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
    let witnesses = G1Projective::normalize_batch(&witnesses);
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
    rounds: VerifyRounds<KzgCommitment, Radix2Coset, Scalar>,
    proof: &KzgProof,
    challenger: &mut Blake3Transcript,
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
    struct PointBatch {
      z: Fr,
      commitments: Vec<G1Affine>,
      values: Vec<Fr>,
    }
    let mut batches: Vec<PointBatch> = Vec::new();
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
    let g = G1Projective::from(self.verifier.g1[0]);
    let mut lhs = G1Projective::zero();
    let mut rhs = G1Projective::zero();
    let mut r_power = Fr::ONE;
    for (batch, &witness) in batches.iter().zip(&proof.0) {
      let mut v_powers = Vec::with_capacity(batch.values.len());
      let mut power = Fr::ONE;
      let mut y = Fr::ZERO;
      for &value in &batch.values {
        v_powers.push(power);
        y += power * value;
        power *= v;
      }
      let c = G1Projective::msm(&batch.commitments, &v_powers)
        .expect("equal lengths");
      lhs += (c - g * y + witness * batch.z) * r_power;
      rhs += witness * r_power;
      r_power *= r;
    }
    let check = Bls12_381::multi_pairing(
      [lhs.into_affine(), (-rhs).into_affine()],
      [self.verifier.g2, self.verifier.tau_g2],
    );
    if check.is_zero() { Ok(()) } else { Err(KzgError::PairingCheckFailed) }
  }
}

impl KzgPcs {
  /// The witness commitment `[(p(X) − p(z)) / (X − z)]·G` of one folded
  /// opening polynomial.
  fn witness(&self, combined: Vec<Fr>, z: Fr) -> G1Projective {
    #[cfg(feature = "cuda")]
    if combined.len() >= 1 << 16 {
      let witness = if cuda::srs_cache::enabled() {
        cuda::srs_cache::single_device_opening(self.srs_owner(), &combined, z)
      } else {
        cuda::single_device_opening(
          &self.prover_srs().g1[..combined.len() - 1],
          &combined,
          z,
        )
      };
      if let Some(witness) = witness {
        return witness;
      }
    }
    self.msm(&divide_by_linear(combined, z))
  }
}

const POLYNOMIAL_BLOCK: usize = 1 << 12;

fn eval_poly_serial(coeffs: &[Fr], z: Fr) -> Fr {
  coeffs.iter().rev().fold(Fr::ZERO, |acc, c| acc * z + c)
}

/// Evaluate coefficient blocks independently, then fold at z^block_size.
fn eval_poly(coeffs: &[Fr], z: Fr) -> Fr {
  if coeffs.len() <= POLYNOMIAL_BLOCK {
    return eval_poly_serial(coeffs, z);
  }
  let blocks: Vec<_> = coeffs
    .par_chunks(POLYNOMIAL_BLOCK)
    .map(|block| eval_poly_serial(block, z))
    .collect();
  eval_poly_serial(&blocks, z.pow([POLYNOMIAL_BLOCK as u64]))
}

/// Synthetic division, reusing the input allocation. Block boundary carries
/// are suffix evaluations; the second pass runs independently in each block.
fn divide_by_linear(mut p: Vec<Fr>, z: Fr) -> Vec<Fr> {
  if p.len() <= 1 {
    return Vec::new();
  }
  #[cfg(feature = "cuda")]
  if p.len() >= 1 << 16 {
    return cuda::divide(&p, z);
  }
  let n = p.len() - 1;
  if n <= POLYNOMIAL_BLOCK {
    let mut carry = Fr::ZERO;
    for value in p[1..].iter_mut().rev() {
      carry = *value + z * carry;
      *value = carry;
    }
  } else {
    let mut boundaries: Vec<_> = p[1..]
      .par_chunks(POLYNOMIAL_BLOCK)
      .map(|block| eval_poly_serial(block, z))
      .collect();
    let full_power = z.pow([POLYNOMIAL_BLOCK as u64]);
    let mut carry = Fr::ZERO;
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

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn disk_coefficients_match_resident_and_detect_changes() {
    use std::io::{Seek, SeekFrom, Write};
    let path = std::env::temp_dir().join(format!(
      "kzg-columns-{}-{}.bin",
      std::process::id(),
      std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos()
    ));
    let mut file = std::fs::File::create_new(&path).unwrap();
    let pcs =
      KzgPcs::new(Arc::new(Srs::unsafe_dev_setup(1 << 17, b"disk-columns")), 2);
    let domain = pcs.natural_domain_for_degree(1 << 17);
    let (_, resident) = pcs.commit(vec![(
      domain,
      RowMajorMatrix::new_col(
        (0..domain.size()).map(Scalar::from_usize).collect(),
      ),
    )]);
    let mut bytes = Vec::new();
    resident.write_checkpoint(&mut bytes).unwrap();
    file.write_all(&bytes).unwrap();
    let disk = KzgProverData::read_checkpoint_file(&path).unwrap();
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
    let expected =
      pcs.open(vec![(&resident, points.clone())], &mut Blake3Transcript::new());
    let actual =
      pcs.open(vec![(&disk, points.clone())], &mut Blake3Transcript::new());
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
        &mut Blake3Transcript::new(),
      )
      .unwrap();
    assert_eq!(actual, expected);
    file.seek(SeekFrom::End(-32)).unwrap();
    file.write_all(&[0; 32]).unwrap();
    assert!(disk.matrices[0].columns[0].load().is_err());
    file.set_len(0).unwrap();
    assert!(disk.matrices[0].columns[0].load().is_err());
    assert!(KzgProverData::read_checkpoint_file(&path).is_err());
    drop(file);
    drop(disk);
    std::fs::remove_file(path).unwrap();
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
      let p: Vec<_> = (0..n).map(|i| Fr::from((i * i + 7) as u64)).collect();
      for z in [Fr::ZERO, Fr::ONE, -Fr::ONE, Fr::from(13u64)] {
        assert_eq!(eval_poly(&p, z), eval_poly_serial(&p, z));
        let mut expected = vec![Fr::ZERO; n.saturating_sub(1)];
        let mut carry = Fr::ZERO;
        for j in (1..n).rev() {
          carry = p[j] + z * carry;
          expected[j - 1] = carry;
        }
        assert_eq!(divide_by_linear(p.clone(), z), expected);
      }
    }
  }

  use multi_stark::traits::Algebra;
  use multi_stark::traits::Field;

  #[test]
  fn chunked_commitment_matches_native_msm_with_tail() {
    let pcs =
      KzgPcs::new(Arc::new(Srs::unsafe_dev_setup(1 << 18, b"chunked-msm")), 4);
    let mut value = Fr::from(17u64);
    let coefficients: Vec<_> = (0..(2 * (1 << 16) + 3))
      .map(|_| {
        value = value.square() + Fr::ONE;
        value
      })
      .collect();
    let expected = G1Projective::msm(
      &pcs.prover_srs().g1[..coefficients.len()],
      &coefficients,
    )
    .unwrap();
    assert_eq!(pcs.msm(&coefficients), expected);
  }

  #[test]
  fn constant_columns_are_detected_on_commit_and_checkpoint_load() {
    let pcs =
      KzgPcs::new(Arc::new(Srs::unsafe_dev_setup(16, b"constant-columns")), 4);
    let domain = pcs.natural_domain_for_degree(16);
    let matrix = RowMajorMatrix::new(
      (0..16)
        .flat_map(|row| [Scalar::from_u8(7), Scalar::from_usize(row)])
        .collect(),
      2,
    );
    let (_, data) = pcs.commit(vec![(domain, matrix)]);
    assert_eq!(data.matrices[0].constant_columns(), [true, false]);
    let mut bytes = Vec::new();
    data.write_checkpoint(&mut bytes).unwrap();
    let loaded = KzgProverData::read_checkpoint(bytes.as_slice()).unwrap();
    assert_eq!(loaded.matrices[0].constant_columns(), [true, false]);
  }

  #[test]
  fn releasing_device_residency_preserves_host_checkpoint() {
    let pcs =
      KzgPcs::new(Arc::new(Srs::unsafe_dev_setup(8, b"release-host-key")), 4);
    let (_, mut data) = pcs.commit(vec![(
      pcs.natural_domain_for_degree(8),
      RowMajorMatrix::new((0..16).map(Scalar::from_u64).collect(), 2),
    )]);
    #[cfg(feature = "cuda")]
    for matrix in &data.matrices {
      let _ = matrix.resident.set(vec![None; matrix.width()]);
    }
    let mut expected = Vec::new();
    data.write_checkpoint(&mut expected).unwrap();
    for _ in 0..2 {
      data.release_device_residency();
      #[cfg(feature = "cuda")]
      assert!(
        data.matrices.iter().all(|matrix| matrix.resident.get().is_none())
      );
      let mut actual = Vec::new();
      data.write_checkpoint(&mut actual).unwrap();
      assert_eq!(actual, expected);
    }
  }

  #[cfg(not(feature = "cuda"))]
  #[test]
  fn idle_memory_release_without_cuda_is_explicit_noop() {
    assert_eq!(
      KzgPcs::release_idle_device_memory(),
      KzgIdleMemoryRelease::default()
    );
  }

  #[test]
  fn mixed_height_openings_verify_without_proving_powers() {
    let pcs = KzgPcs::new(
      Arc::new(Srs::unsafe_dev_setup(16, b"public-degree-test")),
      4,
    );
    let domains =
      [pcs.natural_domain_for_degree(2), pcs.natural_domain_for_degree(16)];
    let (commitment, data) = pcs.commit(
      domains
        .into_iter()
        .map(|d| {
          (d, RowMajorMatrix::new_col(vec![Scalar::from_u8(7); d.size()]))
        })
        .collect(),
    );
    assert_eq!(commitment.0.iter().map(Vec::len).collect::<Vec<_>>(), [1, 1]);
    let z = Scalar::from_u8(19);
    let (values, proof) = pcs.open(
      vec![(&data, vec![vec![z], vec![z]])],
      &mut Blake3Transcript::new(),
    );
    let rounds = vec![(
      commitment,
      domains
        .into_iter()
        .zip(&values[0])
        .map(|(d, v)| (d, vec![(z, v[0].clone())]))
        .collect(),
    )];
    let verifier = KzgPcs::verifier_only(pcs.verifier.clone(), 4);
    assert!(verifier.srs.is_none());
    verifier
      .verify(rounds.clone(), &proof, &mut Blake3Transcript::new())
      .unwrap();
    let mut corrupt = rounds.clone();
    corrupt[0].1[0].1[0].1[0] += Scalar::ONE;
    assert!(
      verifier.verify(corrupt, &proof, &mut Blake3Transcript::new()).is_err()
    );
    let mut oversized = rounds;
    oversized[0].1[0].0.log_size = 5;
    assert!(matches!(
      verifier.verify(oversized, &proof, &mut Blake3Transcript::new()),
      Err(KzgError::ShapeMismatch)
    ));
  }
}

#[cfg(test)]
#[path = "pcs/public_degree_tests.rs"]
mod public_degree_tests;
