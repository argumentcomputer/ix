//! Monomial-basis KZG over BLS12-381 as a crate [`Pcs`].
//!
//! Commitments are per column: interpolate each column of a committed
//! matrix over its domain (radix-2 iFFT) and MSM the coefficients
//! against the SRS — a round's commitment is the vector of G1 points,
//! 48 bytes per column. Shorter polynomials also carry a shifted commitment
//! checked against the SRS degree key. There are no FRI queries.
//!
//! Opening batches per distinct point: all polynomials opened at `z`
//! (across every round and matrix) are folded with powers of one
//! transcript challenge `v`, and a single witness commitment
//! `W_z = [ (Σᵢ vⁱ·pᵢ − Σᵢ vⁱ·pᵢ(z)) / (X − z) ]·G` covers them. The
//! multi-stark opens at `ζ` and the per-trace-height `ζ·gₖ`, so a whole
//! proof carries a handful of G1 points. Verification folds the same
//! combination over the commitments and checks all points with one
//! 2-pairing equation, cross-batched by a second challenge `r`:
//! `e(Σ_z r^z·(C_z − y_z·G + z·W_z), H) = e(Σ_z r^z·W_z, τH)`.
//!
//! The quotient commit follows the core's coefficient-slice convention
//! (`Q(X) = Σₖ X^{k·n}·cₖ(X)`, verifier recombines at ζ): one coset
//! iFFT off the quotient domain, then each length-`n` slice is just a
//! range of the coefficient vector — no evaluation representation ever
//! needed. Trace evaluations on the quotient domain
//! ([`Pcs::get_evaluations_on_domain`]) are coset FFTs from the stored
//! coefficients; that FFT budget is what [`Pcs::max_quotient_degree`]
//! bounds (there is no blowup wall — exceeding it is slow, not
//! unsound, but the build-time check keeps the cost model honest).

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
use super::domain::Radix2Coset;
use super::field::Scalar;
use super::srs::Srs;
use super::transcript::Blake3Transcript;

/// Per-matrix column commitments and optional shifted degree commitments.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KzgCommitment(pub Vec<Vec<G1Affine>>, pub Vec<Vec<G1Affine>>);

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
impl Serialize for KzgCommitment {
  fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
    let mut bytes = Vec::new();
    self
      .0
      .serialize_compressed(&mut bytes)
      .map_err(serde::ser::Error::custom)?;
    self
      .1
      .serialize_compressed(&mut bytes)
      .map_err(serde::ser::Error::custom)?;
    bytes.serialize(serializer)
  }
}
impl<'de> Deserialize<'de> for KzgCommitment {
  fn deserialize<D: Deserializer<'de>>(
    deserializer: D,
  ) -> Result<Self, D::Error> {
    let bytes = Vec::<u8>::deserialize(deserializer)?;
    let mut input = bytes.as_slice();
    let main = Vec::<Vec<G1Affine>>::deserialize_compressed(&mut input)
      .map_err(serde::de::Error::custom)?;
    let shifted = Vec::<Vec<G1Affine>>::deserialize_compressed(&mut input)
      .map_err(serde::de::Error::custom)?;
    if !input.is_empty() {
      return Err(serde::de::Error::custom("trailing commitment bytes"));
    }
    Ok(Self(main, shifted))
  }
}
serde_via_canonical!(KzgProof, Vec<G1Affine>);

/// A committed matrix on the prover side: its domain and each column
/// polynomial in coefficient form (length = domain size).
pub struct CommittedMatrix {
  pub(crate) domain: Radix2Coset,
  columns: Vec<Column>,
}

/// Prover-side retained data for one commitment round.
pub struct KzgProverData {
  commitment: KzgCommitment,
  pub matrices: Vec<CommittedMatrix>,
}

impl KzgProverData {
  /// Save a local prover checkpoint. This is not a verifier-key format.
  pub fn write_checkpoint(
    &self,
    mut out: impl std::io::Write,
  ) -> Result<(), ark_serialize::SerializationError> {
    self.commitment.0.serialize_compressed(&mut out)?;
    self.commitment.1.serialize_compressed(&mut out)?;
    (self.matrices.len() as u64).serialize_compressed(&mut out)?;
    for matrix in &self.matrices {
      (matrix.domain.log_size as u64).serialize_compressed(&mut out)?;
      matrix.domain.shift.0.serialize_compressed(&mut out)?;
      (matrix.columns.len() as u64).serialize_compressed(&mut out)?;
      for column in &matrix.columns {
        (column.len() as u64).serialize_compressed(&mut out)?;
        let mut result = Ok(());
        let mut bytes = vec![0u8; column.len().min(1 << 16) * 32];
        column.visit(|_, values| {
          if result.is_err() {
            return;
          }
          result = values.chunks(1 << 16).try_for_each(|chunk| {
            let bytes = &mut bytes[..chunk.len() * 32];
            bytes
              .par_chunks_mut(32)
              .zip(chunk.par_iter())
              .try_for_each(|(dst, value)| value.serialize_compressed(dst))?;
            out.write_all(bytes)?;
            Ok::<_, ark_serialize::SerializationError>(())
          });
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
    let commitment = KzgCommitment(
      Vec::deserialize_compressed(&mut input)?,
      Vec::deserialize_compressed(&mut input)?,
    );
    let count = usize::try_from(u64::deserialize_compressed(&mut input)?)
      .map_err(|_error| ark_serialize::SerializationError::InvalidData)?;
    if count != commitment.0.len() || count != commitment.1.len() {
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
      let columns: Vec<Vec<Fr>> = Vec::deserialize_compressed(&mut input)?;
      if columns.len() != commitment.0[i].len()
        || columns.iter().any(|c| c.len() != 1usize << log_size)
      {
        return Err(ark_serialize::SerializationError::InvalidData);
      }
      matrices.push(CommittedMatrix {
        domain: Radix2Coset { log_size, shift },
        columns: columns.into_iter().map(Column::from).collect(),
      });
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
    let commitment = KzgCommitment(
      Vec::deserialize_compressed(&mut reader)?,
      Vec::deserialize_compressed(&mut reader)?,
    );
    let count = usize::try_from(u64::deserialize_compressed(&mut reader)?)
      .map_err(|_error| SerializationError::InvalidData)?;
    if count != commitment.0.len() || count != commitment.1.len() {
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
      matrices.push(CommittedMatrix {
        domain: Radix2Coset { log_size, shift },
        columns,
      });
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
    let mut commitment = KzgCommitment(vec![], vec![]);
    let mut matrices = Vec::new();
    for mut part in parts {
      commitment.0.append(&mut part.commitment.0);
      commitment.1.append(&mut part.commitment.1);
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
  DegreeBoundFailed,
}

/// See the module docs.
#[derive(Clone)]
pub struct KzgPcs {
  srs: Arc<Srs>,
  max_quotient_degree: usize,
}

impl KzgPcs {
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

  pub fn new(srs: Arc<Srs>, max_quotient_degree: usize) -> Self {
    Self { srs, max_quotient_degree }
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

  fn commit_columns(&self, columns: &[Column]) -> Vec<G1Affine> {
    let commits: Vec<G1Projective> = columns
      .iter()
      .map(|c| self.msm(&c.load().expect("coefficient checkpoint")))
      .collect();
    G1Projective::normalize_batch(&commits)
  }

  fn msm(&self, coeffs: &[Fr]) -> G1Projective {
    assert!(
      coeffs.len() <= self.srs.max_len(),
      "polynomial length {} exceeds the SRS ({})",
      coeffs.len(),
      self.srs.max_len()
    );
    if coeffs.is_empty() {
      return G1Projective::zero();
    }
    self.msm_at(coeffs, 0)
  }

  fn msm_at(&self, coeffs: &[Fr], shift: usize) -> G1Projective {
    if coeffs.iter().skip(1).all(Zero::is_zero) {
      return self.srs.g1[shift] * coeffs.first().copied().unwrap_or(Fr::ZERO);
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
          let start = shift + batch * CHUNK * concurrency + i * CHUNK;
          G1Projective::msm(&self.srs.g1[start..start + scalars.len()], scalars)
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
  ) -> Vec<Vec<Fr>> {
    assert_eq!(matrix.height(), domain.size(), "matrix height != domain size");
    let width = matrix.width();
    let evals = if width == 1 {
      // The consuming map reuses the transparent scalar vector's allocation.
      vec![matrix.values.into_iter().map(|v| v.0).collect()]
    } else {
      let mut evals: Vec<Vec<Fr>> =
        vec![Vec::with_capacity(matrix.height()); width];
      for (i, value) in matrix.values.into_iter().enumerate() {
        evals[i % width].push(value.0);
      }
      evals
    };
    let ark = Self::ark_domain(domain);
    evals
      .into_iter()
      .map(|mut col| {
        let first = col[0];
        if col.iter().all(|&v| v == first) {
          col.fill(Fr::ZERO);
          col[0] = first;
          col
        } else {
          ark.ifft_in_place(&mut col);
          col
        }
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
      .map(|(domain, matrix)| CommittedMatrix {
        domain,
        columns: Self::interpolate_columns(domain, matrix)
          .into_iter()
          .map(Column::from)
          .collect(),
      })
      .collect();
    let commitment = KzgCommitment(
      matrices.iter().map(|m| self.commit_columns(&m.columns)).collect(),
      matrices
        .iter()
        .map(|m| {
          let shift = self.srs.max_len() - m.domain.size();
          if shift == 0 {
            return vec![];
          }
          let points: Vec<_> = m
            .columns
            .iter()
            .map(|c| {
              self.msm_at(&c.load().expect("coefficient checkpoint"), shift)
            })
            .collect();
          G1Projective::normalize_batch(&points)
        })
        .collect(),
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
        let coefficient_columns: Vec<Column> =
          Self::interpolate_columns(quotient_domain, evaluations)
            .into_iter()
            .map(Column::from)
            .collect();
        // Slice `Q(X) = Σₖ X^{k·n}·cₖ(X)`: slice k of coordinate d
        // is coefficient range [k·n, (k+1)·n), laid out as column
        // `k·D + d` — the order the verifier's ζ-recombination
        // reads.
        let columns: Vec<Column> = (0..quotient_degree)
          .flat_map(|k| {
            coefficient_columns.iter().map(move |c| c.slice(k * n..(k + 1) * n))
          })
          .collect();
        CommittedMatrix {
          domain: Radix2Coset {
            log_size: p3_util::log2_strict_usize(n),
            shift: multi_stark::traits::Algebra::<Scalar>::ONE,
          },
          columns,
        }
      })
      .collect();
    let commitment = KzgCommitment(
      matrices.iter().map(|m| self.commit_columns(&m.columns)).collect(),
      matrices
        .iter()
        .map(|m| {
          let shift = self.srs.max_len() - m.domain.size();
          if shift == 0 {
            return vec![];
          }
          let points: Vec<_> = m
            .columns
            .iter()
            .map(|c| {
              self.msm_at(&c.load().expect("coefficient checkpoint"), shift)
            })
            .collect();
          G1Projective::normalize_batch(&points)
        })
        .collect(),
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
    let _degree_challenge = challenger.sample_challenge();
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
        // Decode a disk column once for all requested points.
        if !points.is_empty() {
          for (column_index, column) in matrix.columns.iter().enumerate() {
            column
              .visit(|start, chunk| {
                for (&z, row) in points.iter().zip(&mut matrix_values) {
                  row[column_index].0 +=
                    eval_poly(chunk, z.0) * z.0.pow([start as u64]);
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
        witnesses.push(self.msm(&divide_by_linear(values, batch.z)));
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
    for (commitment, matrices) in &rounds {
      challenger.observe_commitment(commitment.clone());
      for (domain, _) in matrices {
        challenger.observe_canonical(&(domain.log_size as u64));
      }
    }
    let degree_challenge = challenger.sample_challenge().0;
    let mut weight = Fr::ONE;
    let mut shifted_sum = G1Projective::zero();
    let mut by_degree = vec![G1Projective::zero(); self.srs.degree_keys.len()];
    for (commitment, matrices) in &rounds {
      if commitment.0.len() != matrices.len()
        || commitment.1.len() != matrices.len()
      {
        return Err(KzgError::ShapeMismatch);
      }
      for ((columns, shifted), (domain, _)) in
        commitment.0.iter().zip(&commitment.1).zip(matrices)
      {
        let log = domain.log_size;
        if log >= by_degree.len() {
          return Err(KzgError::ShapeMismatch);
        }
        if domain.size() == self.srs.max_len() {
          if !shifted.is_empty() {
            return Err(KzgError::ShapeMismatch);
          }
        } else {
          if shifted.len() != columns.len() {
            return Err(KzgError::ShapeMismatch);
          }
          for (&c, &s) in columns.iter().zip(shifted) {
            by_degree[log] += c * weight;
            shifted_sum += s * weight;
            weight *= degree_challenge;
          }
        }
      }
    }
    let mut g1 = vec![shifted_sum.into_affine()];
    let mut g2 = vec![self.srs.g2];
    for (sum, key) in by_degree.into_iter().zip(&self.srs.degree_keys) {
      if !sum.is_zero() {
        g1.push((-sum).into_affine());
        g2.push(*key);
      }
    }
    if !Bls12_381::multi_pairing(g1, g2).is_zero() {
      return Err(KzgError::DegreeBoundFailed);
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
    let g = G1Projective::from(self.srs.g1[0]);
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
      [self.srs.g2, self.srs.tau_g2],
    );
    if check.is_zero() { Ok(()) } else { Err(KzgError::PairingCheckFailed) }
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
mod degree_tests {
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
  fn chunked_commitment_matches_native_msm_with_shift_and_tail() {
    let pcs =
      KzgPcs::new(Arc::new(Srs::unsafe_dev_setup(1 << 18, b"chunked-msm")), 4);
    let mut value = Fr::from(17u64);
    let coefficients: Vec<_> = (0..(2 * (1 << 16) + 3))
      .map(|_| {
        value = value.square() + Fr::ONE;
        value
      })
      .collect();
    for shift in [0, 7] {
      let expected = G1Projective::msm(
        &pcs.srs.g1[shift..shift + coefficients.len()],
        &coefficients,
      )
      .unwrap();
      assert_eq!(pcs.msm_at(&coefficients, shift), expected);
    }
  }

  #[test]
  fn mixed_degree_openings_enforce_every_bound() {
    let pcs =
      KzgPcs::new(Arc::new(Srs::unsafe_dev_setup(16, b"degree-test")), 4);
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
    let z = Scalar::from_u8(19);
    let (values, proof) = pcs.open(
      vec![(&data, vec![vec![z], vec![z]])],
      &mut Blake3Transcript::new(),
    );
    let rounds = vec![(
      commitment.clone(),
      domains
        .into_iter()
        .zip(values[0].iter())
        .map(|(d, v)| (d, vec![(z, v[0].clone())]))
        .collect(),
    )];
    pcs.verify(rounds.clone(), &proof, &mut Blake3Transcript::new()).unwrap();
    let mut missing = rounds.clone();
    missing[0].0.1[0].clear();
    assert!(pcs.verify(missing, &proof, &mut Blake3Transcript::new()).is_err());
    let mut corrupt = rounds;
    corrupt[0].0.1[0][0] = pcs.srs.g1[0];
    assert!(matches!(
      pcs.verify(corrupt, &proof, &mut Blake3Transcript::new()),
      Err(KzgError::DegreeBoundFailed)
    ));

    // A valid KZG opening for a polynomial too large for its declared
    // two-row domain must be rejected, even though it fits the global SRS.
    let columns = vec![Column::from(vec![Fr::ZERO, Fr::ZERO, Fr::ONE])];
    let commitment = KzgCommitment(
      pcs.commit_columns(&columns).into_iter().map(|c| vec![c]).collect(),
      vec![vec![pcs.srs.g1[0]]],
    );
    let data = KzgProverData {
      commitment: commitment.clone(),
      matrices: vec![CommittedMatrix { domain: domains[0], columns }],
    };
    let (values, proof) =
      pcs.open(vec![(&data, vec![vec![z]])], &mut Blake3Transcript::new());
    assert!(matches!(
      pcs.verify(
        vec![(
          commitment,
          vec![(domains[0], vec![(z, values[0][0][0].clone())])]
        )],
        &proof,
        &mut Blake3Transcript::new()
      ),
      Err(KzgError::DegreeBoundFailed)
    ));
  }
}
