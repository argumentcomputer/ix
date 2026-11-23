//! Multi-stark [`Pcs`] committing equal-height packs of interleaved columns
//! and opening every pack of every round with one SHPLONK batch
//! ([`super::shplonk`]). Experimental; not used by any production path.
//!
//! Commitment: per round, the matrix shapes and one G1 point per pack
//! ([`layout::plan`]). Opening proof: the evaluations the packs need beyond
//! those requested (a pack opens every column at the union of its matrices'
//! points) and the two SHPLONK witnesses.
//!
//! Transcript order inside [`Pcs::open`]/[`Pcs::verify`]: domain tag; every
//! round's commitment (shapes and pack points) and opening points; every
//! pack's evaluation rows; then `γ`, `[W₁]`, `z`, `[W₂]`. Every claimed value
//! is absorbed before the first batching challenge.

use std::borrow::Cow;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

use ark_ec::CurveGroup;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use multi_stark::traits::{
  Algebra, EvaluationDomain, OpenedValues, OpeningRounds, Pcs, Transcript,
  TwoAdicField, VerifyRounds,
};
use p3_matrix::dense::RowMajorMatrix;
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use super::coefficients::Column;
use super::curve::{Fr, G1_COMPRESSED_BYTES, G1Affine, read_g1_compressed};
use super::pcs::{CoefficientData, CommittedMatrix};
use super::shplonk::{self, Coefficients, PackClaim, PackPolynomial};
use super::{KzgPcs, KzgTranscript, Radix2Coset, Scalar, Srs, VerifierParams};

pub mod config;
pub mod layout;

pub use config::PackedShplonkConfig;

const OPEN_DOMAIN: &[u8] = b"ix/kzg/packed-shplonk-pcs/open/v1\0";
const COMMITMENT_MAGIC: &[u8; 8] = b"IXPSHC02";
const PROOF_MAGIC: &[u8; 8] = b"IXPSHP01";
const MAX_BYTES: usize = 64 << 20;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MatrixShape {
  pub log_size: u8,
  pub width: u32,
  /// Prover-declared next-row class used only by pack planning.
  pub next_row: bool,
}

/// One round: every matrix shape, then one point per planned pack.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Commitment {
  pub matrices: Vec<MatrixShape>,
  pub packs: Vec<G1Affine>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Proof {
  /// Pack evaluations not requested by their matrix, in round, pack, point,
  /// column order.
  pub extra_values: Vec<Scalar>,
  pub opening: shplonk::Proof,
}

fn take<'a>(input: &mut &'a [u8], n: usize) -> Result<&'a [u8], String> {
  if input.len() < n {
    return Err("truncated packed encoding".into());
  }
  let (head, tail) = input.split_at(n);
  *input = tail;
  Ok(head)
}

fn count(input: &mut &[u8], element: usize) -> Result<usize, String> {
  let n = u32::from_le_bytes(take(input, 4)?.try_into().unwrap()) as usize;
  if n > input.len() / element {
    return Err("invalid packed element count".into());
  }
  Ok(n)
}

fn point(input: &mut &[u8]) -> Result<G1Affine, String> {
  read_g1_compressed(input).map_err(|error| error.to_string())
}

fn length(n: usize) -> Result<[u8; 4], String> {
  Ok(u32::try_from(n).map_err(|_error| "packed count overflow")?.to_le_bytes())
}

impl Commitment {
  pub fn to_bytes(&self) -> Result<Vec<u8>, String> {
    let mut out = COMMITMENT_MAGIC.to_vec();
    out.extend(length(self.matrices.len())?);
    for matrix in &self.matrices {
      out.push(matrix.log_size);
      out.extend(matrix.width.to_le_bytes());
      out.push(u8::from(matrix.next_row));
    }
    out.extend(length(self.packs.len())?);
    for pack in &self.packs {
      pack.serialize_compressed(&mut out).map_err(|e| e.to_string())?;
    }
    Ok(out)
  }

  pub fn from_bytes(mut input: &[u8]) -> Result<Self, String> {
    if input.len() > MAX_BYTES || take(&mut input, 8)? != COMMITMENT_MAGIC {
      return Err("invalid packed commitment format".into());
    }
    let n = count(&mut input, 6)?;
    let mut matrices = Vec::with_capacity(n);
    for _ in 0..n {
      let log_size = take(&mut input, 1)?[0];
      let width = u32::from_le_bytes(take(&mut input, 4)?.try_into().unwrap());
      let next_row = match take(&mut input, 1)?[0] {
        0 => false,
        1 => true,
        _ => return Err("invalid packed matrix class".into()),
      };
      if usize::from(log_size) > Scalar::TWO_ADICITY || width == 0 {
        return Err("invalid packed matrix shape".into());
      }
      matrices.push(MatrixShape { log_size, width, next_row });
    }
    let n = count(&mut input, G1_COMPRESSED_BYTES)?;
    let packs = (0..n).map(|_| point(&mut input)).collect::<Result<_, _>>()?;
    if !input.is_empty() {
      return Err("trailing packed commitment bytes".into());
    }
    Ok(Self { matrices, packs })
  }

  fn dimensions(&self) -> Vec<layout::Dimension> {
    self
      .matrices
      .iter()
      .map(|m| (1usize << m.log_size, m.width as usize, m.next_row))
      .collect()
  }
}

impl Proof {
  pub fn to_bytes(&self) -> Result<Vec<u8>, String> {
    let mut out = PROOF_MAGIC.to_vec();
    out.extend(length(self.extra_values.len())?);
    for value in &self.extra_values {
      value.0.serialize_compressed(&mut out).map_err(|e| e.to_string())?;
    }
    for w in [&self.opening.w1, &self.opening.w2] {
      w.serialize_compressed(&mut out).map_err(|e| e.to_string())?;
    }
    Ok(out)
  }

  pub fn from_bytes(mut input: &[u8]) -> Result<Self, String> {
    if input.len() > MAX_BYTES || take(&mut input, 8)? != PROOF_MAGIC {
      return Err("invalid packed proof format".into());
    }
    let n = count(&mut input, 32)?;
    let extra_values = (0..n)
      .map(|_| {
        Fr::deserialize_compressed(&mut input)
          .map(Scalar::new)
          .map_err(|e| e.to_string())
      })
      .collect::<Result<_, _>>()?;
    let w1 = point(&mut input)?;
    let w2 = point(&mut input)?;
    if !input.is_empty() {
      return Err("trailing packed proof bytes".into());
    }
    Ok(Self { extra_values, opening: shplonk::Proof { w1, w2 } })
  }
}

macro_rules! bytes_serde {
  ($type:ty) => {
    impl Serialize for $type {
      fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        self.to_bytes().map_err(serde::ser::Error::custom)?.serialize(s)
      }
    }
    impl<'de> Deserialize<'de> for $type {
      fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        Self::from_bytes(&Vec::<u8>::deserialize(d)?)
          .map_err(serde::de::Error::custom)
      }
    }
  };
}
bytes_serde!(Commitment);
bytes_serde!(Proof);

#[derive(Clone)]
pub struct PackedTranscript(pub KzgTranscript);

impl Transcript for PackedTranscript {
  type F = Scalar;
  type Challenge = Scalar;
  type Commitment = Commitment;
  fn observe_field(&mut self, value: Scalar) {
    self.0.observe_field(value);
  }
  fn observe_field_slice(&mut self, values: &[Scalar]) {
    self.0.observe_field_slice(values);
  }
  fn observe_challenge(&mut self, value: Scalar) {
    self.0.observe_challenge(value);
  }
  fn sample_challenge(&mut self) -> Scalar {
    self.0.sample_challenge()
  }
  fn observe_commitment(&mut self, commitment: Commitment) {
    self.0.observe_bytes(&commitment.to_bytes().expect("bounded commitment"));
  }
}

pub struct ProverData {
  matrices: Vec<CommittedMatrix>,
  layout: Vec<layout::Pack>,
  commitment: Commitment,
}

impl CoefficientData<super::Bn254> for ProverData {
  fn matrix(&self, index: usize) -> Option<&CommittedMatrix> {
    self.matrices.get(index)
  }
}

/// Cumulative wall time spent in this PCS's commitments and openings.
#[derive(Default, Debug)]
pub struct Timings {
  commit_nanos: AtomicU64,
  open_nanos: AtomicU64,
}

impl Timings {
  pub fn commit_seconds(&self) -> f64 {
    std::time::Duration::from_nanos(self.commit_nanos.load(Ordering::Relaxed))
      .as_secs_f64()
  }
  pub fn open_seconds(&self) -> f64 {
    std::time::Duration::from_nanos(self.open_nanos.load(Ordering::Relaxed))
      .as_secs_f64()
  }
  fn add(counter: &AtomicU64, started: std::time::Instant) {
    let nanos = u64::try_from(started.elapsed().as_nanos()).unwrap_or(u64::MAX);
    counter.fetch_add(nanos, Ordering::Relaxed);
  }
}

#[derive(Clone)]
pub struct PackedShplonkPcs {
  base: Arc<KzgPcs>,
  timings: Arc<Timings>,
  /// A commitment computed earlier for the next [`Pcs::commit`] call (the
  /// preprocessed round), used instead of its multi-scalar multiplications
  /// when the round's matrix shapes and pack count match. It affects only
  /// proving: a wrong commitment yields a key the verifier's pin rejects.
  preloaded: Arc<std::sync::Mutex<Option<Commitment>>>,
}

/// Distinct points requested by any matrix of `pack`, in first-appearance
/// order.
fn pack_points(pack: &layout::Pack, points: &[Vec<Scalar>]) -> Vec<Scalar> {
  let mut union = vec![];
  for columns in &pack.columns {
    for &point in &points[columns.matrix] {
      if !union.contains(&point) {
        union.push(point);
      }
    }
  }
  union
}

fn observe_round(
  commitment: &Commitment,
  points: &[Vec<Scalar>],
  transcript: &mut PackedTranscript,
) {
  transcript.observe_commitment(commitment.clone());
  transcript.0.observe_canonical(&(points.len() as u64));
  for points in points {
    transcript.0.observe_canonical(&(points.len() as u64));
    transcript.observe_field_slice(points);
  }
}

enum Held<'a> {
  Constant(Fr),
  Loaded(Cow<'a, [Fr]>),
}

impl Held<'_> {
  fn view(&self) -> Coefficients<'_> {
    match self {
      Self::Constant(value) => Coefficients::Constant(*value),
      Self::Loaded(values) => Coefficients::Dense(values),
    }
  }
}

fn hold(column: &Column) -> Held<'_> {
  match column {
    Column::Constant { value, .. } => Held::Constant(*value),
    _ => Held::Loaded(column.load().expect("trusted coefficient storage")),
  }
}

fn hold_pack<'a>(
  pack: &layout::Pack,
  matrices: &'a [CommittedMatrix],
) -> Vec<Held<'a>> {
  pack
    .columns
    .iter()
    .flat_map(|columns| {
      columns
        .source
        .clone()
        .map(move |c| hold(&matrices[columns.matrix].coefficient_columns()[c]))
    })
    .collect()
}

impl PackedShplonkPcs {
  pub fn new(srs: Arc<Srs>, cap: usize, quotient_degree: usize) -> Self {
    Self {
      base: Arc::new(KzgPcs::with_max_trace_len(srs, cap, quotient_degree)),
      timings: Arc::default(),
      preloaded: Arc::default(),
    }
  }

  pub fn verifier_only(params: VerifierParams, quotient_degree: usize) -> Self {
    Self {
      base: Arc::new(KzgPcs::verifier_only(params, quotient_degree)),
      timings: Arc::default(),
      preloaded: Arc::default(),
    }
  }

  pub fn parameters(&self) -> &VerifierParams {
    self.base.verifier_params()
  }

  pub fn timings(&self) -> &Timings {
    &self.timings
  }

  /// Supplies the commitment of the next [`Pcs::commit`] round (see
  /// `preloaded`). It is consumed by that call whether or not it matches.
  pub fn preload_commitment(&self, commitment: Commitment) {
    *self.preloaded.lock().expect("preloaded commitment lock") =
      Some(commitment);
  }

  /// The pack plan of a commitment, after checking its pack count and points.
  pub fn layout(
    &self,
    commitment: &Commitment,
  ) -> Result<Vec<layout::Pack>, String> {
    let cap = self.parameters().max_trace_len();
    let dimensions = commitment.dimensions();
    if dimensions.iter().any(|&(height, _, _)| height > cap) {
      return Err("packed height exceeds capacity".into());
    }
    if layout::count(&dimensions, cap) != Some(commitment.packs.len()) {
      return Err("wrong packed commitment count".into());
    }
    if commitment.packs.iter().any(|p| {
      !p.is_on_curve() || !p.is_in_correct_subgroup_assuming_on_curve()
    }) {
      return Err("invalid packed commitment point".into());
    }
    layout::plan(&dimensions, cap)
  }

  /// Commit one round of coefficient matrices, in round order, declaring
  /// every matrix a next-row reader (planning by height alone).
  fn commit_matrices(
    &self,
    matrices: Vec<CommittedMatrix>,
  ) -> (Commitment, ProverData) {
    let classes = vec![true; matrices.len()];
    self.commit_classified(matrices, &classes)
  }

  /// Commit one round with each matrix's declared next-row class.
  fn commit_classified(
    &self,
    matrices: Vec<CommittedMatrix>,
    next_rows: &[bool],
  ) -> (Commitment, ProverData) {
    self.commit_known(matrices, next_rows, None)
  }

  fn commit_known(
    &self,
    matrices: Vec<CommittedMatrix>,
    next_rows: &[bool],
    known: Option<Commitment>,
  ) -> (Commitment, ProverData) {
    assert_eq!(matrices.len(), next_rows.len(), "one class per matrix");
    let started = std::time::Instant::now();
    let dimensions: Vec<_> = matrices
      .iter()
      .zip(next_rows)
      .map(|(m, &next)| (m.domain().size(), m.width(), next))
      .collect();
    let plan = layout::plan(&dimensions, self.parameters().max_trace_len())
      .expect("admitted packed dimensions");
    let shapes: Vec<MatrixShape> = matrices
      .iter()
      .zip(next_rows)
      .map(|(m, &next_row)| MatrixShape {
        log_size: u8::try_from(m.domain().log_size).expect("trace domain"),
        width: u32::try_from(m.width()).expect("matrix width"),
        next_row,
      })
      .collect();
    if let Some(known) = known {
      if known.matrices == shapes && known.packs.len() == plan.len() {
        Timings::add(&self.timings.commit_nanos, started);
        tracing::info!(
          packs = known.packs.len(),
          "packed SHPLONK round from a preloaded commitment"
        );
        return (
          known.clone(),
          ProverData { matrices, layout: plan, commitment: known },
        );
      }
      tracing::warn!(
        "preloaded packed commitment does not match the round; committing"
      );
    }
    let interleave = |pack: &layout::Pack| {
      let held = hold_pack(pack, &matrices);
      PackPolynomial {
        height: pack.height,
        columns: held.iter().map(Held::view).collect(),
      }
      .interleave()
    };
    // The next pack is interleaved on the host while the current pack's
    // MSM runs, which keeps at most two packs' coefficients alive.
    let mut packs = Vec::with_capacity(plan.len());
    let mut next = plan.first().map(interleave);
    for following in plan.iter().skip(1).map(Some).chain([None]) {
      let current = next.take().expect("pack interleaved");
      let (point, interleaved) = p3_maybe_rayon::prelude::join(
        || self.base.msm(&current),
        || following.map(interleave),
      );
      packs.push(point);
      next = interleaved;
    }
    let commitment = Commitment {
      matrices: shapes,
      packs: super::curve::G1Projective::normalize_batch(&packs),
    };
    Timings::add(&self.timings.commit_nanos, started);
    tracing::info!(
      packs = commitment.packs.len(),
      seconds = started.elapsed().as_secs_f64(),
      "packed SHPLONK round committed"
    );
    (commitment.clone(), ProverData { matrices, layout: plan, commitment })
  }
}

impl Pcs for PackedShplonkPcs {
  type F = Scalar;
  type Challenge = Scalar;
  type Domain = Radix2Coset;
  type Challenger = PackedTranscript;
  type Commitment = Commitment;
  type ProverData = ProverData;
  type Proof = Proof;
  type Error = String;
  type Evaluations<'a> = RowMajorMatrix<Scalar>;

  fn natural_domain_for_degree(&self, degree: usize) -> Radix2Coset {
    self.base.natural_domain_for_degree(degree)
  }

  fn max_quotient_degree(&self) -> usize {
    self.base.max_quotient_degree()
  }

  fn commit(
    &self,
    evaluations: Vec<(Radix2Coset, RowMajorMatrix<Scalar>)>,
  ) -> (Commitment, ProverData) {
    let matrices: Vec<_> = evaluations
      .into_iter()
      .map(|(domain, matrix)| {
        KzgPcs::<super::Bn254>::interpolate_columns(domain, matrix)
      })
      .collect();
    let classes = vec![true; matrices.len()];
    let known =
      self.preloaded.lock().expect("preloaded commitment lock").take();
    self.commit_known(matrices, &classes, known)
  }

  fn commit_quotient(
    &self,
    quotients: Vec<(Radix2Coset, RowMajorMatrix<Scalar>, usize)>,
  ) -> (Commitment, ProverData) {
    let next_rows = vec![false; quotients.len()];
    self.commit_classified(
      quotients
        .into_iter()
        .map(|(domain, matrix, degree)| {
          KzgPcs::<super::Bn254>::interpolate_quotient(domain, matrix, degree)
        })
        .collect(),
      &next_rows,
    )
  }

  fn get_evaluations_on_domain(
    &self,
    data: &ProverData,
    index: usize,
    domain: Radix2Coset,
  ) -> RowMajorMatrix<Scalar> {
    let matrix = &data.matrices[index];
    self.base.evaluate_matrix_columns(
      matrix,
      domain,
      &(0..matrix.width()).collect::<Vec<_>>(),
    )
  }

  fn open(
    &self,
    rounds: OpeningRounds<'_, ProverData, Scalar>,
    transcript: &mut PackedTranscript,
  ) -> (OpenedValues<Scalar>, Proof) {
    let started = std::time::Instant::now();
    transcript.0.observe_bytes(OPEN_DOMAIN);
    transcript.0.observe_canonical(&(rounds.len() as u64));
    for (data, points) in &rounds {
      assert_eq!(data.matrices.len(), points.len());
      observe_round(&data.commitment, points, transcript);
    }
    let mut opened = vec![];
    let mut extra_values = vec![];
    let mut held = vec![];
    let mut claims = vec![];
    for (data, points) in &rounds {
      let mut round: Vec<_> = points
        .iter()
        .zip(&data.matrices)
        .map(|(points, m)| vec![vec![Scalar::ZERO; m.width()]; points.len()])
        .collect();
      for pack in &data.layout {
        let queries = pack_points(pack, points);
        if queries.is_empty() {
          continue;
        }
        let columns = hold_pack(pack, &data.matrices);
        let polynomial = PackPolynomial {
          height: pack.height,
          columns: columns.iter().map(Held::view).collect(),
        };
        let values: Vec<_> =
          queries.iter().map(|q| polynomial.evaluate(q.0)).collect();
        for (row, &query) in values.iter().zip(&queries) {
          let mut source = 0;
          for columns in &pack.columns {
            let matches: Vec<_> = points[columns.matrix]
              .iter()
              .enumerate()
              .filter_map(|(i, &p)| (p == query).then_some(i))
              .collect();
            for column in columns.source.clone() {
              let value = Scalar::new(row[source]);
              if matches.is_empty() {
                extra_values.push(value);
              }
              for &i in &matches {
                round[columns.matrix][i][column] = value;
              }
              source += 1;
            }
          }
          transcript.observe_field_slice(
            &row.iter().copied().map(Scalar::new).collect::<Vec<_>>(),
          );
        }
        claims.push(PackClaim {
          width: pack.width,
          points: queries.iter().map(|q| q.0).collect(),
          values,
        });
        held.push((pack.height, columns));
      }
      opened.push(round);
    }
    tracing::info!(
      seconds = started.elapsed().as_secs_f64(),
      "packed SHPLONK evaluations"
    );
    let polynomials: Vec<_> = held
      .iter()
      .map(|(height, columns)| PackPolynomial {
        height: *height,
        columns: columns.iter().map(Held::view).collect(),
      })
      .collect();
    let pairs: Vec<_> = polynomials.iter().zip(&claims).collect();
    let opening = shplonk::open(&self.base, &pairs, &mut transcript.0);
    Timings::add(&self.timings.open_nanos, started);
    (opened, Proof { extra_values, opening })
  }

  fn verify(
    &self,
    rounds: VerifyRounds<Commitment, Radix2Coset, Scalar>,
    proof: &Proof,
    transcript: &mut PackedTranscript,
  ) -> Result<(), String> {
    let mut plans = vec![];
    let mut queries = vec![];
    for (commitment, matrices) in &rounds {
      if matrices.len() != commitment.matrices.len() {
        return Err("wrong packed matrix count".into());
      }
      for ((domain, openings), shape) in
        matrices.iter().zip(&commitment.matrices)
      {
        if domain.log_size != usize::from(shape.log_size)
          || domain.shift != <Scalar as Algebra<Scalar>>::ONE
          || openings.iter().any(|(_, v)| v.len() != shape.width as usize)
        {
          return Err("wrong packed matrix opening shape".into());
        }
      }
      plans.push(self.layout(commitment)?);
      queries.push(
        matrices
          .iter()
          .map(|(_, openings)| openings.iter().map(|(p, _)| *p).collect())
          .collect::<Vec<Vec<_>>>(),
      );
    }
    transcript.0.observe_bytes(OPEN_DOMAIN);
    transcript.0.observe_canonical(&(rounds.len() as u64));
    for ((commitment, _), points) in rounds.iter().zip(&queries) {
      observe_round(commitment, points, transcript);
    }
    let mut extras = proof.extra_values.iter();
    let mut packs = vec![];
    for (((commitment, matrices), plan), points) in
      rounds.iter().zip(&plans).zip(&queries)
    {
      for (pack, &point) in plan.iter().zip(&commitment.packs) {
        let pack_queries = pack_points(pack, points);
        if pack_queries.is_empty() {
          continue;
        }
        let mut values = vec![];
        for &query in &pack_queries {
          let mut row = Vec::with_capacity(pack.width);
          for columns in &pack.columns {
            for column in columns.source.clone() {
              let mut matches =
                matrices[columns.matrix].1.iter().filter(|(p, _)| *p == query);
              let value = if let Some((_, first)) = matches.next() {
                if matches.any(|(_, next)| next[column] != first[column]) {
                  return Err("conflicting repeated packed evaluation".into());
                }
                first[column]
              } else {
                *extras.next().ok_or("missing extra packed evaluation")?
              };
              row.push(value);
            }
          }
          transcript.observe_field_slice(&row);
          values.push(row.into_iter().map(|v| v.0).collect());
        }
        packs.push((
          point,
          PackClaim {
            width: pack.width,
            points: pack_queries.iter().map(|q| q.0).collect(),
            values,
          },
        ));
      }
    }
    if extras.next().is_some() {
      return Err("unused extra packed evaluations".into());
    }
    let packs: Vec<_> = packs.iter().map(|(c, claim)| (*c, claim)).collect();
    let pair = shplonk::verify_deferred(
      self.parameters().g1[0],
      &packs,
      &proof.opening,
      &mut transcript.0,
    )
    .map_err(|error| format!("packed SHPLONK opening: {error:?}"))?;
    if !shplonk::pairing_holds(self.parameters(), pair) {
      return Err(format!(
        "packed SHPLONK opening: {:?}",
        shplonk::Error::PairingCheckFailed
      ));
    }
    CAPTURED.with(|captured| {
      let mut captured = captured.borrow_mut();
      if !matches!(*captured, Capture::Idle) {
        *captured = Capture::Captured(Box::new(Verified {
          transcript: transcript.clone(),
          pair,
        }));
      }
    });
    Ok(())
  }
}

/// The state an accepted packed opening leaves: the transcript after `[W₂]`
/// and the deferred pairing pair `(A, B)` with `e(A, [1]₂)·e(B, [τ]₂) = 1`.
#[derive(Clone)]
pub struct Verified {
  pub transcript: PackedTranscript,
  pub pair: [G1Affine; 2],
}

/// This thread's [`capture_verification`] state.
enum Capture {
  /// No capture is running.
  Idle,
  /// A capture is running and no packed opening has been verified yet.
  Armed,
  /// A capture is running and holds the last verified opening.
  Captured(Box<Verified>),
}

std::thread_local! {
  static CAPTURED: std::cell::RefCell<Capture> =
    const { std::cell::RefCell::new(Capture::Idle) };
}

/// Runs `verify`, which must verify one multi-stark proof with this PCS on
/// the current thread, and returns what its packed opening left. Multi-stark
/// samples no challenge after the PCS opening, so the returned transcript is
/// the verifier's final transcript: it has absorbed every commitment, claim,
/// accumulator, evaluation and opening witness of the proof.
pub fn capture_verification<E: std::fmt::Debug>(
  verify: impl FnOnce() -> Result<(), E>,
) -> Result<Verified, String> {
  struct Reset;
  impl Drop for Reset {
    fn drop(&mut self) {
      CAPTURED.with(|captured| captured.replace(Capture::Idle));
    }
  }
  CAPTURED.with(|captured| {
    let mut captured = captured.borrow_mut();
    if !matches!(*captured, Capture::Idle) {
      return Err("nested packed verification capture".to_string());
    }
    *captured = Capture::Armed;
    Ok(())
  })?;
  let reset = Reset;
  let result = verify();
  let verified = match CAPTURED.with(|captured| captured.replace(Capture::Idle))
  {
    Capture::Captured(verified) => Some(*verified),
    Capture::Idle | Capture::Armed => None,
  };
  drop(reset);
  result.map_err(|error| format!("packed verification failed: {error:?}"))?;
  verified.ok_or_else(|| "no packed opening was verified".to_string())
}

#[cfg(test)]
#[path = "packed_shplonk/tests.rs"]
mod tests;
