use super::*;
use crate::kzg::{KzgConfig, TranscriptKind};
use multi_stark::config::ProofConfig;
use multi_stark::traits::TwoAdicField;
use std::sync::Mutex;

/// [`ProofConfig`] over [`PackedShplonkPcs`]. Next-row classes for pack
/// planning: main matrices as set by [`Self::set_main_next_rows`], lookup
/// accumulators always next-row (they chain across rows), quotient chunks
/// never; both quotient paths and both lookup paths declare the same classes.
/// Quotients and lookups use the
/// portable multi-stark host paths unless streaming is selected, which
/// builds them per circuit from committed columns (on the device under the
/// `cuda` feature) exactly as [`KzgConfig`] does. Streaming changes memory
/// use and speed, not the proof.
#[derive(Clone)]
pub struct PackedShplonkConfig {
  pcs: PackedShplonkPcs,
  kind: TranscriptKind,
  key_digest: Option<[u8; 32]>,
  seed: Vec<u8>,
  stream_lookups: bool,
  stream_quotient: bool,
  main_next_rows: Arc<Mutex<Option<Vec<bool>>>>,
}

impl PackedShplonkConfig {
  pub fn new(srs: Arc<Srs>, quotient_degree: usize) -> Self {
    let cap = srs.max_len();
    Self::with_max_trace_len(srs, cap, quotient_degree)
  }

  pub fn with_max_trace_len(
    srs: Arc<Srs>,
    cap: usize,
    quotient_degree: usize,
  ) -> Self {
    Self::from_pcs(PackedShplonkPcs::new(srs, cap, quotient_degree))
  }

  pub fn verifier_only(params: VerifierParams, quotient_degree: usize) -> Self {
    Self::from_pcs(PackedShplonkPcs::verifier_only(params, quotient_degree))
  }

  fn from_pcs(pcs: PackedShplonkPcs) -> Self {
    let mut config = Self {
      pcs,
      kind: TranscriptKind::Blake3,
      key_digest: None,
      seed: vec![],
      stream_lookups: false,
      stream_quotient: false,
      main_next_rows: Arc::default(),
    };
    config.reseed();
    config
  }

  /// The column-PCS seed (setup anchors, trace cap, quotient budget, key)
  /// followed by this protocol's tag, so the two never share challenges.
  fn reseed(&mut self) {
    let mut base = KzgConfig::verifier_only(
      self.pcs.parameters().clone(),
      self.pcs.max_quotient_degree(),
    )
    .with_transcript(self.kind);
    if let Some(digest) = self.key_digest {
      base = base.with_key_digest(digest);
    }
    self.seed = base.transcript_seed().to_vec();
    self.seed.extend_from_slice(b"ix/multi-stark/packed-shplonk/v1\0");
  }

  pub fn with_transcript(mut self, kind: TranscriptKind) -> Self {
    self.kind = kind;
    self.reseed();
    self
  }

  pub fn with_key_digest(mut self, digest: [u8; 32]) -> Self {
    self.key_digest = Some(digest);
    self.reseed();
    self
  }

  pub fn transcript_seed(&self) -> &[u8] {
    &self.seed
  }

  /// Rebuild each circuit's lookup trace from committed columns; see
  /// [`KzgConfig::with_streaming_lookups`].
  pub fn with_streaming_lookups(mut self) -> Self {
    self.stream_lookups = true;
    self
  }

  /// Whether lookup messages can be rebuilt from committed stage-one traces.
  pub const fn uses_streaming_lookups(&self) -> bool {
    self.stream_lookups
  }

  /// Declare the next-row class of each main-trace matrix of the next proof,
  /// one per active circuit in circuit order. The next main commitment
  /// consumes it; without it every main matrix is declared a next-row reader.
  /// Classes only steer pack planning (see [`super::layout`]).
  pub fn set_main_next_rows(&self, next_rows: Vec<bool>) {
    *self.main_next_rows.lock().expect("main class lock") = Some(next_rows);
  }

  /// Evaluate each quotient on trace-sized cosets; see
  /// [`KzgConfig::with_streaming_quotient`].
  pub fn with_streaming_quotient(mut self) -> Self {
    self.stream_quotient = true;
    self
  }
}

impl ProofConfig for PackedShplonkConfig {
  type Pcs = PackedShplonkPcs;
  type Challenge = Scalar;
  type Challenger = PackedTranscript;

  fn pcs(&self) -> &PackedShplonkPcs {
    &self.pcs
  }

  fn accelerated_lookup_commit(
    &self,
    inputs: &[multi_stark::config::LookupCommitInput<'_, Self>],
    beta: Scalar,
    gamma: Scalar,
    mut acc: Scalar,
  ) -> Option<multi_stark::config::AcceleratedLookupCommitment<Self>> {
    if !self.stream_lookups {
      return None;
    }
    let parts = crate::kzg::config::lookup_parts::<crate::kzg::Bn254, _, _>(
      &self.pcs.base,
      inputs,
      beta,
      gamma,
      |matrix| matrix,
    );
    let mut matrices = Vec::with_capacity(parts.len());
    let mut accumulators = Vec::with_capacity(parts.len());
    for (matrix, local) in parts {
      matrices.push(matrix);
      acc += local;
      accumulators.push(acc);
    }
    let (commitment, data) = self.pcs.commit_matrices(matrices);
    Some((commitment, data, accumulators))
  }

  fn accelerated_quotient_commit(
    &self,
    inputs: &[multi_stark::config::QuotientCommitInput<'_, Self>],
    alpha: Scalar,
  ) -> Option<(Commitment, ProverData)> {
    if !self.stream_quotient {
      return None;
    }
    let matrices =
      crate::kzg::config::quotient_parts::<crate::kzg::Bn254, _, _>(
      &self.pcs.base,
      inputs,
      alpha,
      |matrix| matrix,
    );
    let next_rows = vec![false; matrices.len()];
    Some(self.pcs.commit_classified(matrices, &next_rows))
  }

  fn commit_main(
    &self,
    evaluations: Vec<(Radix2Coset, multi_stark::witness::TraceSource<Scalar>)>,
  ) -> (Commitment, ProverData) {
    let matrices: Vec<_> = evaluations
      .into_iter()
      .map(|(domain, trace)| {
        KzgPcs::<crate::kzg::Bn254>::interpolate_columns(domain, trace.materialize())
      })
      .collect();
    let next_rows = self
      .main_next_rows
      .lock()
      .expect("main class lock")
      .take()
      .filter(|classes| classes.len() == matrices.len())
      .unwrap_or_else(|| vec![true; matrices.len()]);
    self.pcs.commit_classified(matrices, &next_rows)
  }

  fn initialise_challenger(&self) -> PackedTranscript {
    let mut transcript = PackedTranscript(KzgTranscript::new(self.kind));
    transcript.0.observe_bytes(&self.seed);
    transcript
  }

  fn max_log_degree(&self) -> usize {
    self.pcs.parameters().max_trace_len().ilog2() as usize
  }

  fn max_log_quotient_domain(&self) -> usize {
    Scalar::TWO_ADICITY
  }

  fn max_quotient_degree(&self) -> usize {
    self.pcs.max_quotient_degree()
  }

  fn log_blowup(&self) -> usize {
    0
  }

  fn omit_unused_next_row_openings(&self) -> bool {
    true
  }

  fn omit_inactive_preprocessed_openings(&self) -> bool {
    true
  }

  fn committed_trace(
    &self,
    data: &ProverData,
    index: usize,
    degree: usize,
  ) -> Option<RowMajorMatrix<Scalar>> {
    Some(self.pcs.get_evaluations_on_domain(
      data,
      index,
      self.pcs.natural_domain_for_degree(degree),
    ))
  }
}
