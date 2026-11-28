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
pub struct PackedShplonkConfig<C: KzgCurve = Bn254> {
  pcs: PackedShplonkPcs<C>,
  kind: TranscriptKind,
  key_digest: Option<[u8; 32]>,
  seed: Vec<u8>,
  stream_lookups: bool,
  stream_quotient: bool,
  main_next_rows: Arc<Mutex<Option<Vec<bool>>>>,
}

impl<C: KzgCurve> PackedShplonkConfig<C> {
  pub fn new(srs: Arc<Srs<C>>, quotient_degree: usize) -> Self {
    let cap = srs.max_len();
    Self::with_max_trace_len(srs, cap, quotient_degree)
  }

  pub fn with_max_trace_len(
    srs: Arc<Srs<C>>,
    cap: usize,
    quotient_degree: usize,
  ) -> Self {
    Self::from_pcs(PackedShplonkPcs::new(srs, cap, quotient_degree))
  }

  pub fn verifier_only(
    params: VerifierParams<C>,
    quotient_degree: usize,
  ) -> Self {
    Self::from_pcs(PackedShplonkPcs::verifier_only(params, quotient_degree))
  }

  fn from_pcs(pcs: PackedShplonkPcs<C>) -> Self {
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
    let mut base = KzgConfig::<C>::verifier_only(
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

  pub fn key_digest(&self) -> Option<&[u8; 32]> {
    self.key_digest.as_ref()
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

/// Populate `system.vk_digest` from `system.circuits` and bind the canonical
/// verifying-key digest (covering `vk_digest`, `preprocessed_indices`, and
/// `preprocessed_commit`) into `system.config`'s transcript seed when no key
/// digest is already bound.
pub fn bind_packed_system_key<C: KzgCurve>(
  system: &mut multi_stark::system::System<PackedShplonkConfig<C>>,
) {
  let vk_digest = multi_stark::system::compute_vk_digest::<
    CurveScalar<C>,
    CurveScalar<C>,
  >(&system.circuits);
  system.vk_digest = vk_digest;
  if system.config.key_digest().is_some() {
    return;
  }
  let mut hasher = blake3::Hasher::new();
  hasher.update(b"ix/packed-shplonk/system-key/v1\0");
  hasher.update(&vk_digest);
  hasher.update(&(system.preprocessed_indices.len() as u64).to_le_bytes());
  for idx in &system.preprocessed_indices {
    match idx {
      Some(i) => {
        hasher.update(&[1u8]);
        hasher.update(&(*i as u64).to_le_bytes());
      },
      None => {
        hasher.update(&[0u8]);
      },
    }
  }
  match &system.preprocessed_commit {
    Some(commit) => {
      hasher.update(&[1u8]);
      hasher.update(&(commit.matrices.len() as u64).to_le_bytes());
      for shape in &commit.matrices {
        hasher.update(&[shape.log_size, u8::from(shape.next_row)]);
        hasher.update(&shape.width.to_le_bytes());
      }
      hasher.update(&(commit.packs.len() as u64).to_le_bytes());
      for point in &commit.packs {
        let mut buf = Vec::with_capacity(C::G1_COMPRESSED_BYTES);
        point
          .serialize_compressed(&mut buf)
          .expect("compressed G1 serialization");
        hasher.update(&buf);
      }
    },
    None => {
      hasher.update(&[0u8]);
    },
  }
  let digest = *hasher.finalize().as_bytes();
  system.config = system.config.clone().with_key_digest(digest);
}

impl<C: KzgCurve> crate::kzg::config::BindSystemKeyDigest
  for PackedShplonkConfig<C>
{
  fn bind_system_key_digest(system: &mut multi_stark::system::System<Self>) {
    bind_packed_system_key(system);
  }
}

impl<C: KzgCurve> ProofConfig for PackedShplonkConfig<C> {
  type Pcs = PackedShplonkPcs<C>;
  type Challenge = CurveScalar<C>;
  type Challenger = PackedTranscript<C>;

  fn pcs(&self) -> &PackedShplonkPcs<C> {
    &self.pcs
  }

  fn accelerated_lookup_commit(
    &self,
    inputs: &[multi_stark::config::LookupCommitInput<'_, Self>],
    beta: CurveScalar<C>,
    gamma: CurveScalar<C>,
    mut acc: CurveScalar<C>,
  ) -> Option<multi_stark::config::AcceleratedLookupCommitment<Self>> {
    if !self.stream_lookups {
      return None;
    }
    let parts = crate::kzg::config::lookup_parts::<C, _, _>(
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
    alpha: CurveScalar<C>,
  ) -> Option<(Commitment<C>, ProverData<C>)> {
    if !self.stream_quotient {
      return None;
    }
    let matrices = crate::kzg::config::quotient_parts::<C, _, _>(
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
    evaluations: Vec<(
      Radix2Coset<C>,
      multi_stark::witness::TraceSource<CurveScalar<C>>,
    )>,
  ) -> (Commitment<C>, ProverData<C>) {
    let matrices: Vec<_> = evaluations
      .into_iter()
      .map(|(domain, trace)| {
        KzgPcs::<C>::interpolate_columns(domain, trace.materialize())
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

  fn initialise_challenger(&self) -> PackedTranscript<C> {
    let mut transcript = PackedTranscript(KzgTranscript::new(self.kind));
    transcript.0.observe_bytes(&self.seed);
    transcript
  }

  // Protocol v5 keeps `observe_shape` aligned with external verifiers while
  // `bind_packed_system_key` / `with_key_digest` absorbs the canonical
  // `vk_digest` and fixed commitments into `transcript_seed`.
  fn protocol_version(&self) -> multi_stark::config::ProtocolVersion {
    multi_stark::config::ProtocolVersion::V5
  }

  fn initialise_challenger_for_mode(
    &self,
    _mode: multi_stark::config::TranscriptMode,
  ) -> PackedTranscript<C> {
    self.initialise_challenger()
  }

  fn validate_commitment_cap(
    &self,
    _commit: &multi_stark::config::Com<Self>,
    _max_log_lde_height: usize,
  ) -> bool {
    true
  }

  fn max_log_degree(&self) -> usize {
    self.pcs.parameters().max_trace_len().ilog2() as usize
  }

  fn max_log_quotient_domain(&self) -> usize {
    CurveScalar::<C>::TWO_ADICITY
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
    data: &ProverData<C>,
    index: usize,
    degree: usize,
  ) -> Option<RowMajorMatrix<CurveScalar<C>>> {
    Some(self.pcs.get_evaluations_on_domain(
      data,
      index,
      self.pcs.natural_domain_for_degree(degree),
    ))
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::kzg::curve::Bls12381;
  use multi_stark::expr::Expr;
  use multi_stark::system::{CircuitInputs, System, SystemWitness};
  use multi_stark::traits::Field;

  fn check_packed_bind<C: KzgCurve>() {
    let srs = Arc::new(Srs::<C>::unsafe_dev_setup(8, b"packed-vk-bind"));
    let make = |c_val: u64, prep_val: u64| {
      let config = PackedShplonkConfig::<C>::new(srs.clone(), 4);
      let (mut system, pk) = System::new(
        config,
        [CircuitInputs {
          main_width: 1,
          preprocessed: Some(RowMajorMatrix::new_col(vec![
            CurveScalar::<C>::from_u64(prep_val),
            CurveScalar::<C>::ZERO,
          ])),
          constraints: vec![
            Expr::main(0) - Expr::constant(CurveScalar::<C>::from_u64(c_val)),
          ],
          ..Default::default()
        }],
      );
      bind_packed_system_key(&mut system);
      (system, pk)
    };
    let (sys_a, pk_a) = make(5, 1);
    let (sys_b, _) = make(6, 1);
    let (sys_c, _) = make(5, 2);

    assert_ne!(sys_a.vk_digest, [0u8; 32]);
    assert!(sys_a.config.key_digest().is_some());
    assert_ne!(sys_a.vk_digest, sys_b.vk_digest);
    assert_ne!(sys_a.config.transcript_seed(), sys_b.config.transcript_seed());
    assert_eq!(sys_a.vk_digest, sys_c.vk_digest);
    assert_ne!(sys_a.config.transcript_seed(), sys_c.config.transcript_seed());

    let witness = SystemWitness::from_stage_1(
      vec![RowMajorMatrix::new_col(vec![CurveScalar::<C>::from_u64(5); 2])],
      &sys_a,
    );
    let proof = sys_a.prove_multiple_claims(&pk_a, &[], witness);
    sys_a.verify_multiple_claims(&[], &proof).unwrap();
    assert!(sys_b.verify_multiple_claims(&[], &proof).is_err());
    assert!(sys_c.verify_multiple_claims(&[], &proof).is_err());
  }

  #[test]
  fn packed_bind_system_key_binds_circuits_and_fixed_commits() {
    check_packed_bind::<Bn254>();
    check_packed_bind::<Bls12381>();
  }
}
