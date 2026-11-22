//! [`ProofConfig`] instantiation for the KZG backend: BN254's
//! scalar field (its own challenge field, `D = 1`), a selected transcript,
//! monomial KZG commitments.

use std::path::{Path, PathBuf};
use std::sync::Arc;

use ark_serialize::CanonicalSerialize;
use p3_maybe_rayon::prelude::*;

use multi_stark::config::ProofConfig;
use multi_stark::traits::Pcs;

#[cfg(feature = "cuda")]
use super::cuda;
use super::field::Scalar;
use super::pcs::{
  CoefficientConfig, CoefficientData, CommittedMatrix, KzgCommitment, KzgPcs,
  KzgProverData,
};
use super::srs::Srs;
use super::transcript::{KzgTranscript, TranscriptKind};
use multi_stark::config::{LookupCommitInput, QuotientCommitInput};

#[derive(Clone)]
pub struct KzgConfig {
  pcs: KzgPcs,
  /// Bytes observed into every fresh challenger: a domain tag, the trace
  /// cap and quotient budget, the public setup and the four anchor points
  /// (see the transcript contract on [`ProofConfig::initialise_challenger`]).
  transcript_seed: Vec<u8>,
  transcript_kind: TranscriptKind,
  key_digest: Option<[u8; 32]>,
  max_log_degree: usize,
  stream_lookups: bool,
  stream_quotient: bool,
  streaming_chunk_size: Option<usize>,
  spill_dir: Option<PathBuf>,
}

impl KzgConfig {
  /// Public parameters are caller-supplied and taken on trust here:
  /// call [`Srs::validate`] first on parameters you did not generate.
  ///
  /// # Panics
  /// Panics if the SRS length is not a power of two (trace domains
  /// are, and `max_log_degree` is read off the SRS).
  pub fn new(srs: Arc<Srs>, max_quotient_degree: usize) -> Self {
    let max_trace_len = srs.max_len();
    Self::with_max_trace_len(srs, max_trace_len, max_quotient_degree)
  }

  /// Bind the admitted trace cap independently of the loaded public-power prefix.
  pub fn with_max_trace_len(
    srs: Arc<Srs>,
    max_trace_len: usize,
    max_quotient_degree: usize,
  ) -> Self {
    let verifier =
      super::VerifierParams::with_max_trace_len(&srs, max_trace_len);
    let mut config = Self::verifier_only(verifier, max_quotient_degree);
    config.pcs =
      KzgPcs::with_max_trace_len(srs, max_trace_len, max_quotient_degree);
    config
  }

  pub fn transcript_seed(&self) -> &[u8] {
    &self.transcript_seed
  }

  /// Construct a verifier without retaining the proving powers. No proving operation is available.
  pub fn verifier_only(
    params: super::VerifierParams,
    max_quotient_degree: usize,
  ) -> Self {
    let max_log_degree = p3_util::log2_strict_usize(params.max_trace_len());
    assert!(max_quotient_degree.is_power_of_two());
    let transcript_kind = TranscriptKind::Blake3;
    let transcript_seed =
      Self::make_transcript_seed(&params, max_quotient_degree, transcript_kind);
    Self {
      pcs: KzgPcs::verifier_only(params, max_quotient_degree),
      transcript_seed,
      transcript_kind,
      key_digest: None,
      max_log_degree,
      stream_lookups: false,
      stream_quotient: false,
      streaming_chunk_size: None,
      spill_dir: None,
    }
  }

  /// Select the Fiat-Shamir protocol and its parameter-binding domain.
  pub fn with_transcript(mut self, kind: TranscriptKind) -> Self {
    self.transcript_seed = Self::make_transcript_seed(
      self.pcs.verifier_params(),
      self.pcs.max_quotient_degree(),
      kind,
    );
    self.transcript_kind = kind;
    if let Some(digest) = self.key_digest {
      self.transcript_seed.extend_from_slice(b"ix/aiur/kzg-key/v1\0");
      self.transcript_seed.extend_from_slice(&digest);
    }
    self
  }

  /// Bind all proof challenges to an independently defined complete key.
  pub fn with_key_digest(mut self, digest: [u8; 32]) -> Self {
    self.key_digest = Some(digest);
    let kind = self.transcript_kind;
    self.with_transcript(kind)
  }

  pub fn key_digest(&self) -> Option<&[u8; 32]> {
    self.key_digest.as_ref()
  }

  pub fn transcript_kind(&self) -> TranscriptKind {
    self.transcript_kind
  }

  fn make_transcript_seed(
    params: &super::VerifierParams,
    max_quotient_degree: usize,
    kind: TranscriptKind,
  ) -> Vec<u8> {
    let domain: &[u8] = match kind {
      TranscriptKind::Blake3 => b"multi-stark/kzg/bn254/blake3/v1",
      TranscriptKind::Keccak256 => b"multi-stark/kzg/bn254/keccak256/v1",
    };
    let mut seed = domain.to_vec();
    for parameter in
      [p3_util::log2_strict_usize(params.max_trace_len()), max_quotient_degree]
    {
      seed.extend(u64::try_from(parameter).unwrap().to_le_bytes());
    }
    seed.extend((params.public_setup.max_degree as u64).to_le_bytes());
    seed.extend(params.public_setup.id);
    // Proving and portable verification bind the same public anchors.
    params.g1[0].serialize_compressed(&mut seed).expect("Vec serialization");
    params.g2.serialize_compressed(&mut seed).expect("Vec serialization");
    params.g1[1].serialize_compressed(&mut seed).expect("Vec serialization");
    params.tau_g2.serialize_compressed(&mut seed).expect("Vec serialization");
    seed
  }

  /// Reconstruct and commit one lookup trace at a time from committed columns.
  /// This changes memory use, not the proof or its transcript.
  pub fn with_streaming_lookups(mut self) -> Self {
    self.stream_lookups = true;
    self
  }

  #[cfg(not(feature = "cuda"))]
  pub(crate) fn stream_lookups(&self) -> bool {
    self.stream_lookups
  }

  /// Whether lookup messages can be rebuilt from committed stage-one traces.
  pub const fn uses_streaming_lookups(&self) -> bool {
    self.stream_lookups
  }

  /// Evaluate each quotient on trace-sized cosets, bounding temporary matrices.
  pub fn with_streaming_quotient(mut self) -> Self {
    self.stream_quotient = true;
    self
  }

  /// Override streaming row/disk chunk sizes for testing multi-chunk boundaries
  /// at small trace heights. Does not change proofs or transcripts.
  #[doc(hidden)]
  pub fn with_streaming_chunk_size(mut self, chunk: usize) -> Self {
    assert!(chunk > 0, "streaming chunk size must be positive");
    self.streaming_chunk_size = Some(chunk);
    self
  }

  /// Spill committed stage-1, stage-2 and quotient polynomial coefficients to
  /// temporary disk-backed columns under `dir` on CPU. Has no effect on CUDA
  /// builds, where coefficients stay host-resident for device transfers.
  pub fn with_disk_spill(mut self, dir: impl Into<PathBuf>) -> Self {
    self.spill_dir = Some(dir.into());
    self
  }

  pub fn spill_dir(&self) -> Option<&Path> {
    self.spill_dir.as_deref()
  }

  /// Default CPU disk-spilling policy when `IX_KZG_DISK_SPILL` is unset:
  /// disabled on CUDA and on CPU hosts with `>= 256 GiB` of available RAM
  /// (where in-memory proving avoids slow network-attached disk I/O), and
  /// enabled on smaller CPU hosts to keep peak RSS bounded around ~50 GiB.
  fn adaptive_disk_spill(avail_gib: Option<usize>, is_cuda: bool) -> bool {
    const IN_RAM_THRESHOLD_GIB: usize = 256;
    !is_cuda && avail_gib.is_none_or(|gib| gib < IN_RAM_THRESHOLD_GIB)
  }

  /// Resolve the CPU disk-spill directory from `IX_KZG_DISK_SPILL` (default
  /// adaptive on CPU — enabled below 256 GiB available RAM, disabled on high-RAM
  /// servers and CUDA) and `IX_KZG_SPILL_DIR` (default `dir`).
  pub(crate) fn resolve_disk_spill_dir(
    default_dir: &Path,
  ) -> Result<Option<PathBuf>, Box<dyn std::error::Error>> {
    let enabled = match std::env::var("IX_KZG_DISK_SPILL") {
      Ok(value) => match value.as_str() {
        "1" | "true" | "yes" => true,
        "0" | "false" | "no" => false,
        other => {
          return Err(
            format!("IX_KZG_DISK_SPILL must be 0 or 1, not {other:?}").into(),
          );
        },
      },
      Err(std::env::VarError::NotPresent) => Self::adaptive_disk_spill(
        crate::pipeline::storage::available_host_gib(),
        cfg!(feature = "cuda"),
      ),
      Err(error) => return Err(error.into()),
    };
    if !enabled || cfg!(feature = "cuda") {
      return Ok(None);
    }
    Ok(Some(
      std::env::var_os("IX_KZG_SPILL_DIR")
        .map_or_else(|| default_dir.to_path_buf(), PathBuf::from),
    ))
  }
}

/// The committed matrix at a round position.
fn committed<D: CoefficientData>(
  (data, index): (&D, usize),
) -> &CommittedMatrix {
  data.matrix(index).expect("committed matrix position")
}

fn all_columns(matrix: &CommittedMatrix) -> Vec<usize> {
  (0..matrix.width()).collect()
}

/// Every circuit's lookup trace as a coefficient matrix, passed to `commit`,
/// with its local accumulator total. Device constructions run concurrently;
/// shapes and storage the kernels do not support use one host working set at
/// a time. Device admission failures are errors.
pub(super) fn lookup_parts<SC: CoefficientConfig, T: Send>(
  pcs: &KzgPcs,
  inputs: &[LookupCommitInput<'_, SC>],
  beta: Scalar,
  gamma: Scalar,
  commit: impl Fn(CommittedMatrix) -> T + Sync,
) -> Vec<(T, Scalar)> {
  #[cfg(feature = "cuda")]
  {
    use rayon::prelude::*;
    let mut parts: Vec<_> = inputs
      .par_iter()
      .map(|input| {
        cuda::lookup::coefficients(input, beta, gamma).map(
          |(columns, local)| {
            let domain = committed(input.stage_1).domain;
            (commit(pcs.coefficient_matrix(domain.log_size, columns)), local)
          },
        )
      })
      .collect();
    for (i, (input, part)) in inputs.iter().zip(&mut parts).enumerate() {
      if part.is_none() {
        tracing::info!(
          curve = super::curve::NAME,
          circuit = i,
          reason = "shape or storage unsupported by CUDA lookup kernels",
          "KZG lookup using CPU construction"
        );
        let (matrix, local) = host_lookup_matrix(pcs, i, input, beta, gamma);
        *part = Some((commit(matrix), local));
      }
    }
    parts.into_iter().map(Option::unwrap).collect()
  }
  #[cfg(not(feature = "cuda"))]
  inputs
    .iter()
    .enumerate()
    .map(|(i, input)| {
      let (matrix, local) = host_lookup_matrix(pcs, i, input, beta, gamma);
      (commit(matrix), local)
    })
    .collect()
}

/// Every circuit's quotient slices as a coefficient matrix, passed to
/// `commit`, with the same device and host split as [`lookup_parts`].
pub(super) fn quotient_parts<SC: CoefficientConfig, T: Send>(
  pcs: &KzgPcs,
  inputs: &[QuotientCommitInput<'_, SC>],
  alpha: Scalar,
  commit: impl Fn(CommittedMatrix) -> T + Sync,
) -> Vec<T> {
  quotient_parts_with_block_size(pcs, inputs, alpha, None, commit)
}

fn quotient_parts_with_block_size<SC: CoefficientConfig, T: Send>(
  pcs: &KzgPcs,
  inputs: &[QuotientCommitInput<'_, SC>],
  alpha: Scalar,
  block_size: Option<usize>,
  commit: impl Fn(CommittedMatrix) -> T + Sync,
) -> Vec<T> {
  #[cfg(feature = "cuda")]
  {
    use rayon::prelude::*;
    let mut parts: Vec<_> = inputs
      .par_iter()
      .map(|input| {
        cuda::quotient::coefficients(input, alpha).map(|columns| {
          assert!(
            !columns.is_empty() && columns.len() <= pcs.max_quotient_degree()
          );
          commit(pcs.coefficient_matrix(input.trace_domain.log_size, columns))
        })
      })
      .collect();
    for (i, (input, part)) in inputs.iter().zip(&mut parts).enumerate() {
      if part.is_none() {
        tracing::info!(
          curve = super::curve::NAME,
          circuit = i,
          reason = "shape or storage unsupported by CUDA quotient kernels",
          "KZG quotient using CPU construction"
        );
        *part = Some(commit(host_quotient_matrix(
          pcs, i, input, alpha, block_size,
        )));
      }
    }
    parts.into_iter().map(Option::unwrap).collect()
  }
  #[cfg(not(feature = "cuda"))]
  inputs
    .iter()
    .enumerate()
    .map(|(i, input)| {
      commit(host_quotient_matrix(pcs, i, input, alpha, block_size))
    })
    .collect()
}

/// One circuit's lookup trace, constructed on the host from committed
/// columns and interpolated, with its local accumulator total.
fn host_lookup_matrix<SC: CoefficientConfig>(
  pcs: &KzgPcs,
  i: usize,
  input: &LookupCommitInput<'_, SC>,
  beta: Scalar,
  gamma: Scalar,
) -> (CommittedMatrix, Scalar) {
  use multi_stark::traits::Algebra;
  use multi_stark::traits::EvaluationDomain;
  let start = std::time::Instant::now();
  let stage_1 = committed(input.stage_1);
  let domain = stage_1.domain;
  let (selected, graph) =
    super::quotient_plan::lookup_graph(&input.circuit.graph);
  tracing::info!(
    circuit = i,
    fixed_columns = selected.len(),
    "KZG lookup fixed columns"
  );
  let fixed = input.preprocessed.filter(|_| !selected.is_empty()).map(|data| {
    pcs.evaluate_matrix_columns(committed(data), domain, &selected)
  });
  let main =
    pcs.evaluate_matrix_columns(stage_1, domain, &all_columns(stage_1));
  const CHUNK: usize = 1 << 12;
  let width = input.circuit.stage_2_width;
  let mut trace = vec![Scalar::ZERO; domain.size() * width];
  // Every chunk starts at zero. Its total determines the prefix
  // offset applied in a second bounded, parallel pass.
  let totals: Vec<_> = trace
    .par_chunks_mut(CHUNK * width)
    .enumerate()
    .map(|(i, dst)| {
      let start = i * CHUNK;
      let values = multi_stark::system::compute_lookup_values_range(
        &graph,
        &main,
        fixed.as_ref(),
        start..start + dst.len() / width,
      );
      let (mut chunks, next) =
        multi_stark::lookup::LookupValues::stage_2_traces(
          &[values],
          &[input.circuit.lookup_group_size],
          beta,
          &gamma,
          Scalar::ZERO,
        );
      dst.copy_from_slice(&chunks.remove(0).values);
      next[0]
    })
    .collect();
  let mut local = Scalar::ZERO;
  let offsets: Vec<_> = totals
    .into_iter()
    .map(|value| {
      let offset = local;
      local += value;
      offset
    })
    .collect();
  trace.par_chunks_mut(CHUNK * width).zip(offsets).for_each(|(dst, offset)| {
    if offset != Scalar::ZERO {
      for value in dst {
        *value += offset;
      }
    }
  });
  drop(main);
  drop(fixed);
  let trace = p3_matrix::dense::RowMajorMatrix::new(trace, width);
  let matrix = KzgPcs::interpolate_columns(domain, trace);
  tracing::info!(
    circuit = i,
    seconds = start.elapsed().as_secs_f64(),
    "KZG lookup constructed"
  );
  (matrix, local)
}

/// One circuit's quotient, evaluated on the host one trace-sized coset at a
/// time with fixed-column passes, then interpolated and sliced.
fn host_quotient_matrix<SC: CoefficientConfig>(
  pcs: &KzgPcs,
  i: usize,
  input: &QuotientCommitInput<'_, SC>,
  alpha: Scalar,
  block_size: Option<usize>,
) -> CommittedMatrix {
  use multi_stark::traits::Algebra;
  use multi_stark::traits::EvaluationDomain;
  use multi_stark::traits::TwoAdicField;
  let start = std::time::Instant::now();
  let n = input.trace_domain.size();
  let ratio = input.quotient_domain.size() / n;
  let generator = Scalar::two_adic_generator(input.quotient_domain.log_size);
  let mut shift = input.quotient_domain.shift;
  let mut values = vec![Scalar::ZERO; input.quotient_domain.size()];
  let mut powers: Vec<_> =
    alpha.powers().take(input.constraint_count).collect();
  powers.reverse();
  let passes = super::quotient_plan::plan(
    &input.circuit.graph,
    input.circuit.lookup_group_size.max(1),
  );
  tracing::info!(circuit = i, fixed_columns = ?passes.iter().map(|p| p.fixed.len()).collect::<Vec<_>>(), "KZG quotient fixed-column passes");
  let stage_1 = committed(input.stage_1);
  let stage_2 = committed(input.stage_2);
  for coset in 0..ratio {
    let domain = super::domain::Radix2Coset {
      log_size: input.trace_domain.log_size,
      shift,
    };
    let main =
      pcs.evaluate_matrix_columns(stage_1, domain, &all_columns(stage_1));
    let stage2 =
      pcs.evaluate_matrix_columns(stage_2, domain, &all_columns(stage_2));
    let selectors =
      super::quotient::CosetSelectors::new(input.trace_domain, domain);
    for pass in &passes {
      let fixed =
        input.preprocessed.filter(|_| !pass.fixed.is_empty()).map(|data| {
          pcs.evaluate_matrix_columns(committed(data), domain, &pass.fixed)
        });
      super::quotient::evaluate_coset(
        input,
        pass,
        domain,
        &selectors,
        &powers,
        fixed.as_ref(),
        &main,
        &stage2,
        coset,
        ratio,
        block_size,
        &mut values,
      );
    }
    shift *= generator;
    tracing::info!(
      circuit = i,
      coset,
      seconds = start.elapsed().as_secs_f64(),
      "KZG quotient coset evaluated"
    );
  }
  let matrix = KzgPcs::interpolate_quotient(
    input.quotient_domain,
    p3_matrix::dense::RowMajorMatrix::new_col(values),
    ratio,
  );
  tracing::info!(
    circuit = i,
    seconds = start.elapsed().as_secs_f64(),
    "KZG quotient constructed"
  );
  matrix
}

impl ProofConfig for KzgConfig {
  fn accelerated_lookup_commit(
    &self,
    inputs: &[LookupCommitInput<'_, Self>],
    beta: Scalar,
    gamma: Scalar,
    mut acc: Scalar,
  ) -> Option<multi_stark::config::AcceleratedLookupCommitment<Self>> {
    if !self.stream_lookups {
      return None;
    }
    let results = lookup_parts(&self.pcs, inputs, beta, gamma, |matrix| {
      self.pcs.commit_matrix(matrix)
    });
    let mut parts = Vec::with_capacity(results.len());
    let mut accumulators = Vec::with_capacity(results.len());
    // Local traces start at zero; only the ordered public totals depend
    // on the preceding circuit's accumulator.
    for (data, local) in results {
      parts.push(data);
      acc += local;
      accumulators.push(acc);
    }
    let (commitment, data) = KzgProverData::concatenate(parts);
    Some((commitment, data, accumulators))
  }

  fn accelerated_quotient_commit(
    &self,
    inputs: &[QuotientCommitInput<'_, Self>],
    alpha: Scalar,
  ) -> Option<(KzgCommitment, KzgProverData)> {
    if !self.stream_quotient {
      return None;
    }
    Some(KzgProverData::concatenate(quotient_parts_with_block_size(
      &self.pcs,
      inputs,
      alpha,
      self.streaming_chunk_size,
      |matrix| self.pcs.commit_matrix(matrix),
    )))
  }

  fn omit_inactive_preprocessed_openings(&self) -> bool {
    true
  }
  fn omit_unused_next_row_openings(&self) -> bool {
    true
  }

  type Pcs = KzgPcs;
  type Challenge = Scalar;
  type Challenger = KzgTranscript;

  fn pcs(&self) -> &KzgPcs {
    &self.pcs
  }

  fn initialise_challenger(&self) -> KzgTranscript {
    let mut challenger = KzgTranscript::new(self.transcript_kind);
    challenger.observe_bytes(&self.transcript_seed);
    challenger
  }

  fn max_log_degree(&self) -> usize {
    self.max_log_degree
  }

  fn max_log_quotient_domain(&self) -> usize {
    <Scalar as multi_stark::traits::TwoAdicField>::TWO_ADICITY
  }

  fn max_quotient_degree(&self) -> usize {
    self.pcs.max_quotient_degree()
  }

  fn log_blowup(&self) -> usize {
    // KZG commits polynomials, not evaluation blowups.
    0
  }
}
#[cfg(test)]
mod tests {
  use super::*;
  use multi_stark::expr::Expr;
  use multi_stark::lookup::Lookup;
  use multi_stark::system::CircuitInputs;
  use multi_stark::system::System;
  use multi_stark::system::SystemWitness;
  use multi_stark::traits::Algebra;
  use multi_stark::traits::Field;
  use p3_matrix::dense::RowMajorMatrix;

  /// `a·b = c` per row, with a self-canceling push/pull lookup pair to
  /// exercise the stage-2 machinery.
  fn mul_circuit() -> CircuitInputs<Scalar> {
    let m = Expr::main;
    CircuitInputs {
      main_width: 3,
      constraints: vec![m(0) * m(1) - m(2)],
      lookups: vec![
        Lookup::push(Expr::constant(Scalar::from_u32(1)), vec![m(0), m(2)]),
        Lookup::pull(Expr::constant(Scalar::from_u32(1)), vec![m(0), m(2)]),
      ],
      ..Default::default()
    }
  }

  fn kzg_system()
  -> (System<KzgConfig>, multi_stark::system::ProverKey<KzgConfig>) {
    let srs = Arc::new(Srs::unsafe_dev_setup(1 << 8, b"test"));
    let config = KzgConfig::new(srs, 8);
    System::new(config, [mul_circuit()])
  }

  fn witness(system: &System<KzgConfig>) -> SystemWitness<Scalar> {
    let f = Scalar::from_u32;
    let trace = RowMajorMatrix::new(
      [2, 3, 6, 4, 5, 20, 7, 8, 56, 1, 1, 1].map(f).to_vec(),
      3,
    );
    SystemWitness::from_stage_1(vec![trace], system)
  }

  #[test]
  fn proof_binds_public_identity_degree_and_trace_cap() {
    let srs = Arc::new(Srs::unsafe_dev_setup(16, b"public-parameters"));
    let params = super::super::VerifierParams::from_srs(&srs);
    let (mut system, key) =
      System::new(KzgConfig::new(srs.clone(), 8), [mul_circuit()]);
    let proof = system.prove_multiple_claims(&key, &[], witness(&system));
    let anchors = Srs::unsafe_dev_setup_prefix(2, 15, b"public-parameters");
    system.config = KzgConfig::verifier_only(
      super::super::VerifierParams::with_max_trace_len(&anchors, 16),
      8,
    );
    system.verify_multiple_claims(&[], &proof).unwrap();
    let mut identity = params.clone();
    identity.public_setup.id[0] ^= 1;
    let mut degree = params;
    degree.public_setup.max_degree = 31;
    for changed in [
      identity,
      degree,
      super::super::VerifierParams::with_max_trace_len(&srs, 8),
    ] {
      system.config = KzgConfig::verifier_only(changed, 8);
      assert!(system.verify_multiple_claims(&[], &proof).is_err());
    }
  }

  #[test]
  fn opens_next_rows_only_when_the_graph_reads_them() {
    let f = Scalar::from_u8;
    let (system, key) = System::new(
      KzgConfig::new(Arc::new(Srs::unsafe_dev_setup(8, b"next-rows")), 4),
      [
        CircuitInputs {
          main_width: 1,
          preprocessed: Some(RowMajorMatrix::new_col(vec![f(7); 4])),
          constraints: vec![Expr::main_next(0) - Expr::preprocessed_next(0)],
          ..Default::default()
        },
        CircuitInputs {
          main_width: 1,
          preprocessed: Some(RowMajorMatrix::new_col(vec![f(9); 2])),
          constraints: vec![Expr::main(0) - Expr::preprocessed(0)],
          ..Default::default()
        },
      ],
    );
    let proof = system.prove_multiple_claims(
      &key,
      &[],
      SystemWitness::from_stage_1(
        vec![
          RowMajorMatrix::new_col(vec![f(7); 4]),
          RowMajorMatrix::new_col(vec![f(9); 2]),
        ],
        &system,
      ),
    );
    system.verify_multiple_claims(&[], &proof).unwrap();
    assert_eq!(
      proof.stage_1_opened_values.iter().map(Vec::len).collect::<Vec<_>>(),
      [2, 1]
    );
    assert_eq!(
      proof
        .preprocessed_opened_values
        .as_ref()
        .unwrap()
        .iter()
        .map(Vec::len)
        .collect::<Vec<_>>(),
      [2, 1]
    );
    let codec =
      super::super::compact::FixedProofCodec::new(&system, &proof.log_degrees)
        .unwrap();
    let decoded = codec.decode(&codec.encode(&proof).unwrap()).unwrap();
    system.verify_multiple_claims(&[], &decoded).unwrap();
    let mut bad = proof.clone();
    bad.stage_1_opened_values[0].pop();
    assert!(system.verify_multiple_claims(&[], &bad).is_err());
    let mut bad = proof.clone();
    bad.preprocessed_opened_values.as_mut().unwrap()[0][1][0] += Scalar::ONE;
    assert!(system.verify_multiple_claims(&[], &bad).is_err());
    let mut bad = proof.clone();
    bad.stage_1_opened_values[1].push(vec![Scalar::ZERO]);
    assert!(system.verify_multiple_claims(&[], &bad).is_err());
    // KZG commits columns separately, so inactive fixed matrices need no openings.
    let partial = system.prove_multiple_claims(
      &key,
      &[],
      SystemWitness::from_stage_1(
        vec![
          RowMajorMatrix::new(vec![], 1),
          RowMajorMatrix::new_col(vec![f(9); 2]),
        ],
        &system,
      ),
    );
    system.verify_multiple_claims(&[], &partial).unwrap();
    assert_eq!(partial.active, [false, true]);
    assert_eq!(
      partial.preprocessed_opened_values.as_ref().unwrap()[0].len(),
      0
    );
    let mut bad = partial.clone();
    bad.preprocessed_opened_values.as_mut().unwrap()[1].clear();
    assert!(system.verify_multiple_claims(&[], &bad).is_err());
    let mut bad = partial;
    bad.preprocessed_opened_values.as_mut().unwrap()[0].push(vec![f(7)]);
    assert!(system.verify_multiple_claims(&[], &bad).is_err());
  }

  #[test]
  fn quotient_slices_fit_an_srs_exactly_as_large_as_the_trace() {
    let config =
      KzgConfig::new(Arc::new(Srs::unsafe_dev_setup(4, b"exact-srs")), 4);
    let (system, key) = System::new(config, [mul_circuit()]);
    let proof = system.prove_multiple_claims(&key, &[], witness(&system));
    system.verify_multiple_claims(&[], &proof).unwrap();
  }

  #[test]
  fn batch_messages_work_with_scalar_challenges() {
    use multi_stark::batch::BatchMessage;
    use multi_stark::batch::ShardInput;
    let config =
      KzgConfig::new(Arc::new(Srs::unsafe_dev_setup(2, b"batch")), 4);
    let (system, key) = System::new(
      config,
      [CircuitInputs {
        main_width: 1,
        preprocessed: Some(RowMajorMatrix::new_col(vec![
          Scalar::ONE,
          Scalar::ZERO,
        ])),
        lookups: vec![Lookup::pull(Expr::preprocessed(0), vec![Expr::main(0)])],
        ..Default::default()
      }],
    );
    let value = Scalar::from_u8(9);
    let witness = SystemWitness::from_stage_1(
      vec![RowMajorMatrix::new_col(vec![value; 2])],
      &system,
    );
    let mut proof = system.prove_batch(
      &key,
      vec![ShardInput { claims: vec![], witness }],
      vec![BatchMessage { args: vec![value], multiplicity: Scalar::ONE }],
    );
    system.verify_batch(&proof).unwrap();
    proof.preamble.messages[0].args[0] += Scalar::ONE;
    assert!(system.verify_batch(&proof).is_err());
  }

  #[test]
  fn kzg_tampering_rejected() {
    let (system, key) = kzg_system();
    let no_claims: &[&[Scalar]] = &[];
    let prove =
      || system.prove_multiple_claims(&key, no_claims, witness(&system));

    let mut tampered = prove();
    tampered.intermediate_accumulators[0] += <Scalar as Algebra<Scalar>>::ONE;
    assert!(system.verify_multiple_claims(no_claims, &tampered).is_err());

    let mut tampered = prove();
    tampered.stage_1_opened_values[0][0][0] += <Scalar as Algebra<Scalar>>::ONE;
    assert!(system.verify_multiple_claims(no_claims, &tampered).is_err());

    let mut tampered = prove();
    tampered.quotient_opened_values[0][0][0] +=
      <Scalar as Algebra<Scalar>>::ONE;
    assert!(system.verify_multiple_claims(no_claims, &tampered).is_err());
  }

  #[test]
  fn adaptive_disk_spill_respects_host_ram_and_backend() {
    assert!(KzgConfig::adaptive_disk_spill(None, false));
    assert!(KzgConfig::adaptive_disk_spill(Some(64), false));
    assert!(KzgConfig::adaptive_disk_spill(Some(192), false));
    assert!(!KzgConfig::adaptive_disk_spill(Some(256), false));
    assert!(!KzgConfig::adaptive_disk_spill(Some(495), false));
    assert!(!KzgConfig::adaptive_disk_spill(None, true));
    assert!(!KzgConfig::adaptive_disk_spill(Some(64), true));
  }
}
