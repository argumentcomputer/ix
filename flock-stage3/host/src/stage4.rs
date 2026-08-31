use anyhow::{Result, bail};
use flock_prover::{
  aggregate::{Accumulator, AggregateProof},
  challenger::Challenger,
  circuit::{Circuit, SigmaAssertion, WiringProof},
  field::{F128, F256, PHI_8_TABLE},
  lincheck::{LincheckGrinding, LincheckProof, MatrixAssertion, SkipPoint},
  matrix_fold::{
    FoldMatrix, FoldProof, JaggedAssertion, JaggedRowWeight, JaggedTable,
    MatrixClaim, Weight, bilinear, discharge_jagged,
  },
  pcs::{Commitment, MergedOpenProof, jagged, ligerito, ring_switch},
  proof::BooleanPiopProof,
  r1cs_hashes::fs_chain::{CvSource, FsChainTrace, trace_duplex_forked},
  schedule::Registry,
  transcript_record::{RecordingChallenger, Stream, StreamWord, TranscriptOp},
  union::{UnionInstance, publics_digest},
  zerocheck::{
    ZerocheckGrinding, ZerocheckProof,
    multilinear::subspace_denominator_pair,
    univariate_skip_optimized::{
      medium_challenges_ghash, small_challenges_ghash,
    },
  },
};
use ix_stage4_trace::{
  ChainedBlake3ChainV1, ChainedBlake3ChallengeSourceV1, ChainedBlake3ChildV1,
  ChainedBlake3PowConstraintV1, ChainedBlake3TranscriptV1,
  ChainingValueSourceV1, CompressionLinkV1, CompressionOutputWordV1,
  CompressionRowV1, F128AlgebraTraceV1, F128CircuitStructureAccumulatorTraceV1,
  F128CircuitStructureMatrixIdV1, F128DeferredMatrixClaimV1, F128EqualityV1,
  F128FamilyHConstantsV1, F128InnerLigeritoCensusV1, F128InnerLigeritoTraceV1,
  F128InputSourceV1, F128JaggedAccumulatorCensusV1,
  F128JaggedAccumulatorTraceV1, F128JaggedComboTermBindingV1,
  F128JaggedFoldClaimBindingV1, F128JaggedMatrixIdV1, F128JaggedRowBindingV1,
  F128LigeritoLevelV1, F128LigeritoOodClaimV1, F128MatrixAccumulatorTraceV1,
  F128MatrixFoldClaimBindingV1, F128MatrixFoldRoundV1, F128MatrixFoldTraceV1,
  F128MatrixSideV1, F128MergedPcsBooleanClaimV1, F128MergedPcsFrontendCensusV1,
  F128MergedPcsFrontendTraceV1, F128MergedPcsRoundV1, F128MultipointRoundV1,
  F128MultipointTwistedAssistCensusV1, F128MultipointTwistedAssistTraceV1,
  F128OperationV1, F128ReferenceV1, F128RingSwitchTraceV1,
  F128StatementBindingTraceV1, F128StaticMatrixIdV1, F128StructuredWeightV1,
  F128VerifierPhaseV1, F128WiringTraceV1, F256IndexPairV1,
  F256LigeritoMessageV1, StreamWordSourceV1,
};

use crate::{STAGE3_STATEMENT_BYTES, Stage3StatementV1};

pub const STAGE4_FLOCK_VERIFIER_WITNESS_DOMAIN: &[u8; 8] = b"IXFLK4W1";
pub const STAGE4_MATRIX_ACCUMULATOR_TRANSCRIPT_DOMAIN: &[u8] =
  b"ix-stage4-matrix-accumulator-v1";

/// Stable transcript operation tree recorded from the pinned Flock verifier.
///
/// Values are stored separately in [`Stage4FlockTranscriptWitnessV1`]. This
/// tree fixes their ordering and the exact chained-BLAKE3 squeeze schedule
/// without making Stage 4 duplicate the verifier's control flow by hand.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Stage4TranscriptOpV1 {
  Label(Vec<u8>),
  ObserveScalar,
  ObserveSlice(u64),
  ObserveBytes(u64),
  SqueezeScalar,
  SqueezeSlice(u64),
  Forked { label: Vec<u8>, ops: Vec<Self> },
  Merge { fork: u64 },
  Pow { bits: u32 },
  LegacyPow { bits: u32 },
}

impl Stage4TranscriptOpV1 {
  fn from_flock(operation: &TranscriptOp) -> Result<Self> {
    Ok(match operation {
      TranscriptOp::Label(label) => Self::Label(label.clone()),
      TranscriptOp::ObserveScalar => Self::ObserveScalar,
      TranscriptOp::ObserveSlice(count) => {
        Self::ObserveSlice(u64::try_from(*count).map_err(|error| {
          anyhow::anyhow!("transcript slice count: {error}")
        })?)
      },
      TranscriptOp::ObserveBytes(length) => {
        Self::ObserveBytes(u64::try_from(*length).map_err(|error| {
          anyhow::anyhow!("transcript byte length: {error}")
        })?)
      },
      TranscriptOp::SqueezeScalar => Self::SqueezeScalar,
      TranscriptOp::SqueezeSlice(count) => {
        Self::SqueezeSlice(u64::try_from(*count).map_err(|error| {
          anyhow::anyhow!("transcript squeeze count: {error}")
        })?)
      },
      TranscriptOp::Forked { label, ops } => Self::Forked {
        label: label.clone(),
        ops: ops.iter().map(Self::from_flock).collect::<Result<Vec<_>>>()?,
      },
      TranscriptOp::Merge { fork } => Self::Merge {
        fork: u64::try_from(*fork)
          .map_err(|error| anyhow::anyhow!("transcript fork index: {error}"))?,
      },
      TranscriptOp::Pow { bits } => Self::Pow { bits: *bits },
      TranscriptOp::LegacyPow { bits } => Self::LegacyPow { bits: *bits },
    })
  }

  fn recursive_len(&self) -> u64 {
    match self {
      Self::Forked { ops, .. } => {
        1 + ops.iter().map(Self::recursive_len).sum::<u64>()
      },
      _ => 1,
    }
  }
}

/// Concrete Fiat-Shamir tape produced while verifying one valid Stage 3 proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stage4FlockTranscriptWitnessV1 {
  shape_digest: [u8; 32],
  operations: Vec<Stage4TranscriptOpV1>,
  observed_values: Vec<[u8; 16]>,
  byte_payloads: Vec<Vec<u8>>,
  challenges: Vec<[u8; 16]>,
  f128_private_values: Vec<[u8; 16]>,
  chained_blake3: ChainedBlake3TranscriptV1,
  f128_algebra: F128AlgebraTraceV1,
}

impl Stage4FlockTranscriptWitnessV1 {
  #[cfg(test)]
  pub(crate) fn from_recording<Ch: Challenger>(
    recording: &RecordingChallenger<Ch>,
    domain: &[u8],
  ) -> Result<Self> {
    Self::from_recording_with_algebra(
      recording,
      domain,
      F128AlgebraTraceV1::default(),
      &[],
    )
  }

  pub(crate) fn from_recording_with_algebra<Ch: Challenger>(
    recording: &RecordingChallenger<Ch>,
    domain: &[u8],
    f128_algebra: F128AlgebraTraceV1,
    f128_private_values: &[F128],
  ) -> Result<Self> {
    let shape = recording.shape();
    let operations = shape
      .ops()
      .iter()
      .map(Stage4TranscriptOpV1::from_flock)
      .collect::<Result<Vec<_>>>()?;
    let chained_blake3 = export_chained_blake3(recording, domain)?;
    Ok(Self {
      shape_digest: shape.digest(),
      operations,
      observed_values: recording
        .values()
        .iter()
        .copied()
        .map(encode_f128)
        .collect(),
      byte_payloads: recording.payloads().to_vec(),
      challenges: recording
        .challenges()
        .iter()
        .copied()
        .map(encode_f128)
        .collect(),
      f128_private_values: f128_private_values
        .iter()
        .copied()
        .map(encode_f128)
        .collect(),
      chained_blake3,
      f128_algebra,
    })
  }

  pub fn shape_digest(&self) -> &[u8; 32] {
    &self.shape_digest
  }

  pub fn operations(&self) -> &[Stage4TranscriptOpV1] {
    &self.operations
  }

  pub fn observed_values(&self) -> &[[u8; 16]] {
    &self.observed_values
  }

  pub fn byte_payloads(&self) -> &[Vec<u8>] {
    &self.byte_payloads
  }

  pub fn challenges(&self) -> &[[u8; 16]] {
    &self.challenges
  }

  pub fn f128_private_values(&self) -> &[[u8; 16]] {
    &self.f128_private_values
  }

  pub fn chained_blake3(&self) -> &ChainedBlake3TranscriptV1 {
    &self.chained_blake3
  }

  pub fn f128_algebra(&self) -> &F128AlgebraTraceV1 {
    &self.f128_algebra
  }

  fn recursive_operation_count(&self) -> u64 {
    self.operations.iter().map(Stage4TranscriptOpV1::recursive_len).sum()
  }
}

/// Product-GKR, public/gate recombination, and the conditional outputs which
/// must enter the circuit-structure accumulator and merged PCS opening.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stage4FlockWiringWitnessV1 {
  trace: F128WiringTraceV1,
  private_values: Vec<[u8; 16]>,
}

impl Stage4FlockWiringWitnessV1 {
  pub const fn trace(&self) -> &F128WiringTraceV1 {
    &self.trace
  }

  pub fn private_values(&self) -> &[[u8; 16]] {
    &self.private_values
  }
}

/// Ring-switch, mixed-batching, and dense-sumcheck portion of the merged PCS
/// verifier. The trace's two conditional outputs feed the jagged assist and
/// inner Ligerito slices which follow it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stage4FlockMergedPcsFrontendWitnessV1 {
  trace: F128MergedPcsFrontendTraceV1,
}

impl Stage4FlockMergedPcsFrontendWitnessV1 {
  pub(crate) const fn new(trace: F128MergedPcsFrontendTraceV1) -> Self {
    Self { trace }
  }

  pub const fn trace(&self) -> &F128MergedPcsFrontendTraceV1 {
    &self.trace
  }

  pub fn census(&self) -> F128MergedPcsFrontendCensusV1 {
    self.trace.census()
  }
}

/// Forked multipoint-twisted replay and the three raw jagged-layout values
/// it exports for deferred accumulation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stage4FlockMultipointTwistedAssistWitnessV1 {
  trace: F128MultipointTwistedAssistTraceV1,
  private_values: Vec<[u8; 16]>,
}

impl Stage4FlockMultipointTwistedAssistWitnessV1 {
  pub const fn trace(&self) -> &F128MultipointTwistedAssistTraceV1 {
    &self.trace
  }

  pub fn private_values(&self) -> &[[u8; 16]] {
    &self.private_values
  }

  pub fn census(&self) -> F128MultipointTwistedAssistCensusV1 {
    self.trace.census()
  }
}

/// Transcript-indexed inner Ligerito replay plus the private opened rows and
/// capped Merkle siblings which authenticate them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stage4FlockInnerLigeritoWitnessV1 {
  trace: F128InnerLigeritoTraceV1,
  private_values: Vec<[u8; 16]>,
  private_digests: Vec<[u8; 32]>,
}

impl Stage4FlockInnerLigeritoWitnessV1 {
  pub const fn trace(&self) -> &F128InnerLigeritoTraceV1 {
    &self.trace
  }

  pub fn private_values(&self) -> &[[u8; 16]] {
    &self.private_values
  }

  pub fn private_digests(&self) -> &[[u8; 32]] {
    &self.private_digests
  }

  pub fn census(&self) -> F128InnerLigeritoCensusV1 {
    self.trace.census()
  }
}

/// Plain matrix evaluation carried to the terminal root discharge.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stage4F128RootMatrixClaimV1 {
  matrix: F128StaticMatrixIdV1,
  row_point: Vec<[u8; 16]>,
  column_point: Vec<[u8; 16]>,
  value: [u8; 16],
}

/// Plain evaluation of the digest-keyed circuit-structure table carried to
/// the terminal direct check.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stage4F128CircuitStructureRootClaimV1 {
  matrix: F128CircuitStructureMatrixIdV1,
  row_point: Vec<[u8; 16]>,
  column_point: Vec<[u8; 16]>,
  value: [u8; 16],
}

/// Plain evaluation of a digest-keyed jagged layout carried to the terminal
/// direct check.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stage4F128JaggedRootClaimV1 {
  matrix: F128JaggedMatrixIdV1,
  row_point: Vec<[u8; 16]>,
  column_point: Vec<[u8; 16]>,
  value: [u8; 16],
}

impl Stage4F128JaggedRootClaimV1 {
  pub const fn matrix(&self) -> F128JaggedMatrixIdV1 {
    self.matrix
  }

  pub fn row_point(&self) -> &[[u8; 16]] {
    &self.row_point
  }

  pub fn column_point(&self) -> &[[u8; 16]] {
    &self.column_point
  }

  pub const fn value(&self) -> &[u8; 16] {
    &self.value
  }

  pub fn check(&self, params: &jagged::JaggedParams) -> bool {
    let table = JaggedTable::from_params(params);
    if self.matrix.row_variables
      != u32::try_from(table.k).expect("jagged row dimension fits u32")
      || self.matrix.column_variables
        != u32::try_from(table.n_col_vars())
          .expect("jagged column dimension fits u32")
      || self.row_point.len() != table.k
      || self.column_point.len() != table.n_col_vars()
    {
      return false;
    }
    let claim = MatrixClaim {
      row: Weight::eq(
        self.row_point.iter().copied().map(decode_f128).collect(),
      ),
      col: Weight::eq(
        self.column_point.iter().copied().map(decode_f128).collect(),
      ),
      value: decode_f128(self.value),
    };
    discharge_jagged(&claim, &table)
  }
}

impl Stage4F128CircuitStructureRootClaimV1 {
  pub const fn matrix(&self) -> F128CircuitStructureMatrixIdV1 {
    self.matrix
  }

  pub fn row_point(&self) -> &[[u8; 16]] {
    &self.row_point
  }

  pub fn column_point(&self) -> &[[u8; 16]] {
    &self.column_point
  }

  pub const fn value(&self) -> &[u8; 16] {
    &self.value
  }

  /// Direct terminal discharge against the circuit table named by the root.
  /// This is deliberately native: the recursive relation verifies the fold,
  /// while the final verifier pays the one digest-keyed table evaluation.
  pub fn check(&self, circuit: &Circuit) -> bool {
    let matrix = SigmaAssertion::matrix(circuit);
    let Some(row_variables) = matrix.n_rows().checked_ilog2() else {
      return false;
    };
    let Some(column_variables) = matrix.n_cols().checked_ilog2() else {
      return false;
    };
    if !matrix.n_rows().is_power_of_two()
      || !matrix.n_cols().is_power_of_two()
      || self.matrix.circuit_digest != circuit.digest()
      || self.matrix.row_variables != row_variables
      || self.matrix.column_variables != column_variables
      || self.row_point.len()
        != usize::try_from(row_variables).expect("u32 fits usize")
      || self.column_point.len()
        != usize::try_from(column_variables).expect("u32 fits usize")
    {
      return false;
    }
    let claim = MatrixClaim {
      row: Weight::eq(
        self.row_point.iter().copied().map(decode_f128).collect(),
      ),
      col: Weight::eq(
        self.column_point.iter().copied().map(decode_f128).collect(),
      ),
      value: decode_f128(self.value),
    };
    bilinear(&claim.row, &claim.col, &matrix) == claim.value
  }
}

impl Stage4F128RootMatrixClaimV1 {
  pub const fn matrix(&self) -> F128StaticMatrixIdV1 {
    self.matrix
  }

  pub fn row_point(&self) -> &[[u8; 16]] {
    &self.row_point
  }

  pub fn column_point(&self) -> &[[u8; 16]] {
    &self.column_point
  }

  pub const fn value(&self) -> &[u8; 16] {
    &self.value
  }
}

/// Auxiliary Boolean, circuit-structure, and jagged-layout folds generated
/// natively after the Stage 3 proof is accepted. Their verifier reads no
/// matrix; the matrices are touched only by the native fold prover and the
/// eventual root discharge.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stage4FlockMatrixAccumulatorWitnessV1 {
  shape_digest: [u8; 32],
  operations: Vec<Stage4TranscriptOpV1>,
  observed_values: Vec<[u8; 16]>,
  byte_payloads: Vec<Vec<u8>>,
  challenges: Vec<[u8; 16]>,
  chained_blake3: ChainedBlake3TranscriptV1,
  trace: F128MatrixAccumulatorTraceV1,
  root_claims: Vec<Stage4F128RootMatrixClaimV1>,
  circuit_structure_trace: F128CircuitStructureAccumulatorTraceV1,
  circuit_structure_root_claim: Stage4F128CircuitStructureRootClaimV1,
  jagged_trace: F128JaggedAccumulatorTraceV1,
  jagged_root_claim: Stage4F128JaggedRootClaimV1,
}

impl Stage4FlockMatrixAccumulatorWitnessV1 {
  pub fn shape_digest(&self) -> &[u8; 32] {
    &self.shape_digest
  }

  pub fn operations(&self) -> &[Stage4TranscriptOpV1] {
    &self.operations
  }

  pub fn observed_values(&self) -> &[[u8; 16]] {
    &self.observed_values
  }

  pub fn byte_payloads(&self) -> &[Vec<u8>] {
    &self.byte_payloads
  }

  pub fn challenges(&self) -> &[[u8; 16]] {
    &self.challenges
  }

  pub fn chained_blake3(&self) -> &ChainedBlake3TranscriptV1 {
    &self.chained_blake3
  }

  pub const fn trace(&self) -> &F128MatrixAccumulatorTraceV1 {
    &self.trace
  }

  pub fn root_claims(&self) -> &[Stage4F128RootMatrixClaimV1] {
    &self.root_claims
  }

  pub const fn circuit_structure_trace(
    &self,
  ) -> &F128CircuitStructureAccumulatorTraceV1 {
    &self.circuit_structure_trace
  }

  pub const fn circuit_structure_root_claim(
    &self,
  ) -> &Stage4F128CircuitStructureRootClaimV1 {
    &self.circuit_structure_root_claim
  }

  pub const fn jagged_trace(&self) -> &F128JaggedAccumulatorTraceV1 {
    &self.jagged_trace
  }

  pub const fn jagged_root_claim(&self) -> &Stage4F128JaggedRootClaimV1 {
    &self.jagged_root_claim
  }

  fn recursive_operation_count(&self) -> u64 {
    self.operations.iter().map(Stage4TranscriptOpV1::recursive_len).sum()
  }

  pub fn census(&self) -> Stage4FlockMatrixAccumulatorCensusV1 {
    let transcript = self.chained_blake3.census();
    let accumulator = self.trace.census();
    Stage4FlockMatrixAccumulatorCensusV1 {
      transcript_operations: self.recursive_operation_count(),
      observed_values: u64::try_from(self.observed_values.len())
        .expect("matrix-accumulator observation count fits u64"),
      byte_payloads: u64::try_from(self.byte_payloads.len())
        .expect("matrix-accumulator payload count fits u64"),
      payload_bytes: self
        .byte_payloads
        .iter()
        .map(|payload| {
          u64::try_from(payload.len()).expect("payload length fits u64")
        })
        .sum(),
      challenges: u64::try_from(self.challenges.len())
        .expect("matrix-accumulator challenge count fits u64"),
      transcript_chains: transcript.chains,
      transcript_stream_words: transcript.stream_words,
      transcript_compression_rows: transcript.compression_rows,
      transcript_squeeze_words: transcript.squeeze_words,
      transcript_pow_constraints: transcript.pow_constraints,
      folds: accumulator.folds,
      input_claims: accumulator.input_claims,
      claim_observations: accumulator.claim_observations,
      bridge_observations: accumulator.bridge_observations,
      rounds: accumulator.rounds,
      root_claims: accumulator.root_claims,
      circuit_structure: self.circuit_structure_trace.census(),
      jagged: self.jagged_trace.census(),
    }
  }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Stage4FlockMatrixAccumulatorCensusV1 {
  pub transcript_operations: u64,
  pub observed_values: u64,
  pub byte_payloads: u64,
  pub payload_bytes: u64,
  pub challenges: u64,
  pub transcript_chains: u64,
  pub transcript_stream_words: u64,
  pub transcript_compression_rows: u64,
  pub transcript_squeeze_words: u64,
  pub transcript_pow_constraints: u64,
  pub folds: u64,
  pub input_claims: u64,
  pub claim_observations: u64,
  pub bridge_observations: u64,
  pub rounds: u64,
  pub root_claims: u64,
  pub circuit_structure:
    ix_stage4_trace::F128CircuitStructureAccumulatorCensusV1,
  pub jagged: F128JaggedAccumulatorCensusV1,
}

/// Exact native inputs from which the canonical Stage 4 Flock verifier
/// witness is generated.
///
/// The proof bundle remains in the pinned Flock wire format. `public_values`
/// and `transcript` are its serializer-independent expansion, obtained only
/// after the native verifier accepts the proof for `stage3_statement`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stage4FlockVerifierWitnessV1 {
  stage3_statement: [u8; STAGE3_STATEMENT_BYTES],
  circuit_digest: [u8; 32],
  public_values: Vec<[u8; 16]>,
  proof_bundle_bytes: Vec<u8>,
  transcript: Stage4FlockTranscriptWitnessV1,
  wiring: Stage4FlockWiringWitnessV1,
  merged_pcs: Stage4FlockMergedPcsFrontendWitnessV1,
  multipoint_assist: Stage4FlockMultipointTwistedAssistWitnessV1,
  inner_ligerito: Stage4FlockInnerLigeritoWitnessV1,
  matrix_accumulator: Stage4FlockMatrixAccumulatorWitnessV1,
  statement_binding: F128StatementBindingTraceV1,
}

impl Stage4FlockVerifierWitnessV1 {
  #[allow(clippy::too_many_arguments)]
  pub(crate) fn new(
    statement: &Stage3StatementV1,
    circuit_digest: [u8; 32],
    public_values: &[F128],
    proof_bundle_bytes: &[u8],
    transcript: Stage4FlockTranscriptWitnessV1,
    wiring: Stage4FlockWiringWitnessV1,
    merged_pcs: Stage4FlockMergedPcsFrontendWitnessV1,
    multipoint_assist: Stage4FlockMultipointTwistedAssistWitnessV1,
    inner_ligerito: Stage4FlockInnerLigeritoWitnessV1,
    matrix_accumulator: Stage4FlockMatrixAccumulatorWitnessV1,
    statement_binding: F128StatementBindingTraceV1,
  ) -> Result<Self> {
    if proof_bundle_bytes.is_empty() {
      bail!("Stage 4 Flock verifier witness has an empty proof bundle");
    }
    transcript
      .f128_algebra
      .validate(
        public_values.len(),
        transcript.observed_values.len(),
        transcript.challenges.len(),
        transcript.f128_private_values.len(),
      )
      .map_err(|error| {
        anyhow::anyhow!("Stage 4 F128 algebra trace: {error}")
      })?;
    wiring.trace.validate(
      public_values.len(),
      transcript.observed_values.len(),
      transcript.challenges.len(),
      wiring.private_values.len(),
    )?;
    if wiring.trace.circuit_digest != circuit_digest {
      bail!("Stage 4 wiring trace names a different Flock circuit");
    }
    merged_pcs.trace.validate(
      public_values.len(),
      transcript.observed_values.len(),
      transcript.challenges.len(),
      transcript.f128_private_values.len(),
      transcript.f128_algebra.operations.len(),
      &transcript.byte_payloads.iter().map(Vec::len).collect::<Vec<_>>(),
      &vec![
        usize::try_from(wiring.trace.packed_claim_variables)
          .expect("packed claim dimension fits usize");
        wiring.trace.gather_observations.len()
      ],
    )?;
    if merged_pcs.trace.packed_direct_observations
      != wiring.trace.gather_observations
    {
      bail!("Stage 4 merged PCS claim order disagrees with wiring");
    }
    multipoint_assist.trace.validate(
      transcript.observed_values.len(),
      transcript.challenges.len(),
      multipoint_assist.private_values.len(),
    )?;
    let dense_variables = merged_pcs.trace.merged_rounds.len();
    let expected_jagged_columns = dense_variables
      .checked_add(1)
      .and_then(|value| value.checked_mul(2))
      .ok_or_else(|| anyhow::anyhow!("Stage 4 jagged dimension overflow"))?;
    if multipoint_assist.trace.frontend_topology_digest
      != merged_pcs.trace.topology_digest()
      || multipoint_assist.trace.matrix.circuit_digest != circuit_digest
      || multipoint_assist.trace.matrix.row_variables
        != merged_pcs.trace.column_variables
      || usize::try_from(multipoint_assist.trace.matrix.column_variables).ok()
        != Some(expected_jagged_columns)
      || multipoint_assist.trace.witness_row_variables
        != merged_pcs.trace.row_variables
      || usize::try_from(multipoint_assist.trace.dense_variables).ok()
        != Some(dense_variables)
      || multipoint_assist.trace.group_column_addresses.len()
        != wiring.trace.gather_high_bits.len()
    {
      bail!("Stage 4 multipoint assist disagrees with the merged frontend");
    }
    inner_ligerito.trace.validate(
      transcript.observed_values.len(),
      transcript.challenges.len(),
      &transcript.byte_payloads.iter().map(Vec::len).collect::<Vec<_>>(),
      inner_ligerito.private_values.len(),
      inner_ligerito.private_digests.len(),
    )?;
    if inner_ligerito.trace.frontend_topology_digest
      != merged_pcs.trace.topology_digest()
      || inner_ligerito.trace.commitment_variables
        != merged_pcs.trace.commitment_variables
      || inner_ligerito.trace.q_eval_observation
        != merged_pcs.trace.q_eval_observation
    {
      bail!("Stage 4 inner Ligerito trace disagrees with the merged frontend");
    }
    matrix_accumulator.trace.validate(
      transcript.f128_algebra.deferred_matrix_claims.len(),
      matrix_accumulator.observed_values.len(),
      matrix_accumulator.byte_payloads.len(),
      matrix_accumulator.challenges.len(),
    )?;
    if matrix_accumulator.root_claims.len()
      != matrix_accumulator.trace.folds.len()
    {
      bail!("Stage 4 matrix accumulator has the wrong root-claim count");
    }
    matrix_accumulator.circuit_structure_trace.validate(
      3,
      matrix_accumulator.observed_values.len(),
      matrix_accumulator.byte_payloads.len(),
      matrix_accumulator.challenges.len(),
    )?;
    let structure_matrix = wiring.trace.structure_matrix();
    let structure_root = &matrix_accumulator.circuit_structure_root_claim;
    if matrix_accumulator.circuit_structure_trace.matrix != structure_matrix
      || structure_root.matrix != structure_matrix
      || structure_root.row_point.len()
        != usize::try_from(structure_matrix.row_variables)
          .expect("structure row dimension fits usize")
      || structure_root.column_point.len()
        != usize::try_from(structure_matrix.column_variables)
          .expect("structure column dimension fits usize")
    {
      bail!("Stage 4 circuit-structure accumulator has the wrong root shape");
    }
    matrix_accumulator.jagged_trace.validate(
      3,
      matrix_accumulator.observed_values.len(),
      matrix_accumulator.byte_payloads.len(),
      matrix_accumulator.challenges.len(),
    )?;
    let jagged_matrix = multipoint_assist.trace.matrix;
    let jagged_root = &matrix_accumulator.jagged_root_claim;
    if matrix_accumulator.jagged_trace.matrix != jagged_matrix
      || jagged_root.matrix != jagged_matrix
      || jagged_matrix.circuit_digest != circuit_digest
      || jagged_root.row_point.len()
        != usize::try_from(jagged_matrix.row_variables)
          .expect("jagged row dimension fits usize")
      || jagged_root.column_point.len()
        != usize::try_from(jagged_matrix.column_variables)
          .expect("jagged column dimension fits usize")
    {
      bail!("Stage 4 jagged accumulator has the wrong root shape");
    }
    let jagged_params = jagged::JaggedParams::from_heights(
      &merged_pcs.trace.jagged_heights,
      usize::try_from(merged_pcs.trace.row_variables)
        .expect("jagged witness row dimension fits usize"),
      dense_variables,
    );
    if !jagged_root.check(&jagged_params) {
      bail!("Stage 4 jagged accumulator failed its native root discharge");
    }
    statement_binding
      .validate(public_values.len(), transcript.byte_payloads.len())?;
    let statement_bytes = statement.to_bytes();
    if statement_binding.statement_domain != statement_bytes[..8]
      || statement_binding.relation_digest != statement_bytes[40..72]
      || statement_binding.config_digest != statement_bytes[72..104]
      || statement_binding.circuit_digest != circuit_digest
    {
      bail!("Stage 4 statement-binding constants disagree with the statement");
    }
    for (position, &index) in
      statement_binding.stage2_digest_public_values.iter().enumerate()
    {
      let start = 8 + 16 * position;
      let expected: [u8; 16] = statement_bytes[start..start + 16]
        .try_into()
        .expect("Stage 2 digest half has 16 bytes");
      if public_values
        .get(usize::try_from(index).expect("u64 fits usize"))
        .copied()
        .map(encode_f128)
        != Some(expected)
      {
        bail!("Stage 4 statement root does not match the Flock public vector");
      }
    }
    Ok(Self {
      stage3_statement: statement
        .to_bytes()
        .try_into()
        .expect("Stage 3 statement has a fixed length"),
      circuit_digest,
      public_values: public_values.iter().copied().map(encode_f128).collect(),
      proof_bundle_bytes: proof_bundle_bytes.to_vec(),
      transcript,
      wiring,
      merged_pcs,
      multipoint_assist,
      inner_ligerito,
      matrix_accumulator,
      statement_binding,
    })
  }

  pub fn stage3_statement_bytes(&self) -> &[u8; STAGE3_STATEMENT_BYTES] {
    &self.stage3_statement
  }

  pub fn stage3_statement_digest(&self) -> [u8; 32] {
    *blake3::hash(&self.stage3_statement).as_bytes()
  }

  pub fn circuit_digest(&self) -> &[u8; 32] {
    &self.circuit_digest
  }

  pub fn public_values(&self) -> &[[u8; 16]] {
    &self.public_values
  }

  pub fn proof_bundle_bytes(&self) -> &[u8] {
    &self.proof_bundle_bytes
  }

  pub fn transcript(&self) -> &Stage4FlockTranscriptWitnessV1 {
    &self.transcript
  }

  pub const fn wiring(&self) -> &Stage4FlockWiringWitnessV1 {
    &self.wiring
  }

  pub const fn merged_pcs(&self) -> &Stage4FlockMergedPcsFrontendWitnessV1 {
    &self.merged_pcs
  }

  pub const fn multipoint_assist(
    &self,
  ) -> &Stage4FlockMultipointTwistedAssistWitnessV1 {
    &self.multipoint_assist
  }

  pub const fn inner_ligerito(&self) -> &Stage4FlockInnerLigeritoWitnessV1 {
    &self.inner_ligerito
  }

  pub const fn matrix_accumulator(
    &self,
  ) -> &Stage4FlockMatrixAccumulatorWitnessV1 {
    &self.matrix_accumulator
  }

  pub const fn statement_binding(&self) -> &F128StatementBindingTraceV1 {
    &self.statement_binding
  }

  pub fn census(&self) -> Stage4FlockVerifierCensusV1 {
    let chained_blake3 = self.transcript.chained_blake3.census();
    let f128_algebra = self.transcript.f128_algebra.census();
    Stage4FlockVerifierCensusV1 {
      public_values: u64::try_from(self.public_values.len())
        .expect("public-value count fits u64"),
      proof_bundle_bytes: u64::try_from(self.proof_bundle_bytes.len())
        .expect("proof length fits u64"),
      transcript_operations: self.transcript.recursive_operation_count(),
      transcript_observed_values: u64::try_from(
        self.transcript.observed_values.len(),
      )
      .expect("observed-value count fits u64"),
      transcript_byte_payloads: u64::try_from(
        self.transcript.byte_payloads.len(),
      )
      .expect("payload count fits u64"),
      transcript_payload_bytes: self
        .transcript
        .byte_payloads
        .iter()
        .map(|payload| {
          u64::try_from(payload.len()).expect("payload length fits u64")
        })
        .sum(),
      transcript_challenges: u64::try_from(self.transcript.challenges.len())
        .expect("challenge count fits u64"),
      f128_private_values: u64::try_from(
        self.transcript.f128_private_values.len(),
      )
      .expect("private-value count fits u64"),
      transcript_chains: chained_blake3.chains,
      transcript_stream_words: chained_blake3.stream_words,
      transcript_compression_rows: chained_blake3.compression_rows,
      transcript_squeeze_words: chained_blake3.squeeze_words,
      transcript_pow_constraints: chained_blake3.pow_constraints,
      f128_operations: f128_algebra.operations,
      f128_additions: f128_algebra.additions,
      f128_multiplications: f128_algebra.multiplications,
      f128_inversions: f128_algebra.inversions,
      f128_equalities: f128_algebra.equalities,
      f128_deferred_matrix_claims: f128_algebra.deferred_matrix_claims,
      wiring: self.wiring.trace.census(),
      merged_pcs: self.merged_pcs.census(),
      multipoint_assist: self.multipoint_assist.census(),
      inner_ligerito: self.inner_ligerito.census(),
      matrix_accumulator: self.matrix_accumulator.census(),
    }
  }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Stage4FlockVerifierCensusV1 {
  pub public_values: u64,
  pub proof_bundle_bytes: u64,
  pub transcript_operations: u64,
  pub transcript_observed_values: u64,
  pub transcript_byte_payloads: u64,
  pub transcript_payload_bytes: u64,
  pub transcript_challenges: u64,
  pub f128_private_values: u64,
  pub transcript_chains: u64,
  pub transcript_stream_words: u64,
  pub transcript_compression_rows: u64,
  pub transcript_squeeze_words: u64,
  pub transcript_pow_constraints: u64,
  pub f128_operations: u64,
  pub f128_additions: u64,
  pub f128_multiplications: u64,
  pub f128_inversions: u64,
  pub f128_equalities: u64,
  pub f128_deferred_matrix_claims: u64,
  pub wiring: ix_stage4_trace::F128WiringCensusV1,
  pub merged_pcs: F128MergedPcsFrontendCensusV1,
  pub multipoint_assist: F128MultipointTwistedAssistCensusV1,
  pub inner_ligerito: F128InnerLigeritoCensusV1,
  pub matrix_accumulator: Stage4FlockMatrixAccumulatorCensusV1,
}

#[derive(Clone, Copy)]
struct TracedF128 {
  value: F128,
  reference: F128ReferenceV1,
}

struct F128AlgebraBuilder {
  trace: F128AlgebraTraceV1,
  phase: F128VerifierPhaseV1,
}

impl Default for F128AlgebraBuilder {
  fn default() -> Self {
    Self {
      trace: F128AlgebraTraceV1::default(),
      phase: F128VerifierPhaseV1::Zerocheck,
    }
  }
}

impl F128AlgebraBuilder {
  fn set_phase(&mut self, phase: F128VerifierPhaseV1) {
    self.phase = phase;
  }

  fn input(&self, value: F128, source: F128InputSourceV1) -> TracedF128 {
    TracedF128 { value, reference: F128ReferenceV1::Input(source) }
  }

  fn constant(&self, value: F128) -> TracedF128 {
    self.input(value, F128InputSourceV1::Constant(encode_f128(value)))
  }

  fn add(&mut self, left: TracedF128, right: TracedF128) -> TracedF128 {
    let reference = F128ReferenceV1::Operation(
      u64::try_from(self.trace.operations.len())
        .expect("F128 operation count fits u64"),
    );
    self.trace.operations.push(F128OperationV1::Add {
      phase: self.phase,
      left: left.reference,
      right: right.reference,
    });
    TracedF128 { value: left.value + right.value, reference }
  }

  fn multiply(&mut self, left: TracedF128, right: TracedF128) -> TracedF128 {
    let reference = F128ReferenceV1::Operation(
      u64::try_from(self.trace.operations.len())
        .expect("F128 operation count fits u64"),
    );
    self.trace.operations.push(F128OperationV1::Multiply {
      phase: self.phase,
      left: left.reference,
      right: right.reference,
    });
    TracedF128 { value: left.value * right.value, reference }
  }

  fn inverse(&mut self, value: TracedF128) -> Result<TracedF128> {
    if value.value.is_zero() {
      bail!("Stage 4 F128 trace encountered a zero inverse");
    }
    let reference = F128ReferenceV1::Operation(
      u64::try_from(self.trace.operations.len())
        .expect("F128 operation count fits u64"),
    );
    self.trace.operations.push(F128OperationV1::Inverse {
      phase: self.phase,
      value: value.reference,
    });
    Ok(TracedF128 { value: value.value.inv(), reference })
  }

  fn assert_equal(
    &mut self,
    left: TracedF128,
    right: TracedF128,
  ) -> Result<()> {
    if left.value != right.value {
      bail!("Stage 4 F128 trace contains a false native equality");
    }
    self.trace.equalities.push(F128EqualityV1 {
      phase: self.phase,
      left: left.reference,
      right: right.reference,
    });
    Ok(())
  }
}

#[derive(Clone, Debug)]
enum IndexedTranscriptEvent {
  Label(Vec<u8>),
  Observe { start: usize, count: usize },
  ObserveBytes { payload: usize, length: usize },
  Squeeze { start: usize, count: usize },
  Pow,
  Other,
}

struct IndexedTranscriptCursor<'a> {
  events: &'a [IndexedTranscriptEvent],
  index: usize,
}

impl<'a> IndexedTranscriptCursor<'a> {
  fn at_label(
    events: &'a [IndexedTranscriptEvent],
    label: &[u8],
  ) -> Result<Self> {
    let index = events
      .iter()
      .position(|event| {
        matches!(event, IndexedTranscriptEvent::Label(found) if found == label)
      })
      .ok_or_else(|| anyhow::anyhow!("missing Stage 4 transcript phase label"))?;
    Ok(Self { events, index: index + 1 })
  }

  fn observe(&mut self, count: usize) -> Result<usize> {
    match self.events.get(self.index) {
      Some(IndexedTranscriptEvent::Observe { start, count: actual })
        if *actual == count =>
      {
        self.index += 1;
        Ok(*start)
      },
      other => bail!(
        "Stage 4 transcript expected an observation of {count} values, got {other:?}"
      ),
    }
  }

  fn observe_bytes(&mut self, length: usize) -> Result<usize> {
    match self.events.get(self.index) {
      Some(IndexedTranscriptEvent::ObserveBytes {
        payload,
        length: actual,
      }) if *actual == length => {
        self.index += 1;
        Ok(*payload)
      },
      other => bail!(
        "Stage 4 transcript expected a byte observation of length {length}, got {other:?}"
      ),
    }
  }

  fn label(&mut self, label: &[u8]) -> Result<()> {
    match self.events.get(self.index) {
      Some(IndexedTranscriptEvent::Label(actual)) if actual == label => {
        self.index += 1;
        Ok(())
      },
      other => bail!(
        "Stage 4 transcript expected label {:?}, got {other:?}",
        String::from_utf8_lossy(label),
      ),
    }
  }

  fn squeeze(&mut self, count: usize) -> Result<usize> {
    while matches!(
      self.events.get(self.index),
      Some(IndexedTranscriptEvent::Pow)
    ) {
      self.index += 1;
    }
    match self.events.get(self.index) {
      Some(IndexedTranscriptEvent::Squeeze { start, count: actual })
        if *actual == count =>
      {
        self.index += 1;
        Ok(*start)
      },
      other => bail!(
        "Stage 4 transcript expected a squeeze of {count} values, got {other:?}"
      ),
    }
  }

  fn finish(self) -> Result<()> {
    if self.index != self.events.len() {
      bail!(
        "Stage 4 transcript has {} unconsumed operations",
        self.events.len() - self.index,
      );
    }
    Ok(())
  }
}

/// Export the statement-prefix locations used by Flock's circuit verifier.
pub(crate) fn export_statement_binding<Ch: Challenger>(
  recording: &RecordingChallenger<Ch>,
  statement: &Stage3StatementV1,
  circuit_digest: [u8; 32],
  public: &[F128],
  stage2_digest_public_values: [usize; 2],
) -> Result<F128StatementBindingTraceV1> {
  let events = indexed_transcript_events(recording.shape().ops());
  let mut cursor =
    IndexedTranscriptCursor::at_label(&events, b"flock-circuit-stmt-v2")?;
  let circuit_digest_payload = cursor.observe_bytes(32)?;
  let public_values_digest_payload = cursor.observe_bytes(32)?;
  if recording.payloads().get(circuit_digest_payload).map(Vec::as_slice)
    != Some(circuit_digest.as_slice())
  {
    bail!("Stage 4 circuit-digest transcript payload mismatch");
  }
  let public_digest = publics_digest(public);
  if recording.payloads().get(public_values_digest_payload).map(Vec::as_slice)
    != Some(public_digest.as_slice())
  {
    bail!("Stage 4 public-values transcript payload mismatch");
  }
  let statement_bytes = statement.to_bytes();
  let trace = F128StatementBindingTraceV1 {
    statement_domain: statement_bytes[..8]
      .try_into()
      .expect("Stage 3 statement domain has eight bytes"),
    relation_digest: *statement.relation_digest(),
    config_digest: *statement.config_digest(),
    circuit_digest,
    circuit_digest_payload: u64::try_from(circuit_digest_payload)
      .expect("payload index fits u64"),
    public_values_digest_payload: u64::try_from(public_values_digest_payload)
      .expect("payload index fits u64"),
    stage2_digest_public_values: stage2_digest_public_values
      .map(|index| u64::try_from(index).expect("public-value index fits u64")),
    public_value_count: u64::try_from(public.len())
      .expect("public-value count fits u64"),
  };
  trace.validate(public.len(), recording.payloads().len())?;
  Ok(trace)
}

/// Export Flock's real Product-GKR wiring verifier into a neutral arithmetic
/// DAG. The two circuit-static helper evaluations intentionally remain
/// private inputs, but leave this boundary as explicit matrix claims; gather
/// values likewise leave as exact packed-direct claims for the PCS replay.
pub(crate) fn export_wiring_f128_algebra<Ch: Challenger>(
  recording: &RecordingChallenger<Ch>,
  circuit: &Circuit,
  public: &[F128],
  proof: &WiringProof,
  sigma: &SigmaAssertion,
) -> Result<Stage4FlockWiringWitnessV1> {
  if !circuit.check_public(public) {
    bail!("Stage 4 wiring public vector does not satisfy the Flock circuit");
  }
  let cells = circuit.cells();
  let (nu, mu) = (cells.nu(), cells.mu());
  if proof.gkr.layers.len() != mu
    || proof.gather.len() != cells.num_gate_slots()
    || sigma.nu != nu
    || sigma.rho.len() != mu
  {
    bail!("Stage 4 wiring proof has the wrong circuit shape");
  }

  let events = indexed_transcript_events(recording.shape().ops());
  let mut cursor = IndexedTranscriptCursor::at_label(
    &events,
    b"flock-product-gkr-batched-v0",
  )?;
  let mut builder = F128AlgebraBuilder::default();
  builder.set_phase(F128VerifierPhaseV1::Wiring);
  let one = builder.constant(F128::ONE);
  let zero = builder.constant(F128::ZERO);

  let alpha = challenge_input(recording, &builder, cursor.squeeze(1)?)?;
  let beta = challenge_input(recording, &builder, cursor.squeeze(1)?)?;
  let top_lhs =
    observed_input(recording, &builder, cursor.observe(1)?, proof.gkr.top_lhs)?;
  let top_rhs =
    observed_input(recording, &builder, cursor.observe(1)?, proof.gkr.top_rhs)?;
  builder.assert_equal(top_lhs, top_rhs)?;

  let mut claim_l = top_lhs;
  let mut claim_r = top_rhs;
  let mut r_point = Vec::new();
  for (layer_index, layer) in proof.gkr.layers.iter().enumerate() {
    if layer.rounds.len() != layer_index {
      bail!("Stage 4 Product-GKR layer has the wrong round count");
    }
    let lambda = challenge_input(recording, &builder, cursor.squeeze(1)?)?;
    let lambda_claim = builder.multiply(lambda, claim_r);
    let mut running = builder.add(claim_l, lambda_claim);
    let mut next_point = Vec::with_capacity(layer_index + 1);
    for (round, &(message_one, message_infinity)) in
      layer.rounds.iter().enumerate()
    {
      let g_one =
        observed_input(recording, &builder, cursor.observe(1)?, message_one)?;
      let g_infinity = observed_input(
        recording,
        &builder,
        cursor.observe(1)?,
        message_infinity,
      )?;
      let r_eq = r_point[round];
      let one_plus_r_eq = builder.add(one, r_eq);
      let r_eq_g_one = builder.multiply(r_eq, g_one);
      let numerator = builder.add(running, r_eq_g_one);
      let inverse = builder.inverse(one_plus_r_eq)?;
      let g_zero = builder.multiply(numerator, inverse);

      let rho = challenge_input(recording, &builder, cursor.squeeze(1)?)?;
      let one_plus_rho = builder.add(one, rho);
      let zero_term = builder.multiply(g_zero, one_plus_rho);
      let one_term = builder.multiply(g_one, rho);
      let infinity_rho = builder.multiply(g_infinity, rho);
      let infinity_term = builder.multiply(infinity_rho, one_plus_rho);
      let finite_terms = builder.add(zero_term, one_term);
      running = builder.add(finite_terms, infinity_term);
      next_point.push(rho);
    }

    let vl0 =
      observed_input(recording, &builder, cursor.observe(1)?, layer.vl0)?;
    let vl1 =
      observed_input(recording, &builder, cursor.observe(1)?, layer.vl1)?;
    let vr0 =
      observed_input(recording, &builder, cursor.observe(1)?, layer.vr0)?;
    let vr1 =
      observed_input(recording, &builder, cursor.observe(1)?, layer.vr1)?;
    let left_gate = builder.multiply(vl0, vl1);
    let right_gate = builder.multiply(vr0, vr1);
    let batched_right = builder.multiply(lambda, right_gate);
    let gate = builder.add(left_gate, batched_right);
    builder.assert_equal(running, gate)?;

    let close = challenge_input(recording, &builder, cursor.squeeze(1)?)?;
    let one_plus_close = builder.add(one, close);
    let left_zero = builder.multiply(one_plus_close, vl0);
    let left_one = builder.multiply(close, vl1);
    claim_l = builder.add(left_zero, left_one);
    let right_zero = builder.multiply(one_plus_close, vr0);
    let right_one = builder.multiply(close, vr1);
    claim_r = builder.add(right_zero, right_one);
    next_point.push(close);
    r_point = next_point;
  }
  if r_point.len() != mu {
    bail!("Stage 4 Product-GKR endpoint has the wrong dimension");
  }

  let f_eval =
    observed_input(recording, &builder, cursor.observe(1)?, proof.gkr.f_eval)?;
  let g_eval =
    observed_input(recording, &builder, cursor.observe(1)?, proof.gkr.g_eval)?;
  let sigma_eval = observed_input(
    recording,
    &builder,
    cursor.observe(1)?,
    proof.gkr.s_sigma_eval,
  )?;
  let closing_digest_challenges = [cursor.squeeze(1)?, cursor.squeeze(1)?];

  if sigma.rho != r_point.iter().map(|value| value.value).collect::<Vec<_>>()
    || sigma.value != proof.gkr.s_sigma_eval
  {
    bail!("Stage 4 deferred sigma assertion disagrees with Product-GKR");
  }
  let private_values = vec![sigma.masked_id_value, sigma.live_value];
  let masked_id =
    private_input(&private_values, &builder, 0, sigma.masked_id_value)?;
  let live = private_input(&private_values, &builder, 1, sigma.live_value)?;
  let beta_plus_one = builder.add(beta, one);
  let live_tail = builder.multiply(beta_plus_one, live);
  let tail = builder.add(live_tail, one);
  let alpha_masked_id = builder.multiply(alpha, masked_id);
  let lhs_without_tail = builder.add(f_eval, alpha_masked_id);
  let lhs = builder.add(lhs_without_tail, tail);
  builder.assert_equal(claim_l, lhs)?;
  let alpha_sigma = builder.multiply(alpha, sigma_eval);
  let rhs_without_tail = builder.add(g_eval, alpha_sigma);
  let rhs = builder.add(rhs_without_tail, tail);
  builder.assert_equal(claim_r, rhs)?;

  let gather_observations =
    find_packed_direct_observations(&events, recording, &proof.gather, 2)?;
  let gather = gather_observations
    .iter()
    .zip(&proof.gather)
    .map(|(&index, &expected)| {
      observed_input(recording, &builder, index, expected)
    })
    .collect::<Result<Vec<_>>>()?;

  // Flock's gather factorization. Gate slots contribute their row-MLE
  // values; public cells contribute their exact statement words.
  let slot_weights = trace_eq_table(&mut builder, &r_point[nu..]);
  let mut recombined = zero;
  for (weight, value) in slot_weights.iter().copied().zip(gather) {
    let term = builder.multiply(weight, value);
    recombined = builder.add(recombined, term);
  }
  let rows = 1usize
    .checked_shl(u32::try_from(nu).map_err(|_| {
      anyhow::anyhow!("Stage 4 wiring row dimension does not fit u32")
    })?)
    .ok_or_else(|| anyhow::anyhow!("Stage 4 wiring row dimension overflow"))?;
  let row_weight_count = public.len().min(rows);
  let row_weights =
    trace_partial_eq_table(&mut builder, &r_point[..nu], row_weight_count)?;
  for (public_index, &value) in public.iter().enumerate() {
    let slot = cells.num_gate_slots() + public_index / rows;
    let row = public_index % rows;
    let slot_weight = slot_weights.get(slot).copied().ok_or_else(|| {
      anyhow::anyhow!("Stage 4 public cell slot is outside the cell space")
    })?;
    let row_weight = row_weights.get(row).copied().ok_or_else(|| {
      anyhow::anyhow!("Stage 4 public cell row is outside the partial eq table")
    })?;
    let cell_weight = builder.multiply(slot_weight, row_weight);
    let public_value = builder.input(
      value,
      F128InputSourceV1::PublicValue(
        u64::try_from(public_index).expect("public index fits u64"),
      ),
    );
    let term = builder.multiply(cell_weight, public_value);
    recombined = builder.add(recombined, term);
  }
  builder.assert_equal(recombined, f_eval)?;
  builder.assert_equal(f_eval, g_eval)?;

  let fixed_public_values = discover_fixed_public_values(circuit, public)?
    .into_iter()
    .map(|value| value.map(encode_f128))
    .collect::<Vec<_>>();
  let rho_challenges = r_point
    .iter()
    .map(|value| match value.reference {
      F128ReferenceV1::Input(F128InputSourceV1::Challenge(index)) => Ok(index),
      _ => bail!("Stage 4 Product-GKR endpoint is not challenge-derived"),
    })
    .collect::<Result<Vec<_>>>()?;
  let sigma_eval_observation = match sigma_eval.reference {
    F128ReferenceV1::Input(F128InputSourceV1::ObservedValue(index)) => index,
    _ => bail!("Stage 4 sigma evaluation is not transcript-observed"),
  };
  let zero_row = vec![F128::ZERO; nu];
  let mut gather_high_bits = Vec::with_capacity(cells.num_gate_slots());
  let mut packed_claim_variables = None;
  for gate in 0..cells.num_gate_slots() {
    let point = cells.gate_claim_point(gate, &zero_row);
    if point.len() < nu {
      bail!("Stage 4 gather point is shorter than its row point");
    }
    packed_claim_variables.get_or_insert(point.len());
    if packed_claim_variables != Some(point.len()) {
      bail!("Stage 4 gather points have inconsistent dimensions");
    }
    gather_high_bits.push(
      point[nu..]
        .iter()
        .map(|value| {
          if *value == F128::ZERO {
            Ok(false)
          } else if *value == F128::ONE {
            Ok(true)
          } else {
            bail!("Stage 4 gather point has a non-Boolean fixed coordinate")
          }
        })
        .collect::<Result<Vec<_>>>()?,
    );
  }
  let packed_claim_variables = packed_claim_variables.unwrap_or(nu);
  let trace = F128WiringTraceV1 {
    circuit_digest: circuit.digest(),
    public_value_count: u64::try_from(public.len())
      .expect("public-value count fits u64"),
    row_variables: u32::try_from(nu).expect("row dimension fits u32"),
    cell_variables: u32::try_from(mu).expect("cell dimension fits u32"),
    packed_claim_variables: u32::try_from(packed_claim_variables)
      .expect("packed claim dimension fits u32"),
    structure_base_variables: u32::try_from(sigma.base_bits)
      .expect("circuit-structure base dimension fits u32"),
    fixed_public_values,
    rho_challenges,
    closing_digest_challenges: closing_digest_challenges
      .map(|index| u64::try_from(index).expect("challenge index fits u64")),
    masked_id_private_value: 0,
    live_private_value: 1,
    sigma_eval_observation,
    gather_observations: gather_observations
      .into_iter()
      .map(|index| u64::try_from(index).expect("observation index fits u64"))
      .collect(),
    gather_high_bits,
    algebra: builder.trace,
  };
  trace.validate(
    public.len(),
    recording.values().len(),
    recording.challenges().len(),
    private_values.len(),
  )?;
  Ok(Stage4FlockWiringWitnessV1 {
    trace,
    private_values: private_values.into_iter().map(encode_f128).collect(),
  })
}

fn trace_eq_table(
  builder: &mut F128AlgebraBuilder,
  point: &[TracedF128],
) -> Vec<TracedF128> {
  let one = builder.constant(F128::ONE);
  let mut table = vec![one];
  for &coordinate in point {
    let zero_factor = builder.add(one, coordinate);
    let mut next = Vec::with_capacity(2 * table.len());
    for &weight in &table {
      next.push(builder.multiply(weight, zero_factor));
    }
    for &weight in &table {
      next.push(builder.multiply(weight, coordinate));
    }
    table = next;
  }
  table
}

fn trace_partial_eq_table(
  builder: &mut F128AlgebraBuilder,
  point: &[TracedF128],
  count: usize,
) -> Result<Vec<TracedF128>> {
  if count == 0 {
    return Ok(Vec::new());
  }
  let low_variables = usize::try_from(count.next_power_of_two().ilog2())
    .expect("partial eq dimension fits usize");
  if low_variables > point.len() {
    bail!("Stage 4 partial eq table exceeds its point dimension");
  }
  let mut table = trace_eq_table(builder, &point[..low_variables]);
  table.truncate(count);
  let one = builder.constant(F128::ONE);
  let high_zero =
    point[low_variables..].iter().copied().fold(one, |weight, coordinate| {
      let factor = builder.add(one, coordinate);
      builder.multiply(weight, factor)
    });
  if low_variables != point.len() {
    for weight in &mut table {
      *weight = builder.multiply(*weight, high_zero);
    }
  }
  Ok(table)
}

fn discover_fixed_public_values(
  circuit: &Circuit,
  public: &[F128],
) -> Result<Vec<Option<F128>>> {
  if !circuit.check_public(public) {
    bail!("Stage 4 cannot inspect an invalid Flock public vector");
  }
  let mut mutated = public.to_vec();
  let mut fixed = Vec::with_capacity(public.len());
  for (index, &value) in public.iter().enumerate() {
    mutated[index] = value + F128::ONE;
    fixed.push((!circuit.check_public(&mutated)).then_some(value));
    mutated[index] = value;
  }
  Ok(fixed)
}

fn find_packed_direct_observations<Ch: Challenger>(
  events: &[IndexedTranscriptEvent],
  recording: &RecordingChallenger<Ch>,
  expected: &[F128],
  ring_switched_claims: usize,
) -> Result<Vec<usize>> {
  let merged = events
    .iter()
    .position(|event| {
      matches!(event, IndexedTranscriptEvent::Label(label) if label == b"flock-merged-open-v1")
    })
    .ok_or_else(|| anyhow::anyhow!("missing Stage 4 merged-opening label"))?;
  let mut candidates = Vec::new();
  for start in merged + 1..events.len() {
    let observations = events.get(start..start + expected.len());
    let Some(observations) = observations else {
      break;
    };
    let mut indices = Vec::with_capacity(expected.len());
    let mut matches = true;
    for (event, value) in observations.iter().zip(expected) {
      let IndexedTranscriptEvent::Observe { start, count: 1 } = event else {
        matches = false;
        break;
      };
      if recording.values().get(*start) != Some(value) {
        matches = false;
        break;
      }
      indices.push(*start);
    }
    if !matches {
      continue;
    }
    let mut next = start + expected.len();
    if matches!(events.get(next), Some(IndexedTranscriptEvent::Pow)) {
      next += 1;
    }
    if matches!(
      events.get(next),
      Some(IndexedTranscriptEvent::Squeeze { count, .. })
        if *count == ring_switched_claims + expected.len()
    ) {
      candidates.push(indices);
    }
  }
  if candidates.len() != 1 {
    bail!(
      "Stage 4 found {} candidate packed-direct gather regions",
      candidates.len(),
    );
  }
  Ok(candidates.pop().expect("one candidate"))
}

/// Export Flock's real leaf-aggregation verifier into the neutral Stage 4
/// matrix-fold schema. The aggregate proof is generated natively; this path
/// records and indexes the verifier replay, then checks every indexed value
/// against the proof and canonical input/root claims.
#[allow(clippy::too_many_arguments)]
pub(crate) fn export_stage4_matrix_accumulator<Ch: Challenger>(
  recording: &RecordingChallenger<Ch>,
  domain: &[u8],
  registry: &Registry,
  circuit: &Circuit,
  assertion: &MatrixAssertion,
  structure_assertion: &SigmaAssertion,
  jagged_assertion: &JaggedAssertion,
  proof: &AggregateProof,
  accumulator: &Accumulator,
  deferred_claims: &[F128DeferredMatrixClaimV1],
) -> Result<Stage4FlockMatrixAccumulatorWitnessV1> {
  if proof.folds.len() != registry.num_boolean()
    || !proof.el_folds.is_empty()
    || proof.sigma_folds.len() != 1
    || proof.jagged_folds.len() != 1
    || accumulator.registry_digest != registry.digest()
    || accumulator.per_type.len() != registry.num_boolean()
    || !accumulator.per_element.is_empty()
    || accumulator.sigma.len() != 1
    || accumulator.jagged.len() != 1
  {
    bail!("Stage 4 Boolean matrix accumulator has the wrong class shape");
  }
  let expected_claims = assertion.claims(registry);
  if deferred_claims.len() != 2 * expected_claims.len() {
    bail!("Stage 4 matrix accumulator has the wrong deferred-claim count");
  }

  let shape = recording.shape();
  let events = indexed_transcript_events(shape.ops());
  let mut cursor =
    IndexedTranscriptCursor::at_label(&events, b"flock-aggregate-v0")?;
  let registry_digest_payload = cursor.observe_bytes(32)?;
  let prior_count_payload = cursor.observe_bytes(1)?;
  if recording.payloads().get(registry_digest_payload).map(Vec::as_slice)
    != Some(registry.digest().as_slice())
    || recording.payloads().get(prior_count_payload).map(Vec::as_slice)
      != Some(&[0_u8][..])
  {
    bail!("Stage 4 matrix accumulator prefix payload mismatch");
  }

  let mut folds = Vec::with_capacity(deferred_claims.len());
  let mut root_claims = Vec::with_capacity(deferred_claims.len());
  for (table, (((proof_a, proof_b), (claim_a, claim_b)), (root_a, root_b))) in
    proof
      .folds
      .iter()
      .zip(&expected_claims)
      .zip(&accumulator.per_type)
      .enumerate()
  {
    for (side, fold_proof, claim, root, claim_index) in [
      (F128MatrixSideV1::A, proof_a, claim_a, root_a, 2 * table),
      (F128MatrixSideV1::B, proof_b, claim_b, root_b, 2 * table + 1),
    ] {
      let deferred = &deferred_claims[claim_index];
      if deferred.matrix.registry_digest != registry.digest()
        || deferred.matrix.table
          != u64::try_from(table).expect("registry table index fits u64")
        || deferred.matrix.side != side
      {
        bail!("Stage 4 matrix accumulator claim order disagrees with lincheck");
      }
      let (fold, root_claim) = export_matrix_fold(
        recording,
        &mut cursor,
        deferred.matrix,
        claim_index,
        claim,
        fold_proof,
        root,
      )?;
      folds.push(fold);
      root_claims.push(root_claim);
    }
  }
  let structure_claims = structure_assertion.claims();
  if structure_claims.len() != 3
    || !structure_assertion.boolean_pins.is_empty()
    || structure_assertion.element_constants.is_some()
    || accumulator.sigma[0].0 != circuit.digest()
  {
    bail!("Stage 4 circuit-structure accumulator has the wrong claim shape");
  }
  cursor.label(b"flock-aggregate-sigma-v1")?;
  let circuit_digest_payload = cursor.observe_bytes(32)?;
  if recording.payloads().get(circuit_digest_payload).map(Vec::as_slice)
    != Some(circuit.digest().as_slice())
  {
    bail!("Stage 4 circuit-structure digest payload mismatch");
  }
  let structure_matrix = F128CircuitStructureMatrixIdV1 {
    circuit_digest: circuit.digest(),
    row_variables: u32::try_from(structure_assertion.nu)
      .expect("structure row dimension fits u32"),
    column_variables: u32::try_from(structure_assertion.base_bits + 3)
      .expect("structure column dimension fits u32"),
  };
  let (circuit_structure_trace, circuit_structure_root_claim) =
    export_circuit_structure_fold(
      recording,
      &mut cursor,
      structure_matrix,
      circuit_digest_payload,
      &structure_claims,
      &proof.sigma_folds[0],
      &accumulator.sigma[0].1,
    )?;
  cursor.label(b"flock-aggregate-jagged-v0")?;
  let jagged_digest_payload = cursor.observe_bytes(32)?;
  if recording.payloads().get(jagged_digest_payload).map(Vec::as_slice)
    != Some(circuit.digest().as_slice())
    || accumulator.jagged[0].0 != circuit.digest()
  {
    bail!("Stage 4 jagged digest payload mismatch");
  }
  let jagged_matrix = F128JaggedMatrixIdV1 {
    circuit_digest: circuit.digest(),
    row_variables: u32::try_from(jagged_assertion.k)
      .expect("jagged row dimension fits u32"),
    column_variables: u32::try_from(2 * (jagged_assertion.m + 1))
      .expect("jagged column dimension fits u32"),
  };
  let (jagged_trace, jagged_root_claim) = export_jagged_fold(
    recording,
    &mut cursor,
    jagged_matrix,
    jagged_digest_payload,
    jagged_assertion,
    &proof.jagged_folds[0],
    &accumulator.jagged[0].1,
  )?;
  cursor.finish()?;

  let trace = F128MatrixAccumulatorTraceV1 {
    registry_digest: registry.digest(),
    registry_digest_payload: u64::try_from(registry_digest_payload)
      .expect("payload index fits u64"),
    prior_count_payload: u64::try_from(prior_count_payload)
      .expect("payload index fits u64"),
    prior_accumulators: 0,
    folds,
  };
  trace.validate(
    deferred_claims.len(),
    recording.values().len(),
    recording.payloads().len(),
    recording.challenges().len(),
  )?;
  if root_claims.len() != trace.folds.len() {
    bail!("Stage 4 matrix accumulator root count mismatch");
  }

  let operations = shape
    .ops()
    .iter()
    .map(Stage4TranscriptOpV1::from_flock)
    .collect::<Result<Vec<_>>>()?;
  Ok(Stage4FlockMatrixAccumulatorWitnessV1 {
    shape_digest: shape.digest(),
    operations,
    observed_values: recording
      .values()
      .iter()
      .copied()
      .map(encode_f128)
      .collect(),
    byte_payloads: recording.payloads().to_vec(),
    challenges: recording
      .challenges()
      .iter()
      .copied()
      .map(encode_f128)
      .collect(),
    chained_blake3: export_chained_blake3(recording, domain)?,
    trace,
    root_claims,
    circuit_structure_trace,
    circuit_structure_root_claim,
    jagged_trace,
    jagged_root_claim,
  })
}

#[allow(clippy::too_many_arguments)]
fn export_jagged_fold<Ch: Challenger>(
  recording: &RecordingChallenger<Ch>,
  cursor: &mut IndexedTranscriptCursor<'_>,
  matrix: F128JaggedMatrixIdV1,
  circuit_digest_payload: usize,
  assertion: &JaggedAssertion,
  proof: &FoldProof,
  root: &MatrixClaim,
) -> Result<(F128JaggedAccumulatorTraceV1, Stage4F128JaggedRootClaimV1)> {
  let claims = assertion.claims();
  let row_variables = usize::try_from(matrix.row_variables)?;
  let column_variables = usize::try_from(matrix.column_variables)?;
  if claims.is_empty()
    || assertion.k != row_variables
    || 2 * (assertion.m + 1) != column_variables
    || claims.iter().any(|claim| claim.col.len() != column_variables)
    || proof.bridge.len() != claims.len()
    || proof.col_rounds.len() != column_variables
    || proof.row_rounds.len() != row_variables
  {
    bail!("Stage 4 jagged fold has an inconsistent shape");
  }

  cursor.label(b"flock-jagged-fold-v0")?;
  let shape_observation = observe_f128(
    recording,
    cursor,
    F128::new(
      u64::try_from(row_variables).expect("row dimension fits u64"),
      u64::try_from(claims.len()).expect("claim count fits u64"),
    ),
  )?;
  let bindings = claims
    .iter()
    .enumerate()
    .map(|(claim_index, claim)| {
      let row = match &claim.row {
        JaggedRowWeight::Eq(scale, point) => F128JaggedRowBindingV1::Eq {
          header_observation: observe_f128(
            recording,
            cursor,
            F128::new(
              0,
              u64::try_from(point.len()).expect("point length fits u64"),
            ),
          )?,
          scale_observation: observe_f128(recording, cursor, *scale)?,
          point_observations: observe_f128_slice(recording, cursor, point)?,
        },
        JaggedRowWeight::Combo(terms) => F128JaggedRowBindingV1::Combo {
          header_observation: observe_f128(
            recording,
            cursor,
            F128::new(
              1,
              u64::try_from(terms.len()).expect("term count fits u64"),
            ),
          )?,
          terms: terms
            .iter()
            .map(|&(coefficient, address)| {
              Ok(F128JaggedComboTermBindingV1 {
                coefficient_observation: observe_f128(
                  recording,
                  cursor,
                  coefficient,
                )?,
                address_observation: observe_f128(
                  recording,
                  cursor,
                  F128::new(u64::from(address), 0),
                )?,
                address,
              })
            })
            .collect::<Result<Vec<_>>>()?,
        },
      };
      Ok(F128JaggedFoldClaimBindingV1 {
        claim: u64::try_from(claim_index).expect("claim index fits u64"),
        row,
        column_point_observations: observe_f128_slice(
          recording, cursor, &claim.col,
        )?,
        value_observation: observe_f128(recording, cursor, claim.value)?,
      })
    })
    .collect::<Result<Vec<_>>>()?;
  let lambda_start = cursor.squeeze(claims.len())?;
  let lambda_challenges = (lambda_start..lambda_start + claims.len())
    .map(|index| u64::try_from(index).expect("challenge index fits u64"))
    .collect();
  let (column_rounds, column_challenges) =
    export_matrix_fold_rounds(recording, cursor, &proof.col_rounds)?;
  let bridge_observations = proof
    .bridge
    .iter()
    .copied()
    .map(|value| observe_f128(recording, cursor, value))
    .collect::<Result<Vec<_>>>()?;
  let mu_start = cursor.squeeze(claims.len())?;
  let mu_challenges = (mu_start..mu_start + claims.len())
    .map(|index| u64::try_from(index).expect("challenge index fits u64"))
    .collect();
  let (row_rounds, row_challenges) =
    export_matrix_fold_rounds(recording, cursor, &proof.row_rounds)?;
  let value_observation = observe_f128(recording, cursor, proof.value)?;
  if root.row.low != [F128::ONE]
    || root.col.low != [F128::ONE]
    || root.row.point != row_challenges
    || root.col.point != column_challenges
    || root.value != proof.value
  {
    bail!("Stage 4 jagged fold output mismatch");
  }
  let trace = F128JaggedAccumulatorTraceV1 {
    matrix,
    circuit_digest_payload: u64::try_from(circuit_digest_payload)
      .expect("payload index fits u64"),
    shape_observation,
    claims: bindings,
    lambda_challenges,
    column_rounds,
    bridge_observations,
    mu_challenges,
    row_rounds,
    value_observation,
  };
  trace.validate(
    claims.len(),
    recording.values().len(),
    recording.payloads().len(),
    recording.challenges().len(),
  )?;
  Ok((
    trace,
    Stage4F128JaggedRootClaimV1 {
      matrix,
      row_point: root.row.point.iter().copied().map(encode_f128).collect(),
      column_point: root.col.point.iter().copied().map(encode_f128).collect(),
      value: encode_f128(root.value),
    },
  ))
}

#[allow(clippy::too_many_arguments)]
fn export_circuit_structure_fold<Ch: Challenger>(
  recording: &RecordingChallenger<Ch>,
  cursor: &mut IndexedTranscriptCursor<'_>,
  matrix: F128CircuitStructureMatrixIdV1,
  circuit_digest_payload: usize,
  claims: &[MatrixClaim],
  proof: &FoldProof,
  root: &MatrixClaim,
) -> Result<(
  F128CircuitStructureAccumulatorTraceV1,
  Stage4F128CircuitStructureRootClaimV1,
)> {
  let row_variables = usize::try_from(matrix.row_variables)?;
  let column_variables = usize::try_from(matrix.column_variables)?;
  if claims.is_empty()
    || claims.iter().any(|claim| {
      claim.row.n_vars() != row_variables
        || claim.col.n_vars() != column_variables
    })
    || proof.bridge.len() != claims.len()
    || proof.col_rounds.len() != column_variables
    || proof.row_rounds.len() != row_variables
  {
    bail!("Stage 4 circuit-structure fold has an inconsistent shape");
  }
  cursor.label(b"flock-matrix-fold-v0")?;
  let bindings = claims
    .iter()
    .enumerate()
    .map(|(claim_index, claim)| {
      Ok(F128MatrixFoldClaimBindingV1 {
        claim: u64::try_from(claim_index).expect("claim index fits u64"),
        row_low_observations: observe_f128_slice(
          recording,
          cursor,
          &claim.row.low,
        )?,
        row_point_observations: observe_f128_slice(
          recording,
          cursor,
          &claim.row.point,
        )?,
        column_low_observations: observe_f128_slice(
          recording,
          cursor,
          &claim.col.low,
        )?,
        column_point_observations: observe_f128_slice(
          recording,
          cursor,
          &claim.col.point,
        )?,
        value_observation: observe_f128(recording, cursor, claim.value)?,
      })
    })
    .collect::<Result<Vec<_>>>()?;
  let lambda_start = cursor.squeeze(claims.len())?;
  let lambda_challenges = (lambda_start..lambda_start + claims.len())
    .map(|index| u64::try_from(index).expect("challenge index fits u64"))
    .collect();
  let (column_rounds, column_challenges) =
    export_matrix_fold_rounds(recording, cursor, &proof.col_rounds)?;
  let bridge_observations = proof
    .bridge
    .iter()
    .copied()
    .map(|value| observe_f128(recording, cursor, value))
    .collect::<Result<Vec<_>>>()?;
  let mu_start = cursor.squeeze(claims.len())?;
  let mu_challenges = (mu_start..mu_start + claims.len())
    .map(|index| u64::try_from(index).expect("challenge index fits u64"))
    .collect();
  let (row_rounds, row_challenges) =
    export_matrix_fold_rounds(recording, cursor, &proof.row_rounds)?;
  let value_observation = observe_f128(recording, cursor, proof.value)?;
  if root.row.low != [F128::ONE]
    || root.col.low != [F128::ONE]
    || root.row.point != row_challenges
    || root.col.point != column_challenges
    || root.value != proof.value
  {
    bail!("Stage 4 circuit-structure fold output mismatch");
  }
  let trace = F128CircuitStructureAccumulatorTraceV1 {
    matrix,
    circuit_digest_payload: u64::try_from(circuit_digest_payload)
      .expect("payload index fits u64"),
    claims: bindings,
    lambda_challenges,
    column_rounds,
    bridge_observations,
    mu_challenges,
    row_rounds,
    value_observation,
  };
  trace.validate(
    claims.len(),
    recording.values().len(),
    recording.payloads().len(),
    recording.challenges().len(),
  )?;
  Ok((
    trace,
    Stage4F128CircuitStructureRootClaimV1 {
      matrix,
      row_point: root.row.point.iter().copied().map(encode_f128).collect(),
      column_point: root.col.point.iter().copied().map(encode_f128).collect(),
      value: encode_f128(root.value),
    },
  ))
}

#[allow(clippy::too_many_arguments)]
fn export_matrix_fold<Ch: Challenger>(
  recording: &RecordingChallenger<Ch>,
  cursor: &mut IndexedTranscriptCursor<'_>,
  matrix: F128StaticMatrixIdV1,
  claim_index: usize,
  claim: &MatrixClaim,
  proof: &FoldProof,
  root: &MatrixClaim,
) -> Result<(F128MatrixFoldTraceV1, Stage4F128RootMatrixClaimV1)> {
  if claim.row.n_vars() != usize::try_from(matrix.variables)?
    || claim.col.n_vars() != usize::try_from(matrix.variables)?
    || proof.bridge.len() != 1
    || proof.col_rounds.len() != usize::try_from(matrix.variables)?
    || proof.row_rounds.len() != usize::try_from(matrix.variables)?
  {
    bail!("Stage 4 matrix fold has an inconsistent shape");
  }
  cursor.label(b"flock-matrix-fold-v0")?;
  let row_low = observe_f128_slice(recording, cursor, &claim.row.low)?;
  let row_point = observe_f128_slice(recording, cursor, &claim.row.point)?;
  let column_low = observe_f128_slice(recording, cursor, &claim.col.low)?;
  let column_point = observe_f128_slice(recording, cursor, &claim.col.point)?;
  let value_observation = observe_f128(recording, cursor, claim.value)?;

  let lambda_start = cursor.squeeze(1)?;
  let (column_rounds, column_challenges) =
    export_matrix_fold_rounds(recording, cursor, &proof.col_rounds)?;
  let bridge_observations = proof
    .bridge
    .iter()
    .copied()
    .map(|value| observe_f128(recording, cursor, value))
    .collect::<Result<Vec<_>>>()?;
  let mu_start = cursor.squeeze(1)?;
  let (row_rounds, row_challenges) =
    export_matrix_fold_rounds(recording, cursor, &proof.row_rounds)?;
  let root_value_observation = observe_f128(recording, cursor, proof.value)?;

  if root.row.low != [F128::ONE]
    || root.col.low != [F128::ONE]
    || root.row.point != row_challenges
    || root.col.point != column_challenges
    || root.value != proof.value
  {
    bail!("Stage 4 matrix fold output disagrees with the native accumulator");
  }

  Ok((
    F128MatrixFoldTraceV1 {
      matrix,
      claims: vec![F128MatrixFoldClaimBindingV1 {
        claim: u64::try_from(claim_index).expect("claim index fits u64"),
        row_low_observations: row_low,
        row_point_observations: row_point,
        column_low_observations: column_low,
        column_point_observations: column_point,
        value_observation,
      }],
      lambda_challenges: vec![
        u64::try_from(lambda_start).expect("challenge index fits u64"),
      ],
      column_rounds,
      bridge_observations,
      mu_challenges: vec![
        u64::try_from(mu_start).expect("challenge index fits u64"),
      ],
      row_rounds,
      value_observation: root_value_observation,
    },
    Stage4F128RootMatrixClaimV1 {
      matrix,
      row_point: root.row.point.iter().copied().map(encode_f128).collect(),
      column_point: root.col.point.iter().copied().map(encode_f128).collect(),
      value: encode_f128(root.value),
    },
  ))
}

fn export_matrix_fold_rounds<Ch: Challenger>(
  recording: &RecordingChallenger<Ch>,
  cursor: &mut IndexedTranscriptCursor<'_>,
  rounds: &[(F128, F128)],
) -> Result<(Vec<F128MatrixFoldRoundV1>, Vec<F128>)> {
  let mut exported = Vec::with_capacity(rounds.len());
  let mut challenges = Vec::with_capacity(rounds.len());
  for &(one, infinity) in rounds {
    let one_observation = observe_f128(recording, cursor, one)?;
    let infinity_observation = observe_f128(recording, cursor, infinity)?;
    let challenge = cursor.squeeze(1)?;
    challenges.push(*recording.challenges().get(challenge).ok_or_else(
      || anyhow::anyhow!("missing Stage 4 matrix-fold challenge {challenge}"),
    )?);
    exported.push(F128MatrixFoldRoundV1 {
      one_observation,
      infinity_observation,
      challenge: u64::try_from(challenge).expect("challenge index fits u64"),
    });
  }
  Ok((exported, challenges))
}

fn observe_f128_slice<Ch: Challenger>(
  recording: &RecordingChallenger<Ch>,
  cursor: &mut IndexedTranscriptCursor<'_>,
  expected: &[F128],
) -> Result<Vec<u64>> {
  let start = cursor.observe(expected.len())?;
  if recording.values().get(start..start + expected.len()) != Some(expected) {
    bail!("Stage 4 matrix-fold slice observation mismatch");
  }
  Ok(
    (start..start + expected.len())
      .map(|index| u64::try_from(index).expect("observation index fits u64"))
      .collect(),
  )
}

fn observe_f128<Ch: Challenger>(
  recording: &RecordingChallenger<Ch>,
  cursor: &mut IndexedTranscriptCursor<'_>,
  expected: F128,
) -> Result<u64> {
  let index = cursor.observe(1)?;
  if recording.values().get(index) != Some(&expected) {
    bail!("Stage 4 matrix-fold scalar observation mismatch");
  }
  Ok(u64::try_from(index).expect("observation index fits u64"))
}

#[derive(Clone)]
struct TracedZerocheckClaim {
  z: TracedF128,
  mlv_challenges: Vec<TracedF128>,
  r_rest: Vec<TracedF128>,
  a_eval: TracedF128,
  b_eval: TracedF128,
  c_eval: TracedF128,
}

#[derive(Clone)]
struct TracedPcsClaim {
  z_skip: TracedF128,
  skip_weights: Vec<TracedF128>,
  x_outer: Vec<TracedF128>,
  value: TracedF128,
}

pub(crate) struct Stage4F128AlgebraExportV1 {
  pub trace: F128AlgebraTraceV1,
  pub private_values: Vec<F128>,
  /// Canonical native assertion matching the deferred trace. Its matrix
  /// evaluations are recomputed from the registry, never copied from the
  /// verifier-ignored serialized fields.
  pub matrix_assertion: MatrixAssertion,
  pcs_claims: Vec<TracedPcsClaim>,
}

fn trace_zerocheck_f128_algebra<Ch: Challenger>(
  recording: &RecordingChallenger<Ch>,
  log_n: usize,
  proof: &ZerocheckProof,
  grinding: ZerocheckGrinding,
  builder: &mut F128AlgebraBuilder,
) -> Result<TracedZerocheckClaim> {
  const K_SKIP: usize = 6;
  const N_INNER: usize = 7;
  if log_n < K_SKIP + N_INNER {
    bail!("Stage 4 zerocheck dimension is too small");
  }
  let rounds = log_n - K_SKIP;
  let ell = 1usize << K_SKIP;
  if proof.round1_ab.len() != ell
    || proof.round1_c.len() != ell
    || proof.multilinear_rounds.len() != rounds
    || proof.grinding_nonces.len() != grinding.nonce_count(log_n)
  {
    bail!("Stage 4 zerocheck proof has the wrong shape");
  }

  let events = indexed_transcript_events(recording.shape().ops());
  let mut cursor =
    IndexedTranscriptCursor::at_label(&events, b"flock-zerocheck-v0")?;
  let r_skip_start = cursor.squeeze(K_SKIP)?;
  let r_outer_count = log_n - K_SKIP - N_INNER;
  let r_outer_start = cursor.squeeze(r_outer_count)?;
  let round1_ab_start = cursor.observe(ell)?;
  let round1_c_start = cursor.observe(ell)?;
  let z_index = cursor.squeeze(1)?;

  for offset in 0..K_SKIP {
    challenge_input(recording, builder, r_skip_start + offset)?;
  }
  let r_outer = (0..r_outer_count)
    .map(|offset| challenge_input(recording, builder, r_outer_start + offset))
    .collect::<Result<Vec<_>>>()?;
  let round1_ab = proof
    .round1_ab
    .iter()
    .copied()
    .enumerate()
    .map(|(offset, value)| {
      observed_input(recording, builder, round1_ab_start + offset, value)
    })
    .collect::<Result<Vec<_>>>()?;
  let round1_c = proof
    .round1_c
    .iter()
    .copied()
    .enumerate()
    .map(|(offset, value)| {
      observed_input(recording, builder, round1_c_start + offset, value)
    })
    .collect::<Result<Vec<_>>>()?;
  let z = challenge_input(recording, builder, z_index)?;

  let computed_c = trace_interpolate_lambda(builder, &round1_c, K_SKIP, z)?;
  if computed_c.value != proof.final_c_eval {
    bail!("Stage 4 zerocheck C interpolation disagrees with the proof");
  }
  let combined = round1_ab
    .iter()
    .copied()
    .zip(round1_c.iter().copied())
    .map(|(ab, c)| builder.add(ab, c))
    .collect::<Vec<_>>();
  let combined_at_z =
    trace_interpolate_combined(builder, &combined, K_SKIP, z)?;
  let mut running = builder.add(combined_at_z, computed_c);

  let mut r_rest = small_challenges_ghash()
    .into_iter()
    .chain(medium_challenges_ghash())
    .map(|value| builder.constant(value))
    .collect::<Vec<_>>();
  r_rest.extend(r_outer);
  if r_rest.len() != rounds {
    bail!("Stage 4 zerocheck rest-point length mismatch");
  }

  let mut mlv_challenges = Vec::with_capacity(rounds);

  for (round, &(message_one, message_infinity)) in
    proof.multilinear_rounds.iter().enumerate()
  {
    let message_one_index = cursor.observe(1)?;
    let message_infinity_index = cursor.observe(1)?;
    let rho_index = cursor.squeeze(1)?;
    let g1 =
      observed_input(recording, builder, message_one_index, message_one)?;
    let g_infinity = observed_input(
      recording,
      builder,
      message_infinity_index,
      message_infinity,
    )?;
    let rho = challenge_input(recording, builder, rho_index)?;
    mlv_challenges.push(rho);
    let one = builder.constant(F128::ONE);
    let one_plus_r_eq = builder.add(one, r_rest[round]);
    let weighted_g1 = builder.multiply(r_rest[round], g1);
    let numerator = builder.add(running, weighted_g1);
    let inverse = builder.inverse(one_plus_r_eq)?;
    let g0 = builder.multiply(numerator, inverse);
    let one_plus_rho = builder.add(one, rho);
    let term_zero = builder.multiply(g0, one_plus_rho);
    let term_one = builder.multiply(g1, rho);
    let infinity_at_rho = builder.multiply(g_infinity, rho);
    let term_infinity = builder.multiply(infinity_at_rho, one_plus_rho);
    let finite_terms = builder.add(term_zero, term_one);
    running = builder.add(finite_terms, term_infinity);
  }

  let final_a_index = cursor.observe(1)?;
  let final_b_index = cursor.observe(1)?;
  let final_a =
    observed_input(recording, builder, final_a_index, proof.final_a_eval)?;
  let final_b =
    observed_input(recording, builder, final_b_index, proof.final_b_eval)?;
  let expected = builder.multiply(final_a, final_b);
  builder.assert_equal(running, expected)?;
  Ok(TracedZerocheckClaim {
    z,
    mlv_challenges,
    r_rest,
    a_eval: final_a,
    b_eval: final_b,
    c_eval: computed_c,
  })
}

/// Export the production standard-RS Boolean PIOP through the succinct
/// lincheck boundary.  The returned DAG checks the zerocheck and the
/// reported-evaluation recombination, while its `deferred_matrix_claims`
/// name the exact registry-static A/B assertions a parent must discharge.
pub(crate) fn export_boolean_piop_f128_algebra<Ch: Challenger>(
  recording: &RecordingChallenger<Ch>,
  union: &UnionInstance<'_>,
  proof: &BooleanPiopProof,
  zerocheck_grinding: ZerocheckGrinding,
  lincheck_grinding: LincheckGrinding,
) -> Result<Stage4F128AlgebraExportV1> {
  let mut builder = F128AlgebraBuilder::default();
  let zerocheck = trace_zerocheck_f128_algebra(
    recording,
    union.m_bool(),
    &proof.zerocheck,
    zerocheck_grinding,
    &mut builder,
  )?;
  builder.set_phase(F128VerifierPhaseV1::Lincheck);

  let mut private_values =
    Vec::with_capacity(2 * union.registry().num_boolean());
  let (matrix_assertion, pcs_claims) = trace_union_lincheck_f128_algebra(
    recording,
    union,
    &proof.lincheck,
    lincheck_grinding,
    &zerocheck,
    &mut private_values,
    &mut builder,
  )?;

  builder.trace.validate(
    0,
    recording.values().len(),
    recording.challenges().len(),
    private_values.len(),
  )?;
  Ok(Stage4F128AlgebraExportV1 {
    trace: builder.trace,
    private_values,
    matrix_assertion,
    pcs_claims,
  })
}

/// Export the prefix of Flock's merged PCS verifier which is native-field
/// arithmetic: two ring switches, mixed batching, and the dense sumcheck.
/// The resulting trace deliberately stops before the forked jagged assist
/// and the inner Ligerito opening, while retaining all wires they consume.
pub(crate) fn export_merged_pcs_frontend<Ch: Challenger>(
  recording: &RecordingChallenger<Ch>,
  union: &UnionInstance<'_>,
  commitment: &Commitment,
  proof: &MergedOpenProof,
  wiring: &F128WiringTraceV1,
  algebra: &Stage4F128AlgebraExportV1,
) -> Result<F128MergedPcsFrontendTraceV1> {
  const LOG_PACKING: usize = 7;
  if algebra.pcs_claims.len() != 2 || proof.ring_switches.len() != 2 {
    bail!("Stage 4 merged PCS requires exactly two Boolean ring switches");
  }
  let dense_rounds = commitment
    .params
    .m
    .checked_sub(LOG_PACKING)
    .ok_or_else(|| anyhow::anyhow!("Stage 4 PCS commitment is too small"))?;
  if proof.merged_rounds.len() != dense_rounds {
    bail!("Stage 4 merged PCS has the wrong dense-round count");
  }

  let events = indexed_transcript_events(recording.shape().ops());
  let mut statement =
    IndexedTranscriptCursor::at_label(&events, b"flock-mixed-v1")?;
  statement.observe_bytes(32)?;
  statement.observe_bytes(8 * union.counts().len())?;
  let commitment_cap_payload =
    statement.observe_bytes(commitment.cap.len() * 32)?;
  if recording.payloads().get(commitment_cap_payload).map(Vec::as_slice)
    != Some(commitment.cap.as_flattened())
  {
    bail!("Stage 4 PCS CAP payload disagrees with the commitment");
  }

  let mut cursor =
    IndexedTranscriptCursor::at_label(&events, b"flock-merged-open-v1")?;
  let mut ring_switches = Vec::with_capacity(2);
  for ring_switch in &proof.ring_switches {
    cursor.label(b"flock-ring-switch-v0")?;
    let s_hat_start = cursor.observe(128)?;
    if recording.values().get(s_hat_start..s_hat_start + 128)
      != Some(ring_switch.s_hat_v.as_slice())
    {
      bail!("Stage 4 ring-switch slices disagree with the transcript");
    }
    let r_dprime_start = cursor.squeeze(LOG_PACKING)?;
    ring_switches.push(F128RingSwitchTraceV1 {
      s_hat_v_observations: (s_hat_start..s_hat_start + 128)
        .map(|index| u64::try_from(index).expect("observation index fits u64"))
        .collect(),
      r_dprime_challenges: (r_dprime_start..r_dprime_start + LOG_PACKING)
        .map(|index| u64::try_from(index).expect("challenge index fits u64"))
        .collect(),
    });
  }

  for &expected in &wiring.gather_observations {
    let found = cursor.observe(1)?;
    if u64::try_from(found).expect("observation index fits u64") != expected {
      bail!("Stage 4 packed-direct order disagrees with the wiring export");
    }
  }
  let batching_start = cursor.squeeze(2 + wiring.gather_observations.len())?;
  let batching_challenges = (batching_start
    ..batching_start + 2 + wiring.gather_observations.len())
    .map(|index| u64::try_from(index).expect("challenge index fits u64"))
    .collect::<Vec<_>>();
  let mut merged_rounds = Vec::with_capacity(dense_rounds);
  for &(one, infinity) in &proof.merged_rounds {
    let one_observation = cursor.observe(1)?;
    let infinity_observation = cursor.observe(1)?;
    if recording.values().get(one_observation) != Some(&one)
      || recording.values().get(infinity_observation) != Some(&infinity)
    {
      bail!("Stage 4 merged sumcheck message disagrees with the transcript");
    }
    let challenge = cursor.squeeze(1)?;
    merged_rounds.push(F128MergedPcsRoundV1 {
      one_observation: u64::try_from(one_observation)
        .expect("observation index fits u64"),
      infinity_observation: u64::try_from(infinity_observation)
        .expect("observation index fits u64"),
      challenge: u64::try_from(challenge).expect("challenge index fits u64"),
    });
  }

  // The inner opening binds q_eval as its sole packed-direct value. Its
  // point is rho and is verifier-derived, so only the value is absorbed.
  let mut inner =
    IndexedTranscriptCursor::at_label(&events, b"flock-pcs-open-batch-v0")?;
  inner.label(b"flock-pcs-packed-direct-v0")?;
  let q_eval_observation = inner.observe(1)?;
  if recording.values().get(q_eval_observation) != Some(&proof.q_eval) {
    bail!("Stage 4 q evaluation disagrees with the inner-opening transcript");
  }

  let heights = union.jagged_heights();
  if heights.is_empty() || !heights.len().is_power_of_two() {
    bail!("Stage 4 jagged PCS height table is not a power-of-two vector");
  }
  let column_variables = usize::try_from(heights.len().ilog2())
    .expect("column dimension fits usize");
  let row_variables = union.n_log();
  let expected_packed_variables = row_variables + column_variables;
  if usize::try_from(wiring.packed_claim_variables).ok()
    != Some(expected_packed_variables)
    || algebra
      .pcs_claims
      .iter()
      .any(|claim| claim.x_outer.len() != 1 + expected_packed_variables)
  {
    bail!("Stage 4 merged PCS point split disagrees with the jagged layout");
  }

  let boolean_claims = algebra
    .pcs_claims
    .iter()
    .map(|claim| F128MergedPcsBooleanClaimV1 {
      z_skip: claim.z_skip.reference,
      skip_weights: claim
        .skip_weights
        .iter()
        .map(|value| value.reference)
        .collect(),
      x_outer: claim.x_outer.iter().map(|value| value.reference).collect(),
      value: claim.value.reference,
    })
    .collect::<Vec<_>>();
  let trace = F128MergedPcsFrontendTraceV1 {
    commitment_variables: u32::try_from(commitment.params.m)
      .map_err(|error| anyhow::anyhow!("commitment dimension: {error}"))?,
    commitment_cap_payload: u64::try_from(commitment_cap_payload)
      .expect("payload index fits u64"),
    commitment_cap_nodes: u32::try_from(commitment.cap.len())
      .map_err(|error| anyhow::anyhow!("commitment CAP size: {error}"))?,
    row_variables: u32::try_from(row_variables)
      .map_err(|error| anyhow::anyhow!("row dimension: {error}"))?,
    column_variables: u32::try_from(column_variables)
      .map_err(|error| anyhow::anyhow!("column dimension: {error}"))?,
    jagged_heights: heights,
    boolean_claims,
    ring_switches,
    packed_direct_observations: wiring.gather_observations.clone(),
    batching_challenges,
    merged_rounds,
    q_eval_observation: u64::try_from(q_eval_observation)
      .expect("observation index fits u64"),
  };
  trace.validate(
    0,
    recording.values().len(),
    recording.challenges().len(),
    algebra.private_values.len(),
    algebra.trace.operations.len(),
    &recording.payloads().iter().map(Vec::len).collect::<Vec<_>>(),
    &vec![expected_packed_variables; wiring.gather_observations.len()],
  )?;
  Ok(trace)
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn export_multipoint_twisted_assist<Ch: Challenger>(
  recording: &RecordingChallenger<Ch>,
  circuit_digest: [u8; 32],
  union: &UnionInstance<'_>,
  proof: &MergedOpenProof,
  wiring: &F128WiringTraceV1,
  algebra: &Stage4F128AlgebraExportV1,
  frontend: &F128MergedPcsFrontendTraceV1,
  deferred: &JaggedAssertion,
) -> Result<Stage4FlockMultipointTwistedAssistWitnessV1> {
  let multipoint = &proof.frobenius;
  let dense_variables = frontend.merged_rounds.len();
  let witness_row_variables = usize::try_from(frontend.row_variables)
    .map_err(|error| anyhow::anyhow!("witness row dimension: {error}"))?;
  let layout_row_variables = usize::try_from(frontend.column_variables)
    .map_err(|error| anyhow::anyhow!("layout row dimension: {error}"))?;
  if multipoint.values.len() != 2
    || multipoint.values.iter().any(|values| values.len() != 128)
    || multipoint.group_values.len() != 1
    || multipoint.rounds.len() != dense_variables
    || multipoint.anchor.rounds.len() != 2 * (dense_variables + 1)
  {
    bail!("Stage 4 multipoint-twisted proof has the wrong shape");
  }
  if deferred.k != layout_row_variables
    || deferred.m != dense_variables
    || deferred.rs.len() != 2
    || deferred.groups.len() != 1
  {
    bail!("Stage 4 deferred jagged assertion has the wrong shape");
  }
  let native_layout = jagged::JaggedParams::from_heights(
    &union.jagged_heights(),
    union.n_log(),
    dense_variables,
  );
  if !deferred.check(&native_layout) {
    bail!("Stage 4 deferred jagged assertion failed direct discharge");
  }

  let events = indexed_transcript_events(recording.shape().ops());
  let mut cursor =
    IndexedTranscriptCursor::at_label(&events, b"flock-multipoint-twisted-v1")?;
  let mut dual_value_observations = Vec::with_capacity(2);
  for values in &multipoint.values {
    let mut indices = Vec::with_capacity(values.len());
    for &expected in values {
      let index = cursor.observe(1)?;
      if recording.values().get(index) != Some(&expected) {
        bail!("Stage 4 multipoint dual value disagrees with the transcript");
      }
      indices.push(
        u64::try_from(index).expect("dual-value observation index fits u64"),
      );
    }
    dual_value_observations.push(indices);
  }
  let mut group_value_observations = Vec::with_capacity(1);
  for &expected in &multipoint.group_values {
    let index = cursor.observe(1)?;
    if recording.values().get(index) != Some(&expected) {
      bail!("Stage 4 multipoint group value disagrees with the transcript");
    }
    group_value_observations.push(
      u64::try_from(index).expect("group-value observation index fits u64"),
    );
  }
  let gamma_challenge = cursor.squeeze(1)?;
  let mut multipoint_rounds = Vec::with_capacity(dense_variables);
  for &(one, infinity) in &multipoint.rounds {
    multipoint_rounds.push(export_multipoint_round(
      recording,
      &mut cursor,
      one,
      infinity,
    )?);
  }

  cursor.label(b"flock-frobenius-assist-v0")?;
  let anchor_value_observation = cursor.observe(1)?;
  if recording.values().get(anchor_value_observation)
    != Some(&multipoint.anchor.v)
  {
    bail!("Stage 4 multipoint anchor value disagrees with the transcript");
  }
  let mut anchor_rounds = Vec::with_capacity(multipoint.anchor.rounds.len());
  for &(one, infinity) in &multipoint.anchor.rounds {
    anchor_rounds.push(export_multipoint_round(
      recording,
      &mut cursor,
      one,
      infinity,
    )?);
  }
  let sigma = anchor_rounds
    .iter()
    .map(|round| {
      recording
        .challenges()
        .get(usize::try_from(round.challenge).expect("challenge index fits"))
        .copied()
        .ok_or_else(|| anyhow::anyhow!("missing Stage 4 anchor challenge"))
    })
    .collect::<Result<Vec<_>>>()?;

  let outer_gammas = frontend
    .batching_challenges
    .iter()
    .skip(2)
    .map(|&index| {
      recording
        .challenges()
        .get(usize::try_from(index).expect("challenge index fits"))
        .copied()
        .ok_or_else(|| {
          anyhow::anyhow!("missing Stage 4 outer batching challenge")
        })
    })
    .collect::<Result<Vec<_>>>()?;
  let group_column_addresses = wiring
    .gather_high_bits
    .iter()
    .map(|bits| {
      bits.iter().enumerate().try_fold(0u32, |address, (bit, set)| {
        if !set {
          return Ok(address);
        }
        let bit = u32::try_from(bit)
          .map_err(|error| anyhow::anyhow!("gather address bit: {error}"))?;
        let mask = 1u32
          .checked_shl(bit)
          .ok_or_else(|| anyhow::anyhow!("gather address exceeds u32"))?;
        Ok(address | mask)
      })
    })
    .collect::<Result<Vec<_>>>()?;
  if group_column_addresses.len() != outer_gammas.len() {
    bail!("Stage 4 scalar-group member count disagrees with batching");
  }

  for (index, claim) in deferred.rs.iter().enumerate() {
    let expected = algebra
      .pcs_claims
      .get(index)
      .ok_or_else(|| anyhow::anyhow!("missing Stage 4 Boolean PCS claim"))?;
    let expected_point = expected
      .x_outer
      .get(1 + witness_row_variables..)
      .ok_or_else(|| anyhow::anyhow!("truncated Stage 4 Boolean PCS point"))?
      .iter()
      .map(|value| value.value)
      .collect::<Vec<_>>();
    match &claim.row {
      JaggedRowWeight::Eq(scale, point)
        if *scale == F128::ONE && *point == expected_point => {},
      _ => bail!("Stage 4 ring-switch jagged row weight disagrees"),
    }
    if claim.col != sigma {
      bail!("Stage 4 ring-switch jagged column point disagrees");
    }
  }
  let (combo, dense) = &deferred.groups[0];
  if !dense.is_empty() {
    bail!("Stage 4 production scalar group unexpectedly has dense members");
  }
  let combo = combo.as_ref().ok_or_else(|| {
    anyhow::anyhow!("Stage 4 production scalar group has no combo claim")
  })?;
  let JaggedRowWeight::Combo(terms) = &combo.row else {
    bail!("Stage 4 scalar-group jagged claim is not a combo");
  };
  if terms.len() != outer_gammas.len()
    || terms.iter().zip(&outer_gammas).zip(&group_column_addresses).any(
      |((&(coefficient, address), expected_coefficient), expected_address)| {
        coefficient != *expected_coefficient || address != *expected_address
      },
    )
    || combo.col != sigma
  {
    bail!("Stage 4 scalar-group jagged claim disagrees with its members");
  }

  let private_values = deferred
    .rs
    .iter()
    .map(|claim| claim.value)
    .chain(std::iter::once(combo.value))
    .map(encode_f128)
    .collect::<Vec<_>>();
  let matrix_column_variables = dense_variables
    .checked_add(1)
    .and_then(|value| value.checked_mul(2))
    .ok_or_else(|| anyhow::anyhow!("Stage 4 jagged matrix arity overflow"))?;
  let trace = F128MultipointTwistedAssistTraceV1 {
    frontend_topology_digest: frontend.topology_digest(),
    matrix: F128JaggedMatrixIdV1 {
      circuit_digest,
      row_variables: u32::try_from(layout_row_variables)
        .map_err(|error| anyhow::anyhow!("jagged row dimension: {error}"))?,
      column_variables: u32::try_from(matrix_column_variables)
        .map_err(|error| anyhow::anyhow!("jagged column dimension: {error}"))?,
    },
    witness_row_variables: u32::try_from(witness_row_variables)
      .map_err(|error| anyhow::anyhow!("witness row dimension: {error}"))?,
    dense_variables: u32::try_from(dense_variables)
      .map_err(|error| anyhow::anyhow!("dense dimension: {error}"))?,
    family_h: family_h_constants(),
    dual_value_observations,
    group_value_observations,
    gamma_challenge: u64::try_from(gamma_challenge)
      .expect("gamma challenge index fits u64"),
    multipoint_rounds,
    anchor_value_observation: u64::try_from(anchor_value_observation)
      .expect("anchor observation index fits u64"),
    anchor_rounds,
    group_column_addresses,
    jagged_claim_private_values: (0..private_values.len())
      .map(|index| u64::try_from(index).expect("private index fits u64"))
      .collect(),
  };
  trace.validate(
    recording.values().len(),
    recording.challenges().len(),
    private_values.len(),
  )?;
  Ok(Stage4FlockMultipointTwistedAssistWitnessV1 { trace, private_values })
}

/// Export the parent-transcript inner Ligerito opening. Query words remain
/// transcript challenges; only opened F128 rows and Merkle siblings become
/// private Stage 4 witness, so the exported topology is query-value
/// independent.
pub(crate) fn export_inner_ligerito<Ch: Challenger>(
  recording: &RecordingChallenger<Ch>,
  commitment: &Commitment,
  proof: &MergedOpenProof,
  frontend: &F128MergedPcsFrontendTraceV1,
) -> Result<Stage4FlockInnerLigeritoWitnessV1> {
  const LOG_PACKING: usize = 7;
  let inner = &proof.inner;
  let ligerito_proof = &inner.ligerito;
  if !inner.ring_switches.is_empty() || !inner.batching_nonces.is_empty() {
    bail!("Stage 4 inner Ligerito is not a single packed-direct opening");
  }
  let config = commitment
    .params
    .ligerito_verifier_config()
    .map_err(|error| anyhow::anyhow!("Stage 4 Ligerito config: {error}"))?;
  if config.merkle_hash != flock_prover::hash::HashKind::Blake3 {
    bail!("Stage 4 inner Ligerito requires the pinned BLAKE3 Merkle hash");
  }
  let log_n =
    commitment.params.m.checked_sub(LOG_PACKING).ok_or_else(|| {
      anyhow::anyhow!("Stage 4 Ligerito commitment is too small")
    })?;
  let levels_count = config
    .recursive_steps
    .checked_add(1)
    .ok_or_else(|| anyhow::anyhow!("Stage 4 Ligerito level overflow"))?;
  if levels_count < 2
    || config.log_inv_rates.len() != levels_count
    || config.recursive_ks.len() != config.recursive_steps
    || config.recursive_log_msg_cols.len() != config.recursive_steps
    || config.queries.len() != levels_count
    || config.stratified.len() != levels_count
    || config.ood_samples.len() != levels_count
    || config.grinding_bits.len() != levels_count
    || config.claim_batch_grinding_bits.len() != levels_count
    || config.consistency_batch_grinding_bits.len() != levels_count
    || config.initial_k != config.initial_log_num_interleaved
    || config.initial_log_msg_cols + config.initial_k != log_n
    || ligerito_proof.initial_cap != commitment.cap
    || ligerito_proof.recursive_caps.len() != config.recursive_steps
    || ligerito_proof.recursive_proofs.len() + 1 != config.recursive_steps
    || !ligerito_proof.sumcheck_transcript.is_empty()
    || ligerito_proof.sumcheck_transcript_f256.is_empty()
    || !ligerito_proof.fold_grinding_nonces.is_empty()
    || ligerito_proof.grinding_nonces.len() != levels_count
    || ligerito_proof.consistency_batch_grinding_nonces.len() != levels_count
    || ligerito_proof.claim_batch_grinding_nonces.len()
      != config.ood_samples.iter().sum::<usize>() + levels_count
  {
    bail!("Stage 4 inner Ligerito proof/config has the wrong shape");
  }

  let events = indexed_transcript_events(recording.shape().ops());
  let mut cursor =
    IndexedTranscriptCursor::at_label(&events, b"flock-pcs-open-batch-v0")?;
  cursor.label(b"flock-pcs-packed-direct-v0")?;
  let q_eval_observation = cursor.observe(1)?;
  if q_eval_observation
    != usize::try_from(frontend.q_eval_observation)
      .expect("frontend observation index fits usize")
    || recording.values().get(q_eval_observation) != Some(&proof.q_eval)
  {
    bail!("Stage 4 inner Ligerito q-evaluation binding disagrees");
  }
  let batching_challenge = cursor.squeeze(1)?;
  let gamma =
    recording.challenges().get(batching_challenge).copied().ok_or_else(
      || anyhow::anyhow!("missing Stage 4 inner batching challenge"),
    )?;

  cursor.label(b"flock-ligerito-basis-f256-split-v0")?;
  let target_observation = cursor.observe(1)?;
  if recording.values().get(target_observation) != Some(&(gamma * proof.q_eval))
  {
    bail!("Stage 4 inner Ligerito target disagrees with q_eval batching");
  }
  let initial_cap_payload =
    export_ligerito_cap(recording, &mut cursor, &ligerito_proof.initial_cap)?;

  let mut tx_index = 0usize;
  let mut ood_index = 0usize;
  let mut private_values = Vec::new();
  let mut private_digests = Vec::new();
  let mut level_0_oods = export_ligerito_oods(
    recording,
    &mut cursor,
    ligerito_proof,
    config.ood_samples[0],
    log_n,
    false,
    &mut ood_index,
    &mut tx_index,
  )?;
  let first_message = export_ligerito_message(
    recording,
    &mut cursor,
    next_ligerito_message(ligerito_proof, &mut tx_index)?,
  )?;
  let (level_0_challenges, level_0_messages) = export_ligerito_rounds(
    recording,
    &mut cursor,
    ligerito_proof,
    config.initial_k,
    &mut tx_index,
  )?;

  let mut next_cap_payload = export_ligerito_cap(
    recording,
    &mut cursor,
    &ligerito_proof.recursive_caps[0],
  )?;
  let mut next_oods = export_ligerito_oods(
    recording,
    &mut cursor,
    ligerito_proof,
    config.ood_samples[1],
    config.initial_log_msg_cols + 1,
    true,
    &mut ood_index,
    &mut tx_index,
  )?;
  let level_0_opening = export_ligerito_opening(
    recording,
    &mut cursor,
    &config,
    0,
    &ligerito_proof.initial_proof.opened_rows,
    &ligerito_proof.initial_proof.merkle_proof,
    commitment.params.num_ntts(),
    true,
    ligerito_proof,
    &mut tx_index,
    &mut private_values,
    &mut private_digests,
  )?;
  let mut levels = vec![build_ligerito_level(
    &config,
    0,
    initial_cap_payload,
    commitment.params.num_ntts(),
    level_0_challenges,
    level_0_messages,
    std::mem::take(&mut level_0_oods),
    level_0_opening,
  )?];

  let mut final_yr_observations = Vec::new();
  for recursive_index in 0..config.recursive_steps {
    let level_index = recursive_index + 1;
    let (lane_challenges, round_messages) = export_ligerito_rounds(
      recording,
      &mut cursor,
      ligerito_proof,
      config.recursive_ks[recursive_index],
      &mut tx_index,
    )?;
    let lane_count = checked_pow2_host(config.recursive_ks[recursive_index])?;
    let is_final = level_index + 1 == levels_count;
    if is_final {
      final_yr_observations = ligerito_proof
        .final_proof
        .yr
        .iter()
        .map(|&expected| {
          let index = cursor.observe(1)?;
          if recording.values().get(index) != Some(&expected) {
            bail!("Stage 4 final Ligerito word disagrees with the transcript");
          }
          Ok(u64::try_from(index).expect("observation index fits u64"))
        })
        .collect::<Result<Vec<_>>>()?;
      let opening = export_ligerito_opening(
        recording,
        &mut cursor,
        &config,
        level_index,
        &ligerito_proof.final_proof.opened_rows,
        &ligerito_proof.final_proof.merkle_proof,
        lane_count,
        false,
        ligerito_proof,
        &mut tx_index,
        &mut private_values,
        &mut private_digests,
      )?;
      levels.push(build_ligerito_level(
        &config,
        level_index,
        next_cap_payload,
        lane_count,
        lane_challenges,
        round_messages,
        std::mem::take(&mut next_oods),
        opening,
      )?);
    } else {
      let following_level = level_index + 1;
      let following_cap_payload = export_ligerito_cap(
        recording,
        &mut cursor,
        &ligerito_proof.recursive_caps[following_level - 1],
      )?;
      let following_oods = export_ligerito_oods(
        recording,
        &mut cursor,
        ligerito_proof,
        config.ood_samples[following_level],
        config.recursive_log_msg_cols[recursive_index] + 1,
        true,
        &mut ood_index,
        &mut tx_index,
      )?;
      let opening_proof = ligerito_proof
        .recursive_proofs
        .get(level_index - 1)
        .ok_or_else(|| anyhow::anyhow!("missing Stage 4 recursive opening"))?;
      let opening = export_ligerito_opening(
        recording,
        &mut cursor,
        &config,
        level_index,
        &opening_proof.opened_rows,
        &opening_proof.merkle_proof,
        lane_count,
        true,
        ligerito_proof,
        &mut tx_index,
        &mut private_values,
        &mut private_digests,
      )?;
      levels.push(build_ligerito_level(
        &config,
        level_index,
        next_cap_payload,
        lane_count,
        lane_challenges,
        round_messages,
        std::mem::take(&mut next_oods),
        opening,
      )?);
      next_cap_payload = following_cap_payload;
      next_oods = following_oods;
    }
  }

  if tx_index != ligerito_proof.sumcheck_transcript_f256.len()
    || ood_index != ligerito_proof.ood_values.len()
  {
    bail!("Stage 4 inner Ligerito exporter left proof messages unconsumed");
  }
  let trace = F128InnerLigeritoTraceV1 {
    frontend_topology_digest: frontend.topology_digest(),
    commitment_variables: u32::try_from(commitment.params.m).map_err(
      |error| anyhow::anyhow!("Ligerito commitment dimension: {error}"),
    )?,
    q_eval_observation: u64::try_from(q_eval_observation)
      .expect("q-evaluation observation fits u64"),
    batching_challenge: u64::try_from(batching_challenge)
      .expect("batching challenge fits u64"),
    target_observation: u64::try_from(target_observation)
      .expect("target observation fits u64"),
    first_message,
    levels,
    final_yr_observations,
  };
  trace.validate(
    recording.values().len(),
    recording.challenges().len(),
    &recording.payloads().iter().map(Vec::len).collect::<Vec<_>>(),
    private_values.len(),
    private_digests.len(),
  )?;
  Ok(Stage4FlockInnerLigeritoWitnessV1 {
    trace,
    private_values,
    private_digests,
  })
}

struct ExportedLigeritoOpening {
  query_challenges: Vec<u64>,
  opened_rows: Vec<Vec<u64>>,
  merkle_paths: Vec<Vec<u64>>,
  alpha_challenges: Vec<u64>,
  intro_message: Option<F256LigeritoMessageV1>,
  beta_challenge: u64,
}

#[allow(clippy::too_many_arguments)]
fn export_ligerito_opening<Ch: Challenger>(
  recording: &RecordingChallenger<Ch>,
  cursor: &mut IndexedTranscriptCursor<'_>,
  config: &ligerito::VerifierConfig,
  level: usize,
  rows: &[Vec<F128>],
  paths: &[[u8; 32]],
  lane_count: usize,
  has_intro: bool,
  proof: &ligerito::LigeritoProof,
  tx_index: &mut usize,
  private_values: &mut Vec<[u8; 16]>,
  private_digests: &mut Vec<[u8; 32]>,
) -> Result<ExportedLigeritoOpening> {
  let schedule = config
    .stratified
    .get(level)
    .ok_or_else(|| anyhow::anyhow!("missing Stage 4 Ligerito schedule"))?;
  let query_count = schedule.queries();
  let query_start = cursor.squeeze(query_count)?;
  let alpha_count = ceil_log2_host(query_count);
  let alpha_start = cursor.squeeze(alpha_count)?;
  let path_length = schedule
    .log_block_len
    .checked_sub(schedule.cap_depth())
    .ok_or_else(|| anyhow::anyhow!("Stage 4 Ligerito cap exceeds its tree"))?;
  if rows.len() != query_count
    || rows.iter().any(|row| row.len() != lane_count)
    || paths.len() != query_count * path_length
  {
    bail!("Stage 4 Ligerito opening has the wrong row/path shape");
  }
  let opened_rows = rows
    .iter()
    .map(|row| {
      row
        .iter()
        .map(|&value| {
          let index = private_values.len();
          private_values.push(encode_f128(value));
          u64::try_from(index).expect("private-value index fits u64")
        })
        .collect::<Vec<_>>()
    })
    .collect();
  let merkle_paths = paths
    .chunks_exact(path_length)
    .map(|path| {
      path
        .iter()
        .map(|&digest| {
          let index = private_digests.len();
          private_digests.push(digest);
          u64::try_from(index).expect("private-digest index fits u64")
        })
        .collect::<Vec<_>>()
    })
    .collect();
  let intro_message = has_intro
    .then(|| {
      export_ligerito_message(
        recording,
        cursor,
        next_ligerito_message(proof, tx_index)?,
      )
    })
    .transpose()?;
  let beta_challenge = cursor.squeeze(1)?;
  Ok(ExportedLigeritoOpening {
    query_challenges: (query_start..query_start + query_count)
      .map(|index| u64::try_from(index).expect("query challenge fits u64"))
      .collect(),
    opened_rows,
    merkle_paths,
    alpha_challenges: (alpha_start..alpha_start + alpha_count)
      .map(|index| u64::try_from(index).expect("alpha challenge fits u64"))
      .collect(),
    intro_message,
    beta_challenge: u64::try_from(beta_challenge)
      .expect("beta challenge fits u64"),
  })
}

#[allow(clippy::too_many_arguments)]
fn build_ligerito_level(
  config: &ligerito::VerifierConfig,
  level: usize,
  cap_payload: usize,
  lane_count: usize,
  lane_challenges: Vec<F256IndexPairV1>,
  round_messages: Vec<F256LigeritoMessageV1>,
  ood_claims: Vec<F128LigeritoOodClaimV1>,
  opening: ExportedLigeritoOpening,
) -> Result<F128LigeritoLevelV1> {
  let schedule = &config.stratified[level];
  let log_message_columns = if level == 0 {
    config.initial_log_msg_cols
  } else {
    config.recursive_log_msg_cols[level - 1]
  };
  Ok(F128LigeritoLevelV1 {
    cap_payload: u64::try_from(cap_payload).expect("cap payload fits u64"),
    cap_nodes: u32::try_from(checked_pow2_host(schedule.cap_depth())?)
      .map_err(|error| anyhow::anyhow!("Ligerito cap size: {error}"))?,
    block_variables: u32::try_from(schedule.log_block_len)
      .map_err(|error| anyhow::anyhow!("Ligerito block dimension: {error}"))?,
    lane_count: u32::try_from(lane_count)
      .map_err(|error| anyhow::anyhow!("Ligerito lane count: {error}"))?,
    log_message_columns: u32::try_from(log_message_columns).map_err(
      |error| anyhow::anyhow!("Ligerito message dimension: {error}"),
    )?,
    summand_depths: schedule
      .summand_depths
      .iter()
      .map(|&depth| {
        u32::try_from(depth)
          .map_err(|error| anyhow::anyhow!("Ligerito summand depth: {error}"))
      })
      .collect::<Result<Vec<_>>>()?,
    query_challenges: opening.query_challenges,
    opened_rows: opening.opened_rows,
    merkle_paths: opening.merkle_paths,
    lane_challenges,
    round_messages,
    alpha_challenges: opening.alpha_challenges,
    ood_claims,
    intro_message: opening.intro_message,
    beta_challenge: opening.beta_challenge,
  })
}

#[allow(clippy::too_many_arguments)]
fn export_ligerito_oods<Ch: Challenger>(
  recording: &RecordingChallenger<Ch>,
  cursor: &mut IndexedTranscriptCursor<'_>,
  proof: &ligerito::LigeritoProof,
  count: usize,
  point_variables: usize,
  has_intro: bool,
  ood_index: &mut usize,
  tx_index: &mut usize,
) -> Result<Vec<F128LigeritoOodClaimV1>> {
  (0..count)
    .map(|_| {
      let point_start = cursor.squeeze(point_variables)?;
      let expected = *proof
        .ood_values
        .get(*ood_index)
        .ok_or_else(|| anyhow::anyhow!("missing Stage 4 Ligerito OOD value"))?;
      *ood_index += 1;
      let value_observation = cursor.observe(1)?;
      if recording.values().get(value_observation) != Some(&expected) {
        bail!("Stage 4 Ligerito OOD value disagrees with the transcript");
      }
      let intro_message = has_intro
        .then(|| {
          export_ligerito_message(
            recording,
            cursor,
            next_ligerito_message(proof, tx_index)?,
          )
        })
        .transpose()?;
      let beta_challenge = cursor.squeeze(1)?;
      Ok(F128LigeritoOodClaimV1 {
        point_challenges: (point_start..point_start + point_variables)
          .map(|index| {
            u64::try_from(index).expect("OOD point challenge fits u64")
          })
          .collect(),
        value_observation: u64::try_from(value_observation)
          .expect("OOD observation fits u64"),
        intro_message,
        beta_challenge: u64::try_from(beta_challenge)
          .expect("OOD beta challenge fits u64"),
      })
    })
    .collect()
}

fn export_ligerito_rounds<Ch: Challenger>(
  recording: &RecordingChallenger<Ch>,
  cursor: &mut IndexedTranscriptCursor<'_>,
  proof: &ligerito::LigeritoProof,
  count: usize,
  tx_index: &mut usize,
) -> Result<(Vec<F256IndexPairV1>, Vec<F256LigeritoMessageV1>)> {
  let mut challenges = Vec::with_capacity(count);
  let mut messages = Vec::with_capacity(count);
  for _ in 0..count {
    let start = cursor.squeeze(2)?;
    challenges.push(F256IndexPairV1 {
      c0: u64::try_from(start).expect("F256 challenge index fits u64"),
      c1: u64::try_from(start + 1).expect("F256 challenge index fits u64"),
    });
    messages.push(export_ligerito_message(
      recording,
      cursor,
      next_ligerito_message(proof, tx_index)?,
    )?);
  }
  Ok((challenges, messages))
}

fn export_ligerito_message<Ch: Challenger>(
  recording: &RecordingChallenger<Ch>,
  cursor: &mut IndexedTranscriptCursor<'_>,
  expected: ligerito::SumcheckMessage256,
) -> Result<F256LigeritoMessageV1> {
  let u_0 = export_ligerito_f256(recording, cursor, expected.u_0)?;
  let u_2 = export_ligerito_f256(recording, cursor, expected.u_2)?;
  Ok(F256LigeritoMessageV1 { u_0, u_2 })
}

fn export_ligerito_f256<Ch: Challenger>(
  recording: &RecordingChallenger<Ch>,
  cursor: &mut IndexedTranscriptCursor<'_>,
  expected: F256,
) -> Result<F256IndexPairV1> {
  let start = cursor.observe(2)?;
  if recording.values().get(start..start + 2)
    != Some(expected.coordinates().as_slice())
  {
    bail!("Stage 4 Ligerito F256 message disagrees with the transcript");
  }
  Ok(F256IndexPairV1 {
    c0: u64::try_from(start).expect("F256 observation index fits u64"),
    c1: u64::try_from(start + 1).expect("F256 observation index fits u64"),
  })
}

fn next_ligerito_message(
  proof: &ligerito::LigeritoProof,
  index: &mut usize,
) -> Result<ligerito::SumcheckMessage256> {
  let message =
    proof.sumcheck_transcript_f256.get(*index).copied().ok_or_else(|| {
      anyhow::anyhow!("missing Stage 4 Ligerito sumcheck message")
    })?;
  *index += 1;
  Ok(message)
}

fn export_ligerito_cap<Ch: Challenger>(
  recording: &RecordingChallenger<Ch>,
  cursor: &mut IndexedTranscriptCursor<'_>,
  cap: &[[u8; 32]],
) -> Result<usize> {
  let payload = cursor.observe_bytes(cap.len() * 32)?;
  if recording.payloads().get(payload).map(Vec::as_slice)
    != Some(cap.as_flattened())
  {
    bail!("Stage 4 Ligerito CAP disagrees with the transcript");
  }
  Ok(payload)
}

fn ceil_log2_host(value: usize) -> usize {
  if value <= 1 {
    0
  } else {
    usize::BITS as usize - (value - 1).leading_zeros() as usize
  }
}

fn checked_pow2_host(exponent: usize) -> Result<usize> {
  1usize
    .checked_shl(
      u32::try_from(exponent)
        .map_err(|error| anyhow::anyhow!("power-of-two exponent: {error}"))?,
    )
    .ok_or_else(|| anyhow::anyhow!("power-of-two dimension overflow"))
}

fn export_multipoint_round<Ch: Challenger>(
  recording: &RecordingChallenger<Ch>,
  cursor: &mut IndexedTranscriptCursor<'_>,
  expected_one: F128,
  expected_infinity: F128,
) -> Result<F128MultipointRoundV1> {
  let one_observation = cursor.observe(1)?;
  let infinity_observation = cursor.observe(1)?;
  if recording.values().get(one_observation) != Some(&expected_one)
    || recording.values().get(infinity_observation) != Some(&expected_infinity)
  {
    bail!("Stage 4 multipoint round disagrees with the transcript");
  }
  let challenge = cursor.squeeze(1)?;
  Ok(F128MultipointRoundV1 {
    one_observation: u64::try_from(one_observation)
      .expect("round observation index fits u64"),
    infinity_observation: u64::try_from(infinity_observation)
      .expect("round observation index fits u64"),
    challenge: u64::try_from(challenge)
      .expect("round challenge index fits u64"),
  })
}

fn family_h_constants() -> F128FamilyHConstantsV1 {
  let inverse_moore = ring_switch::moore_inverse();
  let row = &inverse_moore[..128];
  let ratio = row[8] * row[7].inv();
  let ratio_inverse = ratio.inv();
  let mut origin = row[7];
  for _ in 0..7 {
    origin *= ratio_inverse;
  }
  let mut corrections = [F128::ZERO; 7];
  let mut geometric = origin;
  for (address, &value) in row.iter().enumerate() {
    if address < corrections.len() {
      corrections[address] = value + geometric;
    } else {
      assert_eq!(
        value, geometric,
        "GHASH inverse-Moore row is geometric above address six",
      );
    }
    geometric *= ratio;
  }
  F128FamilyHConstantsV1 {
    geometric_origin: encode_f128(origin),
    geometric_ratio: encode_f128(ratio),
    low_corrections: corrections.map(encode_f128),
  }
}

#[allow(clippy::too_many_arguments)]
fn trace_union_lincheck_f128_algebra<Ch: Challenger>(
  recording: &RecordingChallenger<Ch>,
  union: &UnionInstance<'_>,
  proof: &LincheckProof,
  grinding: LincheckGrinding,
  zerocheck: &TracedZerocheckClaim,
  private_values: &mut Vec<F128>,
  builder: &mut F128AlgebraBuilder,
) -> Result<(MatrixAssertion, Vec<TracedPcsClaim>)> {
  const K_SKIP: usize = 6;
  let registry = union.registry();
  let nu = union.n_log();
  let col_vars = union
    .m_bool()
    .checked_sub(nu)
    .ok_or_else(|| anyhow::anyhow!("Stage 4 lincheck column underflow"))?;
  let inner_rest_len = col_vars.checked_sub(K_SKIP).ok_or_else(|| {
    anyhow::anyhow!("Stage 4 lincheck dimension is too small")
  })?;
  let ell = 1usize << K_SKIP;
  let pinned =
    registry.boolean_types().iter().filter(|ty| ty.const_pin.is_some()).count();
  if proof.rounds.len() != inner_rest_len
    || proof.z_partial.len() != ell
    || proof.grinding_nonces.len()
      != grinding.nonce_count(inner_rest_len, pinned, K_SKIP)
  {
    bail!("Stage 4 union lincheck proof has the wrong shape");
  }
  if zerocheck.mlv_challenges.len() != union.m_bool() - K_SKIP {
    bail!("Stage 4 union lincheck has the wrong zerocheck point shape");
  }

  // UnionInstance::x_ab_from_mlv, preserving the address-order split.
  let mut x_inner_rest = Vec::with_capacity(inner_rest_len);
  x_inner_rest.push(zerocheck.mlv_challenges[0]);
  x_inner_rest.extend_from_slice(&zerocheck.mlv_challenges[1 + nu..]);
  let x_outer = zerocheck.mlv_challenges[1..1 + nu].to_vec();
  if x_inner_rest.len() != inner_rest_len {
    bail!("Stage 4 union lincheck inner point has the wrong shape");
  }

  let events = indexed_transcript_events(recording.shape().ops());
  let mut cursor =
    IndexedTranscriptCursor::at_label(&events, b"flock-lincheck-v0")?;

  let alpha_index = cursor.squeeze(1)?;
  let alpha = challenge_input(recording, builder, alpha_index)?;
  let alpha_a = builder.multiply(alpha, zerocheck.a_eval);
  let mut target = builder.add(alpha_a, zerocheck.b_eval);
  let mut betas = Vec::with_capacity(registry.num_boolean());
  let mut pin_evals = Vec::with_capacity(registry.num_boolean());
  for (ty, &count) in registry.boolean_types().iter().zip(union.counts()) {
    if ty.const_pin.is_some() {
      let beta_index = cursor.squeeze(1)?;
      let beta = challenge_input(recording, builder, beta_index)?;
      let prefix_sum = trace_eq_prefix_sum(builder, &x_outer, count)?;
      let pin_term = builder.multiply(beta, prefix_sum);
      target = builder.add(target, pin_term);
      betas.push(Some(beta));
      pin_evals.push(Some(prefix_sum.value));
    } else {
      betas.push(None);
      pin_evals.push(None);
    }
  }

  let mut running = target;
  let mut r_rounds = Vec::with_capacity(inner_rest_len);
  for &(message_one, message_infinity) in &proof.rounds {
    let one_index = cursor.observe(1)?;
    let infinity_index = cursor.observe(1)?;
    let challenge_index = cursor.squeeze(1)?;
    let q1 = observed_input(recording, builder, one_index, message_one)?;
    let q_infinity =
      observed_input(recording, builder, infinity_index, message_infinity)?;
    let r = challenge_input(recording, builder, challenge_index)?;
    let q0 = builder.add(running, q1);
    let q0_plus_q1 = builder.add(q0, q1);
    let c1 = builder.add(q0_plus_q1, q_infinity);
    let infinity_r = builder.multiply(q_infinity, r);
    let infinity_r_squared = builder.multiply(infinity_r, r);
    let linear = builder.multiply(c1, r);
    let nonconstant = builder.add(infinity_r_squared, linear);
    running = builder.add(nonconstant, q0);
    r_rounds.push(r);
  }

  let z_partial_start = cursor.observe(ell)?;
  let z_partial = proof
    .z_partial
    .iter()
    .copied()
    .enumerate()
    .map(|(offset, value)| {
      observed_input(recording, builder, z_partial_start + offset, value)
    })
    .collect::<Result<Vec<_>>>()?;
  let mut rr = r_rounds;
  rr.reverse();

  // The fresh skip point and collapsed z-claim are consumed by PCS later.
  let inner_skip_index = cursor.squeeze(1)?;
  let inner_skip = challenge_input(recording, builder, inner_skip_index)?;
  let inner_skip_weights =
    trace_lagrange_weights_phi8(builder, K_SKIP, inner_skip)?;
  let w = trace_inner_product(builder, &inner_skip_weights, &z_partial)?;

  // Flock's accumulator path: derive canonical per-matrix values, check that
  // they reproduce the sumcheck target, then export each static claim.  The
  // direct production verifier ignores `proof.matrix_evals`, so copying
  // those serialized fields here would make Stage 4 stricter than Flock.
  let original_skip_weights =
    trace_lagrange_weights_phi8(builder, K_SKIP, zerocheck.z)?;
  let registry_digest = registry.digest();
  let mut reported = builder.constant(F128::ZERO);
  let mut matrix_evals = Vec::with_capacity(registry.num_boolean());
  for (table, ((ty, slot), beta)) in registry
    .boolean_types()
    .iter()
    .zip(registry.slots())
    .zip(betas.iter().copied())
    .enumerate()
  {
    let inner = ty.k_log - K_SKIP;
    let native_row = Weight::low_eq(
      original_skip_weights.iter().map(|value| value.value).collect(),
      x_inner_rest[..inner].iter().map(|value| value.value).collect(),
    );
    let native_column = Weight::low_eq(
      z_partial.iter().map(|value| value.value).collect(),
      rr[..inner].iter().map(|value| value.value).collect(),
    );
    let matrix_eval = (
      bilinear(&native_row, &native_column, &ty.a_0),
      bilinear(&native_row, &native_column, &ty.b_0),
    );
    matrix_evals.push(matrix_eval);
    let advice_index = private_values.len();
    private_values.extend([matrix_eval.0, matrix_eval.1]);
    let advice_a =
      private_input(private_values, builder, advice_index, matrix_eval.0)?;
    let advice_b =
      private_input(private_values, builder, advice_index + 1, matrix_eval.1)?;
    let row_prefix =
      trace_eq_prefix_weight(builder, &x_inner_rest[inner..], slot.prefix);
    let column_prefix =
      trace_eq_prefix_weight(builder, &rr[inner..], slot.prefix);
    let alpha_a = builder.multiply(alpha, advice_a);
    let matrix_pair = builder.add(alpha_a, advice_b);
    let row_scaled = builder.multiply(row_prefix, matrix_pair);
    let slot_term = builder.multiply(column_prefix, row_scaled);
    reported = builder.add(reported, slot_term);

    if let (Some(column), Some(beta)) = (ty.const_pin, beta) {
      let low = column & (ell - 1);
      let high = column >> K_SKIP;
      let high_weight = trace_eq_prefix_weight(builder, &rr[..inner], high);
      let column_weight = builder.multiply(z_partial[low], high_weight);
      let beta_weight = builder.multiply(beta, column_weight);
      let pin_term = builder.multiply(column_prefix, beta_weight);
      reported = builder.add(reported, pin_term);
    }

    let matrix_base = F128StaticMatrixIdV1 {
      registry_digest,
      table: u64::try_from(table).expect("table index fits u64"),
      side: F128MatrixSideV1::A,
      variables: u32::try_from(ty.k_log).expect("matrix arity fits u32"),
    };
    let row = F128StructuredWeightV1 {
      low: original_skip_weights.iter().map(|value| value.reference).collect(),
      point: x_inner_rest[..inner]
        .iter()
        .map(|value| value.reference)
        .collect(),
    };
    let column = F128StructuredWeightV1 {
      low: z_partial.iter().map(|value| value.reference).collect(),
      point: rr[..inner].iter().map(|value| value.reference).collect(),
    };
    builder.trace.deferred_matrix_claims.extend([
      F128DeferredMatrixClaimV1 {
        phase: F128VerifierPhaseV1::Lincheck,
        matrix: matrix_base,
        row: row.clone(),
        column: column.clone(),
        value: advice_a.reference,
      },
      F128DeferredMatrixClaimV1 {
        phase: F128VerifierPhaseV1::Lincheck,
        matrix: F128StaticMatrixIdV1 {
          side: F128MatrixSideV1::B,
          ..matrix_base
        },
        row,
        column,
        value: advice_b.reference,
      },
    ]);
  }
  debug_assert_eq!(private_values.len(), 2 * registry.num_boolean());
  builder.assert_equal(reported, running)?;
  let matrix_assertion = MatrixAssertion {
    alpha: alpha.value,
    z_skip: SkipPoint::Phi8(zerocheck.z.value),
    x_inner_rest: x_inner_rest.iter().map(|value| value.value).collect(),
    rr: rr.iter().map(|value| value.value).collect(),
    z_partial: z_partial.iter().map(|value| value.value).collect(),
    betas: betas.iter().map(|beta| beta.map(|value| value.value)).collect(),
    pin_point: x_outer.iter().map(|value| value.value).collect(),
    pin_evals,
    target: running.value,
    evals: matrix_evals,
  };

  // Reproduce UnionInstance::{ab,c}_claim_point exactly, then retain the
  // reference-bearing form for the merged PCS lowering. The ring-switch
  // verifier calls this complete post-skip point `x_outer`.
  let frozen =
    union.m_total().checked_sub(union.m_bool()).ok_or_else(|| {
      anyhow::anyhow!("Stage 4 Boolean union dimension underflow")
    })?;
  let zero = builder.constant(F128::ZERO);
  let mut ab_x_outer = Vec::with_capacity(1 + nu + rr.len() - 1 + frozen);
  ab_x_outer.push(rr[0]);
  ab_x_outer.extend_from_slice(&x_outer);
  ab_x_outer.extend_from_slice(&rr[1..]);
  ab_x_outer.extend(std::iter::repeat_n(zero, frozen));
  let mut c_x_outer = zerocheck.r_rest.clone();
  c_x_outer.extend(std::iter::repeat_n(zero, frozen));
  let pcs_claims = vec![
    TracedPcsClaim {
      z_skip: inner_skip,
      skip_weights: inner_skip_weights,
      x_outer: ab_x_outer,
      value: w,
    },
    TracedPcsClaim {
      z_skip: zerocheck.z,
      skip_weights: original_skip_weights,
      x_outer: c_x_outer,
      value: zerocheck.c_eval,
    },
  ];

  let native_ab = union.ab_claim_point(
    SkipPoint::Phi8(inner_skip.value),
    &rr.iter().map(|value| value.value).collect::<Vec<_>>(),
    &x_outer.iter().map(|value| value.value).collect::<Vec<_>>(),
  );
  let native_c = union.c_claim_point(
    SkipPoint::Phi8(zerocheck.z.value),
    &zerocheck.r_rest.iter().map(|value| value.value).collect::<Vec<_>>(),
  );
  for ((traced, native), expected_value) in pcs_claims
    .iter()
    .zip([native_ab, native_c])
    .zip([w.value, zerocheck.c_eval.value])
  {
    let native_x_outer = native
      .x_inner_rest
      .iter()
      .chain(&native.x_outer)
      .copied()
      .collect::<Vec<_>>();
    if traced.x_outer.iter().map(|value| value.value).collect::<Vec<_>>()
      != native_x_outer
      || traced.z_skip.value
        != match native.z_skip {
          SkipPoint::Phi8(value) => value,
          SkipPoint::Ag(_) => {
            bail!("Stage 4 RS export encountered an AG PCS claim")
          },
        }
      || traced.value.value != expected_value
    {
      bail!("Stage 4 Boolean PCS claim disagrees with the native union point");
    }
  }
  Ok((matrix_assertion, pcs_claims))
}

fn trace_eq_prefix_weight(
  builder: &mut F128AlgebraBuilder,
  coordinates: &[TracedF128],
  bits: usize,
) -> TracedF128 {
  let one = builder.constant(F128::ONE);
  coordinates.iter().copied().enumerate().fold(
    one,
    |acc, (index, coordinate)| {
      let factor = if (bits >> index) & 1 == 1 {
        coordinate
      } else {
        builder.add(one, coordinate)
      };
      builder.multiply(acc, factor)
    },
  )
}

fn trace_eq_prefix_sum(
  builder: &mut F128AlgebraBuilder,
  point: &[TracedF128],
  count: usize,
) -> Result<TracedF128> {
  let capacity = 1usize
    .checked_shl(u32::try_from(point.len()).unwrap_or(u32::MAX))
    .ok_or_else(|| anyhow::anyhow!("Stage 4 prefix-sum dimension overflow"))?;
  if count > capacity {
    bail!("Stage 4 prefix-sum count exceeds its domain");
  }
  let one = builder.constant(F128::ONE);
  if count == capacity {
    return Ok(one);
  }
  let mut result = builder.constant(F128::ZERO);
  let mut high = one;
  for index in (0..point.len()).rev() {
    if (count >> index) & 1 == 1 {
      let zero_weight = builder.add(one, point[index]);
      let term = builder.multiply(high, zero_weight);
      result = builder.add(result, term);
      high = builder.multiply(high, point[index]);
    } else {
      let zero_weight = builder.add(one, point[index]);
      high = builder.multiply(high, zero_weight);
    }
  }
  Ok(result)
}

fn trace_lagrange_weights_phi8(
  builder: &mut F128AlgebraBuilder,
  dimension: usize,
  point: TracedF128,
) -> Result<Vec<TracedF128>> {
  let count = 1usize << dimension;
  let nodes = &PHI_8_TABLE[..count];
  let scale = trace_coset_scale(builder, nodes, dimension, point)?;
  nodes
    .iter()
    .map(|&node| {
      let node = builder.constant(node);
      let delta = builder.add(point, node);
      let inverse = builder.inverse(delta)?;
      Ok(builder.multiply(scale, inverse))
    })
    .collect()
}

fn trace_inner_product(
  builder: &mut F128AlgebraBuilder,
  left: &[TracedF128],
  right: &[TracedF128],
) -> Result<TracedF128> {
  if left.len() != right.len() {
    bail!("Stage 4 inner-product operands have different lengths");
  }
  Ok(left.iter().copied().zip(right.iter().copied()).fold(
    builder.constant(F128::ZERO),
    |acc, (left, right)| {
      let term = builder.multiply(left, right);
      builder.add(acc, term)
    },
  ))
}

fn trace_interpolate_lambda(
  builder: &mut F128AlgebraBuilder,
  values: &[TracedF128],
  dimension: usize,
  point: TracedF128,
) -> Result<TracedF128> {
  let count = 1usize << dimension;
  let nodes = &PHI_8_TABLE[count..2 * count];
  let scale = trace_coset_scale(builder, nodes, dimension, point)?;
  let mut result = builder.constant(F128::ZERO);
  for (&node, value) in nodes.iter().zip(values.iter().copied()) {
    let delta = builder.add(point, builder.constant(node));
    let inverse = builder.inverse(delta)?;
    let weight = builder.multiply(scale, inverse);
    let term = builder.multiply(weight, value);
    result = builder.add(result, term);
  }
  Ok(result)
}

fn trace_interpolate_combined(
  builder: &mut F128AlgebraBuilder,
  values: &[TracedF128],
  dimension: usize,
  point: TracedF128,
) -> Result<TracedF128> {
  let count = 1usize << dimension;
  let nodes = &PHI_8_TABLE[..2 * count];
  let scale = trace_coset_scale(builder, nodes, dimension + 1, point)?;
  let mut result = builder.constant(F128::ZERO);
  for (&node, value) in nodes[count..].iter().zip(values.iter().copied()) {
    let delta = builder.add(point, builder.constant(node));
    let inverse = builder.inverse(delta)?;
    let weighted = builder.multiply(scale, inverse);
    let term = builder.multiply(weighted, value);
    result = builder.add(result, term);
  }
  Ok(result)
}

fn trace_coset_scale(
  builder: &mut F128AlgebraBuilder,
  nodes: &[F128],
  dimension: usize,
  point: TracedF128,
) -> Result<TracedF128> {
  let mut vanishing = builder.constant(F128::ONE);
  for &node in nodes {
    let delta = builder.add(point, builder.constant(node));
    vanishing = builder.multiply(vanishing, delta);
  }
  if vanishing.value.is_zero() {
    bail!("Stage 4 F128 interpolation point hit a fixed node");
  }
  let denominator_inverse = subspace_denominator_pair(dimension).1;
  Ok(builder.multiply(vanishing, builder.constant(denominator_inverse)))
}

fn observed_input<Ch: Challenger>(
  recording: &RecordingChallenger<Ch>,
  builder: &F128AlgebraBuilder,
  index: usize,
  expected: F128,
) -> Result<TracedF128> {
  let value = *recording
    .values()
    .get(index)
    .ok_or_else(|| anyhow::anyhow!("missing Stage 4 observed value {index}"))?;
  if value != expected {
    bail!("Stage 4 observed value {index} disagrees with zerocheck proof");
  }
  Ok(builder.input(
    value,
    F128InputSourceV1::ObservedValue(
      u64::try_from(index).expect("observation index fits u64"),
    ),
  ))
}

fn challenge_input<Ch: Challenger>(
  recording: &RecordingChallenger<Ch>,
  builder: &F128AlgebraBuilder,
  index: usize,
) -> Result<TracedF128> {
  let value = *recording
    .challenges()
    .get(index)
    .ok_or_else(|| anyhow::anyhow!("missing Stage 4 challenge {index}"))?;
  Ok(builder.input(
    value,
    F128InputSourceV1::Challenge(
      u64::try_from(index).expect("challenge index fits u64"),
    ),
  ))
}

fn private_input(
  values: &[F128],
  builder: &F128AlgebraBuilder,
  index: usize,
  expected: F128,
) -> Result<TracedF128> {
  let value = *values
    .get(index)
    .ok_or_else(|| anyhow::anyhow!("missing Stage 4 private value {index}"))?;
  if value != expected {
    bail!("Stage 4 private value {index} disagrees with lincheck proof");
  }
  Ok(builder.input(
    value,
    F128InputSourceV1::PrivateValue(
      u64::try_from(index).expect("private-value index fits u64"),
    ),
  ))
}

fn indexed_transcript_events(
  operations: &[TranscriptOp],
) -> Vec<IndexedTranscriptEvent> {
  fn walk(
    operations: &[TranscriptOp],
    observed: &mut usize,
    payloads: &mut usize,
    challenges: &mut usize,
    output: &mut Vec<IndexedTranscriptEvent>,
  ) {
    for operation in operations {
      match operation {
        TranscriptOp::Label(label) => {
          output.push(IndexedTranscriptEvent::Label(label.clone()));
        },
        TranscriptOp::ObserveScalar => {
          output.push(IndexedTranscriptEvent::Observe {
            start: *observed,
            count: 1,
          });
          *observed += 1;
        },
        TranscriptOp::ObserveSlice(count) => {
          output.push(IndexedTranscriptEvent::Observe {
            start: *observed,
            count: *count,
          });
          *observed += *count;
        },
        TranscriptOp::SqueezeScalar => {
          output.push(IndexedTranscriptEvent::Squeeze {
            start: *challenges,
            count: 1,
          });
          *challenges += 1;
        },
        TranscriptOp::SqueezeSlice(count) => {
          output.push(IndexedTranscriptEvent::Squeeze {
            start: *challenges,
            count: *count,
          });
          *challenges += *count;
        },
        TranscriptOp::ObserveBytes(length) => {
          output.push(IndexedTranscriptEvent::ObserveBytes {
            payload: *payloads,
            length: *length,
          });
          *payloads += 1;
        },
        TranscriptOp::Pow { .. } | TranscriptOp::LegacyPow { .. } => {
          output.push(IndexedTranscriptEvent::Pow);
          *payloads += 1;
        },
        TranscriptOp::Forked { ops, .. } => {
          walk(ops, observed, payloads, challenges, output);
        },
        TranscriptOp::Merge { .. } => {
          output.push(IndexedTranscriptEvent::Other);
        },
      }
    }
  }

  let mut output = Vec::new();
  walk(operations, &mut 0, &mut 0, &mut 0, &mut output);
  output
}

fn export_chained_blake3<Ch: Challenger>(
  recording: &RecordingChallenger<Ch>,
  domain: &[u8],
) -> Result<ChainedBlake3TranscriptV1> {
  let shape = recording.shape();
  let stream = shape.stream_words_duplex(domain);
  let forked = trace_duplex_forked(
    shape.ops(),
    &stream,
    recording.values(),
    recording.payloads(),
  );
  if stream.forks.len() != forked.children.len() {
    bail!("Stage 4 Flock child-chain count mismatch");
  }
  let parent = export_chain(&stream, &forked.parent)?;
  let children = stream
    .forks
    .iter()
    .zip(&forked.children)
    .map(|(fork_stream, child)| {
      if fork_stream.label != child.label {
        bail!("Stage 4 Flock child-chain label mismatch");
      }
      Ok(ChainedBlake3ChildV1 {
        label: child.label.clone(),
        chain: export_chain(&fork_stream.stream, &child.trace)?,
        parent_seed_squeeze: count_u64(
          child.seed_squeeze,
          "parent seed squeeze",
        )?,
        child_seed_word: count_u64(child.child_seed_word, "child seed word")?,
        child_digest_squeeze: count_u64(
          child.digest_squeeze,
          "child digest squeeze",
        )?,
        parent_digest_word: count_u64(
          child.parent_digest_word,
          "parent digest word",
        )?,
      })
    })
    .collect::<Result<Vec<_>>>()?;
  let challenge_sources = export_challenge_sources(
    shape.ops(),
    &parent,
    &children,
    recording.challenges().len(),
  )?;
  let pow_constraints =
    export_pow_constraints(shape.ops(), &parent, &children)?;
  let exported = ChainedBlake3TranscriptV1 {
    domain: domain.to_vec(),
    parent,
    children,
    challenge_sources,
    pow_constraints,
  };
  let payload_lengths =
    recording.payloads().iter().map(Vec::len).collect::<Vec<_>>();
  exported
    .validate(recording.values().len(), &payload_lengths)
    .map_err(|error| anyhow::anyhow!("invalid Stage 4 Flock trace: {error}"))?;
  Ok(exported)
}

fn export_pow_constraints(
  operations: &[TranscriptOp],
  parent: &ChainedBlake3ChainV1,
  children: &[ChainedBlake3ChildV1],
) -> Result<Vec<ChainedBlake3PowConstraintV1>> {
  let mut constraints = Vec::new();
  let mut next_child = 0usize;
  append_pow_constraints(
    operations,
    0,
    parent,
    children,
    &mut next_child,
    &mut constraints,
  )?;
  if next_child != children.len() {
    bail!("Stage 4 Flock PoW map omitted a child chain");
  }
  Ok(constraints)
}

fn append_pow_constraints(
  operations: &[TranscriptOp],
  chain_index: usize,
  chain: &ChainedBlake3ChainV1,
  children: &[ChainedBlake3ChildV1],
  next_child: &mut usize,
  output: &mut Vec<ChainedBlake3PowConstraintV1>,
) -> Result<()> {
  let mut squeeze_index = 0usize;
  let mut pending_pow = None;
  for operation in operations {
    match operation {
      TranscriptOp::Pow { bits } => {
        if pending_pow.replace(*bits).is_some() {
          bail!("Stage 4 Flock transcript has nested fused PoW markers");
        }
      },
      TranscriptOp::SqueezeScalar | TranscriptOp::SqueezeSlice(_) => {
        if let Some(bits) = pending_pow.take() {
          let row = chain
            .squeeze_words
            .get(squeeze_index)
            .and_then(|words| words.first())
            .ok_or_else(|| {
              anyhow::anyhow!("Stage 4 Flock PoW names a missing squeeze row")
            })?
            .row;
          output.push(ChainedBlake3PowConstraintV1 {
            chain: count_u64(chain_index, "PoW chain")?,
            row,
            bits,
          });
        }
        squeeze_index += 1;
      },
      TranscriptOp::LegacyPow { .. } => {
        bail!("Stage 4 does not accept legacy non-fused Flock PoW")
      },
      TranscriptOp::Forked { ops, .. } => {
        if pending_pow.is_some() {
          bail!("Stage 4 Flock PoW is not followed by a squeeze");
        }
        let child_index = *next_child;
        *next_child += 1;
        let child = children.get(child_index).ok_or_else(|| {
          anyhow::anyhow!("Stage 4 Flock PoW map names a missing child")
        })?;
        append_pow_constraints(
          ops,
          child_index + 1,
          &child.chain,
          children,
          next_child,
          output,
        )?;
      },
      _ if pending_pow.is_some() => {
        bail!("Stage 4 Flock PoW is not followed by a squeeze")
      },
      _ => {},
    }
  }
  if pending_pow.is_some() {
    bail!("Stage 4 Flock transcript ends with an incomplete PoW")
  }
  if squeeze_index != chain.squeeze_words.len() {
    bail!(
      "Stage 4 Flock PoW map consumed {squeeze_index} squeezes; trace has {}",
      chain.squeeze_words.len(),
    );
  }
  Ok(())
}

fn export_challenge_sources(
  operations: &[TranscriptOp],
  parent: &ChainedBlake3ChainV1,
  children: &[ChainedBlake3ChildV1],
  expected_challenges: usize,
) -> Result<Vec<ChainedBlake3ChallengeSourceV1>> {
  let mut sources = Vec::with_capacity(expected_challenges);
  let mut next_child = 0usize;
  append_challenge_sources(
    operations,
    0,
    parent,
    children,
    &mut next_child,
    &mut sources,
  )?;
  if next_child != children.len() {
    bail!("Stage 4 Flock challenge map omitted a child chain");
  }
  if sources.len() != expected_challenges {
    bail!(
      "Stage 4 Flock challenge-source count mismatch: expected {expected_challenges}, got {}",
      sources.len(),
    );
  }
  Ok(sources)
}

fn append_challenge_sources(
  operations: &[TranscriptOp],
  chain_index: usize,
  chain: &ChainedBlake3ChainV1,
  children: &[ChainedBlake3ChildV1],
  next_child: &mut usize,
  output: &mut Vec<ChainedBlake3ChallengeSourceV1>,
) -> Result<()> {
  let mut squeeze_index = 0usize;
  for operation in operations {
    let words = match operation {
      TranscriptOp::SqueezeScalar => Some(1),
      TranscriptOp::SqueezeSlice(count) => Some(*count),
      TranscriptOp::LegacyPow { .. } => {
        squeeze_index += 1;
        None
      },
      TranscriptOp::Forked { ops, .. } => {
        let child_index = *next_child;
        *next_child += 1;
        let child = children.get(child_index).ok_or_else(|| {
          anyhow::anyhow!("Stage 4 Flock challenge map names a missing child")
        })?;
        append_challenge_sources(
          ops,
          child_index + 1,
          &child.chain,
          children,
          next_child,
          output,
        )?;
        None
      },
      _ => None,
    };
    if let Some(words) = words {
      let available =
        chain.squeeze_words.get(squeeze_index).ok_or_else(|| {
          anyhow::anyhow!("Stage 4 Flock challenge map names a missing squeeze")
        })?;
      if available.len() != words {
        bail!(
          "Stage 4 Flock squeeze width mismatch: expected {words}, got {}",
          available.len(),
        );
      }
      for squeeze_word in 0..words {
        output.push(ChainedBlake3ChallengeSourceV1 {
          chain: count_u64(chain_index, "challenge chain")?,
          squeeze: count_u64(squeeze_index, "challenge squeeze")?,
          squeeze_word: count_u64(squeeze_word, "challenge word")?,
        });
      }
      squeeze_index += 1;
    }
  }
  if squeeze_index != chain.squeeze_words.len() {
    bail!(
      "Stage 4 Flock challenge map consumed {squeeze_index} squeezes; trace has {}",
      chain.squeeze_words.len(),
    );
  }
  Ok(())
}

fn export_chain(
  stream: &Stream,
  trace: &FsChainTrace,
) -> Result<ChainedBlake3ChainV1> {
  let row_count = trace.rows.len();
  if trace.links.len() != row_count
    || trace.block_offsets.len() != row_count
    || trace.block_word_counts.len() != row_count
  {
    bail!("Stage 4 Flock compression-trace column mismatch");
  }
  let stream_words = stream
    .words
    .iter()
    .map(|source| {
      Ok(match *source {
        StreamWord::Const(value) => {
          StreamWordSourceV1::Constant(encode_f128(value))
        },
        StreamWord::Value(index) => StreamWordSourceV1::ObservedValue(
          count_u64(index, "observed-value index")?,
        ),
        StreamWord::Bytes { payload, word } => {
          StreamWordSourceV1::BytePayload {
            payload: count_u64(payload, "payload index")?,
            word: count_u64(word, "payload word")?,
          }
        },
      })
    })
    .collect::<Result<Vec<_>>>()?;
  let compression_rows = (0..row_count)
    .map(|index| {
      let (chaining_value, message, counter, block_length, flags) =
        trace.rows[index];
      let link = trace.links[index];
      Ok(CompressionRowV1 {
        chaining_value,
        message,
        counter,
        block_length,
        flags,
        link: CompressionLinkV1 {
          chaining_value: match link.cv {
            CvSource::Iv => ChainingValueSourceV1::Iv,
            CvSource::Row(row) => {
              ChainingValueSourceV1::Row(count_u64(row, "chaining-value row")?)
            },
            CvSource::RowHi(row) => ChainingValueSourceV1::RowHigh(count_u64(
              row,
              "high chaining-value row",
            )?),
          },
          right: link
            .right
            .map(|row| count_u64(row, "right row"))
            .transpose()?,
          repeats: link
            .repeats
            .map(|row| count_u64(row, "repeat row"))
            .transpose()?,
        },
        stream_offset: trace.block_offsets[index]
          .map(|offset| count_u64(offset, "stream offset"))
          .transpose()?,
        stream_word_count: u8::try_from(trace.block_word_counts[index])
          .map_err(|error| anyhow::anyhow!("stream word count: {error}"))?,
      })
    })
    .collect::<Result<Vec<_>>>()?;
  let squeeze_words = trace
    .squeeze_words
    .iter()
    .map(|sources| {
      sources
        .iter()
        .map(|&(row, word)| {
          Ok(CompressionOutputWordV1 {
            row: count_u64(row, "squeeze row")?,
            word: u8::try_from(word)
              .map_err(|error| anyhow::anyhow!("squeeze word: {error}"))?,
          })
        })
        .collect::<Result<Vec<_>>>()
    })
    .collect::<Result<Vec<_>>>()?;
  Ok(ChainedBlake3ChainV1 {
    stream_words,
    finalize_after: stream
      .finalize_after
      .iter()
      .copied()
      .map(|position| count_u64(position, "finalize position"))
      .collect::<Result<Vec<_>>>()?,
    compression_rows,
    squeeze_words,
  })
}

fn count_u64(value: usize, context: &str) -> Result<u64> {
  u64::try_from(value).map_err(|error| anyhow::anyhow!("{context}: {error}"))
}

fn encode_f128(value: F128) -> [u8; 16] {
  let mut encoded = [0u8; 16];
  encoded[..8].copy_from_slice(&value.lo.to_le_bytes());
  encoded[8..].copy_from_slice(&value.hi.to_le_bytes());
  encoded
}

fn decode_f128(value: [u8; 16]) -> F128 {
  F128::new(
    u64::from_le_bytes(
      value[..8].try_into().expect("low F128 half has 8 bytes"),
    ),
    u64::from_le_bytes(
      value[8..].try_into().expect("high F128 half has 8 bytes"),
    ),
  )
}

#[cfg(test)]
mod tests {
  use super::*;
  use flock_prover::challenger::FsChallenger;

  #[test]
  fn transcript_export_preserves_the_real_challenger_tape() {
    let mut recorder = RecordingChallenger::new(
      FsChallenger::with_chained_blake3(b"ix-stage4-export-test"),
    );
    recorder.observe_label(b"phase");
    recorder.observe_f128(F128::new(1, 2));
    let challenge = recorder.sample_f128();
    recorder.observe_bytes(b"payload");
    let exported = Stage4FlockTranscriptWitnessV1::from_recording(
      &recorder,
      b"ix-stage4-export-test",
    )
    .expect("export transcript");

    assert_eq!(exported.operations.len(), 4);
    assert_eq!(exported.observed_values, vec![encode_f128(F128::new(1, 2))]);
    assert_eq!(exported.byte_payloads, vec![b"payload".to_vec()]);
    assert_eq!(exported.challenges, vec![encode_f128(challenge)]);
    assert_ne!(exported.shape_digest, [0; 32]);
    assert_eq!(exported.chained_blake3.census().chains, 1);
    assert_eq!(exported.chained_blake3.census().compression_rows, 2);
    assert_ne!(exported.chained_blake3.topology_digest(), [0; 32]);

    let (r1cs, witness, circuit_output) =
      ix_terminal_circuit::build_chained_blake3_transcript_r1cs(
        exported.chained_blake3(),
        exported.observed_values(),
        exported.byte_payloads(),
        exported.challenges(),
      )
      .expect("compile the recorded Flock tape into Stage 4 R1CS");
    r1cs.check(&witness).expect("satisfy the Stage 4 transcript R1CS");
    assert_eq!(circuit_output.challenges[0].value(), &encode_f128(challenge),);
  }

  #[test]
  fn stage4_binary_field_gadget_matches_pinned_flock() {
    let left = F128::new(0x0123_4567_89ab_cdef, 0xfedc_ba98_7654_3210);
    let right = F128::new(0x0f1e_2d3c_4b5a_6978, 0x8877_6655_4433_2211);
    let expected = left * right;
    let (r1cs, witness, output) =
      ix_terminal_circuit::build_f128_multiplication_r1cs(
        encode_f128(left),
        encode_f128(right),
        ix_terminal_circuit::ConstraintPhase::Zerocheck,
      )
      .expect("compile Flock GF(2^128) multiplication");
    r1cs.check(&witness).expect("satisfy GF(2^128) multiplication");
    assert_eq!(output.value(), &encode_f128(expected));
  }
}
