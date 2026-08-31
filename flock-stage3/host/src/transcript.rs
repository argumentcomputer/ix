//! Exact BLAKE3 `HashChallenger` replay for the Stage 2 verifier transcript.
//!
//! Plonky3's byte challenger replaces its input with `BLAKE3(input)` whenever
//! an empty output buffer is sampled, then pops sample bytes from the END of
//! that digest.  An observation discards any unused output bytes.  This module
//! lowers the protocol-shaped prefix through the PCS opening-batch sample:
//!
//! 1. sample and re-observe the lookup challenge;
//! 2. sample and re-observe the fingerprint challenge;
//! 3. observe Stage 2 data and sample the constraint challenge;
//! 4. observe the quotient commitment and sample zeta;
//! 5. observe all PCS openings, then sample the FRI/PCS batching challenge
//!    used to reduce every opening before the commit-phase folds.
//!
//! The replay can then continue through FRI commitments, commit grinding and
//! betas, the final polynomial/arity observations, query grinding, and every
//! masked query draw. Every BLAKE3 compression is constrained, including
//! chunk-tree parents for messages longer than 1,024 bytes. Sampled Goldilocks
//! limbs are checked canonical. Field sampling constrains one chained digest
//! refill and fails closed only if those eight candidates still contain fewer
//! than two canonical Goldilocks values (seven candidates after a raw PoW
//! draw).

use aiur::vk_codec::AiurVerifyingKey;
use anyhow::{Context, Result, bail};
use bincode::Options;
use flock_prover::{
  challenger::FsChallenger,
  circuit::builder::{
    CircuitShape, GateType, ShapeBuilder, SlotId, SlotWitness, Wire,
  },
  field::F128,
  lincheck::LincheckCircuit,
  pcs::Commitment,
  proof::R1csProofCircuitMerged,
  prover::{self, UnionSlotProverInput},
  r1cs_hashes::{
    blake3 as flock_blake3,
    fs_chain::{CvSource, FsChain, FsChainTrace},
  },
  schedule::{IoWord, TableType},
  union::{SlotWitnessDest, UnionInstance},
  verifier,
};
use ix_terminal::{
  ValidatedP3ProofV1, ValidatedStage2RootV1, fri_parameter_words,
};
use multi_stark::types::FriParameters;
use serde::{Deserialize, Serialize};

use crate::{
  FlockConfigV1, STAGE2_TRANSCRIPT_CONFORMANCE_TRANSCRIPT_DOMAIN,
  binding::{Blake3Gate, IV, pack_bytes, pack_params, pack8, pcs_params},
  boolean::{
    BooleanR1csBuilder, BooleanR1csPlan, generate_boolean_witness,
    generate_boolean_witness_into, write_f128,
  },
  goldilocks::{
    CanonicalGoldilocksPairGate, GOLDILOCKS_MODULUS, build_canonical_pair_r1cs,
    generate_canonical_pair_witness,
  },
  typed_witness::{Stage3OpenedRoundV1, Stage3TypedProofWitnessV1},
};

pub const STAGE2_TRANSCRIPT_CONFORMANCE_ARTIFACT_MAGIC: &[u8; 8] = b"IXFLTR01";

const ARTIFACT_VERSION: u16 = 1;
const CONFIG_OFFSET: usize = 10;
const LENGTHS_OFFSET: usize = CONFIG_OFFSET + 32;
const SEGMENT_COUNT: usize = 4;
const LENGTH_BYTES: usize = SEGMENT_COUNT * 4;
const SEGMENTS_OFFSET: usize = LENGTHS_OFFSET + LENGTH_BYTES;
const CHALLENGE_COUNT: usize = 5;
const CHALLENGE_BYTES: usize = CHALLENGE_COUNT * 16;
const FIXED_SUFFIX_BYTES: usize = CHALLENGE_BYTES + 32 + 8;
const MAX_OBSERVATION_BYTES: usize = 16 * 1024 * 1024;
const MAX_BUNDLE_BYTES: usize = 64 * 1024 * 1024;
const WORD_BYTES: usize = 16;
const MIN_NU: usize = 8;
const MAX_NU: usize = 20;
const MAX_FRI_ROUNDS: usize = 32;
const MAX_FRI_QUERIES: usize = 1_024;
const MAX_CAP_ROOTS: usize = 256;

const SAMPLE_K_LOG: usize = 9;
const SAMPLE_INPUT_BASE: usize = 0;
const SAMPLE_OUTPUT_BASE: usize = 128;
const SAMPLE_COLUMNS: usize = 256;

const FIELD_SAMPLE_K_LOG: usize = 14;
const FIELD_SAMPLE_HIGH_BASE: usize = 0;
const FIELD_SAMPLE_LOW_BASE: usize = 128;
const FIELD_SAMPLE_REFILL_HIGH_BASE: usize = 256;
const FIELD_SAMPLE_REFILL_LOW_BASE: usize = 384;
const FIELD_SAMPLE_OUTPUT_BASE: usize = 512;
const FIELD_SAMPLE_FAILURE_BASE: usize = 640;
const FIELD_SAMPLE_RAW_FIRST_BASE: usize = 768;
const FIELD_SAMPLE_SKIP_OUTPUT_BASE: usize = 896;
const FIELD_SAMPLE_SKIP_FAILURE_BASE: usize = 1_024;
const FIELD_SAMPLE_STATE_LOW_BASE: usize = 1_152;
const FIELD_SAMPLE_STATE_HIGH_BASE: usize = 1_280;
const FIELD_SAMPLE_SKIP_STATE_LOW_BASE: usize = 1_408;
const FIELD_SAMPLE_SKIP_STATE_HIGH_BASE: usize = 1_536;
const FIELD_SAMPLE_COLUMNS: usize = 1_664;

/// The variable observation segments around the fixed challenger operations.
///
/// `initial_observations` is the complete seed/shape/activation/stage-1/
/// claims prefix.  The other fields correspond to the comments on their
/// names and are already serialized exactly as the Stage 2 challenger sees
/// them.  The production composition will build these byte words directly
/// from the typed proof and verifying-key constants.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stage2TranscriptReplayV1 {
  pub initial_observations: Vec<u8>,
  pub stage2_and_accumulator_observations: Vec<u8>,
  pub quotient_commitment_observations: Vec<u8>,
  pub pcs_opening_observations: Vec<u8>,
}

/// Challenges derived by [`Stage2TranscriptReplayV1`], in protocol order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Stage2TranscriptChallengesV1 {
  pub lookup: [u64; 2],
  pub fingerprint: [u64; 2],
  pub constraint: [u64; 2],
  pub zeta: [u64; 2],
  pub pcs_alpha: [u64; 2],
}

/// One of the four byte segments consumed by the constrained Stage 2
/// transcript prefix.
///
/// PCS composition uses these identifiers to consume commitment roots and
/// out-of-domain values from the exact wires already hashed by the
/// transcript, rather than accepting duplicated public values.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Stage2TranscriptSegmentV1 {
  Initial,
  Stage2AndAccumulator,
  QuotientCommitment,
  PcsOpening,
}

impl Stage2TranscriptSegmentV1 {
  pub(crate) const fn index(self) -> usize {
    match self {
      Self::Initial => 0,
      Self::Stage2AndAccumulator => 1,
      Self::QuotientCommitment => 2,
      Self::PcsOpening => 3,
    }
  }
}

/// A little-endian `u64` lane inside one constrained transcript segment.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Stage2TranscriptByteBindingV1 {
  pub segment: Stage2TranscriptSegmentV1,
  pub byte_offset: usize,
}

impl Stage2TranscriptByteBindingV1 {
  pub const fn new(
    segment: Stage2TranscriptSegmentV1,
    byte_offset: usize,
  ) -> Self {
    Self { segment, byte_offset }
  }
}

/// The FRI portion of the Stage 2 byte transcript after the opening-batch
/// challenge has been sampled.
///
/// Commitments are kept as caps so the relation can expose and bind every cap
/// root individually. `query_index_bits` is the exact bit width passed to
/// `SerializingChallenger64::sample_bits`; it equals the global FRI height for
/// the two-adic folding strategy used by Ix.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stage2FriTranscriptReplayV1 {
  pub commit_phase_commitments: Vec<Vec<[u8; 32]>>,
  pub commit_pow_witnesses: Vec<u64>,
  pub final_polynomial: Vec<[u64; 2]>,
  pub log_arities: Vec<u8>,
  pub query_pow_witness: u64,
  pub commit_pow_bits: u8,
  pub query_pow_bits: u8,
  pub num_queries: usize,
  pub query_index_bits: u8,
}

/// Challenges sampled by the FRI verifier after the PCS batching challenge.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stage2FriTranscriptChallengesV1 {
  pub betas: Vec<[u64; 2]>,
  pub query_indices: Vec<u64>,
}

impl Stage2TranscriptReplayV1 {
  /// Replay the exact native byte challenger through the first FRI challenge.
  pub fn challenges(&self) -> Result<Stage2TranscriptChallengesV1> {
    compute_challenges(self)
  }

  /// Build the exact transcript segments from an already validated Stage 2
  /// root and its serializer-independent typed proof witness.
  pub fn from_prepared(
    prepared: &ValidatedStage2RootV1,
    fri: &FriParameters,
  ) -> Result<Self> {
    Self::from_p3(prepared.p3_proof(), fri)
  }

  pub fn from_prepared_and_typed(
    prepared: &ValidatedStage2RootV1,
    fri: &FriParameters,
    typed: &Stage3TypedProofWitnessV1,
  ) -> Result<Self> {
    Self::from_p3_and_typed(prepared.p3_proof(), fri, typed)
  }

  /// Build the exact transcript prefix for any validated Aiur/P3 proof.
  pub fn from_p3(
    prepared: &ValidatedP3ProofV1,
    fri: &FriParameters,
  ) -> Result<Self> {
    let typed = Stage3TypedProofWitnessV1::from_p3(prepared, fri)?;
    Self::from_p3_and_typed(prepared, fri, &typed)
  }

  pub fn from_p3_and_typed(
    prepared: &ValidatedP3ProofV1,
    fri: &FriParameters,
    typed: &Stage3TypedProofWitnessV1,
  ) -> Result<Self> {
    if prepared.statement().fri_parameter_words() != &fri_parameter_words(fri) {
      bail!("P3 transcript uses different FRI parameters");
    }
    typed.ensure_profile(prepared.advice_profile())?;
    let key = AiurVerifyingKey::from_bytes(prepared.verifying_key_bytes())
      .map_err(|error| {
        anyhow::anyhow!("decode Aiur transcript key: {error}")
      })?;
    if key.to_bytes() != prepared.verifying_key_bytes() {
      bail!("Aiur transcript key is not canonically encoded");
    }
    if fri_parameter_words(&key.fri_parameters()) != fri_parameter_words(fri) {
      bail!("Aiur transcript key uses different FRI parameters");
    }
    if key.num_circuits() != typed.active.len() {
      bail!(
        "Aiur transcript key has {} circuits but activation has {} bits",
        key.num_circuits(),
        typed.active.len()
      );
    }

    let mut initial_observations = key.transcript_seed_and_shape_bytes();
    for &active in &typed.active {
      push_u64_observation(&mut initial_observations, u64::from(active));
    }
    if let Some(preprocessed) = key.preprocessed_commitment_roots() {
      push_cap_observations(&mut initial_observations, &preprocessed);
    }
    push_cap_observations(
      &mut initial_observations,
      &typed.commitments.stage_1_trace,
    );
    for &log_degree in &typed.log_degrees {
      push_u64_observation(&mut initial_observations, u64::from(log_degree));
    }
    initial_observations.extend_from_slice(prepared.claims_bytes());

    let mut stage2_and_accumulator_observations = Vec::new();
    push_cap_observations(
      &mut stage2_and_accumulator_observations,
      &typed.commitments.stage_2_trace,
    );
    for &accumulator in &typed.intermediate_accumulators {
      push_extension_observation(
        &mut stage2_and_accumulator_observations,
        accumulator,
      );
    }

    let mut quotient_commitment_observations = Vec::new();
    push_cap_observations(
      &mut quotient_commitment_observations,
      &typed.commitments.quotient_chunks,
    );

    let mut pcs_opening_observations = Vec::new();
    push_opened_round_observations(
      &mut pcs_opening_observations,
      &typed.stage_1_opened_values,
    );
    push_opened_round_observations(
      &mut pcs_opening_observations,
      &typed.stage_2_opened_values,
    );
    push_opened_round_observations(
      &mut pcs_opening_observations,
      &typed.quotient_opened_values,
    );
    if let Some(preprocessed) = &typed.preprocessed_opened_values {
      push_opened_round_observations(
        &mut pcs_opening_observations,
        preprocessed,
      );
    }

    let replay = Self {
      initial_observations,
      stage2_and_accumulator_observations,
      quotient_commitment_observations,
      pcs_opening_observations,
    };
    validate_replay(&replay)?;
    Ok(replay)
  }
}

impl Stage2FriTranscriptReplayV1 {
  /// Build the exact post-opening FRI transcript from the validated Stage 2
  /// advice transport and the commitment parameters embedded in its key.
  pub fn from_prepared(
    prepared: &ValidatedStage2RootV1,
    fri: &FriParameters,
  ) -> Result<Self> {
    Self::from_p3(prepared.p3_proof(), fri)
  }

  pub fn from_prepared_and_typed(
    prepared: &ValidatedStage2RootV1,
    fri: &FriParameters,
    typed: &Stage3TypedProofWitnessV1,
  ) -> Result<Self> {
    Self::from_p3_and_typed(prepared.p3_proof(), fri, typed)
  }

  /// Build the post-opening FRI transcript for any validated Aiur/P3 proof.
  pub fn from_p3(
    prepared: &ValidatedP3ProofV1,
    fri: &FriParameters,
  ) -> Result<Self> {
    let typed = Stage3TypedProofWitnessV1::from_p3(prepared, fri)?;
    Self::from_p3_and_typed(prepared, fri, &typed)
  }

  pub fn from_p3_and_typed(
    prepared: &ValidatedP3ProofV1,
    fri: &FriParameters,
    typed: &Stage3TypedProofWitnessV1,
  ) -> Result<Self> {
    if prepared.statement().fri_parameter_words() != &fri_parameter_words(fri) {
      bail!("P3 FRI transcript uses different FRI parameters");
    }
    typed.ensure_profile(prepared.advice_profile())?;
    let key = AiurVerifyingKey::from_bytes(prepared.verifying_key_bytes())
      .map_err(|error| {
        anyhow::anyhow!("decode Aiur FRI transcript key: {error}")
      })?;
    if key.to_bytes() != prepared.verifying_key_bytes() {
      bail!("Aiur FRI transcript key is not canonically encoded");
    }
    if fri_parameter_words(&key.fri_parameters()) != fri_parameter_words(fri) {
      bail!("Aiur FRI transcript key uses different FRI parameters");
    }

    let first_query = typed
      .opening_proof
      .query_proofs
      .first()
      .ok_or_else(|| anyhow::anyhow!("Stage 2 FRI proof has no queries"))?;
    let log_arities: Vec<u8> = first_query
      .commit_phase_openings
      .iter()
      .map(|step| step.log_arity)
      .collect();
    if typed.opening_proof.query_proofs.iter().any(|query| {
      query
        .commit_phase_openings
        .iter()
        .map(|step| step.log_arity)
        .ne(log_arities.iter().copied())
    }) {
      bail!("Stage 2 FRI queries disagree on the folding-arity schedule");
    }
    let total_log_reduction =
      log_arities.iter().try_fold(0usize, |sum, &arity| {
        sum
          .checked_add(usize::from(arity))
          .ok_or_else(|| anyhow::anyhow!("FRI folding-arity sum overflow"))
      })?;
    let query_index_bits = total_log_reduction
      .checked_add(key.commitment_parameters().log_blowup)
      .and_then(|height| height.checked_add(fri.log_final_poly_len))
      .ok_or_else(|| anyhow::anyhow!("FRI global height overflow"))?;

    let replay = Self {
      commit_phase_commitments: typed
        .opening_proof
        .commit_phase_commits
        .clone(),
      commit_pow_witnesses: typed.opening_proof.commit_pow_witnesses.clone(),
      final_polynomial: typed.opening_proof.final_poly.clone(),
      log_arities,
      query_pow_witness: typed.opening_proof.query_pow_witness,
      commit_pow_bits: u8::try_from(fri.commit_proof_of_work_bits)
        .map_err(|_| anyhow::anyhow!("commit PoW bits exceed u8"))?,
      query_pow_bits: u8::try_from(fri.query_proof_of_work_bits)
        .map_err(|_| anyhow::anyhow!("query PoW bits exceed u8"))?,
      num_queries: fri.num_queries,
      query_index_bits: u8::try_from(query_index_bits)
        .map_err(|_| anyhow::anyhow!("FRI query-index width exceeds u8"))?,
    };
    validate_fri_replay(&replay)?;
    Ok(replay)
  }

  /// Replay the native challenger from the prefix's retained digest state.
  pub fn challenges(
    &self,
    prefix: &Stage2TranscriptReplayV1,
  ) -> Result<Stage2FriTranscriptChallengesV1> {
    compute_fri_challenges(prefix, self)
  }
}

/// A real Flock proof of the transcript prefix relation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stage2TranscriptConformanceArtifactV1 {
  replay: Stage2TranscriptReplayV1,
  challenges: Stage2TranscriptChallengesV1,
  circuit_digest: [u8; 32],
  proof_bundle_bytes: Vec<u8>,
}

impl Stage2TranscriptConformanceArtifactV1 {
  pub fn replay(&self) -> &Stage2TranscriptReplayV1 {
    &self.replay
  }

  pub const fn challenges(&self) -> Stage2TranscriptChallengesV1 {
    self.challenges
  }

  pub fn circuit_digest(&self) -> &[u8; 32] {
    &self.circuit_digest
  }

  pub fn proof_bundle_bytes(&self) -> &[u8] {
    &self.proof_bundle_bytes
  }

  pub fn to_bytes(&self) -> Vec<u8> {
    let segments = replay_segments(&self.replay);
    let segment_bytes: usize =
      segments.iter().map(|segment| segment.len()).sum();
    let mut bytes = Vec::with_capacity(
      SEGMENTS_OFFSET
        + segment_bytes
        + FIXED_SUFFIX_BYTES
        + self.proof_bundle_bytes.len(),
    );
    bytes.extend_from_slice(STAGE2_TRANSCRIPT_CONFORMANCE_ARTIFACT_MAGIC);
    bytes.extend_from_slice(&ARTIFACT_VERSION.to_le_bytes());
    bytes.extend_from_slice(&FlockConfigV1.digest());
    for segment in &segments {
      bytes.extend_from_slice(
        &u32::try_from(segment.len())
          .expect("bounded transcript segment length")
          .to_le_bytes(),
      );
    }
    for segment in &segments {
      bytes.extend_from_slice(segment);
    }
    encode_challenges(&mut bytes, self.challenges);
    bytes.extend_from_slice(&self.circuit_digest);
    bytes.extend_from_slice(
      &u64::try_from(self.proof_bundle_bytes.len())
        .expect("proof bundle length")
        .to_le_bytes(),
    );
    bytes.extend_from_slice(&self.proof_bundle_bytes);
    bytes
  }

  pub fn from_bytes(bytes: &[u8]) -> Result<Self> {
    if bytes.len() < SEGMENTS_OFFSET + FIXED_SUFFIX_BYTES {
      bail!("truncated Flock Stage 2 transcript artifact");
    }
    if &bytes[..8] != STAGE2_TRANSCRIPT_CONFORMANCE_ARTIFACT_MAGIC {
      bail!("invalid Flock Stage 2 transcript artifact magic");
    }
    let version = u16::from_le_bytes(bytes[8..10].try_into().unwrap());
    if version != ARTIFACT_VERSION {
      bail!("unsupported Flock Stage 2 transcript artifact version {version}");
    }
    if bytes[CONFIG_OFFSET..LENGTHS_OFFSET] != FlockConfigV1.digest() {
      bail!("Flock Stage 2 transcript artifact configuration mismatch");
    }

    let mut lengths = [0usize; SEGMENT_COUNT];
    for (index, length) in lengths.iter_mut().enumerate() {
      let offset = LENGTHS_OFFSET + index * 4;
      *length = usize::try_from(u32::from_le_bytes(
        bytes[offset..offset + 4].try_into().unwrap(),
      ))
      .expect("u32 fits usize");
    }
    let segment_bytes = lengths.iter().try_fold(0usize, |total, &length| {
      total
        .checked_add(length)
        .ok_or_else(|| anyhow::anyhow!("transcript segment length overflow"))
    })?;
    let suffix_offset = SEGMENTS_OFFSET
      .checked_add(segment_bytes)
      .ok_or_else(|| anyhow::anyhow!("transcript artifact length overflow"))?;
    let minimum_end = suffix_offset
      .checked_add(FIXED_SUFFIX_BYTES)
      .ok_or_else(|| anyhow::anyhow!("transcript artifact length overflow"))?;
    if bytes.len() < minimum_end {
      bail!("truncated Flock Stage 2 transcript artifact segments");
    }

    let mut cursor = SEGMENTS_OFFSET;
    let mut take_segment = |length: usize| {
      let end = cursor + length;
      let segment = bytes[cursor..end].to_vec();
      cursor = end;
      segment
    };
    let replay = Stage2TranscriptReplayV1 {
      initial_observations: take_segment(lengths[0]),
      stage2_and_accumulator_observations: take_segment(lengths[1]),
      quotient_commitment_observations: take_segment(lengths[2]),
      pcs_opening_observations: take_segment(lengths[3]),
    };
    validate_replay(&replay)?;
    debug_assert_eq!(cursor, suffix_offset);

    let challenges =
      decode_challenges(&bytes[suffix_offset..suffix_offset + CHALLENGE_BYTES]);
    validate_challenges(challenges)?;
    let digest_offset = suffix_offset + CHALLENGE_BYTES;
    let mut circuit_digest = [0u8; 32];
    circuit_digest.copy_from_slice(&bytes[digest_offset..digest_offset + 32]);
    let bundle_length_offset = digest_offset + 32;
    let bundle_len = usize::try_from(u64::from_le_bytes(
      bytes[bundle_length_offset..bundle_length_offset + 8].try_into().unwrap(),
    ))
    .map_err(|_| anyhow::anyhow!("Flock proof length does not fit usize"))?;
    if bundle_len == 0 || bundle_len > MAX_BUNDLE_BYTES {
      bail!("invalid Flock Stage 2 transcript proof length {bundle_len}");
    }
    let bundle_offset = bundle_length_offset + 8;
    let declared_end = bundle_offset
      .checked_add(bundle_len)
      .ok_or_else(|| anyhow::anyhow!("transcript proof length overflow"))?;
    if bytes.len() != declared_end {
      bail!(
        "Flock Stage 2 transcript artifact is {} bytes; header declares {declared_end}",
        bytes.len()
      );
    }
    Ok(Self {
      replay,
      challenges,
      circuit_digest,
      proof_bundle_bytes: bytes[bundle_offset..].to_vec(),
    })
  }
}

#[derive(Serialize, Deserialize)]
struct TranscriptProofBundle {
  commitment: Commitment,
  proof: R1csProofCircuitMerged,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct HashSampleRow(F128);

/// Convert digest bytes `[16..32]` into the first sampled extension element.
///
/// For an input word `[LE(digest[16..24]), LE(digest[24..32])]`, popping
/// bytes from the end and then decoding each draw as LE produces
/// `[BE(digest[24..32]), BE(digest[16..24])]`.
#[derive(Clone, Copy, Debug)]
pub(crate) struct HashSampleGate {
  pub(crate) nu: usize,
}

impl GateType for HashSampleGate {
  type Row = HashSampleRow;
  type Hint = ();

  fn table(&self) -> TableType {
    crate::boolean::table_from_block_r1cs(build_hash_sample_r1cs(self.nu))
      .with_io_schema(vec![IoWord::input(0), IoWord::output(1)])
  }

  fn eval(
    &self,
    inputs: &[F128],
    _hint: &(),
    outputs: &mut Vec<F128>,
  ) -> Self::Row {
    let input = inputs[0];
    outputs.push(sample_word(input));
    HashSampleRow(input)
  }

  fn witness(&self, _rows: &[Self::Row], _nu: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}

pub(crate) fn build_hash_sample_r1cs(
  nu: usize,
) -> flock_prover::r1cs::BlockR1cs {
  hash_sample_plan().block_r1cs(nu)
}

#[cfg(test)]
pub(crate) fn generate_hash_sample_witness(
  rows: &[HashSampleRow],
  nu: usize,
) -> (Vec<F128>, Vec<F128>, Vec<F128>, Vec<u8>) {
  generate_boolean_witness(hash_sample_plan(), rows, nu, |row, bits| {
    write_f128(bits, SAMPLE_INPUT_BASE, row.0);
  })
}

pub(crate) fn generate_hash_sample_witness_into(
  rows: &[HashSampleRow],
  nu: usize,
  dst: SlotWitnessDest<'_>,
) -> Vec<u8> {
  generate_boolean_witness_into(
    hash_sample_plan(),
    rows,
    nu,
    dst,
    |row, bits| {
      write_f128(bits, SAMPLE_INPUT_BASE, row.0);
    },
  )
}

fn hash_sample_plan() -> &'static BooleanR1csPlan {
  static PLAN: std::sync::OnceLock<BooleanR1csPlan> =
    std::sync::OnceLock::new();
  PLAN.get_or_init(|| {
    let mut builder = BooleanR1csBuilder::new(SAMPLE_K_LOG, SAMPLE_COLUMNS);
    for column in SAMPLE_INPUT_BASE..SAMPLE_INPUT_BASE + 128 {
      builder.free_boolean_at(column);
    }
    for output_bit in 0..128 {
      let lane_bit = output_bit % 64;
      let source_lane = if output_bit < 64 { 1 } else { 0 };
      let source =
        SAMPLE_INPUT_BASE + source_lane * 64 + reverse_bytes_bit(lane_bit);
      builder.write_product_of_parities(
        SAMPLE_OUTPUT_BASE + output_bit,
        &[source],
        &[source],
      );
    }
    builder.finish()
  })
}

const fn reverse_bytes_bit(bit: usize) -> usize {
  (7 - bit / 8) * 8 + bit % 8
}

fn sample_word(input: F128) -> F128 {
  F128::new(input.hi.swap_bytes(), input.lo.swap_bytes())
}

/// Eight raw draws from a digest and its chained refill, lowered to the first
/// two canonical Goldilocks values. The second result variant skips the first
/// raw draw, as required when commit-phase grinding consumes it before beta.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct GoldilocksSampleRow([F128; 4]);

#[derive(Clone, Copy, Debug)]
pub(crate) struct GoldilocksSampleGate {
  pub(crate) nu: usize,
}

impl GateType for GoldilocksSampleGate {
  type Row = GoldilocksSampleRow;
  type Hint = ();

  fn table(&self) -> TableType {
    crate::boolean::table_from_block_r1cs(build_goldilocks_sample_r1cs(self.nu))
      .with_io_schema(vec![
        IoWord::input(0),
        IoWord::input(1),
        IoWord::input(2),
        IoWord::input(3),
        IoWord::output(4),
        IoWord::output(5),
        IoWord::output(6),
        IoWord::output(7),
        IoWord::output(8),
        IoWord::output(9),
        IoWord::output(10),
        IoWord::output(11),
        IoWord::output(12),
      ])
  }

  fn eval(
    &self,
    inputs: &[F128],
    _hint: &(),
    outputs: &mut Vec<F128>,
  ) -> Self::Row {
    let words = [inputs[0], inputs[1], inputs[2], inputs[3]];
    let candidates = digest_candidates(words);
    let (sample, failure, used_refill) = select_two_candidates(&candidates, 4);
    let (skip_sample, skip_failure, skip_used_refill) =
      select_two_candidates(&candidates[1..], 3);
    let state =
      if used_refill { [words[3], words[2]] } else { [words[1], words[0]] };
    let skip_state = if skip_used_refill {
      [words[3], words[2]]
    } else {
      [words[1], words[0]]
    };
    outputs.extend_from_slice(&[
      sample,
      F128::new(u64::from(failure), 0),
      F128::new(candidates[0], 0),
      skip_sample,
      F128::new(u64::from(skip_failure), 0),
      state[0],
      state[1],
      skip_state[0],
      skip_state[1],
    ]);
    GoldilocksSampleRow(words)
  }

  fn witness(&self, _rows: &[Self::Row], _nu: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}

pub(crate) fn build_goldilocks_sample_r1cs(
  nu: usize,
) -> flock_prover::r1cs::BlockR1cs {
  goldilocks_sample_plan().block_r1cs(nu)
}

pub(crate) fn generate_goldilocks_sample_witness(
  rows: &[GoldilocksSampleRow],
  nu: usize,
) -> (Vec<F128>, Vec<F128>, Vec<F128>, Vec<u8>) {
  generate_boolean_witness(goldilocks_sample_plan(), rows, nu, |row, bits| {
    write_f128(bits, FIELD_SAMPLE_HIGH_BASE, row.0[0]);
    write_f128(bits, FIELD_SAMPLE_LOW_BASE, row.0[1]);
    write_f128(bits, FIELD_SAMPLE_REFILL_HIGH_BASE, row.0[2]);
    write_f128(bits, FIELD_SAMPLE_REFILL_LOW_BASE, row.0[3]);
  })
}

pub(crate) fn generate_goldilocks_sample_witness_into(
  rows: &[GoldilocksSampleRow],
  nu: usize,
  dst: SlotWitnessDest<'_>,
) -> Vec<u8> {
  generate_boolean_witness_into(
    goldilocks_sample_plan(),
    rows,
    nu,
    dst,
    |row, bits| {
      write_f128(bits, FIELD_SAMPLE_HIGH_BASE, row.0[0]);
      write_f128(bits, FIELD_SAMPLE_LOW_BASE, row.0[1]);
      write_f128(bits, FIELD_SAMPLE_REFILL_HIGH_BASE, row.0[2]);
      write_f128(bits, FIELD_SAMPLE_REFILL_LOW_BASE, row.0[3]);
    },
  )
}

fn goldilocks_sample_plan() -> &'static BooleanR1csPlan {
  static PLAN: std::sync::OnceLock<BooleanR1csPlan> =
    std::sync::OnceLock::new();
  PLAN.get_or_init(|| {
    let mut builder =
      BooleanR1csBuilder::new(FIELD_SAMPLE_K_LOG, FIELD_SAMPLE_COLUMNS);
    let one = builder.alloc_constant_one();
    for column in FIELD_SAMPLE_HIGH_BASE..FIELD_SAMPLE_REFILL_LOW_BASE + 128 {
      builder.free_boolean_at(column);
    }
    let candidate_bits = digest_candidate_columns();
    let rejection: Vec<_> = candidate_bits
      .iter()
      .map(|candidate| rejection_bit(&mut builder, candidate, one))
      .collect();
    let acceptance: Vec<_> = rejection
      .iter()
      .map(|&reject| builder.xor(&[reject, one], one))
      .collect();

    let (first, second, failure) =
      selection_masks(&mut builder, &acceptance, &rejection, one);
    write_selected_word(
      &mut builder,
      FIELD_SAMPLE_OUTPUT_BASE,
      &candidate_bits,
      &first,
      &second,
      one,
    );
    write_flag_word(
      &mut builder,
      FIELD_SAMPLE_FAILURE_BASE,
      failure,
      candidate_bits[0][0],
      one,
    );
    write_candidate_low_word(
      &mut builder,
      FIELD_SAMPLE_RAW_FIRST_BASE,
      &candidate_bits[0],
      one,
    );
    let used_refill =
      selection_uses_refill(&mut builder, &first, &second, 4, one);
    write_selected_state(
      &mut builder,
      FIELD_SAMPLE_STATE_LOW_BASE,
      FIELD_SAMPLE_STATE_HIGH_BASE,
      used_refill,
      one,
    );

    let (skip_first, skip_second, skip_failure) =
      selection_masks(&mut builder, &acceptance[1..], &rejection[1..], one);
    write_selected_word(
      &mut builder,
      FIELD_SAMPLE_SKIP_OUTPUT_BASE,
      &candidate_bits[1..],
      &skip_first,
      &skip_second,
      one,
    );
    write_flag_word(
      &mut builder,
      FIELD_SAMPLE_SKIP_FAILURE_BASE,
      skip_failure,
      candidate_bits[0][0],
      one,
    );
    let skip_used_refill =
      selection_uses_refill(&mut builder, &skip_first, &skip_second, 3, one);
    write_selected_state(
      &mut builder,
      FIELD_SAMPLE_SKIP_STATE_LOW_BASE,
      FIELD_SAMPLE_SKIP_STATE_HIGH_BASE,
      skip_used_refill,
      one,
    );
    builder.finish()
  })
}

fn digest_candidate_columns() -> [[usize; 64]; 8] {
  [
    std::array::from_fn(|bit| {
      FIELD_SAMPLE_HIGH_BASE + 64 + reverse_bytes_bit(bit)
    }),
    std::array::from_fn(|bit| FIELD_SAMPLE_HIGH_BASE + reverse_bytes_bit(bit)),
    std::array::from_fn(|bit| {
      FIELD_SAMPLE_LOW_BASE + 64 + reverse_bytes_bit(bit)
    }),
    std::array::from_fn(|bit| FIELD_SAMPLE_LOW_BASE + reverse_bytes_bit(bit)),
    std::array::from_fn(|bit| {
      FIELD_SAMPLE_REFILL_HIGH_BASE + 64 + reverse_bytes_bit(bit)
    }),
    std::array::from_fn(|bit| {
      FIELD_SAMPLE_REFILL_HIGH_BASE + reverse_bytes_bit(bit)
    }),
    std::array::from_fn(|bit| {
      FIELD_SAMPLE_REFILL_LOW_BASE + 64 + reverse_bytes_bit(bit)
    }),
    std::array::from_fn(|bit| {
      FIELD_SAMPLE_REFILL_LOW_BASE + reverse_bytes_bit(bit)
    }),
  ]
}

fn rejection_bit(
  builder: &mut BooleanR1csBuilder,
  candidate: &[usize; 64],
  one: usize,
) -> usize {
  let high_all = candidate[33..]
    .iter()
    .fold(candidate[32], |all, &bit| builder.and(all, bit));
  let low_any = candidate[1..32].iter().fold(candidate[0], |any, &bit| {
    let both = builder.and(any, bit);
    builder.xor(&[any, bit, both], one)
  });
  builder.and(high_all, low_any)
}

fn selection_masks(
  builder: &mut BooleanR1csBuilder,
  acceptance: &[usize],
  rejection: &[usize],
  one: usize,
) -> (Vec<usize>, Vec<usize>, usize) {
  let zero = builder.xor(&[one, one], one);
  let mut none = one;
  let mut exactly_one = zero;
  let mut first = Vec::with_capacity(acceptance.len());
  let mut second = Vec::with_capacity(acceptance.len());
  for (&accept, &reject) in acceptance.iter().zip(rejection) {
    let first_here = builder.and(none, accept);
    let second_here = builder.and(exactly_one, accept);
    first.push(first_here);
    second.push(second_here);
    let one_stays = builder.and(exactly_one, reject);
    exactly_one = builder.xor(&[one_stays, first_here], one);
    none = builder.and(none, reject);
  }
  let failure = builder.xor(&[none, exactly_one], one);
  (first, second, failure)
}

fn selection_uses_refill(
  builder: &mut BooleanR1csBuilder,
  first: &[usize],
  second: &[usize],
  refill_start: usize,
  one: usize,
) -> usize {
  first[refill_start..].iter().chain(&second[refill_start..]).copied().fold(
    builder.xor(&[one, one], one),
    |used, mask| {
      let both = builder.and(used, mask);
      builder.xor(&[used, mask, both], one)
    },
  )
}

fn write_selected_state(
  builder: &mut BooleanR1csBuilder,
  output_low_base: usize,
  output_high_base: usize,
  use_refill: usize,
  one: usize,
) {
  for (output_base, primary_base, refill_base) in [
    (output_low_base, FIELD_SAMPLE_LOW_BASE, FIELD_SAMPLE_REFILL_LOW_BASE),
    (output_high_base, FIELD_SAMPLE_HIGH_BASE, FIELD_SAMPLE_REFILL_HIGH_BASE),
  ] {
    for bit in 0..128 {
      let primary = primary_base + bit;
      let refill = refill_base + bit;
      let remove_primary = builder.and(use_refill, primary);
      let add_refill = builder.and(use_refill, refill);
      builder.write_xor(
        output_base + bit,
        &[primary, remove_primary, add_refill],
        one,
      );
    }
  }
}

#[allow(clippy::too_many_arguments)]
fn write_selected_word(
  builder: &mut BooleanR1csBuilder,
  output_base: usize,
  candidates: &[[usize; 64]],
  first: &[usize],
  second: &[usize],
  one: usize,
) {
  for bit in 0..64 {
    let first_terms: Vec<_> = candidates
      .iter()
      .zip(first)
      .map(|(candidate, &mask)| builder.and(candidate[bit], mask))
      .collect();
    let second_terms: Vec<_> = candidates
      .iter()
      .zip(second)
      .map(|(candidate, &mask)| builder.and(candidate[bit], mask))
      .collect();
    builder.write_xor(output_base + bit, &first_terms, one);
    builder.write_xor(output_base + 64 + bit, &second_terms, one);
  }
}

fn write_flag_word(
  builder: &mut BooleanR1csBuilder,
  output_base: usize,
  flag: usize,
  zero_source: usize,
  one: usize,
) {
  builder.write_product_of_parities(output_base, &[flag], &[flag]);
  for bit in 1..128 {
    builder.write_xor(output_base + bit, &[zero_source, zero_source], one);
  }
}

fn write_candidate_low_word(
  builder: &mut BooleanR1csBuilder,
  output_base: usize,
  candidate: &[usize; 64],
  one: usize,
) {
  for (bit, &candidate_bit) in candidate.iter().enumerate() {
    builder.write_product_of_parities(
      output_base + bit,
      &[candidate_bit],
      &[candidate_bit],
    );
  }
  for bit in 64..128 {
    builder.write_xor(output_base + bit, &[candidate[0], candidate[0]], one);
  }
}

fn digest_candidates(words: [F128; 4]) -> [u64; 8] {
  [
    words[0].hi.swap_bytes(),
    words[0].lo.swap_bytes(),
    words[1].hi.swap_bytes(),
    words[1].lo.swap_bytes(),
    words[2].hi.swap_bytes(),
    words[2].lo.swap_bytes(),
    words[3].hi.swap_bytes(),
    words[3].lo.swap_bytes(),
  ]
}

fn select_two_candidates(
  candidates: &[u64],
  refill_start: usize,
) -> (F128, bool, bool) {
  let accepted: Vec<_> = candidates
    .iter()
    .copied()
    .enumerate()
    .filter(|&(_, candidate)| candidate < GOLDILOCKS_MODULUS)
    .take(2)
    .collect();
  if accepted.len() == 2 {
    (
      F128::new(accepted[0].1, accepted[1].1),
      false,
      accepted[1].0 >= refill_start,
    )
  } else {
    (F128::ZERO, true, true)
  }
}

const U64_SPLIT_K_LOG: usize = 9;
const U64_SPLIT_INPUT_BASE: usize = 0;
const U64_SPLIT_BIT_BASE: usize = 128;
const U64_SPLIT_QUOTIENT_BASE: usize = 256;
const U64_SPLIT_COLUMNS: usize = 384;

/// Split a low-lane `u64` into its least-significant bit and the remaining
/// quotient. Repeating this gate exposes exactly the low bits consumed by
/// `SerializingChallenger64::sample_bits`, without making those bits separate
/// public inputs.
#[derive(Clone, Copy, Debug)]
pub(crate) struct U64SplitGate {
  pub(crate) nu: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct U64SplitRow(F128);

impl GateType for U64SplitGate {
  type Row = U64SplitRow;
  type Hint = ();

  fn table(&self) -> TableType {
    crate::boolean::table_from_block_r1cs(build_u64_split_r1cs(self.nu))
      .with_io_schema(vec![
        IoWord::input(0),
        IoWord::output(1),
        IoWord::output(2),
      ])
  }

  fn eval(
    &self,
    inputs: &[F128],
    _hint: &(),
    outputs: &mut Vec<F128>,
  ) -> Self::Row {
    let input = inputs[0];
    assert_eq!(input.hi, 0, "u64 split input must occupy the low lane");
    outputs.push(F128::new(input.lo & 1, 0));
    outputs.push(F128::new(input.lo >> 1, 0));
    U64SplitRow(input)
  }

  fn witness(&self, _rows: &[Self::Row], _nu: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}

pub(crate) fn build_u64_split_r1cs(nu: usize) -> flock_prover::r1cs::BlockR1cs {
  u64_split_plan().block_r1cs(nu)
}

pub(crate) fn generate_u64_split_witness_into(
  rows: &[U64SplitRow],
  nu: usize,
  dst: SlotWitnessDest<'_>,
) -> Vec<u8> {
  generate_boolean_witness_into(u64_split_plan(), rows, nu, dst, |row, bits| {
    write_f128(bits, U64_SPLIT_INPUT_BASE, row.0);
  })
}

fn u64_split_plan() -> &'static BooleanR1csPlan {
  static PLAN: std::sync::OnceLock<BooleanR1csPlan> =
    std::sync::OnceLock::new();
  PLAN.get_or_init(|| {
    let mut builder =
      BooleanR1csBuilder::new(U64_SPLIT_K_LOG, U64_SPLIT_COLUMNS);
    let one = builder.alloc_constant_one();
    for bit in 0..64 {
      builder.free_boolean_at(U64_SPLIT_INPUT_BASE + bit);
    }
    for bit in 64..128 {
      builder.assert_zero_at(U64_SPLIT_INPUT_BASE + bit, one);
    }

    let write_copy = |builder: &mut BooleanR1csBuilder, output, source| {
      builder.write_product_of_parities(output, &[source], &[source]);
    };
    let write_zero = |builder: &mut BooleanR1csBuilder, output| {
      builder.write_xor(
        output,
        &[U64_SPLIT_INPUT_BASE, U64_SPLIT_INPUT_BASE],
        one,
      );
    };

    write_copy(&mut builder, U64_SPLIT_BIT_BASE, U64_SPLIT_INPUT_BASE);
    for bit in 1..128 {
      write_zero(&mut builder, U64_SPLIT_BIT_BASE + bit);
    }
    for bit in 0..63 {
      write_copy(
        &mut builder,
        U64_SPLIT_QUOTIENT_BASE + bit,
        U64_SPLIT_INPUT_BASE + bit + 1,
      );
    }
    for bit in 63..128 {
      write_zero(&mut builder, U64_SPLIT_QUOTIENT_BASE + bit);
    }
    builder.finish()
  })
}

#[derive(Clone, Copy)]
pub(crate) struct TranscriptCircuitSlots {
  pub(crate) blake3: SlotId,
  pub(crate) sample: SlotId,
  pub(crate) canonical: SlotId,
}

#[derive(Clone, Copy)]
pub(crate) struct TranscriptChallengeWires {
  pub(crate) lookup: Wire,
  pub(crate) fingerprint: Wire,
  pub(crate) constraint: Wire,
  pub(crate) zeta: Wire,
  pub(crate) pcs_alpha: Wire,
}

impl TranscriptChallengeWires {
  pub(crate) fn all(self) -> [Wire; CHALLENGE_COUNT] {
    [self.lookup, self.fingerprint, self.constraint, self.zeta, self.pcs_alpha]
  }
}

pub(crate) struct TranscriptConstraintRegion {
  pub(crate) inputs: Vec<F128>,
  pub(crate) challenges: TranscriptChallengeWires,
  /// Packed public words for each of the four observation segments. These are
  /// the same wires passed to the BLAKE3 transcript gates.
  pub(crate) observation_words: Vec<Vec<Wire>>,
  /// HashChallenger input state after sampling the PCS challenge. The low
  /// half of this digest remains in the output buffer until the next
  /// observation; every valid FRI proof immediately observes a non-empty cap.
  pub(crate) state_digest: [Wire; 2],
}

struct TranscriptRelation {
  shape: CircuitShape,
  slots: TranscriptCircuitSlots,
  nu: usize,
  inputs: Vec<F128>,
}

impl TranscriptRelation {
  fn build(replay: &Stage2TranscriptReplayV1) -> Result<Self> {
    let nu = transcript_nu(replay)?;
    let mut builder = ShapeBuilder::new(nu);
    let slots = TranscriptCircuitSlots {
      blake3: builder.slot(Blake3Gate { nu }),
      sample: builder.slot(GoldilocksSampleGate { nu }),
      canonical: builder.slot(CanonicalGoldilocksPairGate { nu }),
    };
    let region = constrain_stage2_transcript(&mut builder, slots, replay, nu)?;
    for challenge in region.challenges.all() {
      builder.publish(challenge);
    }
    let shape = builder.finish().map_err(|error| {
      anyhow::anyhow!("build Flock Stage 2 transcript circuit: {error:?}")
    })?;
    Ok(Self { shape, slots, nu, inputs: region.inputs })
  }

  fn public(&self, challenges: Stage2TranscriptChallengesV1) -> Vec<F128> {
    let mut public = self.inputs.clone();
    public.extend(challenge_words(challenges));
    public
  }
}

pub(crate) fn transcript_nu(
  replay: &Stage2TranscriptReplayV1,
) -> Result<usize> {
  let traces = transcript_traces(replay)?;
  let blake3_rows = traces.iter().map(|trace| trace.rows.len()).sum::<usize>()
    + CHALLENGE_COUNT * hash_trace(32).rows.len();
  let needed_rows = blake3_rows.max(CHALLENGE_COUNT).max(1);
  let nu = MIN_NU.max(needed_rows.next_power_of_two().ilog2() as usize);
  if nu > MAX_NU {
    bail!(
      "Stage 2 transcript needs {blake3_rows} BLAKE3 rows (nu={nu}); maximum is nu={MAX_NU}"
    );
  }
  Ok(nu)
}

pub(crate) fn constrain_stage2_transcript(
  builder: &mut ShapeBuilder,
  slots: TranscriptCircuitSlots,
  replay: &Stage2TranscriptReplayV1,
  nu: usize,
) -> Result<TranscriptConstraintRegion> {
  let traces = transcript_traces(replay)?;
  let row_count = traces.iter().map(|trace| trace.rows.len()).sum::<usize>()
    + CHALLENGE_COUNT * hash_trace(32).rows.len();
  if row_count > 1usize << nu {
    bail!("Stage 2 transcript exceeds the supplied Flock row capacity");
  }
  let segment_wires: Vec<Vec<Wire>> = replay_segments(replay)
    .iter()
    .map(|segment| {
      (0..segment.len().div_ceil(WORD_BYTES))
        .map(|_| builder.public_input())
        .collect()
    })
    .collect();

  let mut inputs: Vec<F128> =
    replay_segments(replay).into_iter().flat_map(pack_segment).collect();
  let packed_iv = pack8(&IV);
  let iv = [
    fixed(builder, &mut inputs, packed_iv[0]),
    fixed(builder, &mut inputs, packed_iv[1]),
  ];
  // Data padding is only consumed; assertion zero only receives residual
  // outputs. Keeping the wiring classes separate preserves a directed DAG.
  let data_zero = fixed(builder, &mut inputs, F128::ZERO);
  let assertion_zero = fixed(builder, &mut inputs, F128::ZERO);
  let parameter_wires: Vec<Vec<Wire>> = traces
    .iter()
    .map(|trace| {
      trace
        .rows
        .iter()
        .map(|&(_cv, _message, counter, block_len, flags)| {
          fixed(builder, &mut inputs, pack_params(counter, block_len, flags))
        })
        .collect()
    })
    .collect();

  let digest_1 = constrain_hash(
    builder,
    slots.blake3,
    &traces[0],
    &parameter_wires[0],
    iv,
    data_zero,
    &segment_wires[0],
  )?;
  let sampled = constrain_field_sample(
    builder,
    slots.blake3,
    slots.sample,
    slots.canonical,
    assertion_zero,
    iv,
    data_zero,
    &mut inputs,
    digest_1,
    false,
  )?;
  let lookup = sampled.value;
  let state_1 = sampled.state;

  let digest_2 = constrain_hash(
    builder,
    slots.blake3,
    &traces[1],
    &parameter_wires[1],
    iv,
    data_zero,
    &[state_1[0], state_1[1], lookup],
  )?;
  let sampled = constrain_field_sample(
    builder,
    slots.blake3,
    slots.sample,
    slots.canonical,
    assertion_zero,
    iv,
    data_zero,
    &mut inputs,
    digest_2,
    false,
  )?;
  let fingerprint = sampled.value;
  let state_2 = sampled.state;

  let mut message_3 = vec![state_2[0], state_2[1], fingerprint];
  message_3.extend_from_slice(&segment_wires[1]);
  let digest_3 = constrain_hash(
    builder,
    slots.blake3,
    &traces[2],
    &parameter_wires[2],
    iv,
    data_zero,
    &message_3,
  )?;
  let sampled = constrain_field_sample(
    builder,
    slots.blake3,
    slots.sample,
    slots.canonical,
    assertion_zero,
    iv,
    data_zero,
    &mut inputs,
    digest_3,
    false,
  )?;
  let constraint = sampled.value;
  let state_3 = sampled.state;

  let mut message_4 = vec![state_3[0], state_3[1]];
  message_4.extend_from_slice(&segment_wires[2]);
  let digest_4 = constrain_hash(
    builder,
    slots.blake3,
    &traces[3],
    &parameter_wires[3],
    iv,
    data_zero,
    &message_4,
  )?;
  let sampled = constrain_field_sample(
    builder,
    slots.blake3,
    slots.sample,
    slots.canonical,
    assertion_zero,
    iv,
    data_zero,
    &mut inputs,
    digest_4,
    false,
  )?;
  let zeta = sampled.value;
  let state_4 = sampled.state;

  let mut message_5 = vec![state_4[0], state_4[1]];
  message_5.extend_from_slice(&segment_wires[3]);
  let digest_5 = constrain_hash(
    builder,
    slots.blake3,
    &traces[4],
    &parameter_wires[4],
    iv,
    data_zero,
    &message_5,
  )?;
  let sampled = constrain_field_sample(
    builder,
    slots.blake3,
    slots.sample,
    slots.canonical,
    assertion_zero,
    iv,
    data_zero,
    &mut inputs,
    digest_5,
    false,
  )?;
  let pcs_alpha = sampled.value;
  Ok(TranscriptConstraintRegion {
    inputs,
    challenges: TranscriptChallengeWires {
      lookup,
      fingerprint,
      constraint,
      zeta,
      pcs_alpha,
    },
    observation_words: segment_wires,
    state_digest: sampled.state,
  })
}

#[derive(Clone, Copy)]
pub(crate) struct FriTranscriptCircuitSlots {
  pub(crate) blake3: SlotId,
  pub(crate) sample: SlotId,
  pub(crate) field_sample: SlotId,
  pub(crate) canonical: SlotId,
  pub(crate) repack: SlotId,
  pub(crate) split: SlotId,
}

pub(crate) struct FriTranscriptConstraintRegion {
  pub(crate) inputs: Vec<F128>,
  pub(crate) betas: Vec<Wire>,
  pub(crate) query_index_bits: Vec<Vec<Wire>>,
  pub(crate) commitment_roots: Vec<Vec<[Wire; 2]>>,
  pub(crate) final_polynomial: Vec<Wire>,
}

/// Continue an already constrained Stage 2 transcript through every FRI
/// challenge and query draw. The returned beta/index wires are intended to be
/// consumed directly by the PCS/FRI verifier relation.
pub(crate) fn constrain_stage2_fri_transcript(
  builder: &mut ShapeBuilder,
  slots: FriTranscriptCircuitSlots,
  replay: &Stage2FriTranscriptReplayV1,
  initial_digest: [Wire; 2],
  nu: usize,
) -> Result<FriTranscriptConstraintRegion> {
  validate_fri_replay(replay)?;
  let capacity = 1usize << nu;
  if fri_transcript_blake3_rows(replay)? > capacity
    || fri_transcript_split_rows(replay)? > capacity
  {
    bail!("Stage 2 FRI transcript exceeds the supplied Flock row capacity");
  }
  let mut inputs = Vec::new();
  let packed_iv = pack8(&IV);
  let iv = [
    fixed(builder, &mut inputs, packed_iv[0]),
    fixed(builder, &mut inputs, packed_iv[1]),
  ];
  let data_zero = fixed(builder, &mut inputs, F128::ZERO);
  let assertion_zero = fixed(builder, &mut inputs, F128::ZERO);

  let mut state = initial_digest;
  let mut betas = Vec::with_capacity(replay.commit_phase_commitments.len());
  let mut commitment_roots =
    Vec::with_capacity(replay.commit_phase_commitments.len());
  for (round, cap) in replay.commit_phase_commitments.iter().enumerate() {
    let cap_bytes = cap_observation_bytes(cap);
    let cap_words = declare_public_segment(builder, &mut inputs, &cap_bytes);
    commitment_roots.push(cap_words.as_chunks::<2>().0.to_vec());
    let mut message = Vec::with_capacity(
      2 + cap_words.len() + usize::from(replay.commit_pow_bits != 0),
    );
    message.extend_from_slice(&state);
    message.extend_from_slice(&cap_words);
    if replay.commit_pow_bits != 0 {
      message.push(declare_public_word(
        builder,
        &mut inputs,
        F128::new(replay.commit_pow_witnesses[round], 0),
      ));
    }
    let message_len =
      32 + cap_bytes.len() + usize::from(replay.commit_pow_bits != 0) * 8;
    let trace = hash_trace(message_len);
    let parameters = declare_trace_parameters(builder, &mut inputs, &trace);
    let digest = constrain_hash(
      builder,
      slots.blake3,
      &trace,
      &parameters,
      iv,
      data_zero,
      &message,
    )?;

    let sampled = constrain_field_sample(
      builder,
      slots.blake3,
      slots.field_sample,
      slots.canonical,
      assertion_zero,
      iv,
      data_zero,
      &mut inputs,
      digest,
      replay.commit_pow_bits != 0,
    )?;
    if replay.commit_pow_bits != 0 {
      constrain_low_zero_bits(
        builder,
        slots.split,
        assertion_zero,
        sampled.raw_first,
        replay.commit_pow_bits,
      );
    }
    betas.push(sampled.value);
    state = sampled.state;
  }

  let mut final_suffix = final_observation_bytes(replay);
  if replay.query_pow_bits != 0 {
    push_u64_observation(&mut final_suffix, replay.query_pow_witness);
  }
  let final_words = declare_public_segment(builder, &mut inputs, &final_suffix);
  let final_polynomial = final_words[..replay.final_polynomial.len()].to_vec();
  let mut final_message = Vec::with_capacity(2 + final_words.len());
  final_message.extend_from_slice(&state);
  final_message.extend_from_slice(&final_words);
  let final_trace = hash_trace(32 + final_suffix.len());
  let final_parameters =
    declare_trace_parameters(builder, &mut inputs, &final_trace);
  state = constrain_hash(
    builder,
    slots.blake3,
    &final_trace,
    &final_parameters,
    iv,
    data_zero,
    &final_message,
  )?;

  let draw_count = replay
    .num_queries
    .checked_add(usize::from(replay.query_pow_bits != 0))
    .ok_or_else(|| anyhow::anyhow!("FRI transcript draw count overflow"))?;
  let digest_count = draw_count.div_ceil(4);
  let mut draws = Vec::with_capacity(4 * digest_count);
  for digest_index in 0..digest_count {
    if digest_index != 0 {
      let trace = hash_trace(32);
      let parameters = declare_trace_parameters(builder, &mut inputs, &trace);
      state = constrain_hash(
        builder,
        slots.blake3,
        &trace,
        &parameters,
        iv,
        data_zero,
        &state,
      )?;
    }
    let high_samples = builder.gate(slots.sample, &[state[1]])[0];
    let low_samples = builder.gate(slots.sample, &[state[0]])[0];
    draws.extend(split_sample_lanes(
      builder,
      slots.repack,
      data_zero,
      high_samples,
    ));
    draws.extend(split_sample_lanes(
      builder,
      slots.repack,
      data_zero,
      low_samples,
    ));
  }
  draws.truncate(draw_count);
  let query_draws = if replay.query_pow_bits == 0 {
    &draws[..]
  } else {
    constrain_low_zero_bits(
      builder,
      slots.split,
      assertion_zero,
      draws[0],
      replay.query_pow_bits,
    );
    &draws[1..]
  };
  let query_index_bits = query_draws
    .iter()
    .map(|&draw| {
      split_low_bits(builder, slots.split, draw, replay.query_index_bits)
    })
    .collect();

  Ok(FriTranscriptConstraintRegion {
    inputs,
    betas,
    query_index_bits,
    commitment_roots,
    final_polynomial,
  })
}

fn declare_public_segment(
  builder: &mut ShapeBuilder,
  inputs: &mut Vec<F128>,
  bytes: &[u8],
) -> Vec<Wire> {
  pack_segment(bytes)
    .into_iter()
    .map(|word| declare_public_word(builder, inputs, word))
    .collect()
}

fn declare_public_word(
  builder: &mut ShapeBuilder,
  inputs: &mut Vec<F128>,
  value: F128,
) -> Wire {
  inputs.push(value);
  builder.public_input()
}

fn declare_trace_parameters(
  builder: &mut ShapeBuilder,
  inputs: &mut Vec<F128>,
  trace: &FsChainTrace,
) -> Vec<Wire> {
  trace
    .rows
    .iter()
    .map(|&(_cv, _message, counter, block_len, flags)| {
      fixed(builder, inputs, pack_params(counter, block_len, flags))
    })
    .collect()
}

fn split_sample_lanes(
  builder: &mut ShapeBuilder,
  repack_slot: SlotId,
  zero: Wire,
  samples: Wire,
) -> [Wire; 2] {
  let repacked = builder.gate(repack_slot, &[samples, zero]);
  let low = repacked[3];
  let high_duplicate = repacked[1];
  let high = builder.gate(repack_slot, &[high_duplicate, zero])[3];
  [low, high]
}

fn split_low_bits(
  builder: &mut ShapeBuilder,
  split_slot: SlotId,
  mut value: Wire,
  bits: u8,
) -> Vec<Wire> {
  (0..bits)
    .map(|_| {
      let outputs = builder.gate(split_slot, &[value]);
      value = outputs[1];
      outputs[0]
    })
    .collect()
}

fn constrain_low_zero_bits(
  builder: &mut ShapeBuilder,
  split_slot: SlotId,
  zero: Wire,
  value: Wire,
  bits: u8,
) {
  for bit in split_low_bits(builder, split_slot, value, bits) {
    builder.connect(zero, bit);
  }
}

fn fixed(
  builder: &mut ShapeBuilder,
  fixed_inputs: &mut Vec<F128>,
  value: F128,
) -> Wire {
  fixed_inputs.push(value);
  builder.fixed_public_input(value)
}

struct ConstrainedFieldSample {
  value: Wire,
  raw_first: Wire,
  state: [Wire; 2],
}

#[allow(clippy::too_many_arguments)]
fn constrain_field_sample(
  builder: &mut ShapeBuilder,
  blake3: SlotId,
  sample: SlotId,
  canonical: SlotId,
  zero: Wire,
  iv: [Wire; 2],
  data_zero: Wire,
  inputs: &mut Vec<F128>,
  digest: [Wire; 2],
  skip_first: bool,
) -> Result<ConstrainedFieldSample> {
  let trace = hash_trace(32);
  let parameters = declare_trace_parameters(builder, inputs, &trace);
  let refill = constrain_hash(
    builder,
    blake3,
    &trace,
    &parameters,
    iv,
    data_zero,
    &digest,
  )?;
  let sampled =
    builder.gate(sample, &[digest[1], digest[0], refill[1], refill[0]]);
  let (challenge, failure, state) = if skip_first {
    (sampled[3], sampled[4], [sampled[7], sampled[8]])
  } else {
    (sampled[0], sampled[1], [sampled[5], sampled[6]])
  };
  builder.connect(zero, failure);
  let violation = builder.gate(canonical, &[challenge])[0];
  builder.connect(zero, violation);
  Ok(ConstrainedFieldSample { value: challenge, raw_first: sampled[2], state })
}

pub(crate) fn constrain_hash(
  builder: &mut ShapeBuilder,
  slot: SlotId,
  trace: &FsChainTrace,
  parameters: &[Wire],
  iv: [Wire; 2],
  zero: Wire,
  message: &[Wire],
) -> Result<[Wire; 2]> {
  if parameters.len() != trace.rows.len() {
    bail!("BLAKE3 trace parameter count mismatch");
  }
  let mut row_outputs = Vec::<[Wire; 4]>::with_capacity(trace.rows.len());
  for (row_index, &parameter) in parameters.iter().enumerate() {
    let link = trace.links[row_index];
    let (cv, block) = if let Some(right_row) = link.right {
      let CvSource::Row(left_row) = link.cv else {
        bail!("BLAKE3 parent row does not name its left child");
      };
      let left = row_outputs
        .get(left_row)
        .ok_or_else(|| anyhow::anyhow!("BLAKE3 left-child link is forward"))?;
      let right = row_outputs
        .get(right_row)
        .ok_or_else(|| anyhow::anyhow!("BLAKE3 right-child link is forward"))?;
      (iv, [left[0], left[1], right[0], right[1]])
    } else {
      if link.repeats.is_some() {
        bail!("unexpected BLAKE3 XOF row in a 32-byte transcript hash");
      }
      let cv = match link.cv {
        CvSource::Iv => iv,
        CvSource::Row(source) => {
          let output = row_outputs.get(source).ok_or_else(|| {
            anyhow::anyhow!("BLAKE3 chaining-value link is forward")
          })?;
          [output[0], output[1]]
        },
        CvSource::RowHi(source) => {
          let output = row_outputs.get(source).ok_or_else(|| {
            anyhow::anyhow!("BLAKE3 high-half link is forward")
          })?;
          [output[2], output[3]]
        },
      };
      let offset = trace.block_offsets[row_index].ok_or_else(|| {
        anyhow::anyhow!("BLAKE3 data row is missing its message offset")
      })?;
      if offset % WORD_BYTES != 0 {
        bail!("BLAKE3 message block is not word aligned");
      }
      let first_word = offset / WORD_BYTES;
      let block = std::array::from_fn(|word| {
        message.get(first_word + word).copied().unwrap_or(zero)
      });
      (cv, block)
    };
    let outputs = builder.gate(
      slot,
      &[cv[0], cv[1], block[0], block[1], block[2], block[3], parameter],
    );
    row_outputs.push(outputs.try_into().expect("BLAKE3 gate has four outputs"));
  }
  let root_row = *trace
    .squeezes
    .first()
    .and_then(|rows| rows.first())
    .ok_or_else(|| anyhow::anyhow!("BLAKE3 trace has no root squeeze"))?;
  let root = row_outputs
    .get(root_row)
    .ok_or_else(|| anyhow::anyhow!("BLAKE3 root row is out of range"))?;
  Ok([root[0], root[1]])
}

/// Prove exact Stage 2 transcript replay through the PCS opening-batch sample.
pub fn prove_stage2_transcript_conformance(
  replay: &Stage2TranscriptReplayV1,
) -> Result<Stage2TranscriptConformanceArtifactV1> {
  let challenges = compute_challenges(replay)?;
  let relation = TranscriptRelation::build(replay)?;
  let inputs = relation.inputs.clone();
  let expected_public = relation.public(challenges);
  let witness = relation.shape.run(&inputs, &[]);
  if witness.public != expected_public {
    bail!("Flock transcript circuit disagrees with native HashChallenger");
  }

  let proof_bundle_bytes = prove_relation(&relation, &witness)?;
  Ok(Stage2TranscriptConformanceArtifactV1 {
    replay: replay.clone(),
    challenges,
    circuit_digest: relation.shape.circuit.digest(),
    proof_bundle_bytes,
  })
}

/// Verify and bind a transcript conformance proof to every observation and
/// sampled challenge carried by its strict artifact.
pub fn verify_stage2_transcript_conformance(
  artifact: &Stage2TranscriptConformanceArtifactV1,
) -> Result<()> {
  let challenges = compute_challenges(&artifact.replay)?;
  if challenges != artifact.challenges {
    bail!("Flock Stage 2 transcript artifact challenge mismatch");
  }
  let relation = TranscriptRelation::build(&artifact.replay)?;
  if relation.shape.circuit.digest() != artifact.circuit_digest {
    bail!("Flock Stage 2 transcript circuit digest mismatch");
  }
  let public = relation.public(artifact.challenges);
  verify_relation(&relation, &public, &artifact.proof_bundle_bytes)
}

fn prove_relation(
  relation: &TranscriptRelation,
  witness: &flock_prover::circuit::builder::CircuitWitness,
) -> Result<Vec<u8>> {
  let blake3_rows = witness.rows::<Blake3Gate>(relation.slots.blake3);
  let sample_rows = witness.rows::<GoldilocksSampleGate>(relation.slots.sample);
  let canonical_rows =
    witness.rows::<CanonicalGoldilocksPairGate>(relation.slots.canonical);

  let blake3_r1cs = flock_blake3::build_block_r1cs(relation.nu);
  let blake3_lincheck = blake3_r1cs.csc_lincheck_circuit();
  let sample_r1cs = build_goldilocks_sample_r1cs(relation.nu);
  let sample_lincheck = sample_r1cs.csc_lincheck_circuit();
  let canonical_r1cs = build_canonical_pair_r1cs(relation.nu);
  let canonical_lincheck = canonical_r1cs.csc_lincheck_circuit();

  let mut slots = vec![
    (
      relation.shape.registry_slot(relation.slots.blake3),
      UnionSlotProverInput::new(
        flock_blake3::generate_witness_batch_major_partial(
          blake3_rows,
          relation.nu,
        ),
        blake3_lincheck,
      ),
    ),
    (
      relation.shape.registry_slot(relation.slots.sample),
      UnionSlotProverInput::new(
        generate_goldilocks_sample_witness(sample_rows, relation.nu),
        sample_lincheck,
      ),
    ),
    (
      relation.shape.registry_slot(relation.slots.canonical),
      UnionSlotProverInput::new(
        generate_canonical_pair_witness(canonical_rows, relation.nu),
        canonical_lincheck,
      ),
    ),
  ];
  sort_slots(&mut slots)?;
  let slots = slots.into_iter().map(|(_, input)| input).collect();
  let union =
    UnionInstance::new(&relation.shape.registry, relation.shape.counts.clone());
  let params = pcs_params(&union);
  let mut challenger = FsChallenger::with_chained_blake3(
    STAGE2_TRANSCRIPT_CONFORMANCE_TRANSCRIPT_DOMAIN,
  );
  let (proof, commitment, _) = prover::prove_fast_ligerito_union_circuit(
    &union,
    &relation.shape.circuit,
    &witness.public,
    &params,
    slots,
    Vec::new(),
    &mut challenger,
  );
  let bytes = encode_bundle(&TranscriptProofBundle { commitment, proof })?;
  if bytes.len() > MAX_BUNDLE_BYTES {
    bail!("Flock Stage 2 transcript proof exceeds {MAX_BUNDLE_BYTES} bytes");
  }
  Ok(bytes)
}

fn verify_relation(
  relation: &TranscriptRelation,
  public: &[F128],
  proof_bundle_bytes: &[u8],
) -> Result<()> {
  let bundle = decode_bundle(proof_bundle_bytes)
    .context("decode Flock Stage 2 transcript proof bundle")?;
  let blake3_r1cs = flock_blake3::build_block_r1cs(relation.nu);
  let blake3_lincheck = blake3_r1cs.csc_lincheck_circuit();
  let sample_r1cs = build_goldilocks_sample_r1cs(relation.nu);
  let sample_lincheck = sample_r1cs.csc_lincheck_circuit();
  let canonical_r1cs = build_canonical_pair_r1cs(relation.nu);
  let canonical_lincheck = canonical_r1cs.csc_lincheck_circuit();
  let mut linchecks: Vec<(usize, &dyn LincheckCircuit)> = vec![
    (relation.shape.registry_slot(relation.slots.blake3), blake3_lincheck),
    (relation.shape.registry_slot(relation.slots.sample), sample_lincheck),
    (
      relation.shape.registry_slot(relation.slots.canonical),
      canonical_lincheck,
    ),
  ];
  sort_slots(&mut linchecks)?;
  let linchecks: Vec<&dyn LincheckCircuit> =
    linchecks.into_iter().map(|(_, lincheck)| lincheck).collect();
  let union =
    UnionInstance::new(&relation.shape.registry, relation.shape.counts.clone());
  let params = pcs_params(&union);
  let mut challenger = FsChallenger::with_chained_blake3(
    STAGE2_TRANSCRIPT_CONFORMANCE_TRANSCRIPT_DOMAIN,
  );
  verifier::verify_ligerito_union_circuit(
    &union,
    &relation.shape.circuit,
    public,
    &linchecks,
    &bundle.commitment,
    &bundle.proof,
    &params,
    &mut challenger,
  )
  .map_err(|error| {
    anyhow::anyhow!("Flock Stage 2 transcript proof rejected: {error:?}")
  })?;
  Ok(())
}

fn sort_slots<T>(slots: &mut [(usize, T)]) -> Result<()> {
  slots.sort_by_key(|(index, _)| *index);
  if slots.iter().enumerate().any(|(expected, (actual, _))| expected != *actual)
  {
    bail!("Flock Stage 2 transcript registry is not contiguous");
  }
  Ok(())
}

pub(crate) fn hash_trace(message_len: usize) -> FsChainTrace {
  let mut chain = FsChain::new();
  chain.absorb(&vec![0u8; message_len]);
  let output = chain.finalize(32);
  debug_assert_eq!(output.len(), 32);
  chain.finish()
}

fn transcript_traces(
  replay: &Stage2TranscriptReplayV1,
) -> Result<Vec<FsChainTrace>> {
  validate_replay(replay)?;
  let message_lengths = [
    replay.initial_observations.len(),
    32 + 16,
    32 + 16 + replay.stage2_and_accumulator_observations.len(),
    32 + replay.quotient_commitment_observations.len(),
    32 + replay.pcs_opening_observations.len(),
  ];
  Ok(message_lengths.iter().copied().map(hash_trace).collect())
}

fn compute_challenges(
  replay: &Stage2TranscriptReplayV1,
) -> Result<Stage2TranscriptChallengesV1> {
  Ok(compute_challenges_and_state(replay)?.0)
}

fn compute_challenges_and_state(
  replay: &Stage2TranscriptReplayV1,
) -> Result<(Stage2TranscriptChallengesV1, [u8; 32])> {
  validate_replay(replay)?;

  let digest_1 = hash_parts(&[&replay.initial_observations]);
  let (lookup, state_1) = sample_digest_high(&digest_1)?;
  let lookup_bytes = extension_bytes(lookup);

  let digest_2 = hash_parts(&[&state_1, &lookup_bytes]);
  let (fingerprint, state_2) = sample_digest_high(&digest_2)?;
  let fingerprint_bytes = extension_bytes(fingerprint);

  let digest_3 = hash_parts(&[
    &state_2,
    &fingerprint_bytes,
    &replay.stage2_and_accumulator_observations,
  ]);
  let (constraint, state_3) = sample_digest_high(&digest_3)?;

  let digest_4 =
    hash_parts(&[&state_3, &replay.quotient_commitment_observations]);
  let (zeta, state_4) = sample_digest_high(&digest_4)?;

  let digest_5 = hash_parts(&[&state_4, &replay.pcs_opening_observations]);
  let (pcs_alpha, state_5) = sample_digest_high(&digest_5)?;
  Ok((
    Stage2TranscriptChallengesV1 {
      lookup,
      fingerprint,
      constraint,
      zeta,
      pcs_alpha,
    },
    state_5,
  ))
}

fn compute_fri_challenges(
  prefix: &Stage2TranscriptReplayV1,
  replay: &Stage2FriTranscriptReplayV1,
) -> Result<Stage2FriTranscriptChallengesV1> {
  validate_fri_replay(replay)?;
  let (_, state) = compute_challenges_and_state(prefix)?;
  let mut challenger = NativeByteChallenger {
    input: state.to_vec(),
    // Sampling the PCS extension challenge consumed the high sixteen bytes.
    output: state[..16].to_vec(),
  };
  let mut betas = Vec::with_capacity(replay.commit_phase_commitments.len());
  for (round, cap) in replay.commit_phase_commitments.iter().enumerate() {
    challenger.observe(&cap_observation_bytes(cap));
    if !challenger
      .check_witness(replay.commit_pow_bits, replay.commit_pow_witnesses[round])
    {
      bail!("Stage 2 FRI commit PoW witness {round} is invalid");
    }
    betas.push(challenger.sample_extension()?);
  }
  challenger.observe(&final_observation_bytes(replay));
  if !challenger.check_witness(replay.query_pow_bits, replay.query_pow_witness)
  {
    bail!("Stage 2 FRI query PoW witness is invalid");
  }
  let query_indices = (0..replay.num_queries)
    .map(|_| challenger.sample_bits(replay.query_index_bits))
    .collect();
  Ok(Stage2FriTranscriptChallengesV1 { betas, query_indices })
}

struct NativeByteChallenger {
  input: Vec<u8>,
  output: Vec<u8>,
}

impl NativeByteChallenger {
  fn observe(&mut self, bytes: &[u8]) {
    if bytes.is_empty() {
      return;
    }
    self.output.clear();
    self.input.extend_from_slice(bytes);
  }

  fn sample_u64(&mut self) -> u64 {
    if self.output.is_empty() {
      let digest = *blake3::hash(&self.input).as_bytes();
      self.input = digest.to_vec();
      self.output = digest.to_vec();
    }
    let bytes: [u8; 8] =
      std::array::from_fn(|_| self.output.pop().expect("fresh digest bytes"));
    u64::from_le_bytes(bytes)
  }

  fn sample_extension(&mut self) -> Result<[u64; 2]> {
    let mut accepted = Vec::with_capacity(2);
    loop {
      let value = self.sample_u64();
      if value < GOLDILOCKS_MODULUS {
        accepted.push(value);
        if accepted.len() == 2 {
          return Ok([accepted[0], accepted[1]]);
        }
      }
    }
  }

  fn sample_bits(&mut self, bits: u8) -> u64 {
    debug_assert!(bits < 64);
    self.sample_u64() & ((1u64 << bits) - 1)
  }

  fn check_witness(&mut self, bits: u8, witness: u64) -> bool {
    if bits == 0 {
      return true;
    }
    self.observe(&witness.to_le_bytes());
    self.sample_bits(bits) == 0
  }
}

fn cap_observation_bytes(cap: &[[u8; 32]]) -> Vec<u8> {
  cap.iter().flatten().copied().collect()
}

fn final_observation_bytes(replay: &Stage2FriTranscriptReplayV1) -> Vec<u8> {
  let mut bytes = Vec::with_capacity(
    16 * replay.final_polynomial.len() + 8 * replay.log_arities.len(),
  );
  for &coefficient in &replay.final_polynomial {
    push_extension_observation(&mut bytes, coefficient);
  }
  for &log_arity in &replay.log_arities {
    push_u64_observation(&mut bytes, u64::from(log_arity));
  }
  bytes
}

pub(crate) fn fri_transcript_blake3_rows(
  replay: &Stage2FriTranscriptReplayV1,
) -> Result<usize> {
  validate_fri_replay(replay)?;
  let commit_rows =
    replay.commit_phase_commitments.iter().try_fold(0usize, |rows, cap| {
      let message_len =
        32 + 32 * cap.len() + 8 * usize::from(replay.commit_pow_bits != 0);
      rows
        .checked_add(hash_trace(message_len).rows.len())
        .and_then(|rows| rows.checked_add(hash_trace(32).rows.len()))
        .ok_or_else(|| anyhow::anyhow!("FRI transcript row count overflow"))
    })?;
  let final_rows = hash_trace(
    32 + final_observation_bytes(replay).len()
      + 8 * usize::from(replay.query_pow_bits != 0),
  )
  .rows
  .len();
  let draws = replay.num_queries + usize::from(replay.query_pow_bits != 0);
  let followup_digests = draws.div_ceil(4).saturating_sub(1);
  commit_rows
    .checked_add(final_rows)
    .and_then(|rows| {
      rows.checked_add(followup_digests * hash_trace(32).rows.len())
    })
    .ok_or_else(|| anyhow::anyhow!("FRI transcript row count overflow"))
}

pub(crate) fn fri_transcript_split_rows(
  replay: &Stage2FriTranscriptReplayV1,
) -> Result<usize> {
  validate_fri_replay(replay)?;
  usize::from(replay.commit_pow_bits)
    .checked_mul(replay.commit_phase_commitments.len())
    .and_then(|rows| rows.checked_add(usize::from(replay.query_pow_bits)))
    .and_then(|rows| {
      rows
        .checked_add(replay.num_queries * usize::from(replay.query_index_bits))
    })
    .ok_or_else(|| anyhow::anyhow!("FRI transcript split row count overflow"))
}

fn sample_digest_high(digest: &[u8; 32]) -> Result<([u64; 2], [u8; 32])> {
  let refill = hash_parts(&[digest]);
  let candidates = digest_candidates([
    pack_bytes(&digest[16..]),
    pack_bytes(&digest[..16]),
    pack_bytes(&refill[16..]),
    pack_bytes(&refill[..16]),
  ]);
  let (sample, failure, used_refill) = select_two_candidates(&candidates, 4);
  if failure {
    bail!("Stage 2 transcript needs more than eight Goldilocks candidates");
  }
  Ok(([sample.lo, sample.hi], if used_refill { refill } else { *digest }))
}

fn hash_parts(parts: &[&[u8]]) -> [u8; 32] {
  let mut hasher = blake3::Hasher::new();
  for part in parts {
    hasher.update(part);
  }
  *hasher.finalize().as_bytes()
}

fn extension_bytes(value: [u64; 2]) -> [u8; 16] {
  let mut bytes = [0u8; 16];
  bytes[..8].copy_from_slice(&value[0].to_le_bytes());
  bytes[8..].copy_from_slice(&value[1].to_le_bytes());
  bytes
}

fn push_u64_observation(bytes: &mut Vec<u8>, value: u64) {
  bytes.extend_from_slice(&value.to_le_bytes());
}

fn push_extension_observation(bytes: &mut Vec<u8>, value: [u64; 2]) {
  bytes.extend_from_slice(&extension_bytes(value));
}

fn push_cap_observations(bytes: &mut Vec<u8>, roots: &[[u8; 32]]) {
  for root in roots {
    bytes.extend_from_slice(root);
  }
}

fn push_opened_round_observations(
  bytes: &mut Vec<u8>,
  round: &Stage3OpenedRoundV1,
) {
  for matrix in round {
    for point in matrix {
      for &value in point {
        push_extension_observation(bytes, value);
      }
    }
  }
}

fn replay_segments(replay: &Stage2TranscriptReplayV1) -> [&[u8]; 4] {
  [
    &replay.initial_observations,
    &replay.stage2_and_accumulator_observations,
    &replay.quotient_commitment_observations,
    &replay.pcs_opening_observations,
  ]
}

fn pack_segment(segment: &[u8]) -> Vec<F128> {
  segment
    .chunks(WORD_BYTES)
    .map(|chunk| {
      let mut word = [0u8; WORD_BYTES];
      word[..chunk.len()].copy_from_slice(chunk);
      pack_bytes(&word)
    })
    .collect()
}

pub(crate) fn transcript_challenge_words(
  challenges: Stage2TranscriptChallengesV1,
) -> [F128; 5] {
  [
    pack_extension(challenges.lookup),
    pack_extension(challenges.fingerprint),
    pack_extension(challenges.constraint),
    pack_extension(challenges.zeta),
    pack_extension(challenges.pcs_alpha),
  ]
}

fn challenge_words(challenges: Stage2TranscriptChallengesV1) -> [F128; 5] {
  transcript_challenge_words(challenges)
}

fn pack_extension(value: [u64; 2]) -> F128 {
  F128::new(value[0], value[1])
}

fn validate_replay(replay: &Stage2TranscriptReplayV1) -> Result<()> {
  if replay.initial_observations.is_empty() {
    bail!("Stage 2 transcript initial observations are empty");
  }
  let total =
    replay_segments(replay).iter().try_fold(0usize, |total, segment| {
      total.checked_add(segment.len()).ok_or_else(|| {
        anyhow::anyhow!("Stage 2 transcript observation length overflow")
      })
    })?;
  if total > MAX_OBSERVATION_BYTES {
    bail!(
      "Stage 2 transcript carries {total} observation bytes; maximum is {MAX_OBSERVATION_BYTES}"
    );
  }
  Ok(())
}

fn validate_fri_replay(replay: &Stage2FriTranscriptReplayV1) -> Result<()> {
  let rounds = replay.commit_phase_commitments.len();
  if rounds == 0 || rounds > MAX_FRI_ROUNDS {
    bail!(
      "Stage 2 FRI transcript has {rounds} rounds; expected 1..={MAX_FRI_ROUNDS}"
    );
  }
  if replay.commit_pow_witnesses.len() != rounds
    || replay.log_arities.len() != rounds
  {
    bail!("Stage 2 FRI transcript round-vector lengths disagree");
  }
  if replay.num_queries == 0 || replay.num_queries > MAX_FRI_QUERIES {
    bail!(
      "Stage 2 FRI transcript has {} queries; expected 1..={MAX_FRI_QUERIES}",
      replay.num_queries
    );
  }
  if replay.query_index_bits == 0 || replay.query_index_bits >= 64 {
    bail!(
      "Stage 2 FRI query-index width {} is outside 1..64",
      replay.query_index_bits
    );
  }
  for (label, bits) in
    [("commit", replay.commit_pow_bits), ("query", replay.query_pow_bits)]
  {
    if bits >= 64 || (1u64 << bits) >= GOLDILOCKS_MODULUS {
      bail!("Stage 2 FRI {label} PoW width {bits} is invalid");
    }
  }
  if (1u64 << replay.query_index_bits) >= GOLDILOCKS_MODULUS {
    bail!("Stage 2 FRI query-index mask exceeds the field order");
  }
  if replay.final_polynomial.is_empty()
    || !replay.final_polynomial.len().is_power_of_two()
  {
    bail!(
      "Stage 2 FRI final polynomial length must be a non-zero power of two"
    );
  }
  for coefficient in &replay.final_polynomial {
    if coefficient.iter().any(|&limb| limb >= GOLDILOCKS_MODULUS) {
      bail!("Stage 2 FRI final polynomial contains a non-canonical limb");
    }
  }
  if replay
    .commit_pow_witnesses
    .iter()
    .chain(std::iter::once(&replay.query_pow_witness))
    .any(|&witness| witness >= GOLDILOCKS_MODULUS)
  {
    bail!("Stage 2 FRI transcript contains a non-canonical PoW witness");
  }
  let mut cap_roots = 0usize;
  for cap in &replay.commit_phase_commitments {
    if cap.is_empty() || cap.len() > MAX_CAP_ROOTS {
      bail!(
        "Stage 2 FRI commitment cap has {} roots; expected 1..={MAX_CAP_ROOTS}",
        cap.len()
      );
    }
    cap_roots = cap_roots
      .checked_add(cap.len())
      .ok_or_else(|| anyhow::anyhow!("Stage 2 FRI cap-root count overflow"))?;
  }
  if replay.log_arities.iter().any(|&arity| arity == 0 || arity >= 64) {
    bail!("Stage 2 FRI transcript contains an invalid folding log-arity");
  }
  let observation_bytes = 32usize
    .checked_mul(cap_roots)
    .and_then(|bytes| bytes.checked_add(final_observation_bytes(replay).len()))
    .and_then(|bytes| {
      bytes.checked_add(8 * usize::from(replay.query_pow_bits != 0))
    })
    .ok_or_else(|| {
      anyhow::anyhow!("Stage 2 FRI observation length overflow")
    })?;
  if observation_bytes > MAX_OBSERVATION_BYTES {
    bail!(
      "Stage 2 FRI transcript carries {observation_bytes} observation bytes; maximum is {MAX_OBSERVATION_BYTES}"
    );
  }
  Ok(())
}

fn validate_challenges(challenges: Stage2TranscriptChallengesV1) -> Result<()> {
  for challenge in [
    challenges.lookup,
    challenges.fingerprint,
    challenges.constraint,
    challenges.zeta,
    challenges.pcs_alpha,
  ] {
    if challenge.iter().any(|&value| value >= GOLDILOCKS_MODULUS) {
      bail!("non-canonical Goldilocks transcript challenge");
    }
  }
  Ok(())
}

fn encode_challenges(
  bytes: &mut Vec<u8>,
  challenges: Stage2TranscriptChallengesV1,
) {
  for challenge in [
    challenges.lookup,
    challenges.fingerprint,
    challenges.constraint,
    challenges.zeta,
    challenges.pcs_alpha,
  ] {
    bytes.extend_from_slice(&extension_bytes(challenge));
  }
}

fn decode_challenges(bytes: &[u8]) -> Stage2TranscriptChallengesV1 {
  debug_assert_eq!(bytes.len(), CHALLENGE_BYTES);
  let mut values = [[0u64; 2]; CHALLENGE_COUNT];
  for (value, chunk) in values.iter_mut().zip(bytes.as_chunks::<16>().0) {
    value[0] = u64::from_le_bytes(chunk[..8].try_into().unwrap());
    value[1] = u64::from_le_bytes(chunk[8..].try_into().unwrap());
  }
  Stage2TranscriptChallengesV1 {
    lookup: values[0],
    fingerprint: values[1],
    constraint: values[2],
    zeta: values[3],
    pcs_alpha: values[4],
  }
}

fn encode_bundle(bundle: &TranscriptProofBundle) -> Result<Vec<u8>> {
  bincode::DefaultOptions::new()
    .with_fixint_encoding()
    .serialize(bundle)
    .context("encode Flock Stage 2 transcript proof bundle")
}

fn decode_bundle(bytes: &[u8]) -> Result<TranscriptProofBundle> {
  bincode::DefaultOptions::new()
    .with_fixint_encoding()
    .with_limit(MAX_BUNDLE_BYTES as u64)
    .reject_trailing_bytes()
    .deserialize(bytes)
    .context("invalid Flock Stage 2 transcript proof bundle")
}

#[cfg(test)]
mod tests {
  use super::*;

  fn replay_fixture() -> Stage2TranscriptReplayV1 {
    let mut initial = b"multi-stark/v0".to_vec();
    for value in 0..19u64 {
      initial.extend_from_slice(&(value * 17 + 3).to_le_bytes());
    }
    // Exercise a final partial BLAKE3 word in the first flush.
    initial.extend_from_slice(&[0xa5, 0x5a, 0x11]);

    let stage2_and_accumulator_observations =
      (0..79u8).map(|value| value.wrapping_mul(29)).collect();
    let quotient_commitment_observations =
      (0..32u8).map(|value| value ^ 0x6d).collect();
    let pcs_opening_observations =
      (0..117u8).map(|value| value.wrapping_mul(7).wrapping_add(1)).collect();
    Stage2TranscriptReplayV1 {
      initial_observations: initial,
      stage2_and_accumulator_observations,
      quotient_commitment_observations,
      pcs_opening_observations,
    }
  }

  #[derive(Clone)]
  struct ReferenceHashChallenger {
    input: Vec<u8>,
    output: Vec<u8>,
  }

  impl ReferenceHashChallenger {
    fn new(initial: Vec<u8>) -> Self {
      Self { input: initial, output: Vec::new() }
    }

    fn observe(&mut self, bytes: &[u8]) {
      self.output.clear();
      self.input.extend_from_slice(bytes);
    }

    fn sample8(&mut self) -> [u8; 8] {
      if self.output.is_empty() {
        let digest = *blake3::hash(&self.input).as_bytes();
        self.input = digest.to_vec();
        self.output = digest.to_vec();
      }
      std::array::from_fn(|_| self.output.pop().unwrap())
    }

    fn sample_field(&mut self) -> u64 {
      loop {
        let value = u64::from_le_bytes(self.sample8());
        if value < GOLDILOCKS_MODULUS {
          return value;
        }
      }
    }

    fn sample_ext(&mut self) -> [u64; 2] {
      [self.sample_field(), self.sample_field()]
    }
  }

  #[test]
  fn optimized_replay_matches_hash_challenger_buffers() {
    let replay = replay_fixture();
    let expected = replay.challenges().unwrap();
    let mut challenger =
      ReferenceHashChallenger::new(replay.initial_observations.clone());
    let lookup = challenger.sample_ext();
    challenger.observe(&extension_bytes(lookup));
    let fingerprint = challenger.sample_ext();
    challenger.observe(&extension_bytes(fingerprint));
    challenger.observe(&replay.stage2_and_accumulator_observations);
    let constraint = challenger.sample_ext();
    challenger.observe(&replay.quotient_commitment_observations);
    let zeta = challenger.sample_ext();
    challenger.observe(&replay.pcs_opening_observations);
    let pcs_alpha = challenger.sample_ext();
    assert_eq!(
      expected,
      Stage2TranscriptChallengesV1 {
        lookup,
        fingerprint,
        constraint,
        zeta,
        pcs_alpha,
      }
    );
  }

  #[test]
  fn sample_gate_is_the_reverse_pop_order_permutation() {
    let input = F128::new(0x0706_0504_0302_0100, 0x0f0e_0d0c_0b0a_0908);
    assert_eq!(
      sample_word(input),
      F128::new(0x0809_0a0b_0c0d_0e0f, 0x0001_0203_0405_0607)
    );
    let rows = [HashSampleRow(input)];
    let (z, _, _, _) = generate_hash_sample_witness(&rows, MIN_NU);
    assert!(!z.is_empty());
  }

  #[test]
  fn goldilocks_sample_gate_redraws_and_supports_pow_skip() {
    let cases = [
      (
        [GOLDILOCKS_MODULUS, 5, 6, 7, 8, 9, 10, 11],
        F128::new(5, 6),
        F128::new(5, 6),
        false,
        false,
        false,
        false,
      ),
      (
        [1, GOLDILOCKS_MODULUS, 2, 3, 4, 5, 6, 7],
        F128::new(1, 2),
        F128::new(2, 3),
        false,
        false,
        false,
        false,
      ),
      (
        [GOLDILOCKS_MODULUS, GOLDILOCKS_MODULUS, 2, 3, 4, 5, 6, 7],
        F128::new(2, 3),
        F128::new(2, 3),
        false,
        false,
        false,
        false,
      ),
      (
        [1, 2, GOLDILOCKS_MODULUS, GOLDILOCKS_MODULUS, 4, 5, 6, 7],
        F128::new(1, 2),
        F128::new(2, 4),
        false,
        false,
        false,
        true,
      ),
      (
        [
          GOLDILOCKS_MODULUS,
          GOLDILOCKS_MODULUS,
          GOLDILOCKS_MODULUS,
          3,
          4,
          5,
          6,
          7,
        ],
        F128::new(3, 4),
        F128::new(3, 4),
        false,
        false,
        true,
        true,
      ),
    ];
    for (
      candidates,
      expected,
      expected_skip,
      failure,
      skip_failure,
      used_refill,
      skip_used_refill,
    ) in cases
    {
      let words = [
        F128::new(candidates[1].swap_bytes(), candidates[0].swap_bytes()),
        F128::new(candidates[3].swap_bytes(), candidates[2].swap_bytes()),
        F128::new(candidates[5].swap_bytes(), candidates[4].swap_bytes()),
        F128::new(candidates[7].swap_bytes(), candidates[6].swap_bytes()),
      ];
      let mut outputs = Vec::new();
      GoldilocksSampleGate { nu: MIN_NU }.eval(&words, &(), &mut outputs);
      assert_eq!(outputs[0], expected);
      assert_eq!(outputs[1], F128::new(u64::from(failure), 0));
      assert_eq!(outputs[2], F128::new(candidates[0], 0));
      assert_eq!(outputs[3], expected_skip);
      assert_eq!(outputs[4], F128::new(u64::from(skip_failure), 0));
      let state =
        if used_refill { [words[3], words[2]] } else { [words[1], words[0]] };
      let skip_state = if skip_used_refill {
        [words[3], words[2]]
      } else {
        [words[1], words[0]]
      };
      assert_eq!(outputs[5..7], state);
      assert_eq!(outputs[7..9], skip_state);
      let rows = [GoldilocksSampleRow(words)];
      let (z, _, _, _) = generate_goldilocks_sample_witness(&rows, MIN_NU);
      assert!(!z.is_empty());
    }
  }

  #[test]
  fn u64_split_gate_exposes_low_bits_and_rejects_a_high_lane() {
    let plan = u64_split_plan();
    let r1cs = plan.block_r1cs(MIN_NU);
    let value = 0x8bad_f00d_dead_beefu64;
    let mut row = vec![false; plan.k()];
    plan.fill_row(&mut row, |bits| {
      write_f128(bits, U64_SPLIT_INPUT_BASE, F128::new(value, 0));
    });
    let mut witness = vec![false; r1cs.n()];
    witness[..plan.k()].copy_from_slice(&row);
    assert!(r1cs.satisfies(&witness));
    assert_eq!(row[U64_SPLIT_BIT_BASE], value & 1 == 1);
    for bit in 0..63 {
      assert_eq!(
        row[U64_SPLIT_QUOTIENT_BASE + bit],
        (value >> (bit + 1)) & 1 == 1
      );
    }

    let mut wrong_quotient = witness;
    wrong_quotient[U64_SPLIT_QUOTIENT_BASE + 17] ^= true;
    assert!(!r1cs.satisfies(&wrong_quotient));

    let mut high_lane_row = vec![false; plan.k()];
    plan.fill_row(&mut high_lane_row, |bits| {
      write_f128(bits, U64_SPLIT_INPUT_BASE, F128::new(value, 1));
    });
    let mut high_lane = vec![false; r1cs.n()];
    high_lane[..plan.k()].copy_from_slice(&high_lane_row);
    assert!(!r1cs.satisfies(&high_lane));
  }

  #[test]
  fn circuit_matches_native_replay_and_uses_tree_hashing() {
    let replay = replay_fixture();
    let challenges = replay.challenges().unwrap();
    let relation = TranscriptRelation::build(&replay).unwrap();
    let witness = relation.shape.run(&relation.inputs, &[]);
    assert_eq!(witness.public, relation.public(challenges));

    let mut long = replay;
    long.initial_observations.resize(1_103, 0x42);
    let long_relation = TranscriptRelation::build(&long).unwrap();
    let long_challenges = long.challenges().unwrap();
    let long_witness = long_relation.shape.run(&long_relation.inputs, &[]);
    assert_eq!(long_witness.public, long_relation.public(long_challenges));
    assert!(
      long_witness.rows::<Blake3Gate>(long_relation.slots.blake3).len()
        > witness.rows::<Blake3Gate>(relation.slots.blake3).len()
    );
  }

  #[test]
  fn post_fri_circuit_matches_native_pow_betas_and_refilled_queries() {
    let prefix = replay_fixture();
    let mut replay = Stage2FriTranscriptReplayV1 {
      commit_phase_commitments: vec![
        vec![*blake3::hash(b"fri-cap-0").as_bytes()],
        vec![*blake3::hash(b"fri-cap-1").as_bytes()],
      ],
      commit_pow_witnesses: vec![0, 0],
      final_polynomial: vec![[17, 29]],
      log_arities: vec![1, 1],
      query_pow_witness: 0,
      commit_pow_bits: 2,
      query_pow_bits: 3,
      num_queries: 5,
      query_index_bits: 5,
    };
    let challenges = (0..4_096u64)
      .find_map(|nonce| {
        replay.commit_pow_witnesses = vec![nonce & 15, (nonce >> 4) & 15];
        replay.query_pow_witness = (nonce >> 8) & 15;
        replay.challenges(&prefix).ok()
      })
      .expect("small commit/query PoW fixture has witnesses");

    let nu = 11;
    let mut builder = ShapeBuilder::new(nu);
    let blake3 = builder.slot(Blake3Gate { nu });
    let sample = builder.slot(HashSampleGate { nu });
    let field_sample = builder.slot(GoldilocksSampleGate { nu });
    let canonical = builder.slot(CanonicalGoldilocksPairGate { nu });
    let repack =
      builder.slot(crate::extension::GoldilocksLaneRepackGate { nu });
    let split = builder.slot(U64SplitGate { nu });
    let prefix_region = constrain_stage2_transcript(
      &mut builder,
      TranscriptCircuitSlots { blake3, sample: field_sample, canonical },
      &prefix,
      nu,
    )
    .unwrap();
    let mut inputs = prefix_region.inputs.clone();
    let mut public = inputs.clone();
    for challenge in prefix_region.challenges.all() {
      builder.publish(challenge);
    }
    public.extend(challenge_words(prefix.challenges().unwrap()));

    let fri_region = constrain_stage2_fri_transcript(
      &mut builder,
      FriTranscriptCircuitSlots {
        blake3,
        sample,
        field_sample,
        canonical,
        repack,
        split,
      },
      &replay,
      prefix_region.state_digest,
      nu,
    )
    .unwrap();
    inputs.extend_from_slice(&fri_region.inputs);
    public.extend_from_slice(&fri_region.inputs);
    for &beta in &fri_region.betas {
      builder.publish(beta);
    }
    public.extend(challenges.betas.iter().copied().map(pack_extension));
    for bits in &fri_region.query_index_bits {
      for &bit in bits {
        builder.publish(bit);
      }
    }
    for &index in &challenges.query_indices {
      public.extend(
        (0..replay.query_index_bits)
          .map(|bit| F128::new((index >> bit) & 1, 0)),
      );
    }
    let shape = builder.finish().unwrap();
    let witness = shape.run(&inputs, &[]);
    assert_eq!(witness.public, public);
  }

  #[test]
  fn artifact_parser_is_strict_before_crypto() {
    let replay = replay_fixture();
    let artifact = Stage2TranscriptConformanceArtifactV1 {
      challenges: replay.challenges().unwrap(),
      replay,
      circuit_digest: [7; 32],
      proof_bundle_bytes: vec![1, 2, 3],
    };
    let bytes = artifact.to_bytes();
    assert_eq!(
      Stage2TranscriptConformanceArtifactV1::from_bytes(&bytes).unwrap(),
      artifact
    );

    let mut trailing = bytes.clone();
    trailing.push(0);
    assert!(
      Stage2TranscriptConformanceArtifactV1::from_bytes(&trailing).is_err()
    );
    let mut wrong_config = bytes.clone();
    wrong_config[CONFIG_OFFSET] ^= 1;
    assert!(
      Stage2TranscriptConformanceArtifactV1::from_bytes(&wrong_config).is_err()
    );
    let mut wrong_length = bytes;
    wrong_length[LENGTHS_OFFSET] ^= 1;
    assert!(
      Stage2TranscriptConformanceArtifactV1::from_bytes(&wrong_length).is_err()
    );
  }

  #[test]
  #[ignore = "large upstream Flock proof; run explicitly for transcript conformance"]
  fn real_transcript_round_trip_and_mutations() {
    let artifact = prove_stage2_transcript_conformance(&replay_fixture())
      .expect("prove Stage 2 transcript replay");
    eprintln!(
      "Flock Stage 2 transcript conformance bundle: {} bytes",
      artifact.proof_bundle_bytes().len()
    );
    verify_stage2_transcript_conformance(&artifact)
      .expect("verify Stage 2 transcript replay");

    let encoded = artifact.to_bytes();
    let decoded =
      Stage2TranscriptConformanceArtifactV1::from_bytes(&encoded).unwrap();
    verify_stage2_transcript_conformance(&decoded)
      .expect("verify decoded Stage 2 transcript replay");

    let mut wrong_observation = decoded.clone();
    wrong_observation.replay.pcs_opening_observations[0] ^= 1;
    assert!(verify_stage2_transcript_conformance(&wrong_observation).is_err());

    let mut wrong_challenge = decoded.clone();
    wrong_challenge.challenges.pcs_alpha[0] ^= 1;
    assert!(verify_stage2_transcript_conformance(&wrong_challenge).is_err());

    let mut wrong_proof = decoded;
    let flip_at = wrong_proof.proof_bundle_bytes.len() / 2;
    wrong_proof.proof_bundle_bytes[flip_at] ^= 1;
    assert!(verify_stage2_transcript_conformance(&wrong_proof).is_err());
  }
}
