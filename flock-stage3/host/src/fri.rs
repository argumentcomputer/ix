//! One authenticated binary FRI fold lowered into the Flock relation.
//!
//! This is the first conformance artifact that composes proof semantics rather
//! than testing an isolated primitive. It reconstructs the ordered evaluation
//! pair from the query-index bit, hashes the four Goldilocks coordinates with
//! Plonky3's serialized BLAKE3 leaf convention, authenticates the leaf, derives
//! the bit-reversed subgroup point, and constrains the binary fold.
//!
//! Division is deliberately absent from the circuit. The usual equation
//!
//! `f = (e0 + e1)/2 + beta * (e0 - e1)/(2s)`
//!
//! is constrained in the equivalent denominator-free form
//!
//! `2s*f + beta*e1 = s*(e0 + e1) + beta*e0`.

use ::blake3 as native_blake3;
use aiur::vk_codec::AiurVerifyingKey;
use anyhow::{Context, Result, bail};
use bincode::Options;
use flock_prover::{
  challenger::FsChallenger,
  circuit::builder::{CircuitShape, ShapeBuilder, SlotId, Wire},
  field::F128,
  lincheck::LincheckCircuit,
  pcs::Commitment,
  proof::R1csProofCircuitMerged,
  prover::{self, UnionSlotProverInput},
  r1cs_hashes::blake3 as flock_blake3,
  union::UnionInstance,
  verifier,
};
use ix_terminal::{
  Stage2RootStatementV1, ValidatedStage2RootV1, fri_parameter_words,
};
use multi_stark::{
  p3_field::{BasedVectorSpace, PrimeCharacteristicRing, PrimeField64},
  types::{ExtVal, FriParameters, Val},
};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

use crate::{
  FRI_FOLD_CONFORMANCE_TRANSCRIPT_DOMAIN,
  FRI_QUERY_CONFORMANCE_TRANSCRIPT_DOMAIN, FlockConfigV1,
  PCS_REDUCTION_CONFORMANCE_TRANSCRIPT_DOMAIN,
  STAGE2_AIR_PCS_FRI_CONFORMANCE_TRANSCRIPT_DOMAIN, Stage3TypedProofWitnessV1,
  TRANSCRIPT_BOUND_FRI_CONFORMANCE_TRANSCRIPT_DOMAIN,
  TRANSCRIPT_BOUND_FRI_QUERIES_CONFORMANCE_TRANSCRIPT_DOMAIN,
  TRANSCRIPT_BOUND_PCS_CONFORMANCE_TRANSCRIPT_DOMAIN,
  TRANSCRIPT_BOUND_PCS_FRI_QUERIES_CONFORMANCE_TRANSCRIPT_DOMAIN,
  air::{Stage2AirProgramV1, constrain_stage2_air},
  binding::{
    Blake3Gate, CHUNK_END, CHUNK_START, IV, ROOT, pack_bytes, pack_params,
    pack8, pcs_params,
  },
  equality::{
    F128EqualityGate, build_f128_equality_r1cs, generate_f128_equality_witness,
  },
  extension::{
    GoldilocksCircuitSlots, GoldilocksLaneRepackGate, build_lane_repack_r1cs,
    generate_lane_repack_witness,
  },
  goldilocks::{
    CanonicalGoldilocksPairGate, GOLDILOCKS_MODULUS, GoldilocksAddPairGate,
    build_canonical_pair_r1cs, build_goldilocks_add_r1cs,
    generate_canonical_pair_witness, generate_goldilocks_add_witness,
  },
  merkle::{
    DigestOrderGate, build_digest_order_r1cs, generate_digest_order_witness,
  },
  multiplication::{
    GoldilocksMulPairGate, build_goldilocks_mul_r1cs,
    generate_goldilocks_mul_witness, goldilocks_mul,
  },
  transcript::{
    FriTranscriptCircuitSlots, GoldilocksSampleGate, HashSampleGate,
    Stage2FriTranscriptChallengesV1, Stage2FriTranscriptReplayV1,
    Stage2TranscriptByteBindingV1, Stage2TranscriptReplayV1,
    Stage2TranscriptSegmentV1, TranscriptCircuitSlots, U64SplitGate,
    build_goldilocks_sample_r1cs, build_hash_sample_r1cs, build_u64_split_r1cs,
    constrain_hash, constrain_stage2_fri_transcript,
    constrain_stage2_transcript, fri_transcript_blake3_rows,
    fri_transcript_split_rows, generate_goldilocks_sample_witness,
    generate_hash_sample_witness, generate_u64_split_witness, hash_trace,
    transcript_challenge_words, transcript_nu,
  },
  window::{
    ByteWindowGate, build_byte_window_r1cs, generate_byte_window_witness,
  },
};

pub const FRI_FOLD_CONFORMANCE_ARTIFACT_MAGIC: &[u8; 8] = b"IXFLKFR1";
pub const FRI_COMMIT_PHASE_CONFORMANCE_ARTIFACT_MAGIC: &[u8; 8] = b"IXFLFQ01";
pub const PCS_REDUCTION_CONFORMANCE_ARTIFACT_MAGIC: &[u8; 8] = b"IXFLPR01";
const ARTIFACT_VERSION: u16 = 1;
const CONFIG_OFFSET: usize = 10;
const LOG_HEIGHT_OFFSET: usize = CONFIG_OFFSET + 32;
const QUERY_INDEX_OFFSET: usize = LOG_HEIGHT_OFFSET + 1;
const FOLDED_OFFSET: usize = QUERY_INDEX_OFFSET + 4;
const SIBLING_OFFSET: usize = FOLDED_OFFSET + 16;
const BETA_OFFSET: usize = SIBLING_OFFSET + 16;
const RESULT_OFFSET: usize = BETA_OFFSET + 16;
const PATH_OFFSET: usize = RESULT_OFFSET + 16;
const FIXED_SUFFIX_BYTES: usize = 32 + 32 + 8;
const MAX_BUNDLE_BYTES: usize = 64 * 1024 * 1024;
const MIN_LOG_HEIGHT: u8 = 1;
const MAX_LOG_HEIGHT: u8 = 31;
const MAX_REDUCED_OPENING_WIDTH: usize = 1 << 16;
// The arithmetic slots need enough rows for the bit-reversed exponentiation
// at the maximum supported height. This also keeps every table in a Flock
// Fast128 geometry exercised by the existing conformance proofs.
const NU: usize = 10;

/// The witness values consumed by one binary FRI commit-phase opening.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FriFoldQueryV1 {
  /// Height of the folded row (the original query has one additional bit).
  pub log_height: u8,
  /// Original FRI query index. Bit zero chooses the evaluation within the
  /// pair; bits `1..=log_height` authenticate the pair and derive `s`.
  pub query_index: u32,
  pub folded: [u64; 2],
  pub sibling: [u64; 2],
  pub beta: [u64; 2],
  /// Cap-height-zero authentication path for the row `[e0, e1]`.
  pub opening_proof: Vec<[u8; 32]>,
}

impl FriFoldQueryV1 {
  pub fn folded_result(&self) -> Result<[u64; 2]> {
    validate_query(self)?;
    Ok(native_fold(self))
  }

  pub fn commitment_root(&self) -> Result<[u8; 32]> {
    validate_query(self)?;
    Ok(native_root(self))
  }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FriCommitPhaseRoundV1 {
  pub sibling: [u64; 2],
  pub beta: [u64; 2],
  /// Reduced opening at this folded height, if one is scheduled. It is rolled
  /// in as `beta^2 * reduced_opening` after the binary fold.
  pub reduced_opening: Option<[u64; 2]>,
  pub opening_proof: Vec<[u8; 32]>,
}

/// A complete binary FRI commit-phase fold chain for one sampled query.
///
/// This intentionally excludes reduced-opening roll-ins and transcript replay;
/// those are separate semantic slices. Each round consumes the next low query
/// bit, authenticates its extension pair, and feeds its constrained result
/// directly into the following round. The last result must equal the constant
/// final polynomial.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FriCommitPhaseQueryV1 {
  /// Folded height of the first round. Round `r` has height
  /// `initial_log_height - r`.
  pub initial_log_height: u8,
  pub query_index: u32,
  pub initial_folded: [u64; 2],
  pub rounds: Vec<FriCommitPhaseRoundV1>,
  pub final_polynomial: [u64; 2],
}

impl FriCommitPhaseQueryV1 {
  pub fn commitment_roots(&self) -> Result<Vec<[u8; 32]>> {
    let computation = compute_commit_phase(self)?;
    ensure_final_polynomial(self, &computation)?;
    Ok(computation.roots)
  }

  pub fn folded_results(&self) -> Result<Vec<[u64; 2]>> {
    let computation = compute_commit_phase(self)?;
    ensure_final_polynomial(self, &computation)?;
    Ok(computation.results)
  }
}

/// One authenticated PCS row reduced into the FRI accumulator.
///
/// The conformance circuit supports one BLAKE3 leaf block (at most eight
/// Goldilocks values). Wider rows will use the same arithmetic but require the
/// multi-block/tree leaf hasher before the production relation is complete.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PcsReducedOpeningV1 {
  pub log_height: u8,
  pub query_index: u32,
  pub opened_values: Vec<u64>,
  pub opened_at_z: Vec<[u64; 2]>,
  pub zeta: [u64; 2],
  pub alpha: [u64; 2],
  pub initial_alpha_power: [u64; 2],
  pub initial_accumulator: [u64; 2],
  pub opening_proof: Vec<[u8; 32]>,
}

impl PcsReducedOpeningV1 {
  pub fn reduced_accumulator(&self) -> Result<[u64; 2]> {
    Ok(compute_pcs_reduction(self)?.accumulator)
  }

  pub fn next_alpha_power(&self) -> Result<[u64; 2]> {
    Ok(compute_pcs_reduction(self)?.alpha_power)
  }

  pub fn commitment_root(&self) -> Result<[u8; 32]> {
    Ok(compute_pcs_reduction(self)?.root)
  }
}

/// An opening point used by the specialised Stage 2 PCS verifier.
///
/// Stage 1, Stage 2, and preprocessed matrices are opened at both `zeta` and
/// `zeta * g`, while quotient matrices are opened only at `zeta`. Keeping the
/// point derivation in the relation prevents the prover from supplying a
/// second, unbound point.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Stage2PcsOpeningPointV1 {
  Zeta,
  ZetaNext { log_degree: u8 },
}

/// Verifier-known metadata for one matrix in a Stage 2 input commitment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stage2PcsMatrixV1 {
  /// Log2 of the LDE matrix height, including the FRI blowup.
  pub log_height: u8,
  /// Number of base-field columns in the authenticated row.
  pub width: usize,
  /// Opening points in the exact PCS batching order.
  pub opening_points: Vec<Stage2PcsOpeningPointV1>,
  /// First `u64` lane of this matrix's contiguous extension-valued OOD
  /// openings in the transcript's PCS-opening observation segment.
  pub opened_values: Stage2TranscriptByteBindingV1,
}

/// One multi-matrix MMCS commitment used as a PCS input batch.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stage2PcsBatchV1 {
  /// First `u64` lane of the 32-byte cap-height-zero commitment root in the
  /// constrained transcript prefix.
  pub commitment: Stage2TranscriptByteBindingV1,
  pub matrices: Vec<Stage2PcsMatrixV1>,
}

/// Shared, verifier-known PCS instance for all sampled FRI queries.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stage2PcsInstanceV1 {
  pub log_global_height: u8,
  pub log_blowup: u8,
  pub batches: Vec<Stage2PcsBatchV1>,
}

/// Per-query rows and a legacy full Merkle path for one input batch.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stage2PcsBatchOpeningV1 {
  pub opened_rows: Vec<Vec<u64>>,
  pub opening_proof: Vec<[u8; 32]>,
}

/// Every input-batch opening belonging to one transcript-derived query.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stage2PcsQueryV1 {
  pub batch_openings: Vec<Stage2PcsBatchOpeningV1>,
}

/// One query's authenticated PCS input followed by its FRI commit-phase
/// opening chain.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TranscriptBoundPcsFriQueryV1 {
  pub pcs: Stage2PcsQueryV1,
  pub fri: FriCommitPhaseQueryV1,
}

/// Exact typed Stage 2 PCS/FRI witness prepared for the combined Flock
/// relation. Commitment and OOD bindings point into `prefix`; query indices
/// and betas come from `fri_transcript`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stage2PcsFriWitnessV1 {
  pub prefix: Stage2TranscriptReplayV1,
  pub fri_transcript: Stage2FriTranscriptReplayV1,
  pub pcs_instance: Stage2PcsInstanceV1,
  pub queries: Vec<TranscriptBoundPcsFriQueryV1>,
}

impl Stage2PcsFriWitnessV1 {
  pub fn from_prepared(
    prepared: &ValidatedStage2RootV1,
    fri: &FriParameters,
  ) -> Result<Self> {
    let typed = Stage3TypedProofWitnessV1::from_prepared(prepared, fri)?;
    Self::from_prepared_and_typed(prepared, fri, &typed)
  }

  pub fn from_prepared_and_typed(
    prepared: &ValidatedStage2RootV1,
    fri: &FriParameters,
    typed: &Stage3TypedProofWitnessV1,
  ) -> Result<Self> {
    build_stage2_pcs_fri_witness(prepared, fri, typed)
  }
}

/// All currently lowered Stage 2 verifier semantics: compiled AIR/logUp OOD
/// evaluation plus transcript-bound PCS and every FRI query.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stage2AirPcsFriWitnessV1 {
  pub pcs_fri: Stage2PcsFriWitnessV1,
  pub air: Stage2AirProgramV1,
}

impl Stage2AirPcsFriWitnessV1 {
  pub fn from_prepared(
    prepared: &ValidatedStage2RootV1,
    fri: &FriParameters,
  ) -> Result<Self> {
    let typed = Stage3TypedProofWitnessV1::from_prepared(prepared, fri)?;
    let pcs_fri =
      Stage2PcsFriWitnessV1::from_prepared_and_typed(prepared, fri, &typed)?;
    let air = Stage2AirProgramV1::from_prepared_and_typed(
      prepared,
      fri,
      &pcs_fri.pcs_instance,
      &typed,
    )?;
    Ok(Self { pcs_fri, air })
  }
}

/// Exact circuit census produced by the no-prove Stage 3 preflight.
///
/// Counts are witness rows before Flock pads each table to `2^nu`. Keeping
/// them named makes production-root growth visible without exposing Flock's
/// internal slot identifiers as part of the Ix API.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stage3RelationCensusV1 {
  pub circuit_digest: [u8; 32],
  pub nu: u64,
  pub table_capacity: u64,
  pub relation_inputs: u64,
  pub public_values: u64,
  pub blake3_rows: u64,
  pub digest_order_rows: u64,
  pub goldilocks_add_rows: u64,
  pub goldilocks_mul_rows: u64,
  pub lane_repack_rows: u64,
  pub canonical_goldilocks_rows: u64,
  pub equality_rows: u64,
  pub hash_sample_rows: u64,
  pub field_sample_rows: u64,
  pub u64_split_rows: u64,
  pub byte_window_rows: u64,
}

impl Stage3RelationCensusV1 {
  pub fn total_rows(&self) -> u64 {
    self
      .blake3_rows
      .saturating_add(self.digest_order_rows)
      .saturating_add(self.goldilocks_add_rows)
      .saturating_add(self.goldilocks_mul_rows)
      .saturating_add(self.lane_repack_rows)
      .saturating_add(self.canonical_goldilocks_rows)
      .saturating_add(self.equality_rows)
      .saturating_add(self.hash_sample_rows)
      .saturating_add(self.field_sample_rows)
      .saturating_add(self.u64_split_rows)
      .saturating_add(self.byte_window_rows)
  }
}

/// A real Flock proof of an authenticated Plonky3-compatible binary FRI fold.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FriFoldConformanceArtifactV1 {
  query: FriFoldQueryV1,
  folded_result: [u64; 2],
  circuit_digest: [u8; 32],
  commitment_root: [u8; 32],
  proof_bundle_bytes: Vec<u8>,
}

impl FriFoldConformanceArtifactV1 {
  pub fn to_bytes(&self) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(
      PATH_OFFSET
        + 32 * self.query.opening_proof.len()
        + FIXED_SUFFIX_BYTES
        + self.proof_bundle_bytes.len(),
    );
    bytes.extend_from_slice(FRI_FOLD_CONFORMANCE_ARTIFACT_MAGIC);
    bytes.extend_from_slice(&ARTIFACT_VERSION.to_le_bytes());
    bytes.extend_from_slice(&FlockConfigV1.digest());
    bytes.push(self.query.log_height);
    bytes.extend_from_slice(&self.query.query_index.to_le_bytes());
    encode_extension(&mut bytes, self.query.folded);
    encode_extension(&mut bytes, self.query.sibling);
    encode_extension(&mut bytes, self.query.beta);
    encode_extension(&mut bytes, self.folded_result);
    for sibling in &self.query.opening_proof {
      bytes.extend_from_slice(sibling);
    }
    bytes.extend_from_slice(&self.circuit_digest);
    bytes.extend_from_slice(&self.commitment_root);
    bytes.extend_from_slice(
      &u64::try_from(self.proof_bundle_bytes.len())
        .expect("proof bundle length")
        .to_le_bytes(),
    );
    bytes.extend_from_slice(&self.proof_bundle_bytes);
    bytes
  }

  pub fn from_bytes(bytes: &[u8]) -> Result<Self> {
    if bytes.len() < PATH_OFFSET + FIXED_SUFFIX_BYTES {
      bail!("truncated Flock FRI-fold conformance artifact");
    }
    if &bytes[..8] != FRI_FOLD_CONFORMANCE_ARTIFACT_MAGIC {
      bail!("invalid Flock FRI-fold conformance artifact magic");
    }
    let version = u16::from_le_bytes(bytes[8..10].try_into().unwrap());
    if version != ARTIFACT_VERSION {
      bail!("unsupported Flock FRI-fold artifact version {version}");
    }
    if bytes[CONFIG_OFFSET..LOG_HEIGHT_OFFSET] != FlockConfigV1.digest() {
      bail!("Flock FRI-fold artifact configuration mismatch");
    }
    let log_height = bytes[LOG_HEIGHT_OFFSET];
    validate_log_height(log_height)?;
    let query_index = u32::from_le_bytes(
      bytes[QUERY_INDEX_OFFSET..FOLDED_OFFSET].try_into().unwrap(),
    );
    let folded = decode_extension(&bytes[FOLDED_OFFSET..SIBLING_OFFSET]);
    let sibling = decode_extension(&bytes[SIBLING_OFFSET..BETA_OFFSET]);
    let beta = decode_extension(&bytes[BETA_OFFSET..RESULT_OFFSET]);
    let folded_result = decode_extension(&bytes[RESULT_OFFSET..PATH_OFFSET]);
    let path_end = PATH_OFFSET
      .checked_add(usize::from(log_height) * 32)
      .ok_or_else(|| anyhow::anyhow!("FRI-fold path length overflow"))?;
    let suffix_end = path_end
      .checked_add(FIXED_SUFFIX_BYTES)
      .ok_or_else(|| anyhow::anyhow!("FRI-fold artifact length overflow"))?;
    if bytes.len() < suffix_end {
      bail!("truncated Flock FRI-fold path or proof header");
    }
    let opening_proof =
      bytes[PATH_OFFSET..path_end].as_chunks::<32>().0.to_vec();
    let query = FriFoldQueryV1 {
      log_height,
      query_index,
      folded,
      sibling,
      beta,
      opening_proof,
    };
    validate_query(&query)?;
    validate_extension(folded_result, "folded result")?;
    let mut circuit_digest = [0u8; 32];
    circuit_digest.copy_from_slice(&bytes[path_end..path_end + 32]);
    let mut commitment_root = [0u8; 32];
    commitment_root.copy_from_slice(&bytes[path_end + 32..path_end + 64]);
    let bundle_len = usize::try_from(u64::from_le_bytes(
      bytes[path_end + 64..suffix_end].try_into().unwrap(),
    ))
    .map_err(|error| {
      anyhow::anyhow!("proof bundle length does not fit usize: {error}")
    })?;
    if bundle_len == 0 || bundle_len > MAX_BUNDLE_BYTES {
      bail!("invalid Flock FRI-fold proof bundle length {bundle_len}");
    }
    let expected_len = suffix_end
      .checked_add(bundle_len)
      .ok_or_else(|| anyhow::anyhow!("FRI-fold proof length overflow"))?;
    if bytes.len() != expected_len {
      bail!(
        "Flock FRI-fold artifact is {} bytes; header declares {expected_len}",
        bytes.len()
      );
    }
    let proof_bundle_bytes = bytes[suffix_end..].to_vec();
    decode_bundle(&proof_bundle_bytes)
      .context("decode Flock FRI-fold conformance proof bundle")?;
    Ok(Self {
      query,
      folded_result,
      circuit_digest,
      commitment_root,
      proof_bundle_bytes,
    })
  }

  pub fn query(&self) -> &FriFoldQueryV1 {
    &self.query
  }

  pub fn folded_result(&self) -> [u64; 2] {
    self.folded_result
  }

  pub fn circuit_digest(&self) -> &[u8; 32] {
    &self.circuit_digest
  }

  pub fn commitment_root(&self) -> &[u8; 32] {
    &self.commitment_root
  }

  pub fn proof_bundle_bytes(&self) -> &[u8] {
    &self.proof_bundle_bytes
  }
}

const COMMIT_PHASE_ROUND_COUNT_OFFSET: usize = LOG_HEIGHT_OFFSET + 1;
const COMMIT_PHASE_QUERY_INDEX_OFFSET: usize =
  COMMIT_PHASE_ROUND_COUNT_OFFSET + 1;
const COMMIT_PHASE_INITIAL_OFFSET: usize = COMMIT_PHASE_QUERY_INDEX_OFFSET + 4;
const COMMIT_PHASE_FINAL_OFFSET: usize = COMMIT_PHASE_INITIAL_OFFSET + 16;
const COMMIT_PHASE_ROUNDS_OFFSET: usize = COMMIT_PHASE_FINAL_OFFSET + 16;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FriCommitPhaseConformanceArtifactV1 {
  query: FriCommitPhaseQueryV1,
  circuit_digest: [u8; 32],
  commitment_roots: Vec<[u8; 32]>,
  proof_bundle_bytes: Vec<u8>,
}

impl FriCommitPhaseConformanceArtifactV1 {
  pub fn to_bytes(&self) -> Vec<u8> {
    let round_bytes = self
      .query
      .rounds
      .iter()
      .map(|round| 49 + round.opening_proof.len() * 32)
      .sum::<usize>();
    let mut bytes = Vec::with_capacity(
      COMMIT_PHASE_ROUNDS_OFFSET
        + round_bytes
        + 32
        + self.commitment_roots.len() * 32
        + 8
        + self.proof_bundle_bytes.len(),
    );
    bytes.extend_from_slice(FRI_COMMIT_PHASE_CONFORMANCE_ARTIFACT_MAGIC);
    bytes.extend_from_slice(&ARTIFACT_VERSION.to_le_bytes());
    bytes.extend_from_slice(&FlockConfigV1.digest());
    bytes.push(self.query.initial_log_height);
    bytes.push(u8::try_from(self.query.rounds.len()).expect("FRI round count"));
    bytes.extend_from_slice(&self.query.query_index.to_le_bytes());
    encode_extension(&mut bytes, self.query.initial_folded);
    encode_extension(&mut bytes, self.query.final_polynomial);
    for round in &self.query.rounds {
      encode_extension(&mut bytes, round.sibling);
      encode_extension(&mut bytes, round.beta);
      bytes.push(u8::from(round.reduced_opening.is_some()));
      encode_extension(&mut bytes, round.reduced_opening.unwrap_or([0, 0]));
      for sibling in &round.opening_proof {
        bytes.extend_from_slice(sibling);
      }
    }
    bytes.extend_from_slice(&self.circuit_digest);
    for root in &self.commitment_roots {
      bytes.extend_from_slice(root);
    }
    bytes.extend_from_slice(
      &u64::try_from(self.proof_bundle_bytes.len())
        .expect("proof bundle length")
        .to_le_bytes(),
    );
    bytes.extend_from_slice(&self.proof_bundle_bytes);
    bytes
  }

  pub fn from_bytes(bytes: &[u8]) -> Result<Self> {
    if bytes.len() < COMMIT_PHASE_ROUNDS_OFFSET + 32 + 32 + 8 {
      bail!("truncated Flock FRI commit-phase conformance artifact");
    }
    if &bytes[..8] != FRI_COMMIT_PHASE_CONFORMANCE_ARTIFACT_MAGIC {
      bail!("invalid Flock FRI commit-phase artifact magic");
    }
    let version = u16::from_le_bytes(bytes[8..10].try_into().unwrap());
    if version != ARTIFACT_VERSION {
      bail!("unsupported Flock FRI commit-phase artifact version {version}");
    }
    if bytes[CONFIG_OFFSET..LOG_HEIGHT_OFFSET] != FlockConfigV1.digest() {
      bail!("Flock FRI commit-phase artifact configuration mismatch");
    }
    let initial_log_height = bytes[LOG_HEIGHT_OFFSET];
    validate_log_height(initial_log_height)?;
    let round_count = usize::from(bytes[COMMIT_PHASE_ROUND_COUNT_OFFSET]);
    validate_commit_phase_round_count(initial_log_height, round_count)?;
    let query_index = u32::from_le_bytes(
      bytes[COMMIT_PHASE_QUERY_INDEX_OFFSET..COMMIT_PHASE_INITIAL_OFFSET]
        .try_into()
        .unwrap(),
    );
    let initial_folded = decode_extension(
      &bytes[COMMIT_PHASE_INITIAL_OFFSET..COMMIT_PHASE_FINAL_OFFSET],
    );
    let final_polynomial = decode_extension(
      &bytes[COMMIT_PHASE_FINAL_OFFSET..COMMIT_PHASE_ROUNDS_OFFSET],
    );
    let rounds_bytes =
      commit_phase_rounds_bytes(initial_log_height, round_count)?;
    let rounds_end = COMMIT_PHASE_ROUNDS_OFFSET
      .checked_add(rounds_bytes)
      .ok_or_else(|| anyhow::anyhow!("FRI commit-phase rounds overflow"))?;
    let suffix_len = 32usize
      .checked_add(round_count * 32)
      .and_then(|length| length.checked_add(8))
      .ok_or_else(|| anyhow::anyhow!("FRI commit-phase suffix overflow"))?;
    let suffix_end = rounds_end
      .checked_add(suffix_len)
      .ok_or_else(|| anyhow::anyhow!("FRI commit-phase artifact overflow"))?;
    if bytes.len() < suffix_end {
      bail!("truncated Flock FRI commit-phase rounds or proof header");
    }

    let mut cursor = COMMIT_PHASE_ROUNDS_OFFSET;
    let mut rounds = Vec::with_capacity(round_count);
    for round_index in 0..round_count {
      let log_height = usize::from(initial_log_height) - round_index;
      let sibling = decode_extension(&bytes[cursor..cursor + 16]);
      cursor += 16;
      let beta = decode_extension(&bytes[cursor..cursor + 16]);
      cursor += 16;
      let has_reduced_opening = bytes[cursor];
      cursor += 1;
      if has_reduced_opening > 1 {
        bail!(
          "FRI commit-phase round {round_index} has invalid roll-in flag {has_reduced_opening}"
        );
      }
      let encoded_reduced_opening =
        decode_extension(&bytes[cursor..cursor + 16]);
      cursor += 16;
      let reduced_opening = if has_reduced_opening == 1 {
        Some(encoded_reduced_opening)
      } else {
        if encoded_reduced_opening != [0, 0] {
          bail!("absent FRI reduced opening has nonzero encoding");
        }
        None
      };
      let path_end = cursor + log_height * 32;
      let opening_proof = bytes[cursor..path_end].as_chunks::<32>().0.to_vec();
      cursor = path_end;
      rounds.push(FriCommitPhaseRoundV1 {
        sibling,
        beta,
        reduced_opening,
        opening_proof,
      });
    }
    debug_assert_eq!(cursor, rounds_end);
    let query = FriCommitPhaseQueryV1 {
      initial_log_height,
      query_index,
      initial_folded,
      rounds,
      final_polynomial,
    };
    let computation = compute_commit_phase(&query)?;
    ensure_final_polynomial(&query, &computation)?;

    let mut circuit_digest = [0u8; 32];
    circuit_digest.copy_from_slice(&bytes[rounds_end..rounds_end + 32]);
    let roots_end = rounds_end + 32 + round_count * 32;
    let commitment_roots =
      bytes[rounds_end + 32..roots_end].as_chunks::<32>().0.to_vec();
    let bundle_len = usize::try_from(u64::from_le_bytes(
      bytes[roots_end..suffix_end].try_into().unwrap(),
    ))
    .map_err(|error| {
      anyhow::anyhow!("proof bundle length does not fit usize: {error}")
    })?;
    if bundle_len == 0 || bundle_len > MAX_BUNDLE_BYTES {
      bail!("invalid Flock FRI commit-phase proof length {bundle_len}");
    }
    let expected_len = suffix_end
      .checked_add(bundle_len)
      .ok_or_else(|| anyhow::anyhow!("FRI commit-phase proof overflow"))?;
    if bytes.len() != expected_len {
      bail!(
        "Flock FRI commit-phase artifact is {} bytes; header declares {expected_len}",
        bytes.len()
      );
    }
    let proof_bundle_bytes = bytes[suffix_end..].to_vec();
    decode_bundle(&proof_bundle_bytes)
      .context("decode Flock FRI commit-phase proof bundle")?;
    Ok(Self { query, circuit_digest, commitment_roots, proof_bundle_bytes })
  }

  pub fn query(&self) -> &FriCommitPhaseQueryV1 {
    &self.query
  }

  pub fn circuit_digest(&self) -> &[u8; 32] {
    &self.circuit_digest
  }

  pub fn commitment_roots(&self) -> &[[u8; 32]] {
    &self.commitment_roots
  }

  pub fn proof_bundle_bytes(&self) -> &[u8] {
    &self.proof_bundle_bytes
  }
}

const PCS_WIDTH_OFFSET: usize = LOG_HEIGHT_OFFSET + 1;
const PCS_QUERY_INDEX_OFFSET: usize = PCS_WIDTH_OFFSET + 1;
const PCS_ZETA_OFFSET: usize = PCS_QUERY_INDEX_OFFSET + 4;
const PCS_ALPHA_OFFSET: usize = PCS_ZETA_OFFSET + 16;
const PCS_INITIAL_ALPHA_POWER_OFFSET: usize = PCS_ALPHA_OFFSET + 16;
const PCS_INITIAL_ACCUMULATOR_OFFSET: usize =
  PCS_INITIAL_ALPHA_POWER_OFFSET + 16;
const PCS_REDUCED_ACCUMULATOR_OFFSET: usize =
  PCS_INITIAL_ACCUMULATOR_OFFSET + 16;
const PCS_NEXT_ALPHA_POWER_OFFSET: usize = PCS_REDUCED_ACCUMULATOR_OFFSET + 16;
const PCS_DYNAMIC_OFFSET: usize = PCS_NEXT_ALPHA_POWER_OFFSET + 16;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PcsReductionConformanceArtifactV1 {
  opening: PcsReducedOpeningV1,
  reduced_accumulator: [u64; 2],
  next_alpha_power: [u64; 2],
  circuit_digest: [u8; 32],
  commitment_root: [u8; 32],
  proof_bundle_bytes: Vec<u8>,
}

impl PcsReductionConformanceArtifactV1 {
  pub fn to_bytes(&self) -> Vec<u8> {
    let width = self.opening.opened_values.len();
    let dynamic_bytes =
      width * 8 + width * 16 + self.opening.opening_proof.len() * 32;
    let mut bytes = Vec::with_capacity(
      PCS_DYNAMIC_OFFSET
        + dynamic_bytes
        + FIXED_SUFFIX_BYTES
        + self.proof_bundle_bytes.len(),
    );
    bytes.extend_from_slice(PCS_REDUCTION_CONFORMANCE_ARTIFACT_MAGIC);
    bytes.extend_from_slice(&ARTIFACT_VERSION.to_le_bytes());
    bytes.extend_from_slice(&FlockConfigV1.digest());
    bytes.push(self.opening.log_height);
    bytes.push(u8::try_from(width).expect("PCS row width"));
    bytes.extend_from_slice(&self.opening.query_index.to_le_bytes());
    encode_extension(&mut bytes, self.opening.zeta);
    encode_extension(&mut bytes, self.opening.alpha);
    encode_extension(&mut bytes, self.opening.initial_alpha_power);
    encode_extension(&mut bytes, self.opening.initial_accumulator);
    encode_extension(&mut bytes, self.reduced_accumulator);
    encode_extension(&mut bytes, self.next_alpha_power);
    for value in &self.opening.opened_values {
      bytes.extend_from_slice(&value.to_le_bytes());
    }
    for value in &self.opening.opened_at_z {
      encode_extension(&mut bytes, *value);
    }
    for sibling in &self.opening.opening_proof {
      bytes.extend_from_slice(sibling);
    }
    bytes.extend_from_slice(&self.circuit_digest);
    bytes.extend_from_slice(&self.commitment_root);
    bytes.extend_from_slice(
      &u64::try_from(self.proof_bundle_bytes.len())
        .expect("proof bundle length")
        .to_le_bytes(),
    );
    bytes.extend_from_slice(&self.proof_bundle_bytes);
    bytes
  }

  pub fn from_bytes(bytes: &[u8]) -> Result<Self> {
    if bytes.len() < PCS_DYNAMIC_OFFSET + FIXED_SUFFIX_BYTES {
      bail!("truncated Flock PCS-reduction conformance artifact");
    }
    if &bytes[..8] != PCS_REDUCTION_CONFORMANCE_ARTIFACT_MAGIC {
      bail!("invalid Flock PCS-reduction artifact magic");
    }
    let version = u16::from_le_bytes(bytes[8..10].try_into().unwrap());
    if version != ARTIFACT_VERSION {
      bail!("unsupported Flock PCS-reduction artifact version {version}");
    }
    if bytes[CONFIG_OFFSET..LOG_HEIGHT_OFFSET] != FlockConfigV1.digest() {
      bail!("Flock PCS-reduction artifact configuration mismatch");
    }
    let log_height = bytes[LOG_HEIGHT_OFFSET];
    validate_log_height(log_height)?;
    let width = usize::from(bytes[PCS_WIDTH_OFFSET]);
    validate_reduced_opening_width(width)?;
    let query_index = u32::from_le_bytes(
      bytes[PCS_QUERY_INDEX_OFFSET..PCS_ZETA_OFFSET].try_into().unwrap(),
    );
    let zeta = decode_extension(&bytes[PCS_ZETA_OFFSET..PCS_ALPHA_OFFSET]);
    let alpha = decode_extension(
      &bytes[PCS_ALPHA_OFFSET..PCS_INITIAL_ALPHA_POWER_OFFSET],
    );
    let initial_alpha_power = decode_extension(
      &bytes[PCS_INITIAL_ALPHA_POWER_OFFSET..PCS_INITIAL_ACCUMULATOR_OFFSET],
    );
    let initial_accumulator = decode_extension(
      &bytes[PCS_INITIAL_ACCUMULATOR_OFFSET..PCS_REDUCED_ACCUMULATOR_OFFSET],
    );
    let reduced_accumulator = decode_extension(
      &bytes[PCS_REDUCED_ACCUMULATOR_OFFSET..PCS_NEXT_ALPHA_POWER_OFFSET],
    );
    let next_alpha_power =
      decode_extension(&bytes[PCS_NEXT_ALPHA_POWER_OFFSET..PCS_DYNAMIC_OFFSET]);
    let opened_values_end = PCS_DYNAMIC_OFFSET
      .checked_add(width * 8)
      .ok_or_else(|| anyhow::anyhow!("PCS opened-values length overflow"))?;
    let opened_at_z_end = opened_values_end
      .checked_add(width * 16)
      .ok_or_else(|| anyhow::anyhow!("PCS OOD-values length overflow"))?;
    let path_end = opened_at_z_end
      .checked_add(usize::from(log_height) * 32)
      .ok_or_else(|| anyhow::anyhow!("PCS Merkle path length overflow"))?;
    let suffix_end = path_end
      .checked_add(FIXED_SUFFIX_BYTES)
      .ok_or_else(|| anyhow::anyhow!("PCS artifact length overflow"))?;
    if bytes.len() < suffix_end {
      bail!("truncated Flock PCS values, path, or proof header");
    }
    let opened_values = bytes[PCS_DYNAMIC_OFFSET..opened_values_end]
      .as_chunks::<8>()
      .0
      .iter()
      .map(|word| u64::from_le_bytes(*word))
      .collect();
    let opened_at_z = bytes[opened_values_end..opened_at_z_end]
      .as_chunks::<16>()
      .0
      .iter()
      .map(|value| decode_extension(value))
      .collect();
    let opening_proof =
      bytes[opened_at_z_end..path_end].as_chunks::<32>().0.to_vec();
    let opening = PcsReducedOpeningV1 {
      log_height,
      query_index,
      opened_values,
      opened_at_z,
      zeta,
      alpha,
      initial_alpha_power,
      initial_accumulator,
      opening_proof,
    };
    let computation = compute_pcs_reduction(&opening)?;
    validate_extension(reduced_accumulator, "reduced accumulator")?;
    validate_extension(next_alpha_power, "next alpha power")?;

    let mut circuit_digest = [0u8; 32];
    circuit_digest.copy_from_slice(&bytes[path_end..path_end + 32]);
    let mut commitment_root = [0u8; 32];
    commitment_root.copy_from_slice(&bytes[path_end + 32..path_end + 64]);
    let bundle_len = usize::try_from(u64::from_le_bytes(
      bytes[path_end + 64..suffix_end].try_into().unwrap(),
    ))
    .map_err(|error| {
      anyhow::anyhow!("proof bundle length does not fit usize: {error}")
    })?;
    if bundle_len == 0 || bundle_len > MAX_BUNDLE_BYTES {
      bail!("invalid Flock PCS-reduction proof length {bundle_len}");
    }
    let expected_len = suffix_end
      .checked_add(bundle_len)
      .ok_or_else(|| anyhow::anyhow!("PCS-reduction proof overflow"))?;
    if bytes.len() != expected_len {
      bail!(
        "Flock PCS-reduction artifact is {} bytes; header declares {expected_len}",
        bytes.len()
      );
    }
    let proof_bundle_bytes = bytes[suffix_end..].to_vec();
    decode_bundle(&proof_bundle_bytes)
      .context("decode Flock PCS-reduction proof bundle")?;
    if reduced_accumulator != computation.accumulator
      || next_alpha_power != computation.alpha_power
      || commitment_root != computation.root
    {
      bail!("Flock PCS-reduction artifact carries inconsistent native outputs");
    }
    Ok(Self {
      opening,
      reduced_accumulator,
      next_alpha_power,
      circuit_digest,
      commitment_root,
      proof_bundle_bytes,
    })
  }

  pub fn opening(&self) -> &PcsReducedOpeningV1 {
    &self.opening
  }

  pub fn reduced_accumulator(&self) -> [u64; 2] {
    self.reduced_accumulator
  }

  pub fn next_alpha_power(&self) -> [u64; 2] {
    self.next_alpha_power
  }

  pub fn circuit_digest(&self) -> &[u8; 32] {
    &self.circuit_digest
  }

  pub fn commitment_root(&self) -> &[u8; 32] {
    &self.commitment_root
  }

  pub fn proof_bundle_bytes(&self) -> &[u8] {
    &self.proof_bundle_bytes
  }
}

/// One Flock proof in which the exact Stage 2 BLAKE3 transcript directly
/// supplies zeta and the PCS opening-batch challenge to an authenticated
/// reduced-opening check.
///
/// This is the first composed semantic slice: changing any transcript byte
/// changes the wires used by the PCS arithmetic inside the same circuit.  It
/// remains a conformance artifact, not the complete Stage 3 proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TranscriptBoundPcsReductionArtifactV1 {
  replay: Stage2TranscriptReplayV1,
  opening: PcsReducedOpeningV1,
  reduced_accumulator: [u64; 2],
  next_alpha_power: [u64; 2],
  circuit_digest: [u8; 32],
  commitment_root: [u8; 32],
  proof_bundle_bytes: Vec<u8>,
}

impl TranscriptBoundPcsReductionArtifactV1 {
  pub fn replay(&self) -> &Stage2TranscriptReplayV1 {
    &self.replay
  }

  pub fn opening(&self) -> &PcsReducedOpeningV1 {
    &self.opening
  }

  pub fn reduced_accumulator(&self) -> [u64; 2] {
    self.reduced_accumulator
  }

  pub fn next_alpha_power(&self) -> [u64; 2] {
    self.next_alpha_power
  }

  pub fn circuit_digest(&self) -> &[u8; 32] {
    &self.circuit_digest
  }

  pub fn commitment_root(&self) -> &[u8; 32] {
    &self.commitment_root
  }

  pub fn proof_bundle_bytes(&self) -> &[u8] {
    &self.proof_bundle_bytes
  }
}

/// One Flock proof that continues the exact Stage 2 transcript through FRI,
/// then uses a transcript-derived query index and folding challenges to check
/// one complete authenticated binary commit-phase chain.
///
/// Cap roots and the final polynomial are consumed from the same transcript
/// wires used by the fold relation. This is still a conformance slice: a full
/// Stage 3 proof must check every sampled query and all PCS reduced openings.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TranscriptBoundFriCommitPhaseArtifactV1 {
  prefix: Stage2TranscriptReplayV1,
  fri_transcript: Stage2FriTranscriptReplayV1,
  query_number: usize,
  query: FriCommitPhaseQueryV1,
  circuit_digest: [u8; 32],
  commitment_roots: Vec<[u8; 32]>,
  proof_bundle_bytes: Vec<u8>,
}

impl TranscriptBoundFriCommitPhaseArtifactV1 {
  pub fn prefix(&self) -> &Stage2TranscriptReplayV1 {
    &self.prefix
  }

  pub fn fri_transcript(&self) -> &Stage2FriTranscriptReplayV1 {
    &self.fri_transcript
  }

  pub const fn query_number(&self) -> usize {
    self.query_number
  }

  pub fn query(&self) -> &FriCommitPhaseQueryV1 {
    &self.query
  }

  pub fn circuit_digest(&self) -> &[u8; 32] {
    &self.circuit_digest
  }

  pub fn commitment_roots(&self) -> &[[u8; 32]] {
    &self.commitment_roots
  }

  pub fn proof_bundle_bytes(&self) -> &[u8] {
    &self.proof_bundle_bytes
  }
}

/// One Flock proof of every transcript-derived FRI query. All queries share
/// one constrained transcript, beta vector, cap set, and final polynomial.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TranscriptBoundFriQueriesArtifactV1 {
  prefix: Stage2TranscriptReplayV1,
  fri_transcript: Stage2FriTranscriptReplayV1,
  queries: Vec<FriCommitPhaseQueryV1>,
  circuit_digest: [u8; 32],
  proof_bundle_bytes: Vec<u8>,
}

impl TranscriptBoundFriQueriesArtifactV1 {
  pub fn prefix(&self) -> &Stage2TranscriptReplayV1 {
    &self.prefix
  }

  pub fn fri_transcript(&self) -> &Stage2FriTranscriptReplayV1 {
    &self.fri_transcript
  }

  pub fn queries(&self) -> &[FriCommitPhaseQueryV1] {
    &self.queries
  }

  pub fn circuit_digest(&self) -> &[u8; 32] {
    &self.circuit_digest
  }

  pub fn proof_bundle_bytes(&self) -> &[u8] {
    &self.proof_bundle_bytes
  }
}

/// One Flock proof that authenticates every Stage 2 PCS input row, computes
/// all per-height reduced openings from transcript-bound OOD values, and feeds
/// those accumulators into every transcript-derived FRI query.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TranscriptBoundPcsFriQueriesArtifactV1 {
  prefix: Stage2TranscriptReplayV1,
  fri_transcript: Stage2FriTranscriptReplayV1,
  pcs_instance: Stage2PcsInstanceV1,
  queries: Vec<TranscriptBoundPcsFriQueryV1>,
  circuit_digest: [u8; 32],
  proof_bundle_bytes: Vec<u8>,
}

impl TranscriptBoundPcsFriQueriesArtifactV1 {
  pub fn prefix(&self) -> &Stage2TranscriptReplayV1 {
    &self.prefix
  }

  pub fn fri_transcript(&self) -> &Stage2FriTranscriptReplayV1 {
    &self.fri_transcript
  }

  pub fn pcs_instance(&self) -> &Stage2PcsInstanceV1 {
    &self.pcs_instance
  }

  pub fn queries(&self) -> &[TranscriptBoundPcsFriQueryV1] {
    &self.queries
  }

  pub fn circuit_digest(&self) -> &[u8; 32] {
    &self.circuit_digest
  }

  pub fn proof_bundle_bytes(&self) -> &[u8] {
    &self.proof_bundle_bytes
  }
}

/// A real Flock proof of statement binding and compiled AIR/logUp OOD checks
/// composed with the exact PCS-to-FRI relation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stage2AirPcsFriArtifactV1 {
  witness: Stage2AirPcsFriWitnessV1,
  circuit_digest: [u8; 32],
  proof_bundle_bytes: Vec<u8>,
}

impl Stage2AirPcsFriArtifactV1 {
  pub(crate) fn from_parts(
    witness: Stage2AirPcsFriWitnessV1,
    circuit_digest: [u8; 32],
    proof_bundle_bytes: Vec<u8>,
  ) -> Result<Self> {
    if proof_bundle_bytes.is_empty() {
      bail!("Stage 2 AIR/PCS/FRI proof bundle is empty");
    }
    if proof_bundle_bytes.len() > MAX_BUNDLE_BYTES {
      bail!(
        "Stage 2 AIR/PCS/FRI proof bundle exceeds {MAX_BUNDLE_BYTES} bytes"
      );
    }
    Ok(Self { witness, circuit_digest, proof_bundle_bytes })
  }

  pub fn witness(&self) -> &Stage2AirPcsFriWitnessV1 {
    &self.witness
  }

  pub fn circuit_digest(&self) -> &[u8; 32] {
    &self.circuit_digest
  }

  pub fn proof_bundle_bytes(&self) -> &[u8] {
    &self.proof_bundle_bytes
  }

  pub fn stage2_root_digest(&self) -> &[u8; 32] {
    &self.witness.air.statement_digest
  }
}

#[derive(Serialize, Deserialize)]
struct FriFoldProofBundle {
  commitment: Commitment,
  proof: R1csProofCircuitMerged,
}

pub fn prove_fri_fold_conformance(
  query: &FriFoldQueryV1,
) -> Result<FriFoldConformanceArtifactV1> {
  validate_query(query)?;
  let folded_result = native_fold(query);
  let commitment_root = native_root(query);
  let relation = FriFoldRelation::build(query.log_height)?;
  let inputs = relation_inputs(query, folded_result);
  let expected_public = relation_public(query, folded_result, &commitment_root);
  let proof_bundle_bytes = prove_fri_circuit(
    &relation.shape,
    relation.table_slots(),
    None,
    None,
    None,
    NU,
    &inputs,
    &expected_public,
    FRI_FOLD_CONFORMANCE_TRANSCRIPT_DOMAIN,
  )?;
  Ok(FriFoldConformanceArtifactV1 {
    query: query.clone(),
    folded_result,
    circuit_digest: relation.shape.circuit.digest(),
    commitment_root,
    proof_bundle_bytes,
  })
}

pub fn verify_fri_fold_conformance(
  artifact: &FriFoldConformanceArtifactV1,
) -> Result<()> {
  validate_query(&artifact.query)?;
  if artifact.folded_result != native_fold(&artifact.query) {
    bail!("Flock FRI-fold artifact carries the wrong folded result");
  }
  if artifact.commitment_root != native_root(&artifact.query) {
    bail!("Flock FRI-fold artifact carries the wrong commitment root");
  }
  let relation = FriFoldRelation::build(artifact.query.log_height)?;
  if artifact.circuit_digest != relation.shape.circuit.digest() {
    bail!("Flock FRI-fold conformance circuit digest mismatch");
  }
  let public = relation_public(
    &artifact.query,
    artifact.folded_result,
    &artifact.commitment_root,
  );
  verify_fri_circuit(
    &relation.shape,
    relation.table_slots(),
    None,
    None,
    None,
    NU,
    &public,
    &artifact.proof_bundle_bytes,
    FRI_FOLD_CONFORMANCE_TRANSCRIPT_DOMAIN,
  )
}

pub fn prove_fri_commit_phase_conformance(
  query: &FriCommitPhaseQueryV1,
) -> Result<FriCommitPhaseConformanceArtifactV1> {
  let computation = compute_commit_phase(query)?;
  ensure_final_polynomial(query, &computation)?;
  let relation = FriCommitPhaseRelation::build(query)?;
  let inputs = commit_phase_relation_inputs(query, &computation);
  let public = commit_phase_relation_public(query, &computation);
  let proof_bundle_bytes = prove_fri_circuit(
    &relation.shape,
    relation.slots,
    None,
    None,
    None,
    relation.nu,
    &inputs,
    &public,
    FRI_QUERY_CONFORMANCE_TRANSCRIPT_DOMAIN,
  )?;
  Ok(FriCommitPhaseConformanceArtifactV1 {
    query: query.clone(),
    circuit_digest: relation.shape.circuit.digest(),
    commitment_roots: computation.roots,
    proof_bundle_bytes,
  })
}

pub fn verify_fri_commit_phase_conformance(
  artifact: &FriCommitPhaseConformanceArtifactV1,
) -> Result<()> {
  let computation = compute_commit_phase(&artifact.query)?;
  ensure_final_polynomial(&artifact.query, &computation)?;
  if artifact.commitment_roots != computation.roots {
    bail!("Flock FRI commit-phase artifact carries the wrong round roots");
  }
  let relation = FriCommitPhaseRelation::build(&artifact.query)?;
  if artifact.circuit_digest != relation.shape.circuit.digest() {
    bail!("Flock FRI commit-phase circuit digest mismatch");
  }
  let public = commit_phase_relation_public(&artifact.query, &computation);
  verify_fri_circuit(
    &relation.shape,
    relation.slots,
    None,
    None,
    None,
    relation.nu,
    &public,
    &artifact.proof_bundle_bytes,
    FRI_QUERY_CONFORMANCE_TRANSCRIPT_DOMAIN,
  )
}

pub fn prove_pcs_reduction_conformance(
  opening: &PcsReducedOpeningV1,
) -> Result<PcsReductionConformanceArtifactV1> {
  let computation = compute_pcs_reduction(opening)?;
  let relation = PcsReductionRelation::build(opening)?;
  let inputs = pcs_reduction_relation_inputs(opening, &computation);
  let public = pcs_reduction_relation_public(opening, &computation);
  let proof_bundle_bytes = prove_fri_circuit(
    &relation.shape,
    relation.slots,
    None,
    None,
    None,
    relation.nu,
    &inputs,
    &public,
    PCS_REDUCTION_CONFORMANCE_TRANSCRIPT_DOMAIN,
  )?;
  Ok(PcsReductionConformanceArtifactV1 {
    opening: opening.clone(),
    reduced_accumulator: computation.accumulator,
    next_alpha_power: computation.alpha_power,
    circuit_digest: relation.shape.circuit.digest(),
    commitment_root: computation.root,
    proof_bundle_bytes,
  })
}

pub fn verify_pcs_reduction_conformance(
  artifact: &PcsReductionConformanceArtifactV1,
) -> Result<()> {
  let computation = compute_pcs_reduction(&artifact.opening)?;
  if artifact.reduced_accumulator != computation.accumulator
    || artifact.next_alpha_power != computation.alpha_power
    || artifact.commitment_root != computation.root
  {
    bail!("Flock PCS-reduction artifact carries the wrong native outputs");
  }
  let relation = PcsReductionRelation::build(&artifact.opening)?;
  if artifact.circuit_digest != relation.shape.circuit.digest() {
    bail!("Flock PCS-reduction circuit digest mismatch");
  }
  let public = pcs_reduction_relation_public(&artifact.opening, &computation);
  verify_fri_circuit(
    &relation.shape,
    relation.slots,
    None,
    None,
    None,
    relation.nu,
    &public,
    &artifact.proof_bundle_bytes,
    PCS_REDUCTION_CONFORMANCE_TRANSCRIPT_DOMAIN,
  )
}

pub fn prove_transcript_bound_pcs_reduction_conformance(
  replay: &Stage2TranscriptReplayV1,
  opening: &PcsReducedOpeningV1,
) -> Result<TranscriptBoundPcsReductionArtifactV1> {
  let challenges = replay.challenges()?;
  ensure_transcript_binds_opening(challenges, opening)?;
  let computation = compute_pcs_reduction(opening)?;
  let relation = TranscriptBoundPcsReductionRelation::build(
    replay,
    opening,
    &computation,
    challenges,
  )?;
  let proof_bundle_bytes = prove_fri_circuit(
    &relation.shape,
    relation.slots,
    None,
    None,
    None,
    relation.nu,
    &relation.inputs,
    &relation.public,
    TRANSCRIPT_BOUND_PCS_CONFORMANCE_TRANSCRIPT_DOMAIN,
  )?;
  Ok(TranscriptBoundPcsReductionArtifactV1 {
    replay: replay.clone(),
    opening: opening.clone(),
    reduced_accumulator: computation.accumulator,
    next_alpha_power: computation.alpha_power,
    circuit_digest: relation.shape.circuit.digest(),
    commitment_root: computation.root,
    proof_bundle_bytes,
  })
}

pub fn verify_transcript_bound_pcs_reduction_conformance(
  artifact: &TranscriptBoundPcsReductionArtifactV1,
) -> Result<()> {
  let challenges = artifact.replay.challenges()?;
  ensure_transcript_binds_opening(challenges, &artifact.opening)?;
  let computation = compute_pcs_reduction(&artifact.opening)?;
  if artifact.reduced_accumulator != computation.accumulator
    || artifact.next_alpha_power != computation.alpha_power
    || artifact.commitment_root != computation.root
  {
    bail!("transcript-bound PCS artifact carries the wrong native outputs");
  }
  let relation = TranscriptBoundPcsReductionRelation::build(
    &artifact.replay,
    &artifact.opening,
    &computation,
    challenges,
  )?;
  if artifact.circuit_digest != relation.shape.circuit.digest() {
    bail!("transcript-bound PCS circuit digest mismatch");
  }
  verify_fri_circuit(
    &relation.shape,
    relation.slots,
    None,
    None,
    None,
    relation.nu,
    &relation.public,
    &artifact.proof_bundle_bytes,
    TRANSCRIPT_BOUND_PCS_CONFORMANCE_TRANSCRIPT_DOMAIN,
  )
}

pub fn prove_transcript_bound_fri_commit_phase_conformance(
  prefix: &Stage2TranscriptReplayV1,
  fri_transcript: &Stage2FriTranscriptReplayV1,
  query_number: usize,
  query: &FriCommitPhaseQueryV1,
) -> Result<TranscriptBoundFriCommitPhaseArtifactV1> {
  let challenges = fri_transcript.challenges(prefix)?;
  ensure_transcript_binds_fri_query(
    fri_transcript,
    &challenges,
    query_number,
    query,
  )?;
  let computation = compute_commit_phase(query)?;
  ensure_final_polynomial(query, &computation)?;
  let relation = TranscriptBoundFriCommitPhaseRelation::build(
    prefix,
    fri_transcript,
    &challenges,
    query_number,
    query,
    &computation,
  )?;
  let proof_bundle_bytes = prove_fri_circuit(
    &relation.shape,
    relation.slots,
    Some(relation.sample_slot),
    Some(relation.split_slot),
    relation.window_slot,
    relation.nu,
    &relation.inputs,
    &relation.public,
    TRANSCRIPT_BOUND_FRI_CONFORMANCE_TRANSCRIPT_DOMAIN,
  )?;
  Ok(TranscriptBoundFriCommitPhaseArtifactV1 {
    prefix: prefix.clone(),
    fri_transcript: fri_transcript.clone(),
    query_number,
    query: query.clone(),
    circuit_digest: relation.shape.circuit.digest(),
    commitment_roots: computation.roots,
    proof_bundle_bytes,
  })
}

pub fn verify_transcript_bound_fri_commit_phase_conformance(
  artifact: &TranscriptBoundFriCommitPhaseArtifactV1,
) -> Result<()> {
  let challenges = artifact.fri_transcript.challenges(&artifact.prefix)?;
  ensure_transcript_binds_fri_query(
    &artifact.fri_transcript,
    &challenges,
    artifact.query_number,
    &artifact.query,
  )?;
  let computation = compute_commit_phase(&artifact.query)?;
  ensure_final_polynomial(&artifact.query, &computation)?;
  if artifact.commitment_roots != computation.roots {
    bail!("transcript-bound FRI artifact carries the wrong native roots");
  }
  let relation = TranscriptBoundFriCommitPhaseRelation::build(
    &artifact.prefix,
    &artifact.fri_transcript,
    &challenges,
    artifact.query_number,
    &artifact.query,
    &computation,
  )?;
  if artifact.circuit_digest != relation.shape.circuit.digest() {
    bail!("transcript-bound FRI circuit digest mismatch");
  }
  verify_fri_circuit(
    &relation.shape,
    relation.slots,
    Some(relation.sample_slot),
    Some(relation.split_slot),
    relation.window_slot,
    relation.nu,
    &relation.public,
    &artifact.proof_bundle_bytes,
    TRANSCRIPT_BOUND_FRI_CONFORMANCE_TRANSCRIPT_DOMAIN,
  )
}

pub fn prove_transcript_bound_fri_queries_conformance(
  prefix: &Stage2TranscriptReplayV1,
  fri_transcript: &Stage2FriTranscriptReplayV1,
  queries: &[FriCommitPhaseQueryV1],
) -> Result<TranscriptBoundFriQueriesArtifactV1> {
  let challenges = fri_transcript.challenges(prefix)?;
  let computations = validate_all_transcript_bound_fri_queries(
    fri_transcript,
    &challenges,
    queries,
  )?;
  let relation = TranscriptBoundFriCommitPhaseRelation::build_all(
    prefix,
    fri_transcript,
    &challenges,
    queries,
    &computations,
  )?;
  let proof_bundle_bytes = prove_fri_circuit(
    &relation.shape,
    relation.slots,
    Some(relation.sample_slot),
    Some(relation.split_slot),
    relation.window_slot,
    relation.nu,
    &relation.inputs,
    &relation.public,
    TRANSCRIPT_BOUND_FRI_QUERIES_CONFORMANCE_TRANSCRIPT_DOMAIN,
  )?;
  Ok(TranscriptBoundFriQueriesArtifactV1 {
    prefix: prefix.clone(),
    fri_transcript: fri_transcript.clone(),
    queries: queries.to_vec(),
    circuit_digest: relation.shape.circuit.digest(),
    proof_bundle_bytes,
  })
}

pub fn verify_transcript_bound_fri_queries_conformance(
  artifact: &TranscriptBoundFriQueriesArtifactV1,
) -> Result<()> {
  let challenges = artifact.fri_transcript.challenges(&artifact.prefix)?;
  let computations = validate_all_transcript_bound_fri_queries(
    &artifact.fri_transcript,
    &challenges,
    &artifact.queries,
  )?;
  let relation = TranscriptBoundFriCommitPhaseRelation::build_all(
    &artifact.prefix,
    &artifact.fri_transcript,
    &challenges,
    &artifact.queries,
    &computations,
  )?;
  if artifact.circuit_digest != relation.shape.circuit.digest() {
    bail!("all-query transcript-bound FRI circuit digest mismatch");
  }
  verify_fri_circuit(
    &relation.shape,
    relation.slots,
    Some(relation.sample_slot),
    Some(relation.split_slot),
    relation.window_slot,
    relation.nu,
    &relation.public,
    &artifact.proof_bundle_bytes,
    TRANSCRIPT_BOUND_FRI_QUERIES_CONFORMANCE_TRANSCRIPT_DOMAIN,
  )
}

pub fn prove_transcript_bound_pcs_fri_queries_conformance(
  prefix: &Stage2TranscriptReplayV1,
  fri_transcript: &Stage2FriTranscriptReplayV1,
  pcs_instance: &Stage2PcsInstanceV1,
  queries: &[TranscriptBoundPcsFriQueryV1],
) -> Result<TranscriptBoundPcsFriQueriesArtifactV1> {
  let prefix_challenges = prefix.challenges()?;
  let fri_challenges = fri_transcript.challenges(prefix)?;
  let (fri_computations, pcs_computations) =
    validate_all_transcript_bound_pcs_fri_queries(
      prefix,
      fri_transcript,
      &fri_challenges,
      prefix_challenges,
      pcs_instance,
      queries,
    )?;
  let relation = TranscriptBoundFriCommitPhaseRelation::build_all_with_pcs(
    prefix,
    fri_transcript,
    &fri_challenges,
    pcs_instance,
    queries,
    &fri_computations,
    &pcs_computations,
  )?;
  let proof_bundle_bytes = prove_fri_circuit(
    &relation.shape,
    relation.slots,
    Some(relation.sample_slot),
    Some(relation.split_slot),
    relation.window_slot,
    relation.nu,
    &relation.inputs,
    &relation.public,
    TRANSCRIPT_BOUND_PCS_FRI_QUERIES_CONFORMANCE_TRANSCRIPT_DOMAIN,
  )?;
  Ok(TranscriptBoundPcsFriQueriesArtifactV1 {
    prefix: prefix.clone(),
    fri_transcript: fri_transcript.clone(),
    pcs_instance: pcs_instance.clone(),
    queries: queries.to_vec(),
    circuit_digest: relation.shape.circuit.digest(),
    proof_bundle_bytes,
  })
}

pub fn verify_transcript_bound_pcs_fri_queries_conformance(
  artifact: &TranscriptBoundPcsFriQueriesArtifactV1,
) -> Result<()> {
  let prefix_challenges = artifact.prefix.challenges()?;
  let fri_challenges = artifact.fri_transcript.challenges(&artifact.prefix)?;
  let (fri_computations, pcs_computations) =
    validate_all_transcript_bound_pcs_fri_queries(
      &artifact.prefix,
      &artifact.fri_transcript,
      &fri_challenges,
      prefix_challenges,
      &artifact.pcs_instance,
      &artifact.queries,
    )?;
  let relation = TranscriptBoundFriCommitPhaseRelation::build_all_with_pcs(
    &artifact.prefix,
    &artifact.fri_transcript,
    &fri_challenges,
    &artifact.pcs_instance,
    &artifact.queries,
    &fri_computations,
    &pcs_computations,
  )?;
  if artifact.circuit_digest != relation.shape.circuit.digest() {
    bail!("transcript-bound PCS/FRI all-query circuit digest mismatch");
  }
  verify_fri_circuit(
    &relation.shape,
    relation.slots,
    Some(relation.sample_slot),
    Some(relation.split_slot),
    relation.window_slot,
    relation.nu,
    &relation.public,
    &artifact.proof_bundle_bytes,
    TRANSCRIPT_BOUND_PCS_FRI_QUERIES_CONFORMANCE_TRANSCRIPT_DOMAIN,
  )
}

pub fn prove_stage2_air_pcs_fri_conformance(
  witness: &Stage2AirPcsFriWitnessV1,
) -> Result<Stage2AirPcsFriArtifactV1> {
  prove_stage2_air_pcs_fri_with_domain(
    witness,
    STAGE2_AIR_PCS_FRI_CONFORMANCE_TRANSCRIPT_DOMAIN,
  )
}

pub(crate) fn prove_stage2_air_pcs_fri_production(
  witness: &Stage2AirPcsFriWitnessV1,
) -> Result<Stage2AirPcsFriArtifactV1> {
  prove_stage2_air_pcs_fri_with_domain(witness, crate::STAGE3_TRANSCRIPT_DOMAIN)
}

fn prove_stage2_air_pcs_fri_with_domain(
  witness: &Stage2AirPcsFriWitnessV1,
  transcript_domain: &[u8],
) -> Result<Stage2AirPcsFriArtifactV1> {
  let relation = build_stage2_air_pcs_fri_relation(witness)?;
  let proof_bundle_bytes = prove_fri_circuit(
    &relation.shape,
    relation.slots,
    Some(relation.sample_slot),
    Some(relation.split_slot),
    relation.window_slot,
    relation.nu,
    &relation.inputs,
    &relation.public,
    transcript_domain,
  )?;
  Stage2AirPcsFriArtifactV1::from_parts(
    witness.clone(),
    relation.shape.circuit.digest(),
    proof_bundle_bytes,
  )
}

fn build_stage2_air_pcs_fri_relation(
  witness: &Stage2AirPcsFriWitnessV1,
) -> Result<TranscriptBoundFriCommitPhaseRelation> {
  let pcs_fri = &witness.pcs_fri;
  let prefix_challenges = pcs_fri.prefix.challenges()?;
  let fri_challenges = pcs_fri.fri_transcript.challenges(&pcs_fri.prefix)?;
  let (fri_computations, pcs_computations) =
    validate_all_transcript_bound_pcs_fri_queries(
      &pcs_fri.prefix,
      &pcs_fri.fri_transcript,
      &fri_challenges,
      prefix_challenges,
      &pcs_fri.pcs_instance,
      &pcs_fri.queries,
    )?;
  let relation =
    TranscriptBoundFriCommitPhaseRelation::build_all_with_pcs_and_air(
      &pcs_fri.prefix,
      &pcs_fri.fri_transcript,
      &fri_challenges,
      &pcs_fri.pcs_instance,
      &witness.air,
      &pcs_fri.queries,
      &fri_computations,
      &pcs_computations,
    )?;
  Ok(relation)
}

pub(crate) fn stage2_air_pcs_fri_circuit_digest(
  witness: &Stage2AirPcsFriWitnessV1,
) -> Result<[u8; 32]> {
  Ok(build_stage2_air_pcs_fri_relation(witness)?.shape.circuit.digest())
}

pub(crate) fn preflight_stage2_air_pcs_fri(
  stage2_witness: &Stage2AirPcsFriWitnessV1,
) -> Result<Stage3RelationCensusV1> {
  let relation = build_stage2_air_pcs_fri_relation(stage2_witness)?;
  let evaluated = relation.shape.run(&relation.inputs, &[]);
  if evaluated.public != relation.public {
    bail!("Flock Stage 3 preflight disagrees with native verifier semantics");
  }

  let count = |value: usize, label: &str| {
    u64::try_from(value)
      .map_err(|error| anyhow::anyhow!("{label} exceeds u64: {error}"))
  };
  let nu = count(relation.nu, "Flock table logarithm")?;
  let shift = u32::try_from(nu).map_err(|error| {
    anyhow::anyhow!("Flock table logarithm exceeds u32: {error}")
  })?;
  let table_capacity = 1u64.checked_shl(shift).ok_or_else(|| {
    anyhow::anyhow!("Flock table logarithm {nu} exceeds the preflight report")
  })?;
  let field_sample_rows = relation
    .slots
    .field_sample
    .map_or(0, |slot| evaluated.rows::<GoldilocksSampleGate>(slot).len());
  let byte_window_rows = relation
    .window_slot
    .map_or(0, |slot| evaluated.rows::<ByteWindowGate>(slot).len());

  Ok(Stage3RelationCensusV1 {
    circuit_digest: relation.shape.circuit.digest(),
    nu,
    table_capacity,
    relation_inputs: count(relation.inputs.len(), "relation input count")?,
    public_values: count(relation.public.len(), "public-value count")?,
    blake3_rows: count(
      evaluated.rows::<Blake3Gate>(relation.slots.blake3).len(),
      "BLAKE3 row count",
    )?,
    digest_order_rows: count(
      evaluated.rows::<DigestOrderGate>(relation.slots.order).len(),
      "digest-order row count",
    )?,
    goldilocks_add_rows: count(
      evaluated.rows::<GoldilocksAddPairGate>(relation.slots.add).len(),
      "Goldilocks-add row count",
    )?,
    goldilocks_mul_rows: count(
      evaluated.rows::<GoldilocksMulPairGate>(relation.slots.mul).len(),
      "Goldilocks-mul row count",
    )?,
    lane_repack_rows: count(
      evaluated.rows::<GoldilocksLaneRepackGate>(relation.slots.repack).len(),
      "lane-repack row count",
    )?,
    canonical_goldilocks_rows: count(
      evaluated
        .rows::<CanonicalGoldilocksPairGate>(relation.slots.canonical)
        .len(),
      "canonical-Goldilocks row count",
    )?,
    equality_rows: count(
      evaluated.rows::<F128EqualityGate>(relation.slots.equality).len(),
      "equality row count",
    )?,
    hash_sample_rows: count(
      evaluated.rows::<HashSampleGate>(relation.sample_slot).len(),
      "hash-sample row count",
    )?,
    field_sample_rows: count(field_sample_rows, "field-sample row count")?,
    u64_split_rows: count(
      evaluated.rows::<U64SplitGate>(relation.split_slot).len(),
      "u64-split row count",
    )?,
    byte_window_rows: count(byte_window_rows, "byte-window row count")?,
  })
}

pub fn verify_stage2_air_pcs_fri_conformance(
  artifact: &Stage2AirPcsFriArtifactV1,
) -> Result<()> {
  verify_stage2_air_pcs_fri_with_domain(
    artifact,
    STAGE2_AIR_PCS_FRI_CONFORMANCE_TRANSCRIPT_DOMAIN,
  )
}

pub(crate) fn verify_stage2_air_pcs_fri_production(
  artifact: &Stage2AirPcsFriArtifactV1,
) -> Result<()> {
  verify_stage2_air_pcs_fri_with_domain(
    artifact,
    crate::STAGE3_TRANSCRIPT_DOMAIN,
  )
}

fn verify_stage2_air_pcs_fri_with_domain(
  artifact: &Stage2AirPcsFriArtifactV1,
  transcript_domain: &[u8],
) -> Result<()> {
  let witness = &artifact.witness;
  let relation = build_stage2_air_pcs_fri_relation(witness)?;
  if artifact.circuit_digest != relation.shape.circuit.digest() {
    bail!("Stage 2 AIR/PCS/FRI circuit digest mismatch");
  }
  verify_fri_circuit(
    &relation.shape,
    relation.slots,
    Some(relation.sample_slot),
    Some(relation.split_slot),
    relation.window_slot,
    relation.nu,
    &relation.public,
    &artifact.proof_bundle_bytes,
    transcript_domain,
  )
}

pub fn verify_stage2_air_pcs_fri_conformance_for(
  artifact: &Stage2AirPcsFriArtifactV1,
  expected: &Stage2RootStatementV1,
) -> Result<()> {
  let expected_bytes = expected.to_bytes();
  if artifact.witness.air.statement_prefix != expected_bytes[..80] {
    bail!("Stage 2 AIR/PCS/FRI proof uses a different vk or FRI prefix");
  }
  if artifact.witness.air.statement_digest != expected.digest() {
    bail!("Stage 2 AIR/PCS/FRI proof targets a different Stage 2 root");
  }
  verify_stage2_air_pcs_fri_conformance(artifact)
}

fn validate_all_transcript_bound_pcs_fri_queries(
  prefix: &Stage2TranscriptReplayV1,
  fri_transcript: &Stage2FriTranscriptReplayV1,
  fri_challenges: &Stage2FriTranscriptChallengesV1,
  prefix_challenges: crate::Stage2TranscriptChallengesV1,
  pcs_instance: &Stage2PcsInstanceV1,
  queries: &[TranscriptBoundPcsFriQueryV1],
) -> Result<(Vec<FriCommitPhaseComputation>, Vec<Stage2PcsQueryComputation>)> {
  validate_stage2_pcs_instance(prefix, pcs_instance)?;
  if queries.len() != fri_transcript.num_queries
    || queries.len() != fri_challenges.query_indices.len()
  {
    bail!(
      "all-query PCS/FRI relation has {} queries; transcript requires {}",
      queries.len(),
      fri_transcript.num_queries
    );
  }
  let mut fri_computations = Vec::with_capacity(queries.len());
  let mut pcs_computations = Vec::with_capacity(queries.len());
  for (query_number, query) in queries.iter().enumerate() {
    ensure_transcript_binds_fri_query(
      fri_transcript,
      fri_challenges,
      query_number,
      &query.fri,
    )?;
    let pcs_computation =
      compute_stage2_pcs_query(prefix, pcs_instance, query, prefix_challenges)?;
    ensure_stage2_pcs_feeds_fri(pcs_instance, query, &pcs_computation)?;
    let fri_computation = compute_commit_phase(&query.fri)?;
    ensure_final_polynomial(&query.fri, &fri_computation)?;
    fri_computations.push(fri_computation);
    pcs_computations.push(pcs_computation);
  }
  Ok((fri_computations, pcs_computations))
}

fn validate_all_transcript_bound_fri_queries(
  fri_transcript: &Stage2FriTranscriptReplayV1,
  challenges: &Stage2FriTranscriptChallengesV1,
  queries: &[FriCommitPhaseQueryV1],
) -> Result<Vec<FriCommitPhaseComputation>> {
  if queries.len() != fri_transcript.num_queries
    || queries.len() != challenges.query_indices.len()
  {
    bail!(
      "all-query FRI relation has {} queries; transcript requires {}",
      queries.len(),
      fri_transcript.num_queries
    );
  }
  queries
    .iter()
    .enumerate()
    .map(|(query_number, query)| {
      ensure_transcript_binds_fri_query(
        fri_transcript,
        challenges,
        query_number,
        query,
      )?;
      let computation = compute_commit_phase(query)?;
      ensure_final_polynomial(query, &computation)?;
      Ok(computation)
    })
    .collect()
}

fn ensure_transcript_binds_fri_query(
  fri_transcript: &Stage2FriTranscriptReplayV1,
  challenges: &Stage2FriTranscriptChallengesV1,
  query_number: usize,
  query: &FriCommitPhaseQueryV1,
) -> Result<()> {
  if query_number >= challenges.query_indices.len() {
    bail!("FRI query number {query_number} is out of range");
  }
  if fri_transcript.log_arities.iter().any(|&arity| arity != 1) {
    bail!("binary FRI composition requires every log arity to equal one");
  }
  if query.rounds.len() != challenges.betas.len()
    || query.rounds.len() != fri_transcript.commit_phase_commitments.len()
  {
    bail!("transcript and FRI query round counts disagree");
  }
  for (round, (query_round, &beta)) in
    query.rounds.iter().zip(&challenges.betas).enumerate()
  {
    if query_round.beta != beta {
      bail!("FRI round {round} beta does not equal the transcript challenge");
    }
  }
  let query_index = challenges.query_indices[query_number];
  if u64::from(query.query_index) != query_index {
    bail!("FRI query index does not equal the transcript-derived index");
  }
  if usize::from(fri_transcript.query_index_bits)
    != usize::from(query.initial_log_height) + 1
  {
    bail!("FRI query height does not equal the transcript sampling width");
  }
  if fri_transcript.final_polynomial.as_slice() != [query.final_polynomial] {
    bail!("FRI final polynomial does not equal the transcript observation");
  }
  if fri_transcript.commit_phase_commitments.iter().any(|cap| cap.len() != 1) {
    bail!("current transcript-bound FRI composition requires cap height zero");
  }
  let roots = query.commitment_roots()?;
  for (round, (cap, root)) in
    fri_transcript.commit_phase_commitments.iter().zip(&roots).enumerate()
  {
    if cap[0] != *root {
      bail!(
        "FRI round {round} opening does not authenticate to its transcript cap"
      );
    }
  }
  Ok(())
}

fn ensure_transcript_binds_opening(
  challenges: crate::Stage2TranscriptChallengesV1,
  opening: &PcsReducedOpeningV1,
) -> Result<()> {
  if opening.zeta != challenges.zeta {
    bail!("PCS zeta does not equal the constrained Stage 2 transcript zeta");
  }
  if opening.alpha != challenges.pcs_alpha {
    bail!(
      "PCS batching challenge does not equal the constrained Stage 2 transcript challenge"
    );
  }
  Ok(())
}

struct FriFoldRelation {
  shape: CircuitShape,
  blake3_slot: SlotId,
  order_slot: SlotId,
  add_slot: SlotId,
  mul_slot: SlotId,
  repack_slot: SlotId,
  canonical_slot: SlotId,
  equality_slot: SlotId,
}

#[derive(Clone, Copy)]
struct FriTableSlots {
  blake3: SlotId,
  order: SlotId,
  add: SlotId,
  mul: SlotId,
  repack: SlotId,
  canonical: SlotId,
  equality: SlotId,
  field_sample: Option<SlotId>,
}

impl FriFoldRelation {
  fn build(log_height: u8) -> Result<Self> {
    validate_log_height(log_height)?;
    let mut builder = ShapeBuilder::new(NU);
    let arithmetic = GoldilocksCircuitSlots::declare(&mut builder, NU);
    let blake3_slot = builder.slot(Blake3Gate { nu: NU });
    let order_slot = builder.slot(DigestOrderGate { nu: NU });
    let equality_slot = builder.slot(F128EqualityGate { nu: NU });
    let data_zero = builder.fixed_public_input(F128::ZERO);
    let equality_zero = builder.fixed_public_input(F128::ZERO);

    let packed_iv = pack8(&IV);
    let iv = [
      builder.fixed_public_input(packed_iv[0]),
      builder.fixed_public_input(packed_iv[1]),
    ];
    let leaf_params = builder.fixed_public_input(pack_params(
      0,
      32,
      CHUNK_START | CHUNK_END | ROOT,
    ));
    let node_params = builder.fixed_public_input(pack_params(
      0,
      64,
      CHUNK_START | CHUNK_END | ROOT,
    ));
    let one = builder.fixed_public_input(F128::new(1, 0));
    let factor_wires: Vec<_> = twiddle_factors(log_height)
      .into_iter()
      .map(|factor| builder.fixed_public_input(F128::new(factor, 0)))
      .collect();

    let folded = builder.public_input();
    let sibling = builder.public_input();
    let beta = builder.public_input();
    let index_bits: Vec<_> =
      (0..=log_height).map(|_| builder.public_input()).collect();
    let path: Vec<_> = (0..log_height)
      .map(|_| [builder.public_input(), builder.public_input()])
      .collect();
    let folded_result = builder.public_input();

    let root = constrain_authenticated_fold(
      &mut builder,
      &arithmetic,
      blake3_slot,
      order_slot,
      equality_slot,
      data_zero,
      equality_zero,
      iv,
      leaf_params,
      node_params,
      one,
      &factor_wires,
      folded,
      sibling,
      beta,
      &index_bits,
      &path,
      folded_result,
    );

    builder.publish(root[0]);
    builder.publish(root[1]);
    let shape = builder.finish().map_err(|error| {
      anyhow::anyhow!("build Flock authenticated FRI-fold circuit: {error:?}")
    })?;
    Ok(Self {
      shape,
      blake3_slot,
      order_slot,
      add_slot: arithmetic.add,
      mul_slot: arithmetic.mul,
      repack_slot: arithmetic.repack,
      canonical_slot: arithmetic.canonical,
      equality_slot,
    })
  }

  fn table_slots(&self) -> FriTableSlots {
    FriTableSlots {
      blake3: self.blake3_slot,
      order: self.order_slot,
      add: self.add_slot,
      mul: self.mul_slot,
      repack: self.repack_slot,
      canonical: self.canonical_slot,
      equality: self.equality_slot,
      field_sample: None,
    }
  }
}

struct FriCommitPhaseRelation {
  shape: CircuitShape,
  slots: FriTableSlots,
  nu: usize,
}

struct FriCommitPhaseRoundWires {
  sibling: Wire,
  beta: Wire,
  reduced_opening: Option<Wire>,
  path: Vec<[Wire; 2]>,
  result: Wire,
}

impl FriCommitPhaseRelation {
  fn build(query: &FriCommitPhaseQueryV1) -> Result<Self> {
    validate_commit_phase_structure(query)?;
    let nu = commit_phase_nu(query);
    let mut builder = ShapeBuilder::new(nu);
    let arithmetic = GoldilocksCircuitSlots::declare(&mut builder, nu);
    let blake3 = builder.slot(Blake3Gate { nu });
    let order = builder.slot(DigestOrderGate { nu });
    let equality = builder.slot(F128EqualityGate { nu });
    let slots = FriTableSlots {
      blake3,
      order,
      add: arithmetic.add,
      mul: arithmetic.mul,
      repack: arithmetic.repack,
      canonical: arithmetic.canonical,
      equality,
      field_sample: None,
    };
    let data_zero = builder.fixed_public_input(F128::ZERO);
    let equality_zero = builder.fixed_public_input(F128::ZERO);
    let packed_iv = pack8(&IV);
    let iv = [
      builder.fixed_public_input(packed_iv[0]),
      builder.fixed_public_input(packed_iv[1]),
    ];
    let leaf_params = builder.fixed_public_input(pack_params(
      0,
      32,
      CHUNK_START | CHUNK_END | ROOT,
    ));
    let node_params = builder.fixed_public_input(pack_params(
      0,
      64,
      CHUNK_START | CHUNK_END | ROOT,
    ));
    let one = builder.fixed_public_input(F128::new(1, 0));
    let factor_wires: Vec<Vec<Wire>> = (0..query.rounds.len())
      .map(|round| {
        let log_height = query.initial_log_height - round as u8;
        twiddle_factors(log_height)
          .into_iter()
          .map(|factor| builder.fixed_public_input(F128::new(factor, 0)))
          .collect()
      })
      .collect();

    // Declare all free values before publishing computed roots, keeping the
    // public layout equal to `inputs || roots`.
    let initial_folded = builder.public_input();
    let index_bits: Vec<_> =
      (0..=query.initial_log_height).map(|_| builder.public_input()).collect();
    let round_wires: Vec<_> = (0..query.rounds.len())
      .map(|round| {
        let log_height = usize::from(query.initial_log_height) - round;
        FriCommitPhaseRoundWires {
          sibling: builder.public_input(),
          beta: builder.public_input(),
          reduced_opening: query.rounds[round]
            .reduced_opening
            .map(|_| builder.public_input()),
          path: (0..log_height)
            .map(|_| [builder.public_input(), builder.public_input()])
            .collect(),
          result: builder.public_input(),
        }
      })
      .collect();
    let final_polynomial = builder.public_input();

    let mut folded = initial_folded;
    for (round, wires) in round_wires.iter().enumerate() {
      let root = constrain_authenticated_fold(
        &mut builder,
        &arithmetic,
        blake3,
        order,
        equality,
        data_zero,
        equality_zero,
        iv,
        leaf_params,
        node_params,
        one,
        &factor_wires[round],
        folded,
        wires.sibling,
        wires.beta,
        &index_bits[round..],
        &wires.path,
        wires.result,
      );
      builder.publish(root[0]);
      builder.publish(root[1]);
      folded = if let Some(reduced_opening) = wires.reduced_opening {
        let beta_squared =
          arithmetic.ext2_mul(&mut builder, wires.beta, wires.beta);
        let rollin =
          arithmetic.ext2_mul(&mut builder, beta_squared, reduced_opening);
        arithmetic.add(&mut builder, wires.result, rollin)
      } else {
        wires.result
      };
    }
    let final_residual = builder.gate(equality, &[folded, final_polynomial])[0];
    builder.connect(final_residual, equality_zero);

    let shape = builder.finish().map_err(|error| {
      anyhow::anyhow!("build Flock FRI commit-phase circuit: {error:?}")
    })?;
    Ok(Self { shape, slots, nu })
  }
}

struct PcsReductionRelation {
  shape: CircuitShape,
  slots: FriTableSlots,
  nu: usize,
}

impl PcsReductionRelation {
  fn build(opening: &PcsReducedOpeningV1) -> Result<Self> {
    validate_pcs_reduction(opening)?;
    let nu = pcs_reduction_nu(opening);
    let mut builder = ShapeBuilder::new(nu);
    let arithmetic = GoldilocksCircuitSlots::declare(&mut builder, nu);
    let blake3 = builder.slot(Blake3Gate { nu });
    let order = builder.slot(DigestOrderGate { nu });
    let equality = builder.slot(F128EqualityGate { nu });
    let slots = FriTableSlots {
      blake3,
      order,
      add: arithmetic.add,
      mul: arithmetic.mul,
      repack: arithmetic.repack,
      canonical: arithmetic.canonical,
      equality,
      field_sample: None,
    };
    let data_zero = builder.fixed_public_input(F128::ZERO);
    let equality_zero = builder.fixed_public_input(F128::ZERO);
    let packed_iv = pack8(&IV);
    let iv = [
      builder.fixed_public_input(packed_iv[0]),
      builder.fixed_public_input(packed_iv[1]),
    ];
    let leaf_trace = hash_trace(opening.opened_values.len() * 8);
    let leaf_params: Vec<_> = leaf_trace
      .rows
      .iter()
      .map(|&(_cv, _message, counter, block_len, flags)| {
        builder.fixed_public_input(pack_params(counter, block_len, flags))
      })
      .collect();
    let node_params = builder.fixed_public_input(pack_params(
      0,
      64,
      CHUNK_START | CHUNK_END | ROOT,
    ));
    let one = builder.fixed_public_input(F128::new(1, 0));
    let coset_shift = builder.fixed_public_input(F128::new(7, 0));
    let factor_wires: Vec<_> = pcs_x_factors(opening.log_height)
      .into_iter()
      .map(|factor| builder.fixed_public_input(F128::new(factor, 0)))
      .collect();

    let packed_values: Vec<_> =
      opening.opened_values.chunks(2).map(|_| builder.public_input()).collect();
    let opened_at_z: Vec<_> =
      opening.opened_at_z.iter().map(|_| builder.public_input()).collect();
    let zeta = builder.public_input();
    let alpha = builder.public_input();
    let initial_alpha_power = builder.public_input();
    let initial_accumulator = builder.public_input();
    let index_bits: Vec<_> =
      (0..opening.log_height).map(|_| builder.public_input()).collect();
    let path: Vec<_> = (0..opening.log_height)
      .map(|_| [builder.public_input(), builder.public_input()])
      .collect();
    let denominator = builder.public_input();
    let quotients: Vec<_> =
      opening.opened_values.iter().map(|_| builder.public_input()).collect();
    let reduced_accumulator = builder.public_input();
    let next_alpha_power = builder.public_input();

    for value in [zeta, alpha, initial_alpha_power, initial_accumulator] {
      arithmetic.assert_canonical(&mut builder, value);
    }
    for &value in &opened_at_z {
      arithmetic.assert_canonical(&mut builder, value);
    }
    arithmetic.assert_canonical(&mut builder, denominator);
    for &quotient in &quotients {
      arithmetic.assert_canonical(&mut builder, quotient);
    }

    let mut px_values = Vec::with_capacity(opening.opened_values.len());
    for (packed_index, packed) in packed_values.iter().enumerate() {
      arithmetic.assert_canonical(&mut builder, *packed);
      let lanes = builder.gate(arithmetic.repack, &[*packed, data_zero]);
      px_values.push(lanes[3]);
      if 2 * packed_index + 1 < opening.opened_values.len() {
        let high = builder.gate(arithmetic.repack, &[lanes[1], data_zero])[3];
        px_values.push(high);
      } else {
        let high = builder.gate(arithmetic.repack, &[lanes[1], data_zero])[3];
        let padding_residual = builder.gate(equality, &[high, data_zero])[0];
        builder.connect(padding_residual, equality_zero);
      }
    }

    let mut x = coset_shift;
    for (bit, factor) in index_bits.iter().zip(&factor_wires) {
      let selected =
        builder.gate(order, &[*bit, one, data_zero, *factor, data_zero])[0];
      x = arithmetic.ext2_mul(&mut builder, x, selected);
    }
    let denominator_check = arithmetic.add(&mut builder, denominator, x);
    let denominator_residual =
      builder.gate(equality, &[denominator_check, zeta])[0];
    builder.connect(denominator_residual, equality_zero);

    let mut accumulator = initial_accumulator;
    let mut alpha_power = initial_alpha_power;
    for ((px, pz), quotient) in
      px_values.iter().zip(&opened_at_z).zip(&quotients)
    {
      let quotient_product =
        arithmetic.ext2_mul(&mut builder, denominator, *quotient);
      let reconstructed = arithmetic.add(&mut builder, quotient_product, *px);
      let quotient_residual = builder.gate(equality, &[reconstructed, *pz])[0];
      builder.connect(quotient_residual, equality_zero);
      let term = arithmetic.ext2_mul(&mut builder, alpha_power, *quotient);
      accumulator = arithmetic.add(&mut builder, accumulator, term);
      alpha_power = arithmetic.ext2_mul(&mut builder, alpha_power, alpha);
    }
    let accumulator_residual =
      builder.gate(equality, &[accumulator, reduced_accumulator])[0];
    builder.connect(accumulator_residual, equality_zero);
    let alpha_power_residual =
      builder.gate(equality, &[alpha_power, next_alpha_power])[0];
    builder.connect(alpha_power_residual, equality_zero);

    let mut current = constrain_hash(
      &mut builder,
      blake3,
      &leaf_trace,
      &leaf_params,
      iv,
      data_zero,
      &packed_values,
    )?;
    for (level, sibling) in path.iter().enumerate() {
      let ordered = builder.gate(
        order,
        &[index_bits[level], current[0], current[1], sibling[0], sibling[1]],
      );
      let parent = builder.gate(
        blake3,
        &[
          iv[0],
          iv[1],
          ordered[0],
          ordered[1],
          ordered[2],
          ordered[3],
          node_params,
        ],
      );
      current = [parent[0], parent[1]];
    }
    builder.publish(current[0]);
    builder.publish(current[1]);
    let shape = builder.finish().map_err(|error| {
      anyhow::anyhow!("build Flock PCS-reduction circuit: {error:?}")
    })?;
    Ok(Self { shape, slots, nu })
  }
}

struct TranscriptBoundPcsReductionRelation {
  shape: CircuitShape,
  slots: FriTableSlots,
  nu: usize,
  inputs: Vec<F128>,
  public: Vec<F128>,
}

impl TranscriptBoundPcsReductionRelation {
  fn build(
    replay: &Stage2TranscriptReplayV1,
    opening: &PcsReducedOpeningV1,
    computation: &PcsReductionComputation,
    challenges: crate::Stage2TranscriptChallengesV1,
  ) -> Result<Self> {
    validate_pcs_reduction(opening)?;
    ensure_transcript_binds_opening(challenges, opening)?;
    let transcript_capacity = 1usize << transcript_nu(replay)?;
    let pcs_capacity = 1usize << pcs_reduction_nu(opening);
    let nu = usize::try_from(
      transcript_capacity
        .checked_add(pcs_capacity)
        .ok_or_else(|| anyhow::anyhow!("transcript-bound PCS row overflow"))?
        .next_power_of_two()
        .ilog2(),
    )
    .expect("PCS row logarithm fits usize")
    .max(NU);
    let mut builder = ShapeBuilder::new(nu);
    let arithmetic = GoldilocksCircuitSlots::declare(&mut builder, nu);
    let blake3 = builder.slot(Blake3Gate { nu });
    let order = builder.slot(DigestOrderGate { nu });
    let equality = builder.slot(F128EqualityGate { nu });
    let sample_slot = builder.slot(GoldilocksSampleGate { nu });
    let slots = FriTableSlots {
      blake3,
      order,
      add: arithmetic.add,
      mul: arithmetic.mul,
      repack: arithmetic.repack,
      canonical: arithmetic.canonical,
      equality,
      field_sample: Some(sample_slot),
    };

    // `GoldilocksCircuitSlots::declare` creates its fixed canonical zero first.
    let mut inputs = vec![F128::ZERO];
    let transcript = constrain_stage2_transcript(
      &mut builder,
      TranscriptCircuitSlots {
        blake3,
        sample: sample_slot,
        canonical: arithmetic.canonical,
      },
      replay,
      nu,
    )?;
    inputs.extend_from_slice(&transcript.inputs);
    for challenge in transcript.challenges.all() {
      builder.publish(challenge);
    }
    let mut public = inputs.clone();
    public.extend(transcript_challenge_words(challenges));

    let data_zero =
      record_fixed(&mut builder, &mut inputs, &mut public, F128::ZERO);
    let equality_zero =
      record_fixed(&mut builder, &mut inputs, &mut public, F128::ZERO);
    let packed_iv = pack8(&IV);
    let iv = [
      record_fixed(&mut builder, &mut inputs, &mut public, packed_iv[0]),
      record_fixed(&mut builder, &mut inputs, &mut public, packed_iv[1]),
    ];
    let leaf_trace = hash_trace(opening.opened_values.len() * 8);
    let leaf_params: Vec<_> = leaf_trace
      .rows
      .iter()
      .map(|&(_cv, _message, counter, block_len, flags)| {
        record_fixed(
          &mut builder,
          &mut inputs,
          &mut public,
          pack_params(counter, block_len, flags),
        )
      })
      .collect();
    let node_params = record_fixed(
      &mut builder,
      &mut inputs,
      &mut public,
      pack_params(0, 64, CHUNK_START | CHUNK_END | ROOT),
    );
    let one =
      record_fixed(&mut builder, &mut inputs, &mut public, F128::new(1, 0));
    let coset_shift =
      record_fixed(&mut builder, &mut inputs, &mut public, F128::new(7, 0));
    let factor_wires: Vec<_> = pcs_x_factors(opening.log_height)
      .into_iter()
      .map(|factor| {
        record_fixed(
          &mut builder,
          &mut inputs,
          &mut public,
          F128::new(factor, 0),
        )
      })
      .collect();

    let packed_values: Vec<_> = opening
      .opened_values
      .chunks(2)
      .map(|pair| {
        record_public(
          &mut builder,
          &mut inputs,
          &mut public,
          F128::new(pair[0], pair.get(1).copied().unwrap_or(0)),
        )
      })
      .collect();
    let opened_at_z: Vec<_> = opening
      .opened_at_z
      .iter()
      .copied()
      .map(|value| {
        record_public(
          &mut builder,
          &mut inputs,
          &mut public,
          pack_extension(value),
        )
      })
      .collect();
    let initial_alpha_power = record_public(
      &mut builder,
      &mut inputs,
      &mut public,
      pack_extension(opening.initial_alpha_power),
    );
    let initial_accumulator = record_public(
      &mut builder,
      &mut inputs,
      &mut public,
      pack_extension(opening.initial_accumulator),
    );
    let index_bits: Vec<_> = (0..opening.log_height)
      .map(|bit| {
        record_public(
          &mut builder,
          &mut inputs,
          &mut public,
          F128::new(u64::from((opening.query_index >> bit) & 1), 0),
        )
      })
      .collect();
    let path: Vec<_> = opening
      .opening_proof
      .iter()
      .map(|sibling| {
        let digest = pack_digest(sibling);
        [
          record_public(&mut builder, &mut inputs, &mut public, digest[0]),
          record_public(&mut builder, &mut inputs, &mut public, digest[1]),
        ]
      })
      .collect();
    let denominator = record_public(
      &mut builder,
      &mut inputs,
      &mut public,
      pack_extension(computation.denominator),
    );
    let quotients: Vec<_> = computation
      .quotients
      .iter()
      .copied()
      .map(|quotient| {
        record_public(
          &mut builder,
          &mut inputs,
          &mut public,
          pack_extension(quotient),
        )
      })
      .collect();
    let reduced_accumulator = record_public(
      &mut builder,
      &mut inputs,
      &mut public,
      pack_extension(computation.accumulator),
    );
    let next_alpha_power = record_public(
      &mut builder,
      &mut inputs,
      &mut public,
      pack_extension(computation.alpha_power),
    );

    let zeta = transcript.challenges.zeta;
    let alpha = transcript.challenges.pcs_alpha;
    for value in [zeta, alpha, initial_alpha_power, initial_accumulator] {
      arithmetic.assert_canonical(&mut builder, value);
    }
    for &value in &opened_at_z {
      arithmetic.assert_canonical(&mut builder, value);
    }
    arithmetic.assert_canonical(&mut builder, denominator);
    for &quotient in &quotients {
      arithmetic.assert_canonical(&mut builder, quotient);
    }

    let mut px_values = Vec::with_capacity(opening.opened_values.len());
    for (packed_index, packed) in packed_values.iter().enumerate() {
      arithmetic.assert_canonical(&mut builder, *packed);
      let lanes = builder.gate(arithmetic.repack, &[*packed, data_zero]);
      px_values.push(lanes[3]);
      if 2 * packed_index + 1 < opening.opened_values.len() {
        let high = builder.gate(arithmetic.repack, &[lanes[1], data_zero])[3];
        px_values.push(high);
      } else {
        let high = builder.gate(arithmetic.repack, &[lanes[1], data_zero])[3];
        let padding_residual = builder.gate(equality, &[high, data_zero])[0];
        builder.connect(padding_residual, equality_zero);
      }
    }

    let mut x = coset_shift;
    for (bit, factor) in index_bits.iter().zip(&factor_wires) {
      let selected =
        builder.gate(order, &[*bit, one, data_zero, *factor, data_zero])[0];
      x = arithmetic.ext2_mul(&mut builder, x, selected);
    }
    let denominator_check = arithmetic.add(&mut builder, denominator, x);
    let denominator_residual =
      builder.gate(equality, &[denominator_check, zeta])[0];
    builder.connect(denominator_residual, equality_zero);

    let mut accumulator = initial_accumulator;
    let mut alpha_power = initial_alpha_power;
    for ((px, pz), quotient) in
      px_values.iter().zip(&opened_at_z).zip(&quotients)
    {
      let quotient_product =
        arithmetic.ext2_mul(&mut builder, denominator, *quotient);
      let reconstructed = arithmetic.add(&mut builder, quotient_product, *px);
      let quotient_residual = builder.gate(equality, &[reconstructed, *pz])[0];
      builder.connect(quotient_residual, equality_zero);
      let term = arithmetic.ext2_mul(&mut builder, alpha_power, *quotient);
      accumulator = arithmetic.add(&mut builder, accumulator, term);
      alpha_power = arithmetic.ext2_mul(&mut builder, alpha_power, alpha);
    }
    let accumulator_residual =
      builder.gate(equality, &[accumulator, reduced_accumulator])[0];
    builder.connect(accumulator_residual, equality_zero);
    let alpha_power_residual =
      builder.gate(equality, &[alpha_power, next_alpha_power])[0];
    builder.connect(alpha_power_residual, equality_zero);

    let mut current = constrain_hash(
      &mut builder,
      blake3,
      &leaf_trace,
      &leaf_params,
      iv,
      data_zero,
      &packed_values,
    )?;
    for (level, sibling) in path.iter().enumerate() {
      let ordered = builder.gate(
        order,
        &[index_bits[level], current[0], current[1], sibling[0], sibling[1]],
      );
      let parent = builder.gate(
        blake3,
        &[
          iv[0],
          iv[1],
          ordered[0],
          ordered[1],
          ordered[2],
          ordered[3],
          node_params,
        ],
      );
      current = [parent[0], parent[1]];
    }
    builder.publish(current[0]);
    builder.publish(current[1]);
    public.extend_from_slice(&pack_digest(&computation.root));

    let shape = builder.finish().map_err(|error| {
      anyhow::anyhow!("build transcript-bound PCS circuit: {error:?}")
    })?;
    Ok(Self { shape, slots, nu, inputs, public })
  }
}

struct TranscriptBoundFriCommitPhaseRelation {
  shape: CircuitShape,
  slots: FriTableSlots,
  sample_slot: SlotId,
  split_slot: SlotId,
  window_slot: Option<SlotId>,
  nu: usize,
  inputs: Vec<F128>,
  public: Vec<F128>,
}

#[derive(Clone, Copy)]
struct SelectedFriQuery<'a> {
  query_number: usize,
  query: &'a FriCommitPhaseQueryV1,
  computation: &'a FriCommitPhaseComputation,
  pcs_query: Option<&'a Stage2PcsQueryV1>,
  pcs_computation: Option<&'a Stage2PcsQueryComputation>,
}

impl TranscriptBoundFriCommitPhaseRelation {
  #[allow(clippy::too_many_arguments)]
  fn build(
    prefix: &Stage2TranscriptReplayV1,
    fri_transcript: &Stage2FriTranscriptReplayV1,
    challenges: &Stage2FriTranscriptChallengesV1,
    query_number: usize,
    query: &FriCommitPhaseQueryV1,
    computation: &FriCommitPhaseComputation,
  ) -> Result<Self> {
    Self::build_selected(
      prefix,
      fri_transcript,
      challenges,
      &[SelectedFriQuery {
        query_number,
        query,
        computation,
        pcs_query: None,
        pcs_computation: None,
      }],
      None,
      None,
    )
  }

  fn build_all(
    prefix: &Stage2TranscriptReplayV1,
    fri_transcript: &Stage2FriTranscriptReplayV1,
    challenges: &Stage2FriTranscriptChallengesV1,
    queries: &[FriCommitPhaseQueryV1],
    computations: &[FriCommitPhaseComputation],
  ) -> Result<Self> {
    if queries.len() != computations.len() {
      bail!("FRI query/computation vector lengths disagree");
    }
    let selected: Vec<_> = queries
      .iter()
      .zip(computations)
      .enumerate()
      .map(|(query_number, (query, computation))| SelectedFriQuery {
        query_number,
        query,
        computation,
        pcs_query: None,
        pcs_computation: None,
      })
      .collect();
    Self::build_selected(
      prefix,
      fri_transcript,
      challenges,
      &selected,
      None,
      None,
    )
  }

  fn build_all_with_pcs(
    prefix: &Stage2TranscriptReplayV1,
    fri_transcript: &Stage2FriTranscriptReplayV1,
    challenges: &Stage2FriTranscriptChallengesV1,
    pcs_instance: &Stage2PcsInstanceV1,
    queries: &[TranscriptBoundPcsFriQueryV1],
    fri_computations: &[FriCommitPhaseComputation],
    pcs_computations: &[Stage2PcsQueryComputation],
  ) -> Result<Self> {
    if queries.len() != fri_computations.len()
      || queries.len() != pcs_computations.len()
    {
      bail!("PCS/FRI query and computation vector lengths disagree");
    }
    let selected: Vec<_> = queries
      .iter()
      .zip(fri_computations)
      .zip(pcs_computations)
      .enumerate()
      .map(|(query_number, ((query, computation), pcs_computation))| {
        SelectedFriQuery {
          query_number,
          query: &query.fri,
          computation,
          pcs_query: Some(&query.pcs),
          pcs_computation: Some(pcs_computation),
        }
      })
      .collect();
    Self::build_selected(
      prefix,
      fri_transcript,
      challenges,
      &selected,
      Some(pcs_instance),
      None,
    )
  }

  #[allow(clippy::too_many_arguments)]
  fn build_all_with_pcs_and_air(
    prefix: &Stage2TranscriptReplayV1,
    fri_transcript: &Stage2FriTranscriptReplayV1,
    challenges: &Stage2FriTranscriptChallengesV1,
    pcs_instance: &Stage2PcsInstanceV1,
    air: &Stage2AirProgramV1,
    queries: &[TranscriptBoundPcsFriQueryV1],
    fri_computations: &[FriCommitPhaseComputation],
    pcs_computations: &[Stage2PcsQueryComputation],
  ) -> Result<Self> {
    if queries.len() != fri_computations.len()
      || queries.len() != pcs_computations.len()
    {
      bail!("PCS/FRI query and computation vector lengths disagree");
    }
    let selected: Vec<_> = queries
      .iter()
      .zip(fri_computations)
      .zip(pcs_computations)
      .enumerate()
      .map(|(query_number, ((query, computation), pcs_computation))| {
        SelectedFriQuery {
          query_number,
          query: &query.fri,
          computation,
          pcs_query: Some(&query.pcs),
          pcs_computation: Some(pcs_computation),
        }
      })
      .collect();
    Self::build_selected(
      prefix,
      fri_transcript,
      challenges,
      &selected,
      Some(pcs_instance),
      Some(air),
    )
  }

  fn build_selected(
    prefix: &Stage2TranscriptReplayV1,
    fri_transcript: &Stage2FriTranscriptReplayV1,
    challenges: &Stage2FriTranscriptChallengesV1,
    selected: &[SelectedFriQuery<'_>],
    pcs_instance: Option<&Stage2PcsInstanceV1>,
    air: Option<&Stage2AirProgramV1>,
  ) -> Result<Self> {
    if selected.is_empty() {
      bail!("transcript-bound FRI relation has no selected queries");
    }
    for item in selected {
      ensure_transcript_binds_fri_query(
        fri_transcript,
        challenges,
        item.query_number,
        item.query,
      )?;
      ensure_final_polynomial(item.query, item.computation)?;
      if item.pcs_query.is_some() != pcs_instance.is_some()
        || item.pcs_computation.is_some() != pcs_instance.is_some()
      {
        bail!("transcript-bound FRI relation has inconsistent PCS inputs");
      }
    }
    if air.is_some() && pcs_instance.is_none() {
      bail!("AIR evaluation requires the transcript-bound PCS instance");
    }
    let nu = transcript_bound_fri_nu(
      prefix,
      fri_transcript,
      selected,
      pcs_instance,
      air,
    )?;
    let mut builder = ShapeBuilder::new(nu);
    let arithmetic = GoldilocksCircuitSlots::declare(&mut builder, nu);
    let blake3 = builder.slot(Blake3Gate { nu });
    let order = builder.slot(DigestOrderGate { nu });
    let equality = builder.slot(F128EqualityGate { nu });
    let sample_slot = builder.slot(HashSampleGate { nu });
    let field_sample_slot = builder.slot(GoldilocksSampleGate { nu });
    let split_slot = builder.slot(U64SplitGate { nu });
    let window_slot = pcs_instance.map(|_| builder.slot(ByteWindowGate { nu }));
    let slots = FriTableSlots {
      blake3,
      order,
      add: arithmetic.add,
      mul: arithmetic.mul,
      repack: arithmetic.repack,
      canonical: arithmetic.canonical,
      equality,
      field_sample: Some(field_sample_slot),
    };

    // GoldilocksCircuitSlots declares its canonical-zero fixed input first.
    let mut inputs = vec![F128::ZERO];
    let mut public = vec![F128::ZERO];
    let prefix_region = constrain_stage2_transcript(
      &mut builder,
      TranscriptCircuitSlots {
        blake3,
        sample: field_sample_slot,
        canonical: arithmetic.canonical,
      },
      prefix,
      nu,
    )?;
    inputs.extend_from_slice(&prefix_region.inputs);
    public.extend_from_slice(&prefix_region.inputs);
    for challenge in prefix_region.challenges.all() {
      builder.publish(challenge);
    }
    public.extend(transcript_challenge_words(prefix.challenges()?));

    let fri_region = constrain_stage2_fri_transcript(
      &mut builder,
      FriTranscriptCircuitSlots {
        blake3,
        sample: sample_slot,
        field_sample: field_sample_slot,
        canonical: arithmetic.canonical,
        repack: arithmetic.repack,
        split: split_slot,
      },
      fri_transcript,
      prefix_region.state_digest,
      nu,
    )?;
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
        (0..fri_transcript.query_index_bits)
          .map(|bit| F128::new((index >> bit) & 1, 0)),
      );
    }

    let data_zero =
      record_fixed(&mut builder, &mut inputs, &mut public, F128::ZERO);
    let equality_zero =
      record_fixed(&mut builder, &mut inputs, &mut public, F128::ZERO);
    let packed_iv = pack8(&IV);
    let iv = [
      record_fixed(&mut builder, &mut inputs, &mut public, packed_iv[0]),
      record_fixed(&mut builder, &mut inputs, &mut public, packed_iv[1]),
    ];
    let leaf_params = record_fixed(
      &mut builder,
      &mut inputs,
      &mut public,
      pack_params(0, 32, CHUNK_START | CHUNK_END | ROOT),
    );
    let node_params = record_fixed(
      &mut builder,
      &mut inputs,
      &mut public,
      pack_params(0, 64, CHUNK_START | CHUNK_END | ROOT),
    );
    let one =
      record_fixed(&mut builder, &mut inputs, &mut public, F128::new(1, 0));
    let fixed = TranscriptBoundFriFixedWires {
      blake3,
      order,
      equality,
      data_zero,
      equality_zero,
      iv,
      leaf_params,
      node_params,
      one,
    };
    if let Some(air) = air {
      constrain_stage2_air(
        &mut builder,
        &arithmetic,
        blake3,
        equality,
        equality_zero,
        window_slot.expect("AIR byte-window slot declared above"),
        data_zero,
        one,
        iv,
        &mut inputs,
        &mut public,
        &prefix_region,
        prefix,
        pcs_instance.expect("AIR PCS instance checked above"),
        air,
      )?;
    }
    for item in selected {
      let reduced_openings = if let Some(instance) = pcs_instance {
        Some(constrain_stage2_pcs_query(
          &mut builder,
          &arithmetic,
          fixed,
          &mut inputs,
          &mut public,
          &prefix_region,
          &fri_region,
          window_slot.expect("PCS byte-window slot declared above"),
          instance,
          item.query_number,
          item.pcs_query.expect("PCS query presence checked above"),
          item.pcs_computation.expect("PCS computation presence checked above"),
        )?)
      } else {
        None
      };
      constrain_transcript_bound_fri_query(
        &mut builder,
        &arithmetic,
        fixed,
        &mut inputs,
        &mut public,
        &fri_region,
        item.query_number,
        item.query,
        item.computation,
        reduced_openings.as_ref(),
      );
    }

    let shape = builder.finish().map_err(|error| {
      anyhow::anyhow!("build transcript-bound FRI circuit: {error:?}")
    })?;
    Ok(Self {
      shape,
      slots,
      sample_slot,
      split_slot,
      window_slot,
      nu,
      inputs,
      public,
    })
  }
}

#[derive(Clone, Copy)]
struct TranscriptBoundFriFixedWires {
  blake3: SlotId,
  order: SlotId,
  equality: SlotId,
  data_zero: Wire,
  equality_zero: Wire,
  iv: [Wire; 2],
  leaf_params: Wire,
  node_params: Wire,
  one: Wire,
}

#[allow(clippy::too_many_arguments)]
fn constrain_transcript_bound_fri_query(
  builder: &mut ShapeBuilder,
  arithmetic: &GoldilocksCircuitSlots,
  fixed: TranscriptBoundFriFixedWires,
  inputs: &mut Vec<F128>,
  public: &mut Vec<F128>,
  fri_region: &crate::transcript::FriTranscriptConstraintRegion,
  query_number: usize,
  query: &FriCommitPhaseQueryV1,
  computation: &FriCommitPhaseComputation,
  authenticated_reduced_openings: Option<&BTreeMap<u8, Wire>>,
) {
  let factor_wires: Vec<Vec<Wire>> = computation
    .round_queries
    .iter()
    .map(|round| {
      twiddle_factors(round.log_height)
        .into_iter()
        .map(|factor| {
          record_fixed(builder, inputs, public, F128::new(factor, 0))
        })
        .collect()
    })
    .collect();
  let initial_folded = authenticated_reduced_openings.map_or_else(
    || {
      record_public(
        builder,
        inputs,
        public,
        pack_extension(query.initial_folded),
      )
    },
    |openings| openings[&(query.initial_log_height + 1)],
  );
  let round_wires: Vec<_> = query
    .rounds
    .iter()
    .zip(&computation.fold_results)
    .enumerate()
    .map(|(round, (source, &fold_result))| {
      let depth = usize::from(query.initial_log_height) - round;
      FriCommitPhaseRoundWires {
        sibling: record_public(
          builder,
          inputs,
          public,
          pack_extension(source.sibling),
        ),
        // The beta is the transcript wire, not a duplicated query input.
        beta: fri_region.betas[round],
        reduced_opening: if let Some(openings) = authenticated_reduced_openings
        {
          let height = query.initial_log_height
            - u8::try_from(round).expect("bounded FRI round index");
          openings.get(&height).copied()
        } else {
          source.reduced_opening.map(|value| {
            record_public(builder, inputs, public, pack_extension(value))
          })
        },
        path: source
          .opening_proof
          .iter()
          .take(depth)
          .map(|sibling| {
            let digest = pack_digest(sibling);
            [
              record_public(builder, inputs, public, digest[0]),
              record_public(builder, inputs, public, digest[1]),
            ]
          })
          .collect(),
        result: record_public(
          builder,
          inputs,
          public,
          pack_extension(fold_result),
        ),
      }
    })
    .collect();

  let index_bits = &fri_region.query_index_bits[query_number];
  let mut folded = initial_folded;
  for (round, wires) in round_wires.iter().enumerate() {
    let root = constrain_authenticated_fold(
      builder,
      arithmetic,
      fixed.blake3,
      fixed.order,
      fixed.equality,
      fixed.data_zero,
      fixed.equality_zero,
      fixed.iv,
      fixed.leaf_params,
      fixed.node_params,
      fixed.one,
      &factor_wires[round],
      folded,
      wires.sibling,
      wires.beta,
      &index_bits[round..],
      &wires.path,
      wires.result,
    );
    let cap_root = fri_region.commitment_roots[round][0];
    for lane in 0..2 {
      let residual =
        builder.gate(fixed.equality, &[root[lane], cap_root[lane]])[0];
      builder.connect(residual, fixed.equality_zero);
    }
    folded = if let Some(reduced_opening) = wires.reduced_opening {
      let beta_squared = arithmetic.ext2_mul(builder, wires.beta, wires.beta);
      let rollin = arithmetic.ext2_mul(builder, beta_squared, reduced_opening);
      arithmetic.add(builder, wires.result, rollin)
    } else {
      wires.result
    };
  }
  let final_residual =
    builder.gate(fixed.equality, &[folded, fri_region.final_polynomial[0]])[0];
  builder.connect(final_residual, fixed.equality_zero);
}

struct Stage2PcsRowWires {
  lanes: Vec<Wire>,
  base_extensions: Vec<Wire>,
}

#[allow(clippy::too_many_arguments)]
fn constrain_stage2_pcs_query(
  builder: &mut ShapeBuilder,
  arithmetic: &GoldilocksCircuitSlots,
  fixed: TranscriptBoundFriFixedWires,
  inputs: &mut Vec<F128>,
  public: &mut Vec<F128>,
  prefix_region: &crate::transcript::TranscriptConstraintRegion,
  fri_region: &crate::transcript::FriTranscriptConstraintRegion,
  window: SlotId,
  instance: &Stage2PcsInstanceV1,
  query_number: usize,
  query: &Stage2PcsQueryV1,
  computation: &Stage2PcsQueryComputation,
) -> Result<BTreeMap<u8, Wire>> {
  let index_bits = &fri_region.query_index_bits[query_number];
  let alpha = prefix_region.challenges.pcs_alpha;
  let zeta = prefix_region.challenges.zeta;
  arithmetic.assert_canonical(builder, alpha);
  arithmetic.assert_canonical(builder, zeta);

  let mut all_rows = Vec::with_capacity(instance.batches.len());
  for (batch, opening) in instance.batches.iter().zip(&query.batch_openings) {
    let mut batch_rows = Vec::with_capacity(batch.matrices.len());
    for row in &opening.opened_rows {
      let mut lanes = Vec::with_capacity(row.len());
      let mut base_extensions = Vec::with_capacity(row.len());
      for &value in row {
        let lane =
          record_public(builder, inputs, public, F128::new(value, value));
        arithmetic.assert_canonical(builder, lane);
        let extension =
          builder.gate(arithmetic.repack, &[lane, fixed.data_zero])[3];
        lanes.push(lane);
        base_extensions.push(extension);
      }
      batch_rows.push(Stage2PcsRowWires { lanes, base_extensions });
    }
    all_rows.push(batch_rows);
  }

  // Authenticate every multi-height batch. Rows sharing a height are
  // concatenated in matrix order before hashing; shorter-height leaves are
  // injected on the right after the corresponding path compression.
  for (((batch, opening), batch_computation), rows) in instance
    .batches
    .iter()
    .zip(&query.batch_openings)
    .zip(&computation.batches)
    .zip(&all_rows)
  {
    let log_batch_height =
      batch.matrices.iter().map(|matrix| matrix.log_height).max().unwrap();
    let mut leaves = BTreeMap::new();
    for height in 0..=log_batch_height {
      let leaf_lanes: Vec<_> = batch
        .matrices
        .iter()
        .zip(rows)
        .filter(|(matrix, _)| matrix.log_height == height)
        .flat_map(|(_, row)| row.lanes.iter().copied())
        .collect();
      if leaf_lanes.is_empty() {
        continue;
      }
      let message: Vec<_> = leaf_lanes
        .chunks(2)
        .map(|pair| {
          builder.gate(
            arithmetic.repack,
            &[pair[0], pair.get(1).copied().unwrap_or(fixed.data_zero)],
          )[3]
        })
        .collect();
      let trace = hash_trace(leaf_lanes.len() * 8);
      let parameters: Vec<_> = trace
        .rows
        .iter()
        .map(|&(_cv, _message, counter, block_len, flags)| {
          record_fixed(
            builder,
            inputs,
            public,
            pack_params(counter, block_len, flags),
          )
        })
        .collect();
      let leaf = constrain_hash(
        builder,
        fixed.blake3,
        &trace,
        &parameters,
        fixed.iv,
        fixed.data_zero,
        &message,
      )?;
      leaves.insert(height, leaf);
    }

    let mut current = leaves[&log_batch_height];
    let bit_offset = usize::from(instance.log_global_height - log_batch_height);
    for (level, sibling) in opening.opening_proof.iter().enumerate() {
      let sibling = pack_digest(sibling);
      let sibling = [
        record_public(builder, inputs, public, sibling[0]),
        record_public(builder, inputs, public, sibling[1]),
      ];
      let ordered = builder.gate(
        fixed.order,
        &[
          index_bits[bit_offset + level],
          current[0],
          current[1],
          sibling[0],
          sibling[1],
        ],
      );
      let parent = builder.gate(
        fixed.blake3,
        &[
          fixed.iv[0],
          fixed.iv[1],
          ordered[0],
          ordered[1],
          ordered[2],
          ordered[3],
          fixed.node_params,
        ],
      );
      current = [parent[0], parent[1]];
      let next_height = log_batch_height
        - 1
        - u8::try_from(level).expect("bounded Merkle path level");
      if let Some(&injected) = leaves.get(&next_height) {
        let parent = builder.gate(
          fixed.blake3,
          &[
            fixed.iv[0],
            fixed.iv[1],
            current[0],
            current[1],
            injected[0],
            injected[1],
            fixed.node_params,
          ],
        );
        current = [parent[0], parent[1]];
      }
    }
    let expected = bound_transcript_digest(
      builder,
      window,
      fixed.data_zero,
      inputs,
      public,
      prefix_region,
      batch.commitment,
    );
    for lane in 0..2 {
      let residual =
        builder.gate(fixed.equality, &[current[lane], expected[lane]])[0];
      builder.connect(residual, fixed.equality_zero);
    }
    let _ = batch_computation.root;
  }

  let mut buckets: BTreeMap<u8, (Wire, Wire)> = instance
    .batches
    .iter()
    .flat_map(|batch| batch.matrices.iter().map(|matrix| matrix.log_height))
    .map(|height| (height, (fixed.one, fixed.data_zero)))
    .collect();
  let coset_shift = record_fixed(builder, inputs, public, F128::new(7, 0));

  for (((batch, opening), batch_computation), rows) in instance
    .batches
    .iter()
    .zip(&query.batch_openings)
    .zip(&computation.batches)
    .zip(&all_rows)
  {
    for (((matrix, _row_values), matrix_computation), row) in batch
      .matrices
      .iter()
      .zip(&opening.opened_rows)
      .zip(&batch_computation.matrices)
      .zip(rows)
    {
      let bit_offset =
        usize::from(instance.log_global_height - matrix.log_height);
      let mut x = coset_shift;
      for (bit, factor) in index_bits[bit_offset..]
        .iter()
        .take(usize::from(matrix.log_height))
        .zip(pcs_x_factors(matrix.log_height))
      {
        let factor =
          record_fixed(builder, inputs, public, F128::new(factor, 0));
        let selected = builder.gate(
          fixed.order,
          &[*bit, fixed.one, fixed.data_zero, factor, fixed.data_zero],
        )[0];
        x = arithmetic.ext2_mul(builder, x, selected);
      }

      for (point_index, (point_kind, point_computation)) in
        matrix.opening_points.iter().zip(&matrix_computation.points).enumerate()
      {
        let point = match *point_kind {
          Stage2PcsOpeningPointV1::Zeta => zeta,
          Stage2PcsOpeningPointV1::ZetaNext { log_degree } => {
            let generator = Val::TWO_ADIC_GENERATORS[usize::from(log_degree)]
              .as_canonical_u64();
            let generator =
              record_fixed(builder, inputs, public, F128::new(generator, 0));
            arithmetic.ext2_mul(builder, zeta, generator)
          },
        };
        let denominator = record_public(
          builder,
          inputs,
          public,
          pack_extension(point_computation.denominator),
        );
        arithmetic.assert_canonical(builder, denominator);
        let denominator_check = arithmetic.add(builder, denominator, x);
        assert_f128_equal(
          builder,
          fixed.equality,
          fixed.equality_zero,
          denominator_check,
          point,
        );

        let (mut alpha_power, mut accumulator) = buckets[&matrix.log_height];
        for (column, (&p_at_x, &quotient_value)) in row
          .base_extensions
          .iter()
          .zip(&point_computation.quotients)
          .enumerate()
        {
          let p_at_z = bound_transcript_extension(
            builder,
            window,
            fixed.data_zero,
            inputs,
            public,
            prefix_region,
            matrix.opened_values,
            point_index * matrix.width + column,
          );
          arithmetic.assert_canonical(builder, p_at_z);
          let quotient = record_public(
            builder,
            inputs,
            public,
            pack_extension(quotient_value),
          );
          arithmetic.assert_canonical(builder, quotient);
          let quotient_product =
            arithmetic.ext2_mul(builder, denominator, quotient);
          let reconstructed = arithmetic.add(builder, quotient_product, p_at_x);
          assert_f128_equal(
            builder,
            fixed.equality,
            fixed.equality_zero,
            reconstructed,
            p_at_z,
          );
          let term = arithmetic.ext2_mul(builder, alpha_power, quotient);
          accumulator = arithmetic.add(builder, accumulator, term);
          alpha_power = arithmetic.ext2_mul(builder, alpha_power, alpha);
        }
        buckets.insert(matrix.log_height, (alpha_power, accumulator));
      }
    }
  }

  Ok(
    buckets
      .into_iter()
      .map(|(height, (_, accumulator))| (height, accumulator))
      .collect(),
  )
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn bound_transcript_extension(
  builder: &mut ShapeBuilder,
  window: SlotId,
  data_zero: Wire,
  inputs: &mut Vec<F128>,
  public: &mut Vec<F128>,
  region: &crate::transcript::TranscriptConstraintRegion,
  binding: Stage2TranscriptByteBindingV1,
  extension_offset: usize,
) -> Wire {
  bound_transcript_window(
    builder,
    window,
    data_zero,
    inputs,
    public,
    region,
    binding,
    extension_offset * 16,
  )
}

fn bound_transcript_digest(
  builder: &mut ShapeBuilder,
  window: SlotId,
  data_zero: Wire,
  inputs: &mut Vec<F128>,
  public: &mut Vec<F128>,
  region: &crate::transcript::TranscriptConstraintRegion,
  binding: Stage2TranscriptByteBindingV1,
) -> [Wire; 2] {
  [
    bound_transcript_window(
      builder, window, data_zero, inputs, public, region, binding, 0,
    ),
    bound_transcript_window(
      builder, window, data_zero, inputs, public, region, binding, 16,
    ),
  ]
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn bound_transcript_window(
  builder: &mut ShapeBuilder,
  window: SlotId,
  data_zero: Wire,
  inputs: &mut Vec<F128>,
  public: &mut Vec<F128>,
  region: &crate::transcript::TranscriptConstraintRegion,
  binding: Stage2TranscriptByteBindingV1,
  relative_byte: usize,
) -> Wire {
  let byte_offset = binding.byte_offset + relative_byte;
  let word_index = byte_offset / 16;
  let byte_in_word = byte_offset % 16;
  let words = &region.observation_words[binding.segment.index()];
  let first = words[word_index];
  let second = words.get(word_index + 1).copied().unwrap_or(data_zero);
  let selector =
    record_fixed(builder, inputs, public, F128::new(1 << byte_in_word, 0));
  builder.gate(window, &[first, second, selector])[0]
}

pub(crate) fn assert_f128_equal(
  builder: &mut ShapeBuilder,
  equality: SlotId,
  equality_zero: Wire,
  left: Wire,
  right: Wire,
) {
  let residual = builder.gate(equality, &[left, right])[0];
  builder.connect(residual, equality_zero);
}

fn transcript_bound_fri_nu(
  prefix: &Stage2TranscriptReplayV1,
  fri_transcript: &Stage2FriTranscriptReplayV1,
  selected: &[SelectedFriQuery<'_>],
  pcs_instance: Option<&Stage2PcsInstanceV1>,
  air: Option<&Stage2AirProgramV1>,
) -> Result<usize> {
  let prefix_capacity = 1usize << transcript_nu(prefix)?;
  let commit_capacity = selected.iter().try_fold(0usize, |rows, item| {
    rows.checked_add(1usize << commit_phase_nu(item.query)).ok_or_else(|| {
      anyhow::anyhow!("transcript-bound FRI query row budget overflow")
    })
  })?;
  let fri_blake3_rows = fri_transcript_blake3_rows(fri_transcript)?;
  let fri_split_rows = fri_transcript_split_rows(fri_transcript)?;
  let pcs_capacity = if let Some(instance) = pcs_instance {
    selected.iter().try_fold(0usize, |rows, item| {
      let query = item
        .pcs_query
        .ok_or_else(|| anyhow::anyhow!("missing PCS query row budget"))?;
      rows
        .checked_add(1usize << stage2_pcs_query_nu(instance, query))
        .ok_or_else(|| anyhow::anyhow!("PCS query row budget overflow"))
    })?
  } else {
    0
  };
  let row_budget = prefix_capacity
    .checked_add(commit_capacity)
    .and_then(|rows| rows.checked_add(fri_blake3_rows))
    .and_then(|rows| rows.checked_add(fri_split_rows))
    .and_then(|rows| rows.checked_add(pcs_capacity))
    .and_then(|rows| {
      rows.checked_add(air.map_or(0, Stage2AirProgramV1::row_budget))
    })
    .ok_or_else(|| {
      anyhow::anyhow!("transcript-bound FRI row budget overflow")
    })?;
  Ok(
    usize::try_from(row_budget.max(1).next_power_of_two().ilog2())
      .expect("FRI row logarithm fits usize")
      .max(NU),
  )
}

fn stage2_pcs_query_nu(
  instance: &Stage2PcsInstanceV1,
  query: &Stage2PcsQueryV1,
) -> usize {
  let values = query
    .batch_openings
    .iter()
    .flat_map(|batch| &batch.opened_rows)
    .map(Vec::len)
    .sum::<usize>();
  let points = instance
    .batches
    .iter()
    .flat_map(|batch| &batch.matrices)
    .map(|matrix| matrix.opening_points.len())
    .sum::<usize>();
  let path_nodes = query
    .batch_openings
    .iter()
    .map(|batch| batch.opening_proof.len())
    .sum::<usize>();
  let leaf_rows = instance
    .batches
    .iter()
    .zip(&query.batch_openings)
    .map(|(batch, opening)| {
      (0..=batch.matrices.iter().map(|matrix| matrix.log_height).max().unwrap())
        .filter(|height| {
          batch.matrices.iter().any(|matrix| matrix.log_height == *height)
        })
        .map(|height| {
          let width = batch
            .matrices
            .iter()
            .zip(&opening.opened_rows)
            .filter(|(matrix, _)| matrix.log_height == height)
            .map(|(_, row)| row.len())
            .sum::<usize>();
          hash_trace(width * 8).rows.len()
        })
        .sum::<usize>()
    })
    .sum::<usize>();
  let row_bound = values
    .saturating_mul(256)
    .saturating_add(points.saturating_mul(128))
    .saturating_add(path_nodes.saturating_mul(64))
    .saturating_add(leaf_rows)
    .max(1);
  usize::try_from(row_bound.next_power_of_two().ilog2()).unwrap().max(NU)
}

pub(crate) fn record_fixed(
  builder: &mut ShapeBuilder,
  inputs: &mut Vec<F128>,
  public: &mut Vec<F128>,
  value: F128,
) -> Wire {
  inputs.push(value);
  public.push(value);
  builder.fixed_public_input(value)
}

fn record_public(
  builder: &mut ShapeBuilder,
  inputs: &mut Vec<F128>,
  public: &mut Vec<F128>,
  value: F128,
) -> Wire {
  inputs.push(value);
  public.push(value);
  builder.public_input()
}

#[allow(clippy::too_many_arguments)]
fn constrain_authenticated_fold(
  builder: &mut ShapeBuilder,
  arithmetic: &GoldilocksCircuitSlots,
  blake3_slot: SlotId,
  order_slot: SlotId,
  equality_slot: SlotId,
  data_zero: Wire,
  equality_zero: Wire,
  iv: [Wire; 2],
  leaf_params: Wire,
  node_params: Wire,
  one: Wire,
  factor_wires: &[Wire],
  folded: Wire,
  sibling: Wire,
  beta: Wire,
  index_bits: &[Wire],
  path: &[[Wire; 2]],
  folded_result: Wire,
) -> [Wire; 2] {
  assert_eq!(index_bits.len(), path.len() + 1);
  assert_eq!(factor_wires.len(), path.len());

  // The low query bit determines which value is e0 and which is e1.
  let ordered_evals = builder
    .gate(order_slot, &[index_bits[0], folded, data_zero, sibling, data_zero]);
  let e0 = ordered_evals[0];
  let e1 = ordered_evals[2];

  // ExtensionMmcs serializes `[e0.c0,e0.c1,e1.c0,e1.c1]` as 32 little-
  // endian bytes before hashing the leaf.
  let leaf = builder.gate(
    blake3_slot,
    &[iv[0], iv[1], e0, e1, data_zero, data_zero, leaf_params],
  );
  let mut current = [leaf[0], leaf[1]];
  for (level, sibling_digest) in path.iter().enumerate() {
    let ordered = builder.gate(
      order_slot,
      &[
        index_bits[level + 1],
        current[0],
        current[1],
        sibling_digest[0],
        sibling_digest[1],
      ],
    );
    let parent = builder.gate(
      blake3_slot,
      &[
        iv[0],
        iv[1],
        ordered[0],
        ordered[1],
        ordered[2],
        ordered[3],
        node_params,
      ],
    );
    current = [parent[0], parent[1]];
  }

  // `s = g_(h+1)^reverse_bits(index >> 1, h)`. Each original LSB-first
  // bit selects its corresponding pre-squared factor.
  let mut s = one;
  for (bit, factor) in index_bits[1..].iter().zip(factor_wires) {
    let selected =
      builder.gate(order_slot, &[*bit, one, data_zero, *factor, data_zero])[0];
    s = arithmetic.ext2_mul(builder, s, selected);
  }

  let sum = arithmetic.add(builder, e0, e1);
  let two_s = arithmetic.add(builder, s, s);
  let lhs_fold = arithmetic.ext2_mul(builder, two_s, folded_result);
  let lhs_beta = arithmetic.ext2_mul(builder, beta, e1);
  let lhs = arithmetic.add(builder, lhs_fold, lhs_beta);
  let rhs_sum = arithmetic.ext2_mul(builder, s, sum);
  let rhs_beta = arithmetic.ext2_mul(builder, beta, e0);
  let rhs = arithmetic.add(builder, rhs_sum, rhs_beta);
  let equality_residual = builder.gate(equality_slot, &[lhs, rhs])[0];
  builder.connect(equality_residual, equality_zero);
  current
}

#[allow(clippy::too_many_arguments)]
fn prove_fri_circuit(
  shape: &CircuitShape,
  slots: FriTableSlots,
  sample_slot: Option<SlotId>,
  split_slot: Option<SlotId>,
  window_slot: Option<SlotId>,
  nu: usize,
  inputs: &[F128],
  expected_public: &[F128],
  transcript_domain: &[u8],
) -> Result<Vec<u8>> {
  let witness = shape.run(inputs, &[]);
  if witness.public != expected_public {
    bail!("Flock authenticated-FRI circuit disagrees with native semantics");
  }
  let blake3_rows = witness.rows::<Blake3Gate>(slots.blake3);
  let order_rows = witness.rows::<DigestOrderGate>(slots.order);
  let add_rows = witness.rows::<GoldilocksAddPairGate>(slots.add);
  let mul_rows = witness.rows::<GoldilocksMulPairGate>(slots.mul);
  let repack_rows = witness.rows::<GoldilocksLaneRepackGate>(slots.repack);
  let canonical_rows =
    witness.rows::<CanonicalGoldilocksPairGate>(slots.canonical);
  let equality_rows = witness.rows::<F128EqualityGate>(slots.equality);
  let sample_rows =
    sample_slot.map(|slot| witness.rows::<HashSampleGate>(slot));
  let field_sample_rows =
    slots.field_sample.map(|slot| witness.rows::<GoldilocksSampleGate>(slot));
  let split_rows = split_slot.map(|slot| witness.rows::<U64SplitGate>(slot));
  let window_rows =
    window_slot.map(|slot| witness.rows::<ByteWindowGate>(slot));

  let blake3_r1cs = flock_blake3::build_block_r1cs(nu);
  let blake3_lincheck = blake3_r1cs.csc_lincheck_circuit();
  let order_r1cs = build_digest_order_r1cs(nu);
  let order_lincheck = order_r1cs.csc_lincheck_circuit();
  let add_r1cs = build_goldilocks_add_r1cs(nu);
  let add_lincheck = add_r1cs.csc_lincheck_circuit();
  let mul_r1cs = build_goldilocks_mul_r1cs(nu);
  let mul_lincheck = mul_r1cs.csc_lincheck_circuit();
  let repack_r1cs = build_lane_repack_r1cs(nu);
  let repack_lincheck = repack_r1cs.csc_lincheck_circuit();
  let canonical_r1cs = build_canonical_pair_r1cs(nu);
  let canonical_lincheck = canonical_r1cs.csc_lincheck_circuit();
  let equality_r1cs = build_f128_equality_r1cs(nu);
  let equality_lincheck = equality_r1cs.csc_lincheck_circuit();
  let sample_r1cs = build_hash_sample_r1cs(nu);
  let sample_lincheck = sample_r1cs.csc_lincheck_circuit();
  let field_sample_r1cs = build_goldilocks_sample_r1cs(nu);
  let field_sample_lincheck = field_sample_r1cs.csc_lincheck_circuit();
  let split_r1cs = build_u64_split_r1cs(nu);
  let split_lincheck = split_r1cs.csc_lincheck_circuit();
  let window_r1cs = build_byte_window_r1cs(nu);
  let window_lincheck = window_r1cs.csc_lincheck_circuit();

  let mut slot_inputs = vec![
    (
      shape.registry_slot(slots.blake3),
      UnionSlotProverInput::new(
        flock_blake3::generate_witness_batch_major_partial(blake3_rows, nu),
        blake3_lincheck,
      ),
    ),
    (
      shape.registry_slot(slots.order),
      UnionSlotProverInput::new(
        generate_digest_order_witness(order_rows, nu),
        order_lincheck,
      ),
    ),
    (
      shape.registry_slot(slots.add),
      UnionSlotProverInput::new(
        generate_goldilocks_add_witness(add_rows, nu),
        add_lincheck,
      ),
    ),
    (
      shape.registry_slot(slots.mul),
      UnionSlotProverInput::new(
        generate_goldilocks_mul_witness(mul_rows, nu),
        mul_lincheck,
      ),
    ),
    (
      shape.registry_slot(slots.repack),
      UnionSlotProverInput::new(
        generate_lane_repack_witness(repack_rows, nu),
        repack_lincheck,
      ),
    ),
    (
      shape.registry_slot(slots.canonical),
      UnionSlotProverInput::new(
        generate_canonical_pair_witness(canonical_rows, nu),
        canonical_lincheck,
      ),
    ),
    (
      shape.registry_slot(slots.equality),
      UnionSlotProverInput::new(
        generate_f128_equality_witness(equality_rows, nu),
        equality_lincheck,
      ),
    ),
  ];
  if let (Some(slot), Some(rows)) = (sample_slot, sample_rows) {
    slot_inputs.push((
      shape.registry_slot(slot),
      UnionSlotProverInput::new(
        generate_hash_sample_witness(rows, nu),
        sample_lincheck,
      ),
    ));
  }
  if let (Some(slot), Some(rows)) = (slots.field_sample, field_sample_rows) {
    slot_inputs.push((
      shape.registry_slot(slot),
      UnionSlotProverInput::new(
        generate_goldilocks_sample_witness(rows, nu),
        field_sample_lincheck,
      ),
    ));
  }
  if let (Some(slot), Some(rows)) = (split_slot, split_rows) {
    slot_inputs.push((
      shape.registry_slot(slot),
      UnionSlotProverInput::new(
        generate_u64_split_witness(rows, nu),
        split_lincheck,
      ),
    ));
  }
  if let (Some(slot), Some(rows)) = (window_slot, window_rows) {
    slot_inputs.push((
      shape.registry_slot(slot),
      UnionSlotProverInput::new(
        generate_byte_window_witness(rows, nu),
        window_lincheck,
      ),
    ));
  }
  sort_and_validate_slots(&mut slot_inputs)?;
  let slot_inputs = slot_inputs.into_iter().map(|(_, input)| input).collect();
  let union = UnionInstance::new(&shape.registry, shape.counts.clone());
  let params = pcs_params(&union);
  let mut challenger = FsChallenger::with_chained_blake3(transcript_domain);
  let (proof, commitment, _) = prover::prove_fast_ligerito_union_circuit(
    &union,
    &shape.circuit,
    &witness.public,
    &params,
    slot_inputs,
    Vec::new(),
    &mut challenger,
  );
  let proof_bundle_bytes =
    encode_bundle(&FriFoldProofBundle { commitment, proof })?;
  if proof_bundle_bytes.len() > MAX_BUNDLE_BYTES {
    bail!("Flock authenticated-FRI proof exceeds {MAX_BUNDLE_BYTES} bytes");
  }
  Ok(proof_bundle_bytes)
}

#[allow(clippy::too_many_arguments)]
fn verify_fri_circuit(
  shape: &CircuitShape,
  slots: FriTableSlots,
  sample_slot: Option<SlotId>,
  split_slot: Option<SlotId>,
  window_slot: Option<SlotId>,
  nu: usize,
  public: &[F128],
  proof_bundle_bytes: &[u8],
  transcript_domain: &[u8],
) -> Result<()> {
  let bundle = decode_bundle(proof_bundle_bytes)
    .context("decode Flock authenticated-FRI conformance proof bundle")?;
  let blake3_r1cs = flock_blake3::build_block_r1cs(nu);
  let blake3_lincheck = blake3_r1cs.csc_lincheck_circuit();
  let order_r1cs = build_digest_order_r1cs(nu);
  let order_lincheck = order_r1cs.csc_lincheck_circuit();
  let add_r1cs = build_goldilocks_add_r1cs(nu);
  let add_lincheck = add_r1cs.csc_lincheck_circuit();
  let mul_r1cs = build_goldilocks_mul_r1cs(nu);
  let mul_lincheck = mul_r1cs.csc_lincheck_circuit();
  let repack_r1cs = build_lane_repack_r1cs(nu);
  let repack_lincheck = repack_r1cs.csc_lincheck_circuit();
  let canonical_r1cs = build_canonical_pair_r1cs(nu);
  let canonical_lincheck = canonical_r1cs.csc_lincheck_circuit();
  let equality_r1cs = build_f128_equality_r1cs(nu);
  let equality_lincheck = equality_r1cs.csc_lincheck_circuit();
  let sample_r1cs = build_hash_sample_r1cs(nu);
  let sample_lincheck = sample_r1cs.csc_lincheck_circuit();
  let field_sample_r1cs = build_goldilocks_sample_r1cs(nu);
  let field_sample_lincheck = field_sample_r1cs.csc_lincheck_circuit();
  let split_r1cs = build_u64_split_r1cs(nu);
  let split_lincheck = split_r1cs.csc_lincheck_circuit();
  let window_r1cs = build_byte_window_r1cs(nu);
  let window_lincheck = window_r1cs.csc_lincheck_circuit();

  let mut linchecks: Vec<(usize, &dyn LincheckCircuit)> = vec![
    (shape.registry_slot(slots.blake3), blake3_lincheck),
    (shape.registry_slot(slots.order), order_lincheck),
    (shape.registry_slot(slots.add), add_lincheck),
    (shape.registry_slot(slots.mul), mul_lincheck),
    (shape.registry_slot(slots.repack), repack_lincheck),
    (shape.registry_slot(slots.canonical), canonical_lincheck),
    (shape.registry_slot(slots.equality), equality_lincheck),
  ];
  if let Some(slot) = sample_slot {
    linchecks.push((shape.registry_slot(slot), sample_lincheck));
  }
  if let Some(slot) = slots.field_sample {
    linchecks.push((shape.registry_slot(slot), field_sample_lincheck));
  }
  if let Some(slot) = split_slot {
    linchecks.push((shape.registry_slot(slot), split_lincheck));
  }
  if let Some(slot) = window_slot {
    linchecks.push((shape.registry_slot(slot), window_lincheck));
  }
  sort_and_validate_slots(&mut linchecks)?;
  let linchecks: Vec<&dyn LincheckCircuit> =
    linchecks.into_iter().map(|(_, lincheck)| lincheck).collect();
  let union = UnionInstance::new(&shape.registry, shape.counts.clone());
  let params = pcs_params(&union);
  let mut challenger = FsChallenger::with_chained_blake3(transcript_domain);
  verifier::verify_ligerito_union_circuit(
    &union,
    &shape.circuit,
    public,
    &linchecks,
    &bundle.commitment,
    &bundle.proof,
    &params,
    &mut challenger,
  )
  .map_err(|error| {
    anyhow::anyhow!("Flock authenticated-FRI proof rejected: {error:?}")
  })?;
  Ok(())
}

fn relation_inputs(
  query: &FriFoldQueryV1,
  folded_result: [u64; 2],
) -> Vec<F128> {
  let packed_iv = pack8(&IV);
  let mut inputs = Vec::with_capacity(10 + 4 * usize::from(query.log_height));
  inputs.push(F128::ZERO);
  inputs.push(F128::ZERO);
  inputs.push(F128::ZERO);
  inputs.extend_from_slice(&packed_iv);
  inputs.push(pack_params(0, 32, CHUNK_START | CHUNK_END | ROOT));
  inputs.push(pack_params(0, 64, CHUNK_START | CHUNK_END | ROOT));
  inputs.push(F128::new(1, 0));
  inputs.extend(
    twiddle_factors(query.log_height)
      .into_iter()
      .map(|factor| F128::new(factor, 0)),
  );
  inputs.push(pack_extension(query.folded));
  inputs.push(pack_extension(query.sibling));
  inputs.push(pack_extension(query.beta));
  inputs.extend(
    (0..=query.log_height)
      .map(|bit| F128::new(u64::from((query.query_index >> bit) & 1), 0)),
  );
  for sibling in &query.opening_proof {
    inputs.extend_from_slice(&pack_digest(sibling));
  }
  inputs.push(pack_extension(folded_result));
  inputs
}

fn relation_public(
  query: &FriFoldQueryV1,
  folded_result: [u64; 2],
  root: &[u8; 32],
) -> Vec<F128> {
  let mut public = relation_inputs(query, folded_result);
  public.extend_from_slice(&pack_digest(root));
  public
}

struct FriCommitPhaseComputation {
  round_queries: Vec<FriFoldQueryV1>,
  fold_results: Vec<[u64; 2]>,
  results: Vec<[u64; 2]>,
  roots: Vec<[u8; 32]>,
}

fn compute_commit_phase(
  query: &FriCommitPhaseQueryV1,
) -> Result<FriCommitPhaseComputation> {
  validate_commit_phase_structure(query)?;
  let mut folded = query.initial_folded;
  let mut round_queries = Vec::with_capacity(query.rounds.len());
  let mut fold_results = Vec::with_capacity(query.rounds.len());
  let mut results = Vec::with_capacity(query.rounds.len());
  let mut roots = Vec::with_capacity(query.rounds.len());
  for (round_index, round) in query.rounds.iter().enumerate() {
    let round_u8 = u8::try_from(round_index).expect("bounded FRI round count");
    let fold_query = FriFoldQueryV1 {
      log_height: query.initial_log_height - round_u8,
      query_index: query.query_index >> round_index,
      folded,
      sibling: round.sibling,
      beta: round.beta,
      opening_proof: round.opening_proof.clone(),
    };
    validate_query(&fold_query)?;
    let fold_result = native_fold(&fold_query);
    let result = round.reduced_opening.map_or(fold_result, |reduced_opening| {
      let beta = native_extension(round.beta);
      extension_words(
        native_extension(fold_result)
          + beta * beta * native_extension(reduced_opening),
      )
    });
    roots.push(native_root(&fold_query));
    fold_results.push(fold_result);
    results.push(result);
    round_queries.push(fold_query);
    folded = result;
  }
  Ok(FriCommitPhaseComputation { round_queries, fold_results, results, roots })
}

fn ensure_final_polynomial(
  query: &FriCommitPhaseQueryV1,
  computation: &FriCommitPhaseComputation,
) -> Result<()> {
  if computation.results.last().copied() != Some(query.final_polynomial) {
    bail!("FRI commit-phase fold chain does not equal the final polynomial");
  }
  Ok(())
}

fn commit_phase_relation_inputs(
  query: &FriCommitPhaseQueryV1,
  computation: &FriCommitPhaseComputation,
) -> Vec<F128> {
  let packed_iv = pack8(&IV);
  let factor_count = computation
    .round_queries
    .iter()
    .map(|round| usize::from(round.log_height))
    .sum::<usize>();
  let path_words = computation
    .round_queries
    .iter()
    .map(|round| 2 * round.opening_proof.len())
    .sum::<usize>();
  let mut inputs = Vec::with_capacity(
    8 + factor_count
      + 1
      + usize::from(query.initial_log_height)
      + 1
      + 3 * query.rounds.len()
      + query
        .rounds
        .iter()
        .filter(|round| round.reduced_opening.is_some())
        .count()
      + path_words
      + 1,
  );
  inputs.extend_from_slice(&[F128::ZERO, F128::ZERO, F128::ZERO]);
  inputs.extend_from_slice(&packed_iv);
  inputs.push(pack_params(0, 32, CHUNK_START | CHUNK_END | ROOT));
  inputs.push(pack_params(0, 64, CHUNK_START | CHUNK_END | ROOT));
  inputs.push(F128::new(1, 0));
  for round in &computation.round_queries {
    inputs.extend(
      twiddle_factors(round.log_height)
        .into_iter()
        .map(|factor| F128::new(factor, 0)),
    );
  }
  inputs.push(pack_extension(query.initial_folded));
  inputs.extend(
    (0..=query.initial_log_height)
      .map(|bit| F128::new(u64::from((query.query_index >> bit) & 1), 0)),
  );
  for ((round, source), fold_result) in computation
    .round_queries
    .iter()
    .zip(&query.rounds)
    .zip(&computation.fold_results)
  {
    inputs.push(pack_extension(round.sibling));
    inputs.push(pack_extension(round.beta));
    if let Some(reduced_opening) = source.reduced_opening {
      inputs.push(pack_extension(reduced_opening));
    }
    for sibling in &round.opening_proof {
      inputs.extend_from_slice(&pack_digest(sibling));
    }
    inputs.push(pack_extension(*fold_result));
  }
  inputs.push(pack_extension(query.final_polynomial));
  inputs
}

fn commit_phase_relation_public(
  query: &FriCommitPhaseQueryV1,
  computation: &FriCommitPhaseComputation,
) -> Vec<F128> {
  let mut public = commit_phase_relation_inputs(query, computation);
  for root in &computation.roots {
    public.extend_from_slice(&pack_digest(root));
  }
  public
}

fn commit_phase_nu(query: &FriCommitPhaseQueryV1) -> usize {
  let rounds = query.rounds.len();
  let rollins =
    query.rounds.iter().filter(|round| round.reduced_opening.is_some()).count();
  let height_sum = (0..rounds)
    .map(|round| usize::from(query.initial_log_height) - round)
    .sum::<usize>();
  let extension_multiplications = height_sum + 4 * rounds + 2 * rollins;
  let row_bound = [
    5 * extension_multiplications + 4 * rounds + rollins,
    2 * extension_multiplications,
    3 * extension_multiplications,
    9 * extension_multiplications + 4 * rounds + rollins,
    2 * height_sum + rounds,
    height_sum + rounds,
    rounds + 1,
  ]
  .into_iter()
  .max()
  .unwrap();
  usize::try_from(row_bound.next_power_of_two().ilog2()).unwrap().max(NU)
}

fn validate_commit_phase_structure(
  query: &FriCommitPhaseQueryV1,
) -> Result<()> {
  validate_log_height(query.initial_log_height)?;
  validate_commit_phase_round_count(
    query.initial_log_height,
    query.rounds.len(),
  )?;
  if u64::from(query.query_index) >= 1u64 << (query.initial_log_height + 1) {
    bail!(
      "FRI commit-phase query index {} does not fit {} bits",
      query.query_index,
      query.initial_log_height + 1
    );
  }
  validate_extension(query.initial_folded, "initial folded evaluation")?;
  validate_extension(query.final_polynomial, "final polynomial")?;
  for (round_index, round) in query.rounds.iter().enumerate() {
    let expected_depth = usize::from(query.initial_log_height) - round_index;
    if round.opening_proof.len() != expected_depth {
      bail!(
        "FRI commit-phase round {round_index} has path depth {}; expected {expected_depth}",
        round.opening_proof.len()
      );
    }
    validate_extension(round.sibling, "FRI round sibling")?;
    validate_extension(round.beta, "FRI round challenge")?;
    if let Some(reduced_opening) = round.reduced_opening {
      validate_extension(reduced_opening, "FRI reduced opening")?;
    }
  }
  Ok(())
}

fn validate_commit_phase_round_count(
  initial_log_height: u8,
  round_count: usize,
) -> Result<()> {
  // Every round lowers the authenticated tree by one level. The height is
  // already capped by `MAX_LOG_HEIGHT`, so this is a protocol-derived bound
  // rather than a second, arbitrary implementation ceiling. The
  // transcript-bound path additionally fixes the exact count through its
  // folding-arity schedule and FRI parameters.
  let maximum = usize::from(initial_log_height);
  if !(1..=maximum).contains(&round_count) {
    bail!("FRI commit-phase round count {round_count}; expected 1..={maximum}");
  }
  Ok(())
}

fn commit_phase_rounds_bytes(
  initial_log_height: u8,
  round_count: usize,
) -> Result<usize> {
  validate_commit_phase_round_count(initial_log_height, round_count)?;
  (0..round_count).try_fold(0usize, |length, round| {
    let depth = usize::from(initial_log_height) - round;
    length
      .checked_add(49 + depth * 32)
      .ok_or_else(|| anyhow::anyhow!("FRI commit-phase round bytes overflow"))
  })
}

fn build_stage2_pcs_fri_witness(
  prepared: &ValidatedStage2RootV1,
  fri: &FriParameters,
  typed: &Stage3TypedProofWitnessV1,
) -> Result<Stage2PcsFriWitnessV1> {
  typed.ensure_profile(prepared.advice_profile())?;
  let key = AiurVerifyingKey::from_bytes(prepared.verifying_key_bytes())
    .map_err(|error| anyhow::anyhow!("decode Aiur PCS key: {error}"))?;
  if key.to_bytes() != prepared.verifying_key_bytes() {
    bail!("Aiur PCS key is not canonically encoded");
  }
  if key.commitment_parameters().cap_height != 0 {
    bail!("Stage 3 PCS lowering currently requires cap height zero");
  }
  if fri_parameter_words(&key.fri_parameters()) != fri_parameter_words(fri) {
    bail!("Stage 3 PCS lowering uses different FRI parameters");
  }

  let prefix =
    Stage2TranscriptReplayV1::from_prepared_and_typed(prepared, fri, typed)?;
  let fri_transcript =
    Stage2FriTranscriptReplayV1::from_prepared_and_typed(prepared, fri, typed)?;
  let metadata = key.pcs_circuit_metadata();
  if metadata.len() != typed.active.len() {
    bail!("Aiur PCS metadata and activation lengths disagree");
  }
  let active_indices: Vec<_> = typed
    .active
    .iter()
    .enumerate()
    .filter_map(|(index, &active)| active.then_some(index))
    .collect();
  if active_indices.len() != typed.log_degrees.len() {
    bail!("Aiur PCS active-circuit and log-degree counts disagree");
  }
  let mut active_position = vec![None; typed.active.len()];
  for (position, &circuit) in active_indices.iter().enumerate() {
    active_position[circuit] = Some(position);
  }

  let preprocessed_roots = key.preprocessed_commitment_roots();
  let initial_preprocessed_offset = key
    .transcript_seed_and_shape_bytes()
    .len()
    .checked_add(typed.active.len() * 8)
    .ok_or_else(|| anyhow::anyhow!("initial transcript offset overflow"))?;
  let initial_stage_1_offset = initial_preprocessed_offset
    .checked_add(
      preprocessed_roots.as_ref().map_or(0, |roots| roots.len() * 32),
    )
    .ok_or_else(|| anyhow::anyhow!("Stage 1 commitment offset overflow"))?;
  ensure_single_root(&typed.commitments.stage_1_trace, "Stage 1")?;
  ensure_single_root(&typed.commitments.stage_2_trace, "Stage 2")?;
  ensure_single_root(&typed.commitments.quotient_chunks, "quotient")?;

  let log_blowup = u8::try_from(key.commitment_parameters().log_blowup)
    .map_err(|_| anyhow::anyhow!("PCS blowup height exceeds u8"))?;
  let mut opening_offset = 0usize;

  let mut stage_1_matrices = Vec::with_capacity(active_indices.len());
  for (position, &circuit_index) in active_indices.iter().enumerate() {
    let circuit = metadata[circuit_index];
    ensure_opened_matrix_shape(
      &typed.stage_1_opened_values,
      position,
      2,
      circuit.main_width,
      "Stage 1",
    )?;
    let log_degree = typed.log_degrees[position];
    stage_1_matrices.push(stage2_pcs_matrix(
      log_degree,
      log_blowup,
      circuit.main_width,
      vec![
        Stage2PcsOpeningPointV1::Zeta,
        Stage2PcsOpeningPointV1::ZetaNext { log_degree },
      ],
      &mut opening_offset,
    )?);
  }

  let mut stage_2_matrices = Vec::with_capacity(active_indices.len());
  for (position, &circuit_index) in active_indices.iter().enumerate() {
    let circuit = metadata[circuit_index];
    ensure_opened_matrix_shape(
      &typed.stage_2_opened_values,
      position,
      2,
      circuit.stage_2_width,
      "Stage 2",
    )?;
    let log_degree = typed.log_degrees[position];
    stage_2_matrices.push(stage2_pcs_matrix(
      log_degree,
      log_blowup,
      circuit.stage_2_width,
      vec![
        Stage2PcsOpeningPointV1::Zeta,
        Stage2PcsOpeningPointV1::ZetaNext { log_degree },
      ],
      &mut opening_offset,
    )?);
  }

  let mut quotient_matrices = Vec::with_capacity(active_indices.len());
  for (position, &circuit_index) in active_indices.iter().enumerate() {
    let circuit = metadata[circuit_index];
    ensure_opened_matrix_shape(
      &typed.quotient_opened_values,
      position,
      1,
      circuit.quotient_width,
      "quotient",
    )?;
    quotient_matrices.push(stage2_pcs_matrix(
      typed.log_degrees[position],
      log_blowup,
      circuit.quotient_width,
      vec![Stage2PcsOpeningPointV1::Zeta],
      &mut opening_offset,
    )?);
  }

  let mut batches = vec![
    Stage2PcsBatchV1 {
      commitment: Stage2TranscriptByteBindingV1::new(
        Stage2TranscriptSegmentV1::Initial,
        initial_stage_1_offset,
      ),
      matrices: stage_1_matrices,
    },
    Stage2PcsBatchV1 {
      commitment: Stage2TranscriptByteBindingV1::new(
        Stage2TranscriptSegmentV1::Stage2AndAccumulator,
        0,
      ),
      matrices: stage_2_matrices,
    },
    Stage2PcsBatchV1 {
      commitment: Stage2TranscriptByteBindingV1::new(
        Stage2TranscriptSegmentV1::QuotientCommitment,
        0,
      ),
      matrices: quotient_matrices,
    },
  ];

  if let Some(roots) = &preprocessed_roots {
    ensure_single_root(roots, "preprocessed")?;
    let opened =
      typed.preprocessed_opened_values.as_ref().ok_or_else(|| {
        anyhow::anyhow!("preprocessed commitment has no opened-value round")
      })?;
    let mut preprocessed: Vec<_> = metadata
      .iter()
      .enumerate()
      .filter_map(|(circuit, metadata)| {
        metadata.preprocessed_slot.map(|slot| (slot, circuit, *metadata))
      })
      .collect();
    preprocessed.sort_by_key(|(slot, _, _)| *slot);
    if opened.len() != preprocessed.len() {
      bail!("preprocessed PCS metadata and opened-value counts disagree");
    }
    let mut matrices = Vec::with_capacity(preprocessed.len());
    for (expected_slot, (slot, circuit_index, circuit)) in
      preprocessed.into_iter().enumerate()
    {
      if slot != expected_slot {
        bail!("preprocessed PCS slots are not contiguous");
      }
      let (log_degree, opening_points) =
        if let Some(position) = active_position[circuit_index] {
          ensure_opened_matrix_shape(
            opened,
            slot,
            2,
            circuit.preprocessed_width,
            "preprocessed",
          )?;
          let log_degree = typed.log_degrees[position];
          (
            log_degree,
            vec![
              Stage2PcsOpeningPointV1::Zeta,
              Stage2PcsOpeningPointV1::ZetaNext { log_degree },
            ],
          )
        } else {
          ensure_opened_matrix_shape(
            opened,
            slot,
            0,
            circuit.preprocessed_width,
            "inactive preprocessed",
          )?;
          let height = circuit.preprocessed_height;
          if !height.is_power_of_two() {
            bail!("preprocessed matrix height is not a power of two");
          }
          (
            u8::try_from(height.ilog2())
              .map_err(|_| anyhow::anyhow!("preprocessed height exceeds u8"))?,
            Vec::new(),
          )
        };
      matrices.push(stage2_pcs_matrix(
        log_degree,
        log_blowup,
        circuit.preprocessed_width,
        opening_points,
        &mut opening_offset,
      )?);
    }
    batches.push(Stage2PcsBatchV1 {
      commitment: Stage2TranscriptByteBindingV1::new(
        Stage2TranscriptSegmentV1::Initial,
        initial_preprocessed_offset,
      ),
      matrices,
    });
  } else if typed.preprocessed_opened_values.is_some() {
    bail!("proof has preprocessed openings but the key has no commitment");
  }
  if opening_offset != prefix.pcs_opening_observations.len() {
    bail!(
      "Stage 2 PCS adapter consumed {opening_offset} opening bytes; transcript has {}",
      prefix.pcs_opening_observations.len()
    );
  }

  let pcs_instance = Stage2PcsInstanceV1 {
    log_global_height: fri_transcript.query_index_bits,
    log_blowup,
    batches,
  };
  validate_stage2_pcs_instance(&prefix, &pcs_instance)?;
  let prefix_challenges = prefix.challenges()?;
  let fri_challenges = fri_transcript.challenges(&prefix)?;
  if typed.opening_proof.query_proofs.len()
    != fri_challenges.query_indices.len()
  {
    bail!("typed PCS query count disagrees with transcript samples");
  }
  if typed.opening_proof.final_poly.as_slice()
    != fri_transcript.final_polynomial
  {
    bail!("typed and transcript final polynomials disagree");
  }
  let final_polynomial =
    *typed.opening_proof.final_poly.first().ok_or_else(|| {
      anyhow::anyhow!("Stage 2 FRI final polynomial is empty")
    })?;
  if typed.opening_proof.final_poly.len() != 1 {
    bail!(
      "Stage 3 PCS/FRI adapter currently requires a constant final polynomial"
    );
  }

  let mut queries = Vec::with_capacity(fri_challenges.query_indices.len());
  for (query_number, (typed_query, &query_index)) in typed
    .opening_proof
    .query_proofs
    .iter()
    .zip(&fri_challenges.query_indices)
    .enumerate()
  {
    if typed_query.input_proof.len() != pcs_instance.batches.len() {
      bail!("typed PCS query {query_number} has the wrong batch count");
    }
    let pcs = Stage2PcsQueryV1 {
      batch_openings: typed_query
        .input_proof
        .iter()
        .map(|opening| Stage2PcsBatchOpeningV1 {
          opened_rows: opening.opened_values.clone(),
          opening_proof: opening.opening_proof.clone(),
        })
        .collect(),
    };
    if typed_query.commit_phase_openings.len() != fri_challenges.betas.len() {
      bail!("typed FRI query {query_number} has the wrong round count");
    }
    let rounds: Vec<_> = typed_query
      .commit_phase_openings
      .iter()
      .zip(&fri_challenges.betas)
      .enumerate()
      .map(|(round, (opening, &beta))| {
        if opening.log_arity != 1 || opening.sibling_values.len() != 1 {
          bail!("typed FRI query {query_number} round {round} is not binary");
        }
        Ok(FriCommitPhaseRoundV1 {
          sibling: opening.sibling_values[0],
          beta,
          reduced_opening: None,
          opening_proof: opening.opening_proof.clone(),
        })
      })
      .collect::<Result<_>>()?;
    let mut query = TranscriptBoundPcsFriQueryV1 {
      pcs,
      fri: FriCommitPhaseQueryV1 {
        initial_log_height: pcs_instance
          .log_global_height
          .checked_sub(1)
          .ok_or_else(|| anyhow::anyhow!("FRI global height is zero"))?,
        query_index: u32::try_from(query_index)
          .map_err(|_| anyhow::anyhow!("FRI query index exceeds u32"))?,
        initial_folded: [0, 0],
        rounds,
        final_polynomial,
      },
    };
    let computation = compute_stage2_pcs_query(
      &prefix,
      &pcs_instance,
      &query,
      prefix_challenges,
    )?;
    query.fri.initial_folded = *computation
      .reduced_openings
      .get(&pcs_instance.log_global_height)
      .ok_or_else(|| {
        anyhow::anyhow!("typed PCS query has no initial bucket")
      })?;
    for (round, opening) in query.fri.rounds.iter_mut().enumerate() {
      let height = pcs_instance.log_global_height
        - 1
        - u8::try_from(round).expect("bounded FRI round index");
      opening.reduced_opening =
        computation.reduced_openings.get(&height).copied();
    }
    ensure_stage2_pcs_feeds_fri(&pcs_instance, &query, &computation)?;
    let fri_computation = compute_commit_phase(&query.fri)?;
    ensure_final_polynomial(&query.fri, &fri_computation)?;
    ensure_transcript_binds_fri_query(
      &fri_transcript,
      &fri_challenges,
      query_number,
      &query.fri,
    )?;
    queries.push(query);
  }

  Ok(Stage2PcsFriWitnessV1 { prefix, fri_transcript, pcs_instance, queries })
}

fn ensure_single_root(roots: &[[u8; 32]], label: &str) -> Result<()> {
  if roots.len() != 1 {
    bail!("{label} PCS commitment has {} roots; expected one", roots.len());
  }
  Ok(())
}

fn ensure_opened_matrix_shape(
  round: &[Vec<Vec<[u64; 2]>>],
  matrix: usize,
  points: usize,
  width: usize,
  label: &str,
) -> Result<()> {
  let opened = round.get(matrix).ok_or_else(|| {
    anyhow::anyhow!("{label} opened matrix {matrix} is missing")
  })?;
  if opened.len() != points {
    bail!(
      "{label} opened matrix {matrix} has {} points; expected {points}",
      opened.len()
    );
  }
  if opened.iter().any(|values| values.len() != width) {
    bail!("{label} opened matrix {matrix} has the wrong width");
  }
  Ok(())
}

fn stage2_pcs_matrix(
  log_degree: u8,
  log_blowup: u8,
  width: usize,
  opening_points: Vec<Stage2PcsOpeningPointV1>,
  opening_offset: &mut usize,
) -> Result<Stage2PcsMatrixV1> {
  let opened_values = Stage2TranscriptByteBindingV1::new(
    Stage2TranscriptSegmentV1::PcsOpening,
    *opening_offset,
  );
  *opening_offset = opening_points
    .len()
    .checked_mul(width)
    .and_then(|count| count.checked_mul(16))
    .and_then(|bytes| opening_offset.checked_add(bytes))
    .ok_or_else(|| anyhow::anyhow!("PCS opening transcript offset overflow"))?;
  Ok(Stage2PcsMatrixV1 {
    log_height: log_degree
      .checked_add(log_blowup)
      .ok_or_else(|| anyhow::anyhow!("PCS matrix height overflow"))?,
    width,
    opening_points,
    opened_values,
  })
}

struct Stage2PcsPointComputation {
  denominator: [u64; 2],
  quotients: Vec<[u64; 2]>,
}

struct Stage2PcsMatrixComputation {
  points: Vec<Stage2PcsPointComputation>,
}

struct Stage2PcsBatchComputation {
  root: [u8; 32],
  matrices: Vec<Stage2PcsMatrixComputation>,
}

struct Stage2PcsQueryComputation {
  batches: Vec<Stage2PcsBatchComputation>,
  reduced_openings: BTreeMap<u8, [u64; 2]>,
}

fn validate_stage2_pcs_instance(
  replay: &Stage2TranscriptReplayV1,
  instance: &Stage2PcsInstanceV1,
) -> Result<()> {
  validate_log_height(instance.log_global_height)?;
  if instance.log_blowup >= instance.log_global_height {
    bail!(
      "Stage 2 PCS blowup height {} must be below global height {}",
      instance.log_blowup,
      instance.log_global_height
    );
  }
  if instance.batches.is_empty() {
    bail!("Stage 2 PCS instance has no input batches");
  }

  let mut observed_global_height = 0u8;
  for (batch_index, batch) in instance.batches.iter().enumerate() {
    validate_transcript_binding(
      replay,
      batch.commitment,
      4,
      &format!("PCS batch {batch_index} commitment"),
    )?;
    if batch.matrices.is_empty() {
      bail!("Stage 2 PCS batch {batch_index} has no matrices");
    }
    let batch_max =
      batch.matrices.iter().map(|matrix| matrix.log_height).max().unwrap();
    observed_global_height = observed_global_height.max(batch_max);
    if batch_max > instance.log_global_height {
      bail!(
        "Stage 2 PCS batch {batch_index} height {batch_max} exceeds global height {}",
        instance.log_global_height
      );
    }
    for (matrix_index, matrix) in batch.matrices.iter().enumerate() {
      if matrix.log_height > batch_max {
        unreachable!("batch maximum was computed from all matrices");
      }
      validate_reduced_opening_width(matrix.width)?;
      for point in &matrix.opening_points {
        if let Stage2PcsOpeningPointV1::ZetaNext { log_degree } = point
          && usize::from(*log_degree) >= Val::TWO_ADIC_GENERATORS.len()
        {
          bail!(
            "Stage 2 PCS batch {batch_index} matrix {matrix_index} opening generator exceeds Goldilocks two-adicity"
          );
        }
      }
      let lane_count = matrix
        .opening_points
        .len()
        .checked_mul(matrix.width)
        .and_then(|count| count.checked_mul(2))
        .ok_or_else(|| {
          anyhow::anyhow!("Stage 2 PCS OOD binding length overflow")
        })?;
      validate_transcript_binding(
        replay,
        matrix.opened_values,
        lane_count,
        &format!("PCS batch {batch_index} matrix {matrix_index} OOD values"),
      )?;
    }
  }
  if observed_global_height != instance.log_global_height {
    bail!(
      "Stage 2 PCS global height is {}; tallest matrix has height {observed_global_height}",
      instance.log_global_height
    );
  }
  Ok(())
}

fn validate_stage2_pcs_query(
  replay: &Stage2TranscriptReplayV1,
  instance: &Stage2PcsInstanceV1,
  query: &TranscriptBoundPcsFriQueryV1,
) -> Result<()> {
  validate_stage2_pcs_instance(replay, instance)?;
  if query.pcs.batch_openings.len() != instance.batches.len() {
    bail!(
      "Stage 2 PCS query has {} batch openings; expected {}",
      query.pcs.batch_openings.len(),
      instance.batches.len()
    );
  }
  if query.fri.initial_log_height + 1 != instance.log_global_height {
    bail!("Stage 2 PCS and FRI global heights disagree");
  }
  if usize::from(instance.log_global_height - instance.log_blowup)
    != query.fri.rounds.len()
  {
    bail!("Stage 2 PCS and FRI final heights disagree");
  }
  for (batch_index, (batch, opening)) in
    instance.batches.iter().zip(&query.pcs.batch_openings).enumerate()
  {
    if opening.opened_rows.len() != batch.matrices.len() {
      bail!(
        "Stage 2 PCS batch {batch_index} has {} opened rows; expected {}",
        opening.opened_rows.len(),
        batch.matrices.len()
      );
    }
    let batch_max =
      batch.matrices.iter().map(|matrix| matrix.log_height).max().unwrap();
    if opening.opening_proof.len() != usize::from(batch_max) {
      bail!(
        "Stage 2 PCS batch {batch_index} path has {} siblings; expected {batch_max}",
        opening.opening_proof.len()
      );
    }
    for (matrix_index, (matrix, row)) in
      batch.matrices.iter().zip(&opening.opened_rows).enumerate()
    {
      if row.len() != matrix.width {
        bail!(
          "Stage 2 PCS batch {batch_index} matrix {matrix_index} row width is {}; expected {}",
          row.len(),
          matrix.width
        );
      }
      for (column, &value) in row.iter().enumerate() {
        if value >= GOLDILOCKS_MODULUS {
          bail!(
            "Stage 2 PCS batch {batch_index} matrix {matrix_index} column {column} is not canonical Goldilocks"
          );
        }
      }
    }
  }
  Ok(())
}

fn compute_stage2_pcs_query(
  replay: &Stage2TranscriptReplayV1,
  instance: &Stage2PcsInstanceV1,
  query: &TranscriptBoundPcsFriQueryV1,
  challenges: crate::Stage2TranscriptChallengesV1,
) -> Result<Stage2PcsQueryComputation> {
  validate_stage2_pcs_query(replay, instance, query)?;
  let alpha = native_extension(challenges.pcs_alpha);
  let zeta = native_extension(challenges.zeta);
  let mut buckets: BTreeMap<u8, (ExtVal, ExtVal)> = instance
    .batches
    .iter()
    .flat_map(|batch| batch.matrices.iter().map(|matrix| matrix.log_height))
    .map(|height| (height, (ExtVal::ONE, ExtVal::ZERO)))
    .collect();
  let mut batches = Vec::with_capacity(instance.batches.len());

  for (batch, opening) in instance.batches.iter().zip(&query.pcs.batch_openings)
  {
    let root = native_stage2_pcs_batch_root(
      instance.log_global_height,
      query.fri.query_index,
      batch,
      opening,
    );
    if root != read_bound_digest(replay, batch.commitment)? {
      bail!(
        "Stage 2 PCS input opening does not authenticate to its transcript commitment"
      );
    }
    let mut matrices = Vec::with_capacity(batch.matrices.len());
    for (matrix_index, (matrix, row)) in
      batch.matrices.iter().zip(&opening.opened_rows).enumerate()
    {
      let local_index = query.fri.query_index
        >> (instance.log_global_height - matrix.log_height);
      let x = ExtVal::new([
        Val::from_u64(pcs_query_point(matrix.log_height, local_index)),
        Val::ZERO,
      ]);
      let opened_at_z = read_bound_extensions(
        replay,
        matrix.opened_values,
        matrix.opening_points.len() * matrix.width,
      )?;
      let mut points = Vec::with_capacity(matrix.opening_points.len());
      for (point_index, point_kind) in matrix.opening_points.iter().enumerate()
      {
        let point = native_stage2_pcs_point(zeta, *point_kind);
        let denominator = point - x;
        if denominator == ExtVal::ZERO {
          bail!(
            "Stage 2 PCS batch matrix {matrix_index} opening point {point_index} equals its query point"
          );
        }
        let values = &opened_at_z
          [point_index * matrix.width..(point_index + 1) * matrix.width];
        let mut quotients = Vec::with_capacity(matrix.width);
        let (alpha_power, accumulator) = buckets
          .get_mut(&matrix.log_height)
          .expect("one PCS bucket per matrix height");
        for (&p_at_x, &p_at_z) in row.iter().zip(values) {
          let p_at_x = ExtVal::new([Val::from_u64(p_at_x), Val::ZERO]);
          let quotient = (native_extension(p_at_z) - p_at_x) / denominator;
          *accumulator += *alpha_power * quotient;
          *alpha_power *= alpha;
          quotients.push(extension_words(quotient));
        }
        points.push(Stage2PcsPointComputation {
          denominator: extension_words(denominator),
          quotients,
        });
      }
      matrices.push(Stage2PcsMatrixComputation { points });
    }
    batches.push(Stage2PcsBatchComputation { root, matrices });
  }

  let reduced_openings = buckets
    .into_iter()
    .map(|(height, (_, accumulator))| (height, extension_words(accumulator)))
    .collect();
  Ok(Stage2PcsQueryComputation { batches, reduced_openings })
}

fn ensure_stage2_pcs_feeds_fri(
  instance: &Stage2PcsInstanceV1,
  query: &TranscriptBoundPcsFriQueryV1,
  computation: &Stage2PcsQueryComputation,
) -> Result<()> {
  let initial =
    computation.reduced_openings.get(&instance.log_global_height).ok_or_else(
      || anyhow::anyhow!("missing initial Stage 2 reduced opening"),
    )?;
  if query.fri.initial_folded != *initial {
    bail!("FRI initial value is not the authenticated PCS reduced opening");
  }
  for (round, fri_round) in query.fri.rounds.iter().enumerate() {
    let height = instance.log_global_height
      - 1
      - u8::try_from(round).expect("bounded FRI round index");
    let expected = computation.reduced_openings.get(&height).copied();
    if fri_round.reduced_opening != expected {
      bail!(
        "FRI round {round} reduced-opening schedule disagrees with PCS buckets"
      );
    }
  }
  let covered_minimum = instance.log_global_height
    - u8::try_from(query.fri.rounds.len()).expect("bounded FRI round count");
  if computation.reduced_openings.keys().any(|&height| {
    height != instance.log_global_height && height < covered_minimum
  }) {
    bail!("PCS reduced opening remains below the FRI final height");
  }
  Ok(())
}

fn native_stage2_pcs_point(
  zeta: ExtVal,
  point: Stage2PcsOpeningPointV1,
) -> ExtVal {
  match point {
    Stage2PcsOpeningPointV1::Zeta => zeta,
    Stage2PcsOpeningPointV1::ZetaNext { log_degree } => {
      let generator = Val::TWO_ADIC_GENERATORS[usize::from(log_degree)];
      zeta * ExtVal::new([generator, Val::ZERO])
    },
  }
}

fn native_stage2_pcs_batch_root(
  log_global_height: u8,
  query_index: u32,
  batch: &Stage2PcsBatchV1,
  opening: &Stage2PcsBatchOpeningV1,
) -> [u8; 32] {
  let log_batch_height =
    batch.matrices.iter().map(|matrix| matrix.log_height).max().unwrap();
  let local_index = query_index >> (log_global_height - log_batch_height);
  let mut current = native_stage2_pcs_leaf(batch, opening, log_batch_height);
  for (level, sibling) in opening.opening_proof.iter().enumerate() {
    let mut message = [0u8; 64];
    let (left, right) = if (local_index >> level) & 1 == 0 {
      (&current, sibling)
    } else {
      (sibling, &current)
    };
    message[..32].copy_from_slice(left);
    message[32..].copy_from_slice(right);
    current = *native_blake3::hash(&message).as_bytes();
    let next_height = log_batch_height
      - 1
      - u8::try_from(level).expect("bounded Merkle path level");
    if batch.matrices.iter().any(|matrix| matrix.log_height == next_height) {
      let injected = native_stage2_pcs_leaf(batch, opening, next_height);
      let mut message = [0u8; 64];
      message[..32].copy_from_slice(&current);
      message[32..].copy_from_slice(&injected);
      current = *native_blake3::hash(&message).as_bytes();
    }
  }
  current
}

fn native_stage2_pcs_leaf(
  batch: &Stage2PcsBatchV1,
  opening: &Stage2PcsBatchOpeningV1,
  log_height: u8,
) -> [u8; 32] {
  let mut bytes = Vec::new();
  for (matrix, row) in batch.matrices.iter().zip(&opening.opened_rows) {
    if matrix.log_height == log_height {
      for &value in row {
        bytes.extend_from_slice(&value.to_le_bytes());
      }
    }
  }
  *native_blake3::hash(&bytes).as_bytes()
}

fn validate_transcript_binding(
  replay: &Stage2TranscriptReplayV1,
  binding: Stage2TranscriptByteBindingV1,
  lane_count: usize,
  label: &str,
) -> Result<()> {
  let bytes = transcript_segment(replay, binding.segment);
  let start = binding.byte_offset;
  let end = lane_count
    .checked_mul(8)
    .and_then(|length| start.checked_add(length))
    .ok_or_else(|| anyhow::anyhow!("{label} byte range overflow"))?;
  if end > bytes.len() {
    bail!(
      "{label} binding ends at byte {end}; transcript segment has {} bytes",
      bytes.len()
    );
  }
  Ok(())
}

fn read_bound_digest(
  replay: &Stage2TranscriptReplayV1,
  binding: Stage2TranscriptByteBindingV1,
) -> Result<[u8; 32]> {
  validate_transcript_binding(replay, binding, 4, "PCS commitment")?;
  let bytes = transcript_segment(replay, binding.segment);
  let start = binding.byte_offset;
  Ok(bytes[start..start + 32].try_into().unwrap())
}

fn read_bound_extensions(
  replay: &Stage2TranscriptReplayV1,
  binding: Stage2TranscriptByteBindingV1,
  count: usize,
) -> Result<Vec<[u64; 2]>> {
  validate_transcript_binding(replay, binding, count * 2, "PCS OOD opening")?;
  let bytes = transcript_segment(replay, binding.segment);
  let start = binding.byte_offset;
  (0..count)
    .map(|index| {
      let offset = start + index * 16;
      let value = [
        u64::from_le_bytes(bytes[offset..offset + 8].try_into().unwrap()),
        u64::from_le_bytes(bytes[offset + 8..offset + 16].try_into().unwrap()),
      ];
      validate_extension(value, "transcript-bound PCS OOD value")?;
      Ok(value)
    })
    .collect()
}

fn transcript_segment(
  replay: &Stage2TranscriptReplayV1,
  segment: Stage2TranscriptSegmentV1,
) -> &[u8] {
  match segment {
    Stage2TranscriptSegmentV1::Initial => &replay.initial_observations,
    Stage2TranscriptSegmentV1::Stage2AndAccumulator => {
      &replay.stage2_and_accumulator_observations
    },
    Stage2TranscriptSegmentV1::QuotientCommitment => {
      &replay.quotient_commitment_observations
    },
    Stage2TranscriptSegmentV1::PcsOpening => &replay.pcs_opening_observations,
  }
}

struct PcsReductionComputation {
  denominator: [u64; 2],
  quotients: Vec<[u64; 2]>,
  accumulator: [u64; 2],
  alpha_power: [u64; 2],
  root: [u8; 32],
}

fn compute_pcs_reduction(
  opening: &PcsReducedOpeningV1,
) -> Result<PcsReductionComputation> {
  validate_pcs_reduction(opening)?;
  let x = ExtVal::new([
    Val::from_u64(pcs_query_point(opening.log_height, opening.query_index)),
    Val::ZERO,
  ]);
  let zeta = native_extension(opening.zeta);
  let denominator = zeta - x;
  if denominator == ExtVal::ZERO {
    bail!("PCS reduced opening has zeta equal to the query-domain point");
  }
  let alpha = native_extension(opening.alpha);
  let mut alpha_power = native_extension(opening.initial_alpha_power);
  let mut accumulator = native_extension(opening.initial_accumulator);
  let mut quotients = Vec::with_capacity(opening.opened_values.len());
  for (&px, &pz) in opening.opened_values.iter().zip(&opening.opened_at_z) {
    let px = ExtVal::new([Val::from_u64(px), Val::ZERO]);
    let pz = native_extension(pz);
    let quotient = (pz - px) / denominator;
    accumulator += alpha_power * quotient;
    alpha_power *= alpha;
    quotients.push(extension_words(quotient));
  }
  Ok(PcsReductionComputation {
    denominator: extension_words(denominator),
    quotients,
    accumulator: extension_words(accumulator),
    alpha_power: extension_words(alpha_power),
    root: native_pcs_row_root(opening),
  })
}

fn pcs_reduction_relation_inputs(
  opening: &PcsReducedOpeningV1,
  computation: &PcsReductionComputation,
) -> Vec<F128> {
  let packed_iv = pack8(&IV);
  let width = opening.opened_values.len();
  let mut inputs = Vec::with_capacity(
    9 + usize::from(opening.log_height)
      + width.div_ceil(2)
      + width
      + 4
      + usize::from(opening.log_height) * 3
      + 1
      + width
      + 2,
  );
  inputs.extend_from_slice(&[F128::ZERO, F128::ZERO, F128::ZERO]);
  inputs.extend_from_slice(&packed_iv);
  inputs.extend(hash_trace(width * 8).rows.iter().map(
    |&(_cv, _message, counter, block_len, flags)| {
      pack_params(counter, block_len, flags)
    },
  ));
  inputs.push(pack_params(0, 64, CHUNK_START | CHUNK_END | ROOT));
  inputs.push(F128::new(1, 0));
  inputs.push(F128::new(7, 0));
  inputs.extend(
    pcs_x_factors(opening.log_height)
      .into_iter()
      .map(|factor| F128::new(factor, 0)),
  );
  for pair in opening.opened_values.chunks(2) {
    inputs.push(F128::new(pair[0], pair.get(1).copied().unwrap_or(0)));
  }
  inputs.extend(opening.opened_at_z.iter().copied().map(pack_extension));
  inputs.push(pack_extension(opening.zeta));
  inputs.push(pack_extension(opening.alpha));
  inputs.push(pack_extension(opening.initial_alpha_power));
  inputs.push(pack_extension(opening.initial_accumulator));
  inputs.extend(
    (0..opening.log_height)
      .map(|bit| F128::new(u64::from((opening.query_index >> bit) & 1), 0)),
  );
  for sibling in &opening.opening_proof {
    inputs.extend_from_slice(&pack_digest(sibling));
  }
  inputs.push(pack_extension(computation.denominator));
  inputs.extend(computation.quotients.iter().copied().map(pack_extension));
  inputs.push(pack_extension(computation.accumulator));
  inputs.push(pack_extension(computation.alpha_power));
  inputs
}

fn pcs_reduction_relation_public(
  opening: &PcsReducedOpeningV1,
  computation: &PcsReductionComputation,
) -> Vec<F128> {
  let mut public = pcs_reduction_relation_inputs(opening, computation);
  public.extend_from_slice(&pack_digest(&computation.root));
  public
}

fn validate_pcs_reduction(opening: &PcsReducedOpeningV1) -> Result<()> {
  validate_log_height(opening.log_height)?;
  validate_reduced_opening_width(opening.opened_values.len())?;
  if opening.opened_at_z.len() != opening.opened_values.len() {
    bail!(
      "PCS reduced opening has {} base values but {} OOD values",
      opening.opened_values.len(),
      opening.opened_at_z.len()
    );
  }
  if opening.opening_proof.len() != usize::from(opening.log_height) {
    bail!(
      "PCS reduced opening has path depth {}; expected {}",
      opening.opening_proof.len(),
      opening.log_height
    );
  }
  if u64::from(opening.query_index) >= 1u64 << opening.log_height {
    bail!(
      "PCS query index {} does not fit {} bits",
      opening.query_index,
      opening.log_height
    );
  }
  for (column, &value) in opening.opened_values.iter().enumerate() {
    if value >= GOLDILOCKS_MODULUS {
      bail!("PCS opened value {column} is not canonical Goldilocks");
    }
  }
  for (column, &value) in opening.opened_at_z.iter().enumerate() {
    validate_extension(value, &format!("PCS OOD value {column}"))?;
  }
  for (value, name) in [
    (opening.zeta, "PCS zeta"),
    (opening.alpha, "PCS alpha"),
    (opening.initial_alpha_power, "PCS initial alpha power"),
    (opening.initial_accumulator, "PCS initial accumulator"),
  ] {
    validate_extension(value, name)?;
  }
  Ok(())
}

fn validate_reduced_opening_width(width: usize) -> Result<()> {
  if !(1..=MAX_REDUCED_OPENING_WIDTH).contains(&width) {
    bail!(
      "PCS reduced-opening width {width}; expected 1..={MAX_REDUCED_OPENING_WIDTH}"
    );
  }
  Ok(())
}

fn pcs_reduction_nu(opening: &PcsReducedOpeningV1) -> usize {
  let width = opening.opened_values.len();
  let height = usize::from(opening.log_height);
  // This deliberately over-approximates the busiest shared slot. It keeps the
  // circuit builder fail-closed while supporting tree-hashed rows wider than a
  // single BLAKE3 block.
  let row_bound = width
    .saturating_mul(128)
    .saturating_add(height.saturating_mul(64))
    .saturating_add(hash_trace(width * 8).rows.len())
    .max(1);
  usize::try_from(row_bound.next_power_of_two().ilog2()).unwrap().max(NU)
}

fn native_pcs_row_root(opening: &PcsReducedOpeningV1) -> [u8; 32] {
  let mut leaf = Vec::with_capacity(opening.opened_values.len() * 8);
  for value in &opening.opened_values {
    leaf.extend_from_slice(&value.to_le_bytes());
  }
  let mut current = *native_blake3::hash(&leaf).as_bytes();
  for (level, sibling) in opening.opening_proof.iter().enumerate() {
    let mut block = [0u8; 64];
    let (left, right) = if (opening.query_index >> level) & 1 == 0 {
      (&current, sibling)
    } else {
      (sibling, &current)
    };
    block[..32].copy_from_slice(left);
    block[32..].copy_from_slice(right);
    current = *native_blake3::hash(&block).as_bytes();
  }
  current
}

fn pcs_query_point(log_height: u8, query_index: u32) -> u64 {
  pcs_x_factors(log_height)
    .into_iter()
    .enumerate()
    .filter(|(bit, _)| (query_index >> bit) & 1 == 1)
    .fold(7, |point, (_, factor)| goldilocks_mul(point, factor))
}

fn twiddle_factors(log_height: u8) -> Vec<u64> {
  reversed_exponent_factors(log_height + 1, log_height)
}

fn pcs_x_factors(log_height: u8) -> Vec<u64> {
  reversed_exponent_factors(log_height, log_height)
}

fn reversed_exponent_factors(generator_log: u8, exponent_bits: u8) -> Vec<u64> {
  let generator =
    Val::TWO_ADIC_GENERATORS[usize::from(generator_log)].as_canonical_u64();
  (0..exponent_bits)
    .map(|bit| {
      let squarings = usize::from(exponent_bits - 1 - bit);
      (0..squarings).fold(generator, |value, _| goldilocks_mul(value, value))
    })
    .collect()
}

fn subgroup_point(query: &FriFoldQueryV1) -> u64 {
  let index = query.query_index >> 1;
  twiddle_factors(query.log_height)
    .into_iter()
    .enumerate()
    .filter(|(bit, _)| (index >> bit) & 1 == 1)
    .fold(1, |point, (_, factor)| goldilocks_mul(point, factor))
}

fn ordered_evaluations(query: &FriFoldQueryV1) -> ([u64; 2], [u64; 2]) {
  if query.query_index & 1 == 0 {
    (query.folded, query.sibling)
  } else {
    (query.sibling, query.folded)
  }
}

fn native_fold(query: &FriFoldQueryV1) -> [u64; 2] {
  let (e0_words, e1_words) = ordered_evaluations(query);
  let e0 = native_extension(e0_words);
  let e1 = native_extension(e1_words);
  let beta = native_extension(query.beta);
  let s = Val::from_u64(subgroup_point(query));
  let two = Val::ONE + Val::ONE;
  let half = ExtVal::new([two, Val::ZERO]);
  let two_s = ExtVal::new([two * s, Val::ZERO]);
  extension_words((e0 + e1) / half + beta * ((e0 - e1) / two_s))
}

fn native_root(query: &FriFoldQueryV1) -> [u8; 32] {
  let (e0, e1) = ordered_evaluations(query);
  let mut leaf = [0u8; 32];
  for (chunk, word) in
    leaf.as_chunks_mut::<8>().0.iter_mut().zip([e0[0], e0[1], e1[0], e1[1]])
  {
    chunk.copy_from_slice(&word.to_le_bytes());
  }
  let mut current = *native_blake3::hash(&leaf).as_bytes();
  for (level, sibling) in query.opening_proof.iter().enumerate() {
    let mut block = [0u8; 64];
    let direction = (query.query_index >> (level + 1)) & 1;
    let (left, right) =
      if direction == 0 { (&current, sibling) } else { (sibling, &current) };
    block[..32].copy_from_slice(left);
    block[32..].copy_from_slice(right);
    current = *native_blake3::hash(&block).as_bytes();
  }
  current
}

fn native_extension(value: [u64; 2]) -> ExtVal {
  ExtVal::new(value.map(Val::from_u64))
}

fn extension_words(value: ExtVal) -> [u64; 2] {
  let coefficients: &[Val] = value.as_basis_coefficients_slice();
  [coefficients[0].as_canonical_u64(), coefficients[1].as_canonical_u64()]
}

fn pack_extension(value: [u64; 2]) -> F128 {
  F128::new(value[0], value[1])
}

fn pack_digest(digest: &[u8; 32]) -> [F128; 2] {
  [pack_bytes(&digest[..16]), pack_bytes(&digest[16..])]
}

fn validate_query(query: &FriFoldQueryV1) -> Result<()> {
  validate_log_height(query.log_height)?;
  if query.opening_proof.len() != usize::from(query.log_height) {
    bail!(
      "FRI-fold opening has depth {}; expected {} for cap height zero",
      query.opening_proof.len(),
      query.log_height
    );
  }
  if u64::from(query.query_index) >= 1u64 << (query.log_height + 1) {
    bail!(
      "FRI query index {} does not fit {} bits",
      query.query_index,
      query.log_height + 1
    );
  }
  validate_extension(query.folded, "folded evaluation")?;
  validate_extension(query.sibling, "sibling evaluation")?;
  validate_extension(query.beta, "FRI challenge")?;
  Ok(())
}

fn validate_log_height(log_height: u8) -> Result<()> {
  if !(MIN_LOG_HEIGHT..=MAX_LOG_HEIGHT).contains(&log_height) {
    bail!(
      "FRI fold log height {log_height}; expected {MIN_LOG_HEIGHT}..={MAX_LOG_HEIGHT}"
    );
  }
  Ok(())
}

fn validate_extension(value: [u64; 2], name: &str) -> Result<()> {
  for (coordinate, word) in value.into_iter().enumerate() {
    if word >= GOLDILOCKS_MODULUS {
      bail!("{name} coordinate {coordinate} is not canonical Goldilocks");
    }
  }
  Ok(())
}

fn encode_extension(bytes: &mut Vec<u8>, value: [u64; 2]) {
  bytes.extend_from_slice(&value[0].to_le_bytes());
  bytes.extend_from_slice(&value[1].to_le_bytes());
}

fn decode_extension(bytes: &[u8]) -> [u64; 2] {
  [
    u64::from_le_bytes(bytes[..8].try_into().unwrap()),
    u64::from_le_bytes(bytes[8..16].try_into().unwrap()),
  ]
}

fn sort_and_validate_slots<T>(slots: &mut [(usize, T)]) -> Result<()> {
  slots.sort_by_key(|(slot, _)| *slot);
  for (expected, (observed, _)) in slots.iter().enumerate() {
    if *observed != expected {
      bail!(
        "Flock FRI-fold table registry is incomplete: expected slot {expected}, observed {observed}"
      );
    }
  }
  Ok(())
}

fn encode_bundle(bundle: &FriFoldProofBundle) -> Result<Vec<u8>> {
  bincode::DefaultOptions::new()
    .with_fixint_encoding()
    .serialize(bundle)
    .context("encode Flock FRI-fold conformance proof bundle")
}

fn decode_bundle(bytes: &[u8]) -> Result<FriFoldProofBundle> {
  bincode::DefaultOptions::new()
    .with_fixint_encoding()
    .with_limit(MAX_BUNDLE_BYTES as u64)
    .reject_trailing_bytes()
    .deserialize(bytes)
    .context("invalid Flock FRI-fold conformance proof bundle")
}

#[cfg(test)]
mod tests {
  use aiur::vk_codec::aiur_config_system_to_bytes;
  use ix_terminal::validate_and_expand_root_inputs;
  use multi_stark::{
    expr::Expr,
    lookup::{Lookup, WidthBinding},
    p3_matrix::dense::RowMajorMatrix,
    system::{CircuitInputs, System, SystemWitness},
    types::{CommitmentParameters, GoldilocksBlake3Config},
  };

  use super::*;

  fn prepared_stage2_pcs_fixture()
  -> (ValidatedStage2RootV1, FriParameters, Vec<u8>, Vec<u8>, Vec<u8>) {
    const CLAIM_WORDS: usize = 18;
    const CLAIM_CIRCUIT_WIDTH: usize = CLAIM_WORDS + 2;
    const TALL_HEIGHT: usize = 8;
    const SHORT_HEIGHT: usize = 4;

    let commitment = CommitmentParameters { log_blowup: 1, cap_height: 0 };
    let fri = FriParameters {
      log_final_poly_len: 0,
      max_log_arity: 1,
      num_queries: 2,
      commit_proof_of_work_bits: 0,
      query_proof_of_work_bits: 0,
    };
    let claim: Vec<_> = (0..CLAIM_WORDS)
      .map(|word| Val::from_u64(0x100 + u64::try_from(word).unwrap()))
      .collect();
    let claim_lookup = Lookup::pull(
      Expr::main(0),
      (1..=CLAIM_WORDS)
        .map(|column| Expr::main(u32::try_from(column).unwrap()))
        .collect(),
    );
    let multiplicity = Expr::main(0);
    let multiplicity_is_boolean =
      multiplicity.clone() * (multiplicity - Expr::constant(Val::ONE));
    let preprocessed_matches =
      Expr::main(u32::try_from(CLAIM_CIRCUIT_WIDTH - 1).unwrap())
        - Expr::preprocessed(0);
    let short_first =
      Expr::IsFirstRow * (Expr::main(0) - Expr::constant(Val::from_u64(7)));
    let short_transition = Expr::IsTransition
      * (Expr::main_next(0) - Expr::main(0) - Expr::constant(Val::from_u64(9)));
    let config = GoldilocksBlake3Config::new(commitment, fri)
      .with_width_binding(WidthBinding::ByConstruction);
    let (system, key) = System::new(
      config,
      [
        CircuitInputs { main_width: 1, ..Default::default() },
        CircuitInputs {
          main_width: CLAIM_CIRCUIT_WIDTH,
          preprocessed: Some(RowMajorMatrix::new(
            (0..TALL_HEIGHT)
              .map(|row| Val::from_u64(5 * u64::try_from(row).unwrap() + 3))
              .collect(),
            1,
          )),
          constraints: vec![multiplicity_is_boolean, preprocessed_matches],
          lookups: vec![claim_lookup],
          ..Default::default()
        },
        CircuitInputs {
          main_width: 3,
          constraints: vec![short_first, short_transition],
          ..Default::default()
        },
      ],
    );

    let mut tall_values = vec![Val::ZERO; TALL_HEIGHT * CLAIM_CIRCUIT_WIDTH];
    tall_values[0] = Val::ONE;
    tall_values[1..=CLAIM_WORDS].copy_from_slice(&claim);
    for row in 0..TALL_HEIGHT {
      tall_values[row * CLAIM_CIRCUIT_WIDTH + CLAIM_CIRCUIT_WIDTH - 1] =
        Val::from_u64(5 * u64::try_from(row).unwrap() + 3);
    }
    let tall_trace = RowMajorMatrix::new(tall_values, CLAIM_CIRCUIT_WIDTH);
    let short_trace = RowMajorMatrix::new(
      (0..SHORT_HEIGHT * 3)
        .map(|word| Val::from_u64(3 * u64::try_from(word).unwrap() + 7))
        .collect(),
      3,
    );
    let proof = system.prove(
      &key,
      &claim,
      SystemWitness::from_stage_1(
        vec![RowMajorMatrix::new(Vec::new(), 1), tall_trace, short_trace],
        &system,
      ),
    );
    system.verify(&claim, &proof).expect("fixture proof must verify");

    let vk_bytes = aiur_config_system_to_bytes(&system, commitment, fri);
    let claim_bytes: Vec<_> = claim
      .iter()
      .flat_map(|word| word.as_canonical_u64().to_le_bytes())
      .collect();
    let proof_bytes = proof.to_bytes().expect("encode fixture proof");
    let prepared = validate_and_expand_root_inputs(
      &vk_bytes,
      &claim_bytes,
      &proof_bytes,
      &fri,
    )
    .expect("validate and expand fixture proof");
    (prepared, fri, vk_bytes, claim_bytes, proof_bytes)
  }

  fn fixture() -> FriFoldQueryV1 {
    FriFoldQueryV1 {
      log_height: 4,
      query_index: 0b1_0110,
      folded: [0x1234_5678_9abc_def0, 0x0fed_cba9_8765_4321],
      sibling: [17, GOLDILOCKS_MODULUS - 9],
      beta: [0x1111_2222_3333_4444, 0x5555_6666_7777_8888],
      opening_proof: (0..4u8)
        .map(|level| {
          *native_blake3::hash(&[b'f', b'r', b'i', level]).as_bytes()
        })
        .collect(),
    }
  }

  fn commit_phase_fixture() -> FriCommitPhaseQueryV1 {
    let mut query = FriCommitPhaseQueryV1 {
      initial_log_height: 4,
      query_index: 0b1_0110,
      initial_folded: [0x1234_5678_9abc_def0, 0x0fed_cba9_8765_4321],
      rounds: (0..3u8)
        .map(|round| {
          let depth = 4 - usize::from(round);
          FriCommitPhaseRoundV1 {
            sibling: [
              17 + u64::from(round),
              GOLDILOCKS_MODULUS - 9 - u64::from(round),
            ],
            beta: [
              0x1111_2222_3333_4444 + u64::from(round),
              0x5555_6666_7777_8888 + u64::from(round),
            ],
            reduced_opening: (round != 1)
              .then_some([100 + u64::from(round), 200 + u64::from(round)]),
            opening_proof: (0..depth)
              .map(|level| {
                *native_blake3::hash(&[
                  b'q',
                  round,
                  u8::try_from(level).unwrap(),
                ])
                .as_bytes()
              })
              .collect(),
          }
        })
        .collect(),
      final_polynomial: [0, 0],
    };
    let computation = compute_commit_phase(&query).unwrap();
    query.final_polynomial = *computation.results.last().unwrap();
    query
  }

  fn pcs_reduction_fixture() -> PcsReducedOpeningV1 {
    PcsReducedOpeningV1 {
      log_height: 4,
      query_index: 0b1010,
      opened_values: vec![3, 5, 8, 13, 21],
      opened_at_z: vec![
        [34, 55],
        [89, 144],
        [233, 377],
        [610, 987],
        [1597, 2584],
      ],
      zeta: [0x1020_3040_5060_7080, 0x1122_3344_5566_7788],
      alpha: [0x3141_5926_5358_9793, 0x2384_6264_3383_2795],
      initial_alpha_power: [7, 11],
      initial_accumulator: [17, 19],
      opening_proof: (0..4u8)
        .map(|level| {
          *native_blake3::hash(&[b'p', b'c', b's', level]).as_bytes()
        })
        .collect(),
    }
  }

  fn wide_pcs_reduction_fixture() -> PcsReducedOpeningV1 {
    let mut opening = pcs_reduction_fixture();
    opening.opened_values = (0..129u64).map(|column| 3 * column + 5).collect();
    opening.opened_at_z =
      (0..129u64).map(|column| [7 * column + 11, 13 * column + 17]).collect();
    opening
  }

  fn transcript_replay_fixture() -> Stage2TranscriptReplayV1 {
    let mut initial_observations = b"multi-stark/v0".to_vec();
    for value in 0..19u64 {
      initial_observations.extend_from_slice(&(value * 17 + 3).to_le_bytes());
    }
    initial_observations.extend_from_slice(&[0xa5, 0x5a, 0x11]);
    Stage2TranscriptReplayV1 {
      initial_observations,
      stage2_and_accumulator_observations: (0..79u8)
        .map(|value| value.wrapping_mul(29))
        .collect(),
      quotient_commitment_observations: (0..32u8)
        .map(|value| value ^ 0x6d)
        .collect(),
      pcs_opening_observations: (0..117u8)
        .map(|value| value.wrapping_mul(7).wrapping_add(1))
        .collect(),
    }
  }

  fn transcript_bound_pcs_fixture()
  -> (Stage2TranscriptReplayV1, PcsReducedOpeningV1) {
    let replay = transcript_replay_fixture();
    let challenges = replay.challenges().unwrap();
    let mut opening = pcs_reduction_fixture();
    opening.zeta = challenges.zeta;
    opening.alpha = challenges.pcs_alpha;
    (replay, opening)
  }

  fn zero_extension_tree(log_height: u8) -> (Vec<[u8; 32]>, [u8; 32]) {
    let mut current = *native_blake3::hash(&[0u8; 32]).as_bytes();
    let mut path = Vec::with_capacity(usize::from(log_height));
    for _ in 0..log_height {
      path.push(current);
      let mut message = [0u8; 64];
      message[..32].copy_from_slice(&current);
      message[32..].copy_from_slice(&current);
      current = *native_blake3::hash(&message).as_bytes();
    }
    (path, current)
  }

  fn transcript_bound_fri_fixture_with_round_count(
    round_count: usize,
  ) -> (
    Stage2TranscriptReplayV1,
    Stage2FriTranscriptReplayV1,
    FriCommitPhaseQueryV1,
  ) {
    let prefix = transcript_replay_fixture();
    // Model the production binary schedule with logBlowup=2 and a constant
    // final polynomial: global height = rounds + 2, while the first folded
    // height is global height - 1.
    assert!((1..=30).contains(&round_count));
    let initial_log_height = u8::try_from(round_count + 1).unwrap();
    let trees: Vec<_> = (0..round_count)
      .map(|round| {
        zero_extension_tree(initial_log_height - u8::try_from(round).unwrap())
      })
      .collect();
    let mut fri_transcript = Stage2FriTranscriptReplayV1 {
      commit_phase_commitments: trees
        .iter()
        .map(|(_, root)| vec![*root])
        .collect(),
      commit_pow_witnesses: vec![0; round_count],
      final_polynomial: vec![[0, 0]],
      log_arities: vec![1; round_count],
      query_pow_witness: 0,
      commit_pow_bits: 0,
      query_pow_bits: 4,
      num_queries: 5,
      query_index_bits: initial_log_height + 1,
    };
    let challenges = (0..1_000u64)
      .find_map(|witness| {
        fri_transcript.query_pow_witness = witness;
        fri_transcript.challenges(&prefix).ok()
      })
      .expect("small query-PoW fixture has a witness");
    let query = FriCommitPhaseQueryV1 {
      initial_log_height,
      query_index: u32::try_from(challenges.query_indices[0]).unwrap(),
      initial_folded: [0, 0],
      rounds: trees
        .into_iter()
        .zip(challenges.betas)
        .map(|((opening_proof, _), beta)| FriCommitPhaseRoundV1 {
          sibling: [0, 0],
          beta,
          reduced_opening: None,
          opening_proof,
        })
        .collect(),
      final_polynomial: [0, 0],
    };
    (prefix, fri_transcript, query)
  }

  fn transcript_bound_fri_fixture() -> (
    Stage2TranscriptReplayV1,
    Stage2FriTranscriptReplayV1,
    FriCommitPhaseQueryV1,
  ) {
    transcript_bound_fri_fixture_with_round_count(3)
  }

  fn transcript_bound_fri_all_queries_fixture() -> (
    Stage2TranscriptReplayV1,
    Stage2FriTranscriptReplayV1,
    Vec<FriCommitPhaseQueryV1>,
  ) {
    let (prefix, mut fri_transcript, template) = transcript_bound_fri_fixture();
    fri_transcript.num_queries = 2;
    let challenges = fri_transcript.challenges(&prefix).unwrap();
    let queries = challenges
      .query_indices
      .iter()
      .map(|&query_index| {
        let mut query = template.clone();
        query.query_index = u32::try_from(query_index).unwrap();
        query
      })
      .collect();
    (prefix, fri_transcript, queries)
  }

  fn linear_base_value(slope: u64, intercept: u64, x: u64) -> u64 {
    (Val::from_u64(slope) * Val::from_u64(x) + Val::from_u64(intercept))
      .as_canonical_u64()
  }

  fn linear_extension_value(slope: u64, intercept: u64, x: ExtVal) -> [u64; 2] {
    extension_words(
      ExtVal::new([Val::from_u64(slope), Val::ZERO]) * x
        + ExtVal::new([Val::from_u64(intercept), Val::ZERO]),
    )
  }

  fn hash_base_rows(rows: &[&[u64]]) -> [u8; 32] {
    let mut bytes = Vec::new();
    for row in rows {
      for &value in *row {
        bytes.extend_from_slice(&value.to_le_bytes());
      }
    }
    *native_blake3::hash(&bytes).as_bytes()
  }

  fn hash_children(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
    let mut bytes = [0u8; 64];
    bytes[..32].copy_from_slice(left);
    bytes[32..].copy_from_slice(right);
    *native_blake3::hash(&bytes).as_bytes()
  }

  fn multiheight_batch_root_and_path(
    matrix_heights: &[u8],
    matrix_rows: &[Vec<Vec<u64>>],
    query_index: usize,
  ) -> ([u8; 32], Vec<[u8; 32]>) {
    let log_max = *matrix_heights.iter().max().unwrap();
    let leaf_layer = |height: u8| {
      (0..1usize << height)
        .map(|row_index| {
          let rows: Vec<_> = matrix_heights
            .iter()
            .zip(matrix_rows)
            .filter(|(matrix_height, _)| **matrix_height == height)
            .map(|(_, rows)| rows[row_index].as_slice())
            .collect();
          hash_base_rows(&rows)
        })
        .collect::<Vec<_>>()
    };
    let mut current = leaf_layer(log_max);
    let mut index = query_index;
    let mut path = Vec::with_capacity(usize::from(log_max));
    for next_height in (0..log_max).rev() {
      path.push(current[index ^ 1]);
      let mut parents: Vec<_> = current
        .as_chunks::<2>()
        .0
        .iter()
        .map(|children| hash_children(&children[0], &children[1]))
        .collect();
      if matrix_heights.contains(&next_height) {
        for (parent, injected) in
          parents.iter_mut().zip(leaf_layer(next_height))
        {
          *parent = hash_children(parent, &injected);
        }
      }
      current = parents;
      index >>= 1;
    }
    (current[0], path)
  }

  fn constant_extension_tree_root_and_path(
    value: [u64; 2],
    log_height: u8,
    query_index: usize,
  ) -> ([u8; 32], Vec<[u8; 32]>) {
    let mut leaf_bytes = [0u8; 32];
    for (chunk, word) in leaf_bytes
      .as_chunks_mut::<8>()
      .0
      .iter_mut()
      .zip([value[0], value[1], value[0], value[1]])
    {
      chunk.copy_from_slice(&word.to_le_bytes());
    }
    let leaf = *native_blake3::hash(&leaf_bytes).as_bytes();
    let mut current = vec![leaf; 1usize << log_height];
    let mut index = query_index;
    let mut path = Vec::with_capacity(usize::from(log_height));
    for _ in 0..log_height {
      path.push(current[index ^ 1]);
      current = current
        .as_chunks::<2>()
        .0
        .iter()
        .map(|children| hash_children(&children[0], &children[1]))
        .collect();
      index >>= 1;
    }
    (current[0], path)
  }

  fn transcript_bound_pcs_fri_fixture() -> (
    Stage2TranscriptReplayV1,
    Stage2FriTranscriptReplayV1,
    Stage2PcsInstanceV1,
    Vec<TranscriptBoundPcsFriQueryV1>,
  ) {
    const LOG_GLOBAL: u8 = 4;
    const LOG_BLOWUP: u8 = 1;
    let matrix_heights = [4u8, 3u8];
    let matrix_rows = vec![
      (0..1u32 << matrix_heights[0])
        .map(|index| {
          let x = pcs_query_point(matrix_heights[0], index);
          vec![linear_base_value(2, 11, x), linear_base_value(3, 17, x)]
        })
        .collect::<Vec<_>>(),
      (0..1u32 << matrix_heights[1])
        .map(|index| {
          let x = pcs_query_point(matrix_heights[1], index);
          vec![linear_base_value(5, 23, x)]
        })
        .collect::<Vec<_>>(),
    ];
    let (input_root, _) =
      multiheight_batch_root_and_path(&matrix_heights, &matrix_rows, 0);

    let mut prefix = Stage2TranscriptReplayV1 {
      initial_observations: input_root.to_vec(),
      stage2_and_accumulator_observations: vec![0x31; 48],
      quotient_commitment_observations: vec![0x52; 32],
      pcs_opening_observations: vec![0; 3 * 16],
    };
    let zeta = native_extension(prefix.challenges().unwrap().zeta);
    let opened_values = [
      linear_extension_value(2, 11, zeta),
      linear_extension_value(3, 17, zeta),
      linear_extension_value(5, 23, zeta),
    ];
    prefix.pcs_opening_observations.clear();
    for value in opened_values {
      encode_extension(&mut prefix.pcs_opening_observations, value);
    }

    let prefix_challenges = prefix.challenges().unwrap();
    let alpha = native_extension(prefix_challenges.pcs_alpha);
    let max_reduced = ExtVal::new([Val::from_u64(2), Val::ZERO])
      + alpha * ExtVal::new([Val::from_u64(3), Val::ZERO]);
    let shorter_reduced = ExtVal::new([Val::from_u64(5), Val::ZERO]);
    let mut current = max_reduced;
    let mut round_values = Vec::new();

    let (round_0_root, _) =
      constant_extension_tree_root_and_path(extension_words(current), 3, 0);
    let mut fri_transcript = Stage2FriTranscriptReplayV1 {
      commit_phase_commitments: vec![
        vec![round_0_root],
        vec![[0; 32]],
        vec![[0; 32]],
      ],
      commit_pow_witnesses: vec![0; 3],
      final_polynomial: vec![[0, 0]],
      log_arities: vec![1; 3],
      query_pow_witness: 0,
      commit_pow_bits: 0,
      query_pow_bits: 0,
      num_queries: 1,
      query_index_bits: LOG_GLOBAL,
    };
    let beta_0 =
      native_extension(fri_transcript.challenges(&prefix).unwrap().betas[0]);
    round_values.push(extension_words(current));
    current += beta_0 * beta_0 * shorter_reduced;
    let (round_1_root, _) =
      constant_extension_tree_root_and_path(extension_words(current), 2, 0);
    fri_transcript.commit_phase_commitments[1][0] = round_1_root;

    let _beta_1 = fri_transcript.challenges(&prefix).unwrap().betas[1];
    round_values.push(extension_words(current));
    let (round_2_root, _) =
      constant_extension_tree_root_and_path(extension_words(current), 1, 0);
    fri_transcript.commit_phase_commitments[2][0] = round_2_root;
    round_values.push(extension_words(current));
    fri_transcript.final_polynomial[0] = extension_words(current);
    let challenges = fri_transcript.challenges(&prefix).unwrap();
    let query_index = u32::try_from(challenges.query_indices[0]).unwrap();

    let (_, input_path) = multiheight_batch_root_and_path(
      &matrix_heights,
      &matrix_rows,
      usize::try_from(query_index).unwrap(),
    );
    let batch_opening = Stage2PcsBatchOpeningV1 {
      opened_rows: vec![
        matrix_rows[0][usize::try_from(query_index).unwrap()].clone(),
        matrix_rows[1][usize::try_from(query_index >> 1).unwrap()].clone(),
      ],
      opening_proof: input_path,
    };
    let rounds = (0..3usize)
      .map(|round| {
        let tree_height = 3 - u8::try_from(round).unwrap();
        let row_index = usize::try_from(query_index >> (round + 1)).unwrap();
        let (_, path) = constant_extension_tree_root_and_path(
          round_values[round],
          tree_height,
          row_index,
        );
        FriCommitPhaseRoundV1 {
          sibling: round_values[round],
          beta: challenges.betas[round],
          reduced_opening: (round == 0)
            .then_some(extension_words(shorter_reduced)),
          opening_proof: path,
        }
      })
      .collect();
    let fri_query = FriCommitPhaseQueryV1 {
      initial_log_height: LOG_GLOBAL - 1,
      query_index,
      initial_folded: extension_words(max_reduced),
      rounds,
      final_polynomial: extension_words(current),
    };
    let instance = Stage2PcsInstanceV1 {
      log_global_height: LOG_GLOBAL,
      log_blowup: LOG_BLOWUP,
      batches: vec![Stage2PcsBatchV1 {
        commitment: Stage2TranscriptByteBindingV1::new(
          Stage2TranscriptSegmentV1::Initial,
          0,
        ),
        matrices: vec![
          Stage2PcsMatrixV1 {
            log_height: matrix_heights[0],
            width: 2,
            opening_points: vec![Stage2PcsOpeningPointV1::Zeta],
            opened_values: Stage2TranscriptByteBindingV1::new(
              Stage2TranscriptSegmentV1::PcsOpening,
              0,
            ),
          },
          Stage2PcsMatrixV1 {
            log_height: matrix_heights[1],
            width: 1,
            opening_points: vec![Stage2PcsOpeningPointV1::Zeta],
            opened_values: Stage2TranscriptByteBindingV1::new(
              Stage2TranscriptSegmentV1::PcsOpening,
              32,
            ),
          },
        ],
      }],
    };
    let query = TranscriptBoundPcsFriQueryV1 {
      pcs: Stage2PcsQueryV1 { batch_openings: vec![batch_opening] },
      fri: fri_query,
    };
    (prefix, fri_transcript, instance, vec![query])
  }

  #[test]
  fn native_fold_satisfies_denominator_free_identity() {
    for query_index in [0, 1, 0b1_0110, 0b1_1111] {
      let mut query = fixture();
      query.query_index = query_index;
      let result = native_extension(query.folded_result().unwrap());
      let (e0, e1) = ordered_evaluations(&query);
      let e0 = native_extension(e0);
      let e1 = native_extension(e1);
      let beta = native_extension(query.beta);
      let s = ExtVal::new([Val::from_u64(subgroup_point(&query)), Val::ZERO]);
      let two_s = s + s;
      assert_eq!(two_s * result + beta * e1, s * (e0 + e1) + beta * e0);
    }
  }

  #[test]
  fn leaf_and_path_bind_pair_order_and_all_index_bits() {
    let query = fixture();
    let root = query.commitment_root().unwrap();
    let mut pair_bit = query.clone();
    pair_bit.query_index ^= 1;
    assert_ne!(pair_bit.commitment_root().unwrap(), root);
    let mut path_bit = query.clone();
    path_bit.query_index ^= 1 << 3;
    assert_ne!(path_bit.commitment_root().unwrap(), root);
    assert_ne!(
      pair_bit.folded_result().unwrap(),
      query.folded_result().unwrap()
    );
  }

  #[test]
  fn parser_is_strict_before_crypto() {
    let query = fixture();
    let artifact = FriFoldConformanceArtifactV1 {
      folded_result: query.folded_result().unwrap(),
      commitment_root: query.commitment_root().unwrap(),
      query,
      circuit_digest: [7; 32],
      proof_bundle_bytes: vec![1, 2, 3],
    };
    let mut bytes = artifact.to_bytes();
    assert!(FriFoldConformanceArtifactV1::from_bytes(&bytes).is_err());
    bytes[0] ^= 1;
    assert!(FriFoldConformanceArtifactV1::from_bytes(&bytes).is_err());
  }

  #[test]
  fn commit_phase_threads_shifted_index_and_folded_results() {
    let query = commit_phase_fixture();
    let computation = compute_commit_phase(&query).unwrap();
    ensure_final_polynomial(&query, &computation).unwrap();
    assert_eq!(computation.round_queries.len(), 3);
    assert_eq!(
      computation.round_queries[1].query_index,
      query.query_index >> 1
    );
    assert_eq!(computation.round_queries[1].folded, computation.results[0]);
    assert_ne!(computation.fold_results[0], computation.results[0]);
    assert_eq!(computation.fold_results[1], computation.results[1]);
    assert_eq!(computation.results[2], query.final_polynomial);
    assert_eq!(query.commitment_roots().unwrap(), computation.roots);

    let mut wrong_beta = query.clone();
    wrong_beta.rounds[1].beta[0] ^= 1;
    assert!(wrong_beta.folded_results().is_err());
  }

  #[test]
  fn deep_binary_fri_schedules_construct_and_evaluate() {
    for round_count in [9, 16, 30] {
      let (prefix, fri_transcript, query) =
        transcript_bound_fri_fixture_with_round_count(round_count);
      validate_commit_phase_structure(&query).unwrap();
      assert_eq!(query.rounds.len(), round_count);

      let challenges = fri_transcript.challenges(&prefix).unwrap();
      ensure_transcript_binds_fri_query(
        &fri_transcript,
        &challenges,
        0,
        &query,
      )
      .unwrap();
      let computation = compute_commit_phase(&query).unwrap();
      ensure_final_polynomial(&query, &computation).unwrap();

      let relation = TranscriptBoundFriCommitPhaseRelation::build(
        &prefix,
        &fri_transcript,
        &challenges,
        0,
        &query,
        &computation,
      )
      .unwrap();
      let witness = relation.shape.run(&relation.inputs, &[]);
      assert_eq!(witness.public, relation.public);

      let mut missing_last_round = query.clone();
      missing_last_round.rounds.pop();
      assert!(
        ensure_transcript_binds_fri_query(
          &fri_transcript,
          &challenges,
          0,
          &missing_last_round,
        )
        .is_err()
      );

      let mut wrong_last_path = query;
      wrong_last_path.rounds.last_mut().unwrap().opening_proof[0][0] ^= 1;
      assert!(
        ensure_transcript_binds_fri_query(
          &fri_transcript,
          &challenges,
          0,
          &wrong_last_path,
        )
        .is_err()
      );
    }
  }

  #[test]
  fn commit_phase_parser_is_strict_before_crypto() {
    let query = commit_phase_fixture();
    let artifact = FriCommitPhaseConformanceArtifactV1 {
      commitment_roots: query.commitment_roots().unwrap(),
      query,
      circuit_digest: [9; 32],
      proof_bundle_bytes: vec![1, 2, 3],
    };
    let mut bytes = artifact.to_bytes();
    assert!(FriCommitPhaseConformanceArtifactV1::from_bytes(&bytes).is_err());
    bytes[0] ^= 1;
    assert!(FriCommitPhaseConformanceArtifactV1::from_bytes(&bytes).is_err());
  }

  #[test]
  fn pcs_reduction_quotients_and_accumulator_match_reference_field() {
    let opening = pcs_reduction_fixture();
    let computation = compute_pcs_reduction(&opening).unwrap();
    let denominator = native_extension(computation.denominator);
    for (((&px, &pz), &quotient), column) in opening
      .opened_values
      .iter()
      .zip(&opening.opened_at_z)
      .zip(&computation.quotients)
      .zip(0..opening.opened_values.len())
    {
      let px = ExtVal::new([Val::from_u64(px), Val::ZERO]);
      assert_eq!(
        denominator * native_extension(quotient) + px,
        native_extension(pz),
        "column {column}"
      );
    }
    assert_eq!(opening.reduced_accumulator().unwrap(), computation.accumulator);
    assert_eq!(opening.next_alpha_power().unwrap(), computation.alpha_power);
    assert_eq!(opening.commitment_root().unwrap(), computation.root);

    let mut changed_index = opening;
    changed_index.query_index ^= 1;
    assert_ne!(changed_index.commitment_root().unwrap(), computation.root);
  }

  #[test]
  fn pcs_leaf_hash_supports_multiple_blocks_and_blake3_chunks() {
    let opening = wide_pcs_reduction_fixture();
    assert!(opening.opened_values.len() * 8 > 1_024);
    let computation = compute_pcs_reduction(&opening).unwrap();
    let relation = PcsReductionRelation::build(&opening).unwrap();
    let inputs = pcs_reduction_relation_inputs(&opening, &computation);
    let public = pcs_reduction_relation_public(&opening, &computation);
    let witness = relation.shape.run(&inputs, &[]);
    assert_eq!(witness.public, public);
    assert!(
      witness.rows::<Blake3Gate>(relation.slots.blake3).len()
        > opening.opening_proof.len() + 1
    );
    assert_eq!(computation.root, native_pcs_row_root(&opening));
  }

  #[test]
  fn pcs_reduction_parser_is_strict_before_crypto() {
    let opening = pcs_reduction_fixture();
    let computation = compute_pcs_reduction(&opening).unwrap();
    let artifact = PcsReductionConformanceArtifactV1 {
      opening,
      reduced_accumulator: computation.accumulator,
      next_alpha_power: computation.alpha_power,
      circuit_digest: [11; 32],
      commitment_root: computation.root,
      proof_bundle_bytes: vec![1, 2, 3],
    };
    let mut bytes = artifact.to_bytes();
    assert!(PcsReductionConformanceArtifactV1::from_bytes(&bytes).is_err());
    bytes[0] ^= 1;
    assert!(PcsReductionConformanceArtifactV1::from_bytes(&bytes).is_err());
  }

  #[test]
  fn transcript_challenges_feed_pcs_wires_in_one_circuit() {
    let (replay, opening) = transcript_bound_pcs_fixture();
    let challenges = replay.challenges().unwrap();
    let computation = compute_pcs_reduction(&opening).unwrap();
    let relation = TranscriptBoundPcsReductionRelation::build(
      &replay,
      &opening,
      &computation,
      challenges,
    )
    .unwrap();
    let witness = relation.shape.run(&relation.inputs, &[]);
    assert_eq!(witness.public, relation.public);

    let mut wrong_opening = opening;
    wrong_opening.alpha[0] ^= 1;
    assert!(
      TranscriptBoundPcsReductionRelation::build(
        &replay,
        &wrong_opening,
        &compute_pcs_reduction(&wrong_opening).unwrap(),
        challenges,
      )
      .is_err()
    );
  }

  #[test]
  fn transcript_betas_indices_caps_and_final_poly_feed_one_fri_circuit() {
    let (prefix, fri_transcript, query) = transcript_bound_fri_fixture();
    let challenges = fri_transcript.challenges(&prefix).unwrap();
    assert_eq!(challenges.query_indices.len(), 5);
    let computation = compute_commit_phase(&query).unwrap();
    let relation = TranscriptBoundFriCommitPhaseRelation::build(
      &prefix,
      &fri_transcript,
      &challenges,
      0,
      &query,
      &computation,
    )
    .unwrap();
    let witness = relation.shape.run(&relation.inputs, &[]);
    assert_eq!(witness.public, relation.public);

    let mut wrong_beta = query.clone();
    wrong_beta.rounds[0].beta[0] ^= 1;
    assert!(
      ensure_transcript_binds_fri_query(
        &fri_transcript,
        &challenges,
        0,
        &wrong_beta,
      )
      .is_err()
    );
    let mut wrong_index = query;
    wrong_index.query_index ^= 1;
    assert!(
      ensure_transcript_binds_fri_query(
        &fri_transcript,
        &challenges,
        0,
        &wrong_index,
      )
      .is_err()
    );
  }

  #[test]
  fn one_transcript_drives_every_fri_query_in_one_circuit() {
    let (prefix, fri_transcript, queries) =
      transcript_bound_fri_all_queries_fixture();
    let challenges = fri_transcript.challenges(&prefix).unwrap();
    let computations = validate_all_transcript_bound_fri_queries(
      &fri_transcript,
      &challenges,
      &queries,
    )
    .unwrap();
    let relation = TranscriptBoundFriCommitPhaseRelation::build_all(
      &prefix,
      &fri_transcript,
      &challenges,
      &queries,
      &computations,
    )
    .unwrap();
    let witness = relation.shape.run(&relation.inputs, &[]);
    assert_eq!(witness.public, relation.public);

    let mut missing = queries.clone();
    missing.pop();
    assert!(
      validate_all_transcript_bound_fri_queries(
        &fri_transcript,
        &challenges,
        &missing,
      )
      .is_err()
    );
  }

  #[test]
  fn authenticated_multiheight_pcs_buckets_feed_fri_in_one_circuit() {
    let (prefix, fri_transcript, pcs_instance, queries) =
      transcript_bound_pcs_fri_fixture();
    let prefix_challenges = prefix.challenges().unwrap();
    let fri_challenges = fri_transcript.challenges(&prefix).unwrap();
    let (fri_computations, pcs_computations) =
      validate_all_transcript_bound_pcs_fri_queries(
        &prefix,
        &fri_transcript,
        &fri_challenges,
        prefix_challenges,
        &pcs_instance,
        &queries,
      )
      .unwrap();
    assert_eq!(pcs_computations[0].reduced_openings.len(), 2);
    let relation = TranscriptBoundFriCommitPhaseRelation::build_all_with_pcs(
      &prefix,
      &fri_transcript,
      &fri_challenges,
      &pcs_instance,
      &queries,
      &fri_computations,
      &pcs_computations,
    )
    .unwrap();
    let witness = relation.shape.run(&relation.inputs, &[]);
    assert_eq!(witness.public, relation.public);
    assert!(witness.rows::<Blake3Gate>(relation.slots.blake3).len() > 20);

    let mut wrong_row = queries.clone();
    wrong_row[0].pcs.batch_openings[0].opened_rows[1][0] ^= 1;
    assert!(
      validate_all_transcript_bound_pcs_fri_queries(
        &prefix,
        &fri_transcript,
        &fri_challenges,
        prefix_challenges,
        &pcs_instance,
        &wrong_row,
      )
      .is_err()
    );
    let mut wrong_rollin = queries;
    wrong_rollin[0].fri.rounds[0].reduced_opening.as_mut().unwrap()[0] ^= 1;
    assert!(
      validate_all_transcript_bound_pcs_fri_queries(
        &prefix,
        &fri_transcript,
        &fri_challenges,
        prefix_challenges,
        &pcs_instance,
        &wrong_rollin,
      )
      .is_err()
    );
  }

  #[test]
  fn real_stage2_root_lowers_to_the_combined_pcs_fri_relation() {
    let (prepared, fri, vk_bytes, claim_bytes, proof_bytes) =
      prepared_stage2_pcs_fixture();
    let lowered =
      Stage2PcsFriWitnessV1::from_prepared(&prepared, &fri).unwrap();

    assert_eq!(lowered.pcs_instance.batches.len(), 4);
    assert!(
      lowered
        .pcs_instance
        .batches
        .iter()
        .take(3)
        .all(|batch| batch.matrices.len() == 2)
    );
    assert_eq!(lowered.pcs_instance.batches.get(3).unwrap().matrices.len(), 1);
    assert_eq!(lowered.queries.len(), fri.num_queries);

    let prefix_challenges = lowered.prefix.challenges().unwrap();
    let fri_challenges =
      lowered.fri_transcript.challenges(&lowered.prefix).unwrap();
    let report = crate::FlockStage3Backend
      .preflight_stage2(&vk_bytes, &claim_bytes, &proof_bytes, &fri)
      .unwrap();
    let census = &report.relation;
    assert!(census.nu >= u64::try_from(NU).unwrap());
    assert!(census.blake3_rows > 0);
    assert!(census.total_rows() > census.blake3_rows);
    assert_eq!(report.advice.queries, u64::try_from(fri.num_queries).unwrap());
    assert_eq!(report.stage2_root_digest, prepared.statement().digest());
    assert!(report.to_string().contains("gate rows: blake3="));

    let mut wrong_row = lowered.queries;
    wrong_row[0].pcs.batch_openings[0].opened_rows[0][0] ^= 1;
    assert!(
      validate_all_transcript_bound_pcs_fri_queries(
        &lowered.prefix,
        &lowered.fri_transcript,
        &fri_challenges,
        prefix_challenges,
        &lowered.pcs_instance,
        &wrong_row,
      )
      .is_err()
    );
  }

  #[test]
  #[ignore = "real production Flock proof of a complete Stage 2 verifier"]
  fn real_stage2_production_artifact_round_trip() {
    let total_started = std::time::Instant::now();

    let fixture_started = std::time::Instant::now();
    let (prepared, fri, vk_bytes, claim_bytes, proof_bytes) =
      prepared_stage2_pcs_fixture();
    let fixture_elapsed = fixture_started.elapsed();

    let backend = crate::FlockStage3Backend;

    let prove_started = std::time::Instant::now();
    let artifact = backend
      .prove_stage2(&vk_bytes, &claim_bytes, &proof_bytes, &fri)
      .expect("prove complete Stage 3 relation");
    let prove_elapsed = prove_started.elapsed();

    let encode_started = std::time::Instant::now();
    let encoded = artifact.to_bytes();
    let encode_elapsed = encode_started.elapsed();
    eprintln!(
      "Flock complete Stage 3 artifact: {} bytes (payload: {} bytes)",
      encoded.len(),
      artifact.proof_bytes().len(),
    );

    let decode_started = std::time::Instant::now();
    let decoded = crate::Stage3ArtifactV1::from_bytes(&encoded).unwrap();
    let decode_elapsed = decode_started.elapsed();

    let valid_verify_started = std::time::Instant::now();
    backend
      .verify_stage2(&decoded, decoded.statement())
      .expect("verify complete Stage 3 relation");
    let valid_verify_elapsed = valid_verify_started.elapsed();

    let wrong_relation =
      crate::Stage3StatementV1::new(prepared.statement(), [0xa5; 32]);
    let wrong_relation_started = std::time::Instant::now();
    assert!(backend.verify_stage2(&decoded, &wrong_relation).is_err());
    let wrong_relation_elapsed = wrong_relation_started.elapsed();

    let corrupt_decode_started = std::time::Instant::now();
    let mut corrupted = encoded;
    let flip_at = corrupted.len() - 1;
    corrupted[flip_at] ^= 1;
    let corrupted = crate::Stage3ArtifactV1::from_bytes(&corrupted).unwrap();
    let corrupt_decode_elapsed = corrupt_decode_started.elapsed();

    let corrupt_verify_started = std::time::Instant::now();
    assert!(backend.verify_stage2(&corrupted, corrupted.statement()).is_err());
    let corrupt_verify_elapsed = corrupt_verify_started.elapsed();

    let total_elapsed = total_started.elapsed();
    let negative_checks_elapsed =
      wrong_relation_elapsed + corrupt_decode_elapsed + corrupt_verify_elapsed;
    eprintln!(
      concat!(
        "Flock complete Stage 3 timings (seconds):\n",
        "  fixture setup:                    {:>10.3}\n",
        "  prove:                            {:>10.3}\n",
        "  artifact encode:                  {:>10.3}\n",
        "  artifact decode:                  {:>10.3}\n",
        "  valid cryptographic verification: {:>10.3}\n",
        "  reject wrong relation statement:  {:>10.6}\n",
        "  corrupt and decode artifact:       {:>10.3}\n",
        "  reject corrupted proof:           {:>10.3}\n",
        "  all negative checks:               {:>10.3}\n",
        "  total:                             {:>10.3}",
      ),
      fixture_elapsed.as_secs_f64(),
      prove_elapsed.as_secs_f64(),
      encode_elapsed.as_secs_f64(),
      decode_elapsed.as_secs_f64(),
      valid_verify_elapsed.as_secs_f64(),
      wrong_relation_elapsed.as_secs_f64(),
      corrupt_decode_elapsed.as_secs_f64(),
      corrupt_verify_elapsed.as_secs_f64(),
      negative_checks_elapsed.as_secs_f64(),
      total_elapsed.as_secs_f64(),
    );
  }

  #[test]
  #[ignore = "real Flock authenticated FRI-fold proof; run explicitly"]
  fn real_authenticated_fri_fold_round_trip_and_mutations() {
    let artifact = prove_fri_fold_conformance(&fixture()).expect("prove fold");
    eprintln!(
      "Flock authenticated FRI-fold conformance bundle: {} bytes",
      artifact.proof_bundle_bytes().len()
    );
    verify_fri_fold_conformance(&artifact).expect("verify fold");
    let decoded =
      FriFoldConformanceArtifactV1::from_bytes(&artifact.to_bytes()).unwrap();
    verify_fri_fold_conformance(&decoded).expect("verify decoded fold");

    let mut wrong_sibling = decoded.clone();
    wrong_sibling.query.opening_proof[2][7] ^= 1;
    assert!(verify_fri_fold_conformance(&wrong_sibling).is_err());
    let mut wrong_beta = decoded.clone();
    wrong_beta.query.beta[1] ^= 1;
    assert!(verify_fri_fold_conformance(&wrong_beta).is_err());
    let mut wrong_result = decoded.clone();
    wrong_result.folded_result[0] ^= 1;
    assert!(verify_fri_fold_conformance(&wrong_result).is_err());
    let mut wrong_proof = decoded;
    let flip_at = wrong_proof.proof_bundle_bytes.len() / 2;
    wrong_proof.proof_bundle_bytes[flip_at] ^= 1;
    assert!(verify_fri_fold_conformance(&wrong_proof).is_err());
  }

  #[test]
  #[ignore = "real Flock FRI commit-phase query proof; run explicitly"]
  fn real_fri_commit_phase_round_trip_and_mutations() {
    let artifact = prove_fri_commit_phase_conformance(&commit_phase_fixture())
      .expect("prove commit phase");
    eprintln!(
      "Flock FRI commit-phase conformance bundle: {} bytes",
      artifact.proof_bundle_bytes().len()
    );
    verify_fri_commit_phase_conformance(&artifact)
      .expect("verify commit phase");
    let decoded =
      FriCommitPhaseConformanceArtifactV1::from_bytes(&artifact.to_bytes())
        .unwrap();
    verify_fri_commit_phase_conformance(&decoded)
      .expect("verify decoded commit phase");

    let mut wrong_path = decoded.clone();
    wrong_path.query.rounds[1].opening_proof[0][5] ^= 1;
    assert!(verify_fri_commit_phase_conformance(&wrong_path).is_err());
    let mut wrong_final = decoded.clone();
    wrong_final.query.final_polynomial[1] ^= 1;
    assert!(verify_fri_commit_phase_conformance(&wrong_final).is_err());
    let mut wrong_root = decoded.clone();
    wrong_root.commitment_roots[2][3] ^= 1;
    assert!(verify_fri_commit_phase_conformance(&wrong_root).is_err());
    let mut wrong_proof = decoded;
    let flip_at = wrong_proof.proof_bundle_bytes.len() / 2;
    wrong_proof.proof_bundle_bytes[flip_at] ^= 1;
    assert!(verify_fri_commit_phase_conformance(&wrong_proof).is_err());
  }

  #[test]
  #[ignore = "real Flock authenticated PCS-reduction proof; run explicitly"]
  fn real_pcs_reduction_round_trip_and_mutations() {
    let artifact = prove_pcs_reduction_conformance(&pcs_reduction_fixture())
      .expect("prove PCS reduction");
    eprintln!(
      "Flock PCS-reduction conformance bundle: {} bytes",
      artifact.proof_bundle_bytes().len()
    );
    verify_pcs_reduction_conformance(&artifact).expect("verify PCS reduction");
    let decoded =
      PcsReductionConformanceArtifactV1::from_bytes(&artifact.to_bytes())
        .unwrap();
    verify_pcs_reduction_conformance(&decoded)
      .expect("verify decoded PCS reduction");

    let mut wrong_value = decoded.clone();
    wrong_value.opening.opened_values[2] ^= 1;
    assert!(verify_pcs_reduction_conformance(&wrong_value).is_err());
    let mut wrong_ood = decoded.clone();
    wrong_ood.opening.opened_at_z[1][0] ^= 1;
    assert!(verify_pcs_reduction_conformance(&wrong_ood).is_err());
    let mut wrong_result = decoded.clone();
    wrong_result.reduced_accumulator[0] ^= 1;
    assert!(verify_pcs_reduction_conformance(&wrong_result).is_err());
    let mut wrong_proof = decoded;
    let flip_at = wrong_proof.proof_bundle_bytes.len() / 2;
    wrong_proof.proof_bundle_bytes[flip_at] ^= 1;
    assert!(verify_pcs_reduction_conformance(&wrong_proof).is_err());
  }

  #[test]
  #[ignore = "real transcript-bound Flock PCS proof; run explicitly"]
  fn real_transcript_bound_pcs_round_trip_and_mutations() {
    let (replay, opening) = transcript_bound_pcs_fixture();
    let artifact =
      prove_transcript_bound_pcs_reduction_conformance(&replay, &opening)
        .expect("prove transcript-bound PCS reduction");
    eprintln!(
      "Flock transcript-bound PCS conformance bundle: {} bytes",
      artifact.proof_bundle_bytes().len()
    );
    verify_transcript_bound_pcs_reduction_conformance(&artifact)
      .expect("verify transcript-bound PCS reduction");

    let mut wrong_transcript = artifact.clone();
    wrong_transcript.replay.pcs_opening_observations[0] ^= 1;
    assert!(
      verify_transcript_bound_pcs_reduction_conformance(&wrong_transcript)
        .is_err()
    );
    let mut wrong_opening = artifact.clone();
    wrong_opening.opening.opened_values[0] ^= 1;
    assert!(
      verify_transcript_bound_pcs_reduction_conformance(&wrong_opening)
        .is_err()
    );
    let mut wrong_proof = artifact;
    let flip_at = wrong_proof.proof_bundle_bytes.len() / 2;
    wrong_proof.proof_bundle_bytes[flip_at] ^= 1;
    assert!(
      verify_transcript_bound_pcs_reduction_conformance(&wrong_proof).is_err()
    );
  }

  #[test]
  #[ignore = "real transcript-bound Flock FRI-query proof; run explicitly"]
  fn real_transcript_bound_fri_round_trip_and_mutations() {
    let (prefix, fri_transcript, query) = transcript_bound_fri_fixture();
    let artifact = prove_transcript_bound_fri_commit_phase_conformance(
      &prefix,
      &fri_transcript,
      0,
      &query,
    )
    .expect("prove transcript-bound FRI query");
    eprintln!(
      "Flock transcript-bound FRI-query conformance bundle: {} bytes",
      artifact.proof_bundle_bytes().len()
    );
    verify_transcript_bound_fri_commit_phase_conformance(&artifact)
      .expect("verify transcript-bound FRI query");

    let mut wrong_cap = artifact.clone();
    wrong_cap.fri_transcript.commit_phase_commitments[1][0][7] ^= 1;
    assert!(
      verify_transcript_bound_fri_commit_phase_conformance(&wrong_cap).is_err()
    );
    let mut wrong_query = artifact.clone();
    wrong_query.query.query_index ^= 1;
    assert!(
      verify_transcript_bound_fri_commit_phase_conformance(&wrong_query)
        .is_err()
    );
    let mut wrong_final = artifact.clone();
    wrong_final.fri_transcript.final_polynomial[0][0] ^= 1;
    assert!(
      verify_transcript_bound_fri_commit_phase_conformance(&wrong_final)
        .is_err()
    );
    let mut wrong_proof = artifact;
    let flip_at = wrong_proof.proof_bundle_bytes.len() / 2;
    wrong_proof.proof_bundle_bytes[flip_at] ^= 1;
    assert!(
      verify_transcript_bound_fri_commit_phase_conformance(&wrong_proof)
        .is_err()
    );
  }

  #[test]
  #[ignore = "real all-query transcript-bound Flock FRI proof; run explicitly"]
  fn real_transcript_bound_fri_all_queries_round_trip_and_mutations() {
    let (prefix, fri_transcript, queries) =
      transcript_bound_fri_all_queries_fixture();
    let artifact = prove_transcript_bound_fri_queries_conformance(
      &prefix,
      &fri_transcript,
      &queries,
    )
    .expect("prove every transcript-bound FRI query");
    eprintln!(
      "Flock all-query transcript-bound FRI bundle: {} bytes",
      artifact.proof_bundle_bytes().len()
    );
    verify_transcript_bound_fri_queries_conformance(&artifact)
      .expect("verify every transcript-bound FRI query");

    let mut wrong_query = artifact.clone();
    wrong_query.queries[1].query_index ^= 1;
    assert!(
      verify_transcript_bound_fri_queries_conformance(&wrong_query).is_err()
    );
    let mut missing_query = artifact.clone();
    missing_query.queries.pop();
    assert!(
      verify_transcript_bound_fri_queries_conformance(&missing_query).is_err()
    );
    let mut wrong_proof = artifact;
    let flip_at = wrong_proof.proof_bundle_bytes.len() / 2;
    wrong_proof.proof_bundle_bytes[flip_at] ^= 1;
    assert!(
      verify_transcript_bound_fri_queries_conformance(&wrong_proof).is_err()
    );
  }

  #[test]
  #[ignore = "real transcript-bound PCS-to-FRI Flock proof; run explicitly"]
  fn real_transcript_bound_pcs_fri_round_trip_and_mutations() {
    let (prefix, fri_transcript, pcs_instance, queries) =
      transcript_bound_pcs_fri_fixture();
    let artifact = prove_transcript_bound_pcs_fri_queries_conformance(
      &prefix,
      &fri_transcript,
      &pcs_instance,
      &queries,
    )
    .expect("prove transcript-bound PCS-to-FRI relation");
    eprintln!(
      "Flock transcript-bound PCS-to-FRI bundle: {} bytes",
      artifact.proof_bundle_bytes().len()
    );
    verify_transcript_bound_pcs_fri_queries_conformance(&artifact)
      .expect("verify transcript-bound PCS-to-FRI relation");

    let mut wrong_row = artifact.clone();
    wrong_row.queries[0].pcs.batch_openings[0].opened_rows[0][0] ^= 1;
    assert!(
      verify_transcript_bound_pcs_fri_queries_conformance(&wrong_row).is_err()
    );
    let mut wrong_ood = artifact.clone();
    wrong_ood.prefix.pcs_opening_observations[0] ^= 1;
    assert!(
      verify_transcript_bound_pcs_fri_queries_conformance(&wrong_ood).is_err()
    );
    let mut wrong_proof = artifact;
    let flip_at = wrong_proof.proof_bundle_bytes.len() / 2;
    wrong_proof.proof_bundle_bytes[flip_at] ^= 1;
    assert!(
      verify_transcript_bound_pcs_fri_queries_conformance(&wrong_proof)
        .is_err()
    );
  }
}
