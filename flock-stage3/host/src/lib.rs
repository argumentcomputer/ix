//! Ix Stage 3 backend for a specialised Aiur verifier over Flock's binary
//! field proof system.

mod air;
mod arithmetic;
mod artifact;
mod binding;
mod boolean;
mod config;
mod conformance;
mod equality;
mod extension;
mod fri;
mod goldilocks;
mod limits;
mod merkle;
mod multiplication;
mod prepared;
mod relation;
mod report;
mod sizing;
mod transcript;
mod typed_witness;
mod window;

#[cfg(test)]
mod test_support;

use aiur::vk_codec::AiurVerifyingKey;
use anyhow::{Result, bail};
use ix_terminal::{
  Stage2AdviceProfileV1, ValidatedStage2RootV1,
  validate_and_expand_root_inputs_bounded,
};
use multi_stark::types::FriParameters;
use std::fmt;

pub use air::{Stage2ActiveAirCircuitV1, Stage2AirProgramV1};
pub use arithmetic::{
  ARITHMETIC_CONFORMANCE_ARTIFACT_MAGIC, ArithmeticConformanceArtifactV1,
  GoldilocksAddPairV1, GoldilocksExt2MulV1, GoldilocksMulPairV1,
  prove_arithmetic_conformance, verify_arithmetic_conformance,
};
use artifact::Stage3ProductionPayloadV1;
pub use artifact::{
  MAX_STAGE3_ARTIFACT_BYTES, MAX_STAGE3_PROOF_BYTES, STAGE3_STATEMENT_BYTES,
  STAGE3_STATEMENT_DOMAIN, Stage3ArtifactV1, Stage3ArtifactWriterV1,
  Stage3StatementV1,
};
pub use binding::{
  STAGE3_BINDING_ARTIFACT_MAGIC, Stage3BindingArtifactV1,
  prove_stage3_statement_binding, stage3_statement_binding_circuit_digest,
  verify_stage3_statement_binding, verify_stage3_statement_binding_for,
};
pub use config::{
  ARITHMETIC_CONFORMANCE_TRANSCRIPT_DOMAIN,
  ENGINE_CONFORMANCE_TRANSCRIPT_DOMAIN, FLOCK_UPSTREAM_REVISION,
  FRI_FOLD_CONFORMANCE_TRANSCRIPT_DOMAIN,
  FRI_QUERY_CONFORMANCE_TRANSCRIPT_DOMAIN, FlockConfigV1,
  MERKLE_CONFORMANCE_TRANSCRIPT_DOMAIN,
  PCS_REDUCTION_CONFORMANCE_TRANSCRIPT_DOMAIN,
  STAGE2_AIR_PCS_FRI_CONFORMANCE_TRANSCRIPT_DOMAIN,
  STAGE2_TRANSCRIPT_CONFORMANCE_TRANSCRIPT_DOMAIN, STAGE3_TRANSCRIPT_DOMAIN,
  TRANSCRIPT_BOUND_FRI_CONFORMANCE_TRANSCRIPT_DOMAIN,
  TRANSCRIPT_BOUND_FRI_QUERIES_CONFORMANCE_TRANSCRIPT_DOMAIN,
  TRANSCRIPT_BOUND_PCS_CONFORMANCE_TRANSCRIPT_DOMAIN,
  TRANSCRIPT_BOUND_PCS_FRI_QUERIES_CONFORMANCE_TRANSCRIPT_DOMAIN,
};
pub use conformance::{
  EngineConformanceArtifact, prove_engine_conformance,
  verify_engine_conformance,
};
pub use flock_prover::r1cs_hashes::blake3::Compression;
pub use fri::{
  FRI_COMMIT_PHASE_CONFORMANCE_ARTIFACT_MAGIC,
  FRI_FOLD_CONFORMANCE_ARTIFACT_MAGIC, FriCommitPhaseConformanceArtifactV1,
  FriCommitPhaseQueryV1, FriCommitPhaseRoundV1, FriFoldConformanceArtifactV1,
  FriFoldQueryV1, PCS_REDUCTION_CONFORMANCE_ARTIFACT_MAGIC,
  PcsReducedOpeningV1, PcsReductionConformanceArtifactV1,
  Stage2AirPcsFriArtifactV1, Stage2AirPcsFriWitnessV1, Stage2PcsBatchOpeningV1,
  Stage2PcsBatchV1, Stage2PcsFriWitnessV1, Stage2PcsInstanceV1,
  Stage2PcsMatrixV1, Stage2PcsOpeningPointV1, Stage2PcsQueryV1,
  Stage3RelationCensusV1, TranscriptBoundFriCommitPhaseArtifactV1,
  TranscriptBoundFriQueriesArtifactV1, TranscriptBoundPcsFriQueriesArtifactV1,
  TranscriptBoundPcsFriQueryV1, TranscriptBoundPcsReductionArtifactV1,
  prove_fri_commit_phase_conformance, prove_fri_fold_conformance,
  prove_pcs_reduction_conformance, prove_stage2_air_pcs_fri_conformance,
  prove_transcript_bound_fri_commit_phase_conformance,
  prove_transcript_bound_fri_queries_conformance,
  prove_transcript_bound_pcs_fri_queries_conformance,
  prove_transcript_bound_pcs_reduction_conformance,
  verify_fri_commit_phase_conformance, verify_fri_fold_conformance,
  verify_pcs_reduction_conformance, verify_stage2_air_pcs_fri_conformance,
  verify_stage2_air_pcs_fri_conformance_for,
  verify_transcript_bound_fri_commit_phase_conformance,
  verify_transcript_bound_fri_queries_conformance,
  verify_transcript_bound_pcs_fri_queries_conformance,
  verify_transcript_bound_pcs_reduction_conformance,
};
pub use limits::Stage3ResourceLimitsV1;
pub use merkle::{
  MERKLE_CONFORMANCE_ARTIFACT_MAGIC, MerkleConformanceArtifactV1, MerklePathV1,
  prove_merkle_conformance, verify_merkle_conformance,
};
pub use prepared::{Stage3PreparedRootV1, Stage3ProofTimingsV1};
pub use relation::{
  STAGE3_RELATION_MANIFEST_DOMAIN, STAGE3_VERIFIER_PHASES_V1,
  Stage3LoweringStatusV1, Stage3RelationBoundsV1, Stage3RelationManifestV1,
  Stage3VerifierPhaseV1,
};
pub use report::{
  Stage3PreflightTimingsV1, Stage3ResourceReportV1, Stage3TableReportV1,
  process_peak_rss_bytes as stage3_process_peak_rss_bytes,
};
pub use transcript::{
  STAGE2_TRANSCRIPT_CONFORMANCE_ARTIFACT_MAGIC,
  Stage2FriTranscriptChallengesV1, Stage2FriTranscriptReplayV1,
  Stage2TranscriptByteBindingV1, Stage2TranscriptChallengesV1,
  Stage2TranscriptConformanceArtifactV1, Stage2TranscriptReplayV1,
  Stage2TranscriptSegmentV1, prove_stage2_transcript_conformance,
  verify_stage2_transcript_conformance,
};
pub use typed_witness::{
  STAGE3_TYPED_WITNESS_LAYOUT_DOMAIN, Stage3DigestV1, Stage3ExtensionValueV1,
  Stage3OpenedRoundV1, Stage3TypedBatchOpeningV1, Stage3TypedCommitPhaseStepV1,
  Stage3TypedCommitmentsV1, Stage3TypedFriProofV1, Stage3TypedProofCountsV1,
  Stage3TypedProofWitnessV1, Stage3TypedQueryProofV1,
};

/// Result of compiling and evaluating the complete Stage 3 relation without
/// invoking the Flock prover. This is the mandatory cost/compatibility gate
/// before attempting a production-sized aggregate root.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stage3PreflightReportV1 {
  pub stage2_root_digest: [u8; 32],
  pub relation_digest: [u8; 32],
  pub stage3_statement_digest: [u8; 32],
  pub verifying_key_digest: [u8; 32],
  pub compact_proof_digest: [u8; 32],
  pub typed_witness_layout_digest: [u8; 32],
  pub activation: Vec<bool>,
  pub log_degrees: Vec<u8>,
  pub fri_parameter_words: [u64; 5],
  pub verifying_key_bytes: u64,
  pub claim_bytes: u64,
  pub compact_proof_bytes: u64,
  pub advice: Stage2AdviceProfileV1,
  pub relation: Stage3RelationCensusV1,
  pub resources: Stage3ResourceReportV1,
  pub limits: Stage3ResourceLimitsV1,
  pub timings: Stage3PreflightTimingsV1,
  pub process_peak_rss_bytes: Option<u64>,
}

impl fmt::Display for Stage3PreflightReportV1 {
  fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
    let hex = |digest| blake3::Hash::from_bytes(digest).to_hex();
    writeln!(formatter, "Flock Stage 3 preflight accepted the aggregate root")?;
    writeln!(formatter, "  Stage 2 root: {}", hex(self.stage2_root_digest))?;
    writeln!(formatter, "  relation:     {}", hex(self.relation_digest))?;
    writeln!(
      formatter,
      "  Stage 3 stmt: {}",
      hex(self.stage3_statement_digest)
    )?;
    writeln!(
      formatter,
      "  transport: vk={} B, claim={} B, compact proof={} B, advice={} B",
      self.verifying_key_bytes,
      self.claim_bytes,
      self.compact_proof_bytes,
      self.advice.advice_bytes,
    )?;
    writeln!(
      formatter,
      "  Stage 2 shape: circuits={}/{} active, queries={}, FRI rounds={}, input rounds/query={}",
      self.advice.active_circuits,
      self.advice.total_circuits,
      self.advice.queries,
      self.advice.fri_rounds,
      self.advice.input_rounds_per_query,
    )?;
    writeln!(
      formatter,
      "  openings: input siblings={}, FRI siblings={}, base values={}, FRI extension siblings={}, other extensions={}",
      self.advice.input_merkle_siblings,
      self.advice.fri_merkle_siblings,
      self.advice.opened_base_values,
      self.advice.fri_sibling_extension_values,
      self.advice.other_extension_values,
    )?;
    writeln!(
      formatter,
      "  Flock relation: nu={}, capacity/table={}, inputs={}, public={}, rows={}",
      self.relation.nu,
      self.relation.table_capacity,
      self.relation.relation_inputs,
      self.relation.public_values,
      self.relation.total_rows(),
    )?;
    writeln!(
      formatter,
      "  gate rows: blake3={}, order={}, add={}, mul={}, repack={}, canonical={}, equality={}, hash-sample={}, field-sample={}, split={}, window={}",
      self.relation.blake3_rows,
      self.relation.digest_order_rows,
      self.relation.goldilocks_add_rows,
      self.relation.goldilocks_mul_rows,
      self.relation.lane_repack_rows,
      self.relation.canonical_goldilocks_rows,
      self.relation.equality_rows,
      self.relation.hash_sample_rows,
      self.relation.field_sample_rows,
      self.relation.u64_split_rows,
      self.relation.byte_window_rows,
    )?;
    writeln!(
      formatter,
      "  union: virtual log={}, committed log={}, dense={} B, padded z/a/b={} B",
      self.resources.virtual_union_log,
      self.resources.committed_union_log,
      self.resources.dense_witness_bytes,
      self.resources.padded_union_witness_bytes,
    )?;
    writeln!(
      formatter,
      "  PCS: message={} B, codeword={} B, lanes={}, log inverse rate={}",
      self.resources.pcs_message_bytes,
      self.resources.pcs_codeword_bytes,
      self.resources.pcs_lanes,
      self.resources.pcs_log_inverse_rate,
    )?;
    writeln!(
      formatter,
      "  fresh preparation (us): native={}, lowering={}, compile={}, evaluate={}, total={}",
      self.timings.native_prepare_us,
      self.timings.lowering_us,
      self.timings.compile_us,
      self.timings.evaluate_us,
      self.timings.total_us,
    )?;
    write!(
      formatter,
      "  memory: process lifetime peak={:?} B; PCS/compiler scratch is additional to padded witness",
      self.process_peak_rss_bytes,
    )
  }
}

/// Host facade for the production Stage 3 relation.
#[derive(Clone, Copy, Debug, Default)]
pub struct FlockStage3Backend;

impl FlockStage3Backend {
  /// Verify the compact Stage 2 root and produce the exact vk/claims/advice
  /// transport that the Flock relation must consume. This is usable while the
  /// relation itself is still being lowered.
  pub fn prepare_witness(
    self,
    vk_bytes: &[u8],
    claim_bytes: &[u8],
    proof_bytes: &[u8],
    fri: &FriParameters,
  ) -> Result<ValidatedStage2RootV1> {
    self.prepare_witness_with_limits(
      vk_bytes,
      claim_bytes,
      proof_bytes,
      fri,
      Stage3ResourceLimitsV1::default(),
    )
  }

  pub fn prepare_witness_with_limits(
    self,
    vk_bytes: &[u8],
    claim_bytes: &[u8],
    proof_bytes: &[u8],
    fri: &FriParameters,
    limits: Stage3ResourceLimitsV1,
  ) -> Result<ValidatedStage2RootV1> {
    limits.ensure_transport(vk_bytes, claim_bytes, proof_bytes, fri)?;
    // Fail before relation construction on an invalid compact root. The Flock
    // relation repeats verification; this native validation/expansion pass is
    // the inexpensive guard needed before allocating a production-scale
    // circuit.
    let prepared = validate_and_expand_root_inputs_bounded(
      vk_bytes,
      claim_bytes,
      proof_bytes,
      fri,
      limits.max_advice_bytes,
    )?;
    limits.ensure_prepared(&prepared)?;
    Ok(prepared)
  }

  /// Admit, compile, and evaluate once. The caller owns the relation and may
  /// explicitly reuse it for proving or verification; no root is retained in
  /// a process-global cache by the production workflow.
  pub fn prepare_stage2(
    self,
    vk_bytes: &[u8],
    claim_bytes: &[u8],
    proof_bytes: &[u8],
    fri: &FriParameters,
  ) -> Result<Stage3PreparedRootV1> {
    self.prepare_stage2_with_limits(
      vk_bytes,
      claim_bytes,
      proof_bytes,
      fri,
      Stage3ResourceLimitsV1::default(),
    )
  }

  pub fn prepare_stage2_with_limits(
    self,
    vk_bytes: &[u8],
    claim_bytes: &[u8],
    proof_bytes: &[u8],
    fri: &FriParameters,
    limits: Stage3ResourceLimitsV1,
  ) -> Result<Stage3PreparedRootV1> {
    Stage3LoweringStatusV1::current().ensure_complete()?;
    Stage3PreparedRootV1::new(vk_bytes, claim_bytes, proof_bytes, fri, limits)
  }

  /// Validate a compact aggregate root, compile the complete specialised
  /// relation, and evaluate every gate without running the Flock prover.
  pub fn preflight_stage2(
    self,
    vk_bytes: &[u8],
    claim_bytes: &[u8],
    proof_bytes: &[u8],
    fri: &FriParameters,
  ) -> Result<Stage3PreflightReportV1> {
    Ok(
      self
        .prepare_stage2(vk_bytes, claim_bytes, proof_bytes, fri)?
        .report()
        .clone(),
    )
  }

  /// Compile and content-address the complete relation for a prepared root.
  /// This builds the circuit but does not run the expensive Flock prover.
  pub fn relation_manifest(
    self,
    prepared: &ValidatedStage2RootV1,
  ) -> Result<Stage3RelationManifestV1> {
    Stage3RelationManifestV1::for_prepared(prepared)
  }

  /// Decode the verified advice transport into the primitive, fixed-schema
  /// witness consumed by the no-RISC-V Flock lowering.
  pub fn prepare_typed_proof_witness(
    self,
    prepared: &ValidatedStage2RootV1,
    fri: &FriParameters,
  ) -> Result<Stage3TypedProofWitnessV1> {
    Stage3TypedProofWitnessV1::from_prepared(prepared, fri)
  }

  /// Construct a public Stage 3 statement only from a complete manifest that
  /// is specialised to the exact shape of this prepared root.
  pub fn prepare_statement(
    self,
    prepared: &ValidatedStage2RootV1,
    manifest: &Stage3RelationManifestV1,
  ) -> Result<Stage3StatementV1> {
    manifest.ensure_matches(prepared)?;
    Ok(Stage3StatementV1::new(
      prepared.statement(),
      manifest.relation_digest()?,
    ))
  }

  /// Validate and lower a compact Stage 2 proof, prove the complete
  /// statement/AIR/PCS/FRI relation using the production transcript domain,
  /// verify it, and return its strictly framed Stage 3 artifact.
  pub fn prove_stage2(
    self,
    vk_bytes: &[u8],
    claim_bytes: &[u8],
    proof_bytes: &[u8],
    fri: &FriParameters,
  ) -> Result<Stage3ArtifactV1> {
    self.prepare_stage2(vk_bytes, claim_bytes, proof_bytes, fri)?.prove()
  }

  /// Run the mandatory no-prove gate and then prove using the same validated
  /// root, typed witness, and explicitly owned relation. The returned artifact
  /// has also passed the production Flock verifier.
  pub fn preflight_and_prove_stage2(
    self,
    vk_bytes: &[u8],
    claim_bytes: &[u8],
    proof_bytes: &[u8],
    fri: &FriParameters,
  ) -> Result<(Stage3PreflightReportV1, Stage3ArtifactV1)> {
    let prepared =
      self.prepare_stage2(vk_bytes, claim_bytes, proof_bytes, fri)?;
    let report = prepared.report().clone();
    let artifact = prepared.prove()?;
    Ok((report, artifact))
  }

  /// Verify the expected public statement, reconstruct the fixed relation
  /// from canonical Stage 2 inputs, pin its manifest digest, and verify the
  /// Flock proof under the production transcript domain.
  pub fn verify_stage2(
    self,
    artifact: &Stage3ArtifactV1,
    expected: &Stage3StatementV1,
  ) -> Result<()> {
    artifact.ensure_statement(expected)?;
    let payload = Stage3ProductionPayloadV1::decode(artifact.proof_bytes())?;
    Stage3ResourceLimitsV1::default().ensure_raw_transport(
      payload.vk_bytes(),
      payload.claim_bytes(),
      payload.stage2_proof_bytes(),
    )?;
    let key = AiurVerifyingKey::from_bytes(payload.vk_bytes())
      .map_err(|error| anyhow::anyhow!("decode Stage 3 Aiur key: {error}"))?;
    let fri = key.fri_parameters();
    let prepared = self.prepare_stage2(
      payload.vk_bytes(),
      payload.claim_bytes(),
      payload.stage2_proof_bytes(),
      &fri,
    )?;
    if prepared.statement() != expected {
      bail!("Stage 3 relation manifest does not match the expected relation");
    }
    prepared.verify(artifact)
  }

  /// Verify an artifact against the exact canonical aggregate-root transport
  /// from which it was produced. The expected statement and relation digest
  /// are rebuilt from these external inputs; no artifact-supplied statement is
  /// used as its own trust anchor.
  ///
  /// Requiring the embedded compact transport to match also lets this path
  /// reuse one native validation and one relation build.
  pub fn verify_stage2_for_root(
    self,
    artifact: &Stage3ArtifactV1,
    vk_bytes: &[u8],
    claim_bytes: &[u8],
    proof_bytes: &[u8],
    fri: &FriParameters,
  ) -> Result<()> {
    let payload = Stage3ProductionPayloadV1::decode(artifact.proof_bytes())?;
    for (observed, external, label) in [
      (payload.vk_bytes(), vk_bytes, "verifying key"),
      (payload.claim_bytes(), claim_bytes, "claim"),
      (payload.stage2_proof_bytes(), proof_bytes, "compact proof"),
    ] {
      if observed != external {
        bail!("Stage 3 artifact embeds a different Stage 2 {label} transport");
      }
    }

    self
      .prepare_stage2(vk_bytes, claim_bytes, proof_bytes, fri)?
      .verify(artifact)
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn malformed_stage2_input_fails_before_proving() {
    let fri = FriParameters {
      log_final_poly_len: 0,
      max_log_arity: 1,
      num_queries: 100,
      commit_proof_of_work_bits: 0,
      query_proof_of_work_bits: 20,
    };
    assert!(
      FlockStage3Backend
        .prove_stage2(b"vk", &[0; 144], b"proof", &fri)
        .is_err()
    );
    assert!(
      FlockStage3Backend
        .preflight_and_prove_stage2(b"vk", &[0; 144], b"proof", &fri)
        .is_err()
    );
    assert!(Stage3LoweringStatusV1::current().is_complete());
  }
}
