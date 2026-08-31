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
mod merkle;
mod multiplication;
mod relation;
mod transcript;
mod typed_witness;
mod window;

use aiur::vk_codec::AiurVerifyingKey;
use anyhow::{Result, bail};
use ix_terminal::{
  Stage2AdviceProfileV1, ValidatedStage2RootV1,
  validate_and_expand_root_inputs, validate_root_inputs,
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
  STAGE3_STATEMENT_BYTES, STAGE3_STATEMENT_DOMAIN, Stage3ArtifactV1,
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
use fri::{
  preflight_stage2_air_pcs_fri, prove_stage2_air_pcs_fri_production,
  verify_stage2_air_pcs_fri_production,
};
pub use merkle::{
  MERKLE_CONFORMANCE_ARTIFACT_MAGIC, MerkleConformanceArtifactV1, MerklePathV1,
  prove_merkle_conformance, verify_merkle_conformance,
};
pub use relation::{
  STAGE3_RELATION_MANIFEST_DOMAIN, STAGE3_VERIFIER_PHASES_V1,
  Stage3LoweringStatusV1, Stage3RelationBoundsV1, Stage3RelationManifestV1,
  Stage3VerifierPhaseV1,
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
  pub verifying_key_bytes: u64,
  pub claim_bytes: u64,
  pub compact_proof_bytes: u64,
  pub advice: Stage2AdviceProfileV1,
  pub relation: Stage3RelationCensusV1,
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
    write!(
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
    // Fail before relation construction on an invalid compact root. The
    // Flock relation repeats verification; this native pass is only the
    // inexpensive guard needed before allocating a production-scale circuit.
    validate_root_inputs(vk_bytes, claim_bytes, proof_bytes, fri)?;
    validate_and_expand_root_inputs(vk_bytes, claim_bytes, proof_bytes, fri)
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
    Stage3LoweringStatusV1::current().ensure_complete()?;
    let prepared =
      self.prepare_witness(vk_bytes, claim_bytes, proof_bytes, fri)?;
    let witness = Stage2AirPcsFriWitnessV1::from_prepared(&prepared, fri)?;
    let relation = preflight_stage2_air_pcs_fri(&witness)?;
    let manifest = Stage3RelationManifestV1::for_prepared_and_program_digest(
      &prepared,
      relation.circuit_digest,
    )?;
    let statement = self.prepare_statement(&prepared, &manifest)?;
    Ok(Stage3PreflightReportV1 {
      stage2_root_digest: prepared.statement().digest(),
      relation_digest: manifest.relation_digest()?,
      stage3_statement_digest: statement.digest(),
      verifying_key_bytes: u64::try_from(vk_bytes.len()).map_err(|error| {
        anyhow::anyhow!("verifying-key length exceeds u64: {error}")
      })?,
      claim_bytes: u64::try_from(claim_bytes.len()).map_err(|error| {
        anyhow::anyhow!("claim length exceeds u64: {error}")
      })?,
      compact_proof_bytes: u64::try_from(proof_bytes.len()).map_err(
        |error| anyhow::anyhow!("compact-proof length exceeds u64: {error}"),
      )?,
      advice: prepared.advice_profile().clone(),
      relation,
    })
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
  /// is specialised to, and has capacity for, this prepared root.
  pub fn prepare_statement(
    self,
    prepared: &ValidatedStage2RootV1,
    manifest: &Stage3RelationManifestV1,
  ) -> Result<Stage3StatementV1> {
    manifest.ensure_accommodates(prepared)?;
    Ok(Stage3StatementV1::new(
      prepared.statement(),
      manifest.relation_digest()?,
    ))
  }

  /// Validate and lower a compact Stage 2 proof, prove the complete
  /// statement/AIR/PCS/FRI relation using the production transcript domain,
  /// and return its strictly framed Stage 3 artifact.
  pub fn prove_stage2(
    self,
    vk_bytes: &[u8],
    claim_bytes: &[u8],
    proof_bytes: &[u8],
    fri: &FriParameters,
  ) -> Result<Stage3ArtifactV1> {
    Stage3LoweringStatusV1::current().ensure_complete()?;
    let prepared =
      self.prepare_witness(vk_bytes, claim_bytes, proof_bytes, fri)?;
    let witness = Stage2AirPcsFriWitnessV1::from_prepared(&prepared, fri)?;
    let flock_artifact = prove_stage2_air_pcs_fri_production(&witness)?;
    let manifest = Stage3RelationManifestV1::for_prepared_and_program_digest(
      &prepared,
      *flock_artifact.circuit_digest(),
    )?;
    let statement = self.prepare_statement(&prepared, &manifest)?;
    let payload = Stage3ProductionPayloadV1::new(
      vk_bytes,
      claim_bytes,
      proof_bytes,
      *flock_artifact.circuit_digest(),
      flock_artifact.proof_bundle_bytes(),
    )?
    .encode()?;
    Stage3ArtifactV1::new(statement, payload)
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
    let key = AiurVerifyingKey::from_bytes(payload.vk_bytes())
      .map_err(|error| anyhow::anyhow!("decode Stage 3 Aiur key: {error}"))?;
    let fri = key.fri_parameters();
    let prepared = self.prepare_witness(
      payload.vk_bytes(),
      payload.claim_bytes(),
      payload.stage2_proof_bytes(),
      &fri,
    )?;
    if prepared.statement().digest() != *expected.stage2_root_digest() {
      bail!("Stage 3 proof targets a different Stage 2 root");
    }
    let witness = Stage2AirPcsFriWitnessV1::from_prepared(&prepared, &fri)?;
    let manifest = Stage3RelationManifestV1::for_prepared_and_program_digest(
      &prepared,
      payload.circuit_digest(),
    )?;
    if manifest.relation_digest()? != *expected.relation_digest() {
      bail!("Stage 3 relation manifest does not match the expected relation");
    }
    let flock_artifact = Stage2AirPcsFriArtifactV1::from_parts(
      witness,
      payload.circuit_digest(),
      payload.flock_proof_bundle_bytes().to_vec(),
    )?;
    verify_stage2_air_pcs_fri_production(&flock_artifact)
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
    assert!(Stage3LoweringStatusV1::current().is_complete());
  }
}
