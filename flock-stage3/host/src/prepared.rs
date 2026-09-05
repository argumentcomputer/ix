//! Explicit ownership of one admitted, compiled and evaluated aggregate root.

use anyhow::{Result, bail};
use multi_stark::types::FriParameters;
use serde::Serialize;
use std::time::Instant;

use crate::{
  FlockStage3Backend, Stage2AirPcsFriWitnessV1, Stage3ArtifactV1,
  Stage3PreflightReportV1, Stage3PreflightTimingsV1, Stage3RelationManifestV1,
  Stage3ResourceLimitsV1, Stage3StatementV1, Stage3TypedProofWitnessV1,
  artifact::Stage3ProductionPayloadV1,
  fri::CompiledStage3Relation,
  report::{elapsed_us, process_peak_rss_bytes},
};

/// Reusable within an operation; dropping it releases its relation and root
/// transport. Only invariant R1CS/lincheck tables are shared across roots.
pub struct Stage3PreparedRootV1 {
  report: Stage3PreflightReportV1,
  statement: Stage3StatementV1,
  relation: CompiledStage3Relation,
  vk_bytes: Vec<u8>,
  claim_bytes: Vec<u8>,
  proof_bytes: Vec<u8>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Stage3ProofTimingsV1 {
  pub prove_us: u64,
  pub self_verify_us: u64,
  pub package_us: u64,
  pub total_us: u64,
}

impl Stage3PreparedRootV1 {
  pub(crate) fn new(
    vk_bytes: &[u8],
    claim_bytes: &[u8],
    proof_bytes: &[u8],
    fri: &FriParameters,
    limits: Stage3ResourceLimitsV1,
  ) -> Result<Self> {
    let total = Instant::now();
    let started = Instant::now();
    let prepared = FlockStage3Backend.prepare_witness_with_limits(
      vk_bytes,
      claim_bytes,
      proof_bytes,
      fri,
      limits,
    )?;
    let native_prepare_us = elapsed_us(started);
    let started = Instant::now();
    let typed = Stage3TypedProofWitnessV1::from_prepared(&prepared, fri)?;
    let witness = Stage2AirPcsFriWitnessV1::from_prepared_and_typed(
      &prepared, fri, &typed,
    )?;
    let lowering_us = elapsed_us(started);
    let started = Instant::now();
    let relation = CompiledStage3Relation::build(&witness, limits)?;
    let census = relation.census()?;
    let resources = relation.resources()?;
    limits.ensure_union_witness(resources.padded_union_witness_bytes)?;
    let manifest = Stage3RelationManifestV1::for_prepared_and_typed(
      &prepared,
      &typed,
      census.circuit_digest,
    )?;
    let relation_digest = manifest.relation_digest()?;
    let statement =
      Stage3StatementV1::new(prepared.statement(), relation_digest);
    let compile_us = elapsed_us(started);
    let started = Instant::now();
    relation.evaluate()?;
    let evaluate_us = elapsed_us(started);
    let report = Stage3PreflightReportV1 {
      stage2_root_digest: prepared.statement().digest(),
      relation_digest,
      stage3_statement_digest: statement.digest(),
      verifying_key_digest: *prepared.statement().verifying_key_digest(),
      compact_proof_digest: *blake3::hash(proof_bytes).as_bytes(),
      typed_witness_layout_digest: typed.layout_digest(),
      activation: typed.active,
      log_degrees: typed.log_degrees,
      fri_parameter_words: *prepared.statement().fri_parameter_words(),
      verifying_key_bytes: vk_bytes.len() as u64,
      claim_bytes: claim_bytes.len() as u64,
      compact_proof_bytes: proof_bytes.len() as u64,
      advice: prepared.advice_profile().clone(),
      relation: census,
      resources,
      limits,
      timings: Stage3PreflightTimingsV1 {
        native_prepare_us,
        lowering_us,
        compile_us,
        evaluate_us,
        total_us: elapsed_us(total),
      },
      process_peak_rss_bytes: process_peak_rss_bytes(),
    };
    Ok(Self {
      report,
      statement,
      relation,
      vk_bytes: vk_bytes.to_vec(),
      claim_bytes: claim_bytes.to_vec(),
      proof_bytes: proof_bytes.to_vec(),
    })
  }

  pub fn report(&self) -> &Stage3PreflightReportV1 {
    &self.report
  }

  pub fn statement(&self) -> &Stage3StatementV1 {
    &self.statement
  }

  pub fn prove(&self) -> Result<Stage3ArtifactV1> {
    self.prove_with_timings().map(|(artifact, _)| artifact)
  }

  pub fn prove_with_timings(
    &self,
  ) -> Result<(Stage3ArtifactV1, Stage3ProofTimingsV1)> {
    let total = Instant::now();
    let started = Instant::now();
    let bundle = self.relation.prove()?;
    let prove_us = elapsed_us(started);
    let started = Instant::now();
    self.relation.verify(self.report.relation.circuit_digest, &bundle)?;
    let self_verify_us = elapsed_us(started);
    let started = Instant::now();
    let payload = Stage3ProductionPayloadV1::new(
      &self.vk_bytes,
      &self.claim_bytes,
      &self.proof_bytes,
      self.report.relation.circuit_digest,
      &bundle,
    )?
    .encode()?;
    let artifact = Stage3ArtifactV1::new(self.statement.clone(), payload)?;
    Ok((
      artifact,
      Stage3ProofTimingsV1 {
        prove_us,
        self_verify_us,
        package_us: elapsed_us(started),
        total_us: elapsed_us(total),
      },
    ))
  }

  /// Verify against the already admitted external root, without repeating
  /// native verification, lowering, or compilation.
  pub fn verify(&self, artifact: &Stage3ArtifactV1) -> Result<()> {
    artifact.ensure_statement(&self.statement)?;
    let payload = Stage3ProductionPayloadV1::decode(artifact.proof_bytes())?;
    for (observed, external, label) in [
      (payload.vk_bytes(), self.vk_bytes.as_slice(), "verifying key"),
      (payload.claim_bytes(), self.claim_bytes.as_slice(), "claim"),
      (
        payload.stage2_proof_bytes(),
        self.proof_bytes.as_slice(),
        "compact proof",
      ),
    ] {
      if observed != external {
        bail!("Stage 3 artifact embeds a different Stage 2 {label} transport");
      }
    }
    self
      .relation
      .verify(payload.circuit_digest(), payload.flock_proof_bundle_bytes())
  }
}
