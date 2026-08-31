//! Stage-neutral P3 verifier leaf used by the Flock Stage 2 backend.
//!
//! This is the first executable Stage 2 boundary: it accepts a canonical
//! ten-word IxVM proof, lowers all eleven P3 verifier phases, and proves the
//! resulting relation under a Stage2-specific Flock transcript.  It does not
//! yet claim to implement `CheckEnv` folding or Flock recursion; those layers
//! consume this leaf verifier once their public-claim relations are present.

use std::{fmt, time::Instant};

use anyhow::{Result, bail};
use flock_prover::{hash::HashKind, pcs::ligerito::LigeritoProfile};
use ix_terminal::{
  P3AdviceProfileV1, P3ClaimLayoutV1, P3ProofStatementV1, ValidatedP3ProofV1,
  fri_parameter_words, validate_and_expand_p3_inputs,
};
use multi_stark::types::FriParameters;

use crate::{
  FLOCK_UPSTREAM_REVISION, Stage2AirPcsFriArtifactV1, Stage2AirPcsFriWitnessV1,
  Stage2PcsFriWitnessV1, Stage2RelationMemoryEstimateV1,
  Stage2RelationSizingV1, Stage3LoweringStatusV1, Stage3RelationCensusV1,
  Stage3TypedProofWitnessV1,
  fri::{
    p3_verifier_leaf_circuit_digest, preflight_p3_verifier_leaf,
    preflight_stage2_pcs_fri_prefix, prove_p3_verifier_leaf,
    size_p3_verifier_leaf, size_stage2_pcs_fri_prefix, verify_p3_verifier_leaf,
  },
};

pub const FLOCK_STAGE2_P3_LEAF_TRANSCRIPT_DOMAIN: &[u8] =
  b"ix:flock-stage2:p3-leaf-verifier:v1";

const FLOCK_STAGE2_CONFIG_DOMAIN: &[u8; 8] = b"IXF2CF01";
const FLOCK_STAGE2_CONFIG_VERSION: u16 = 1;
const FIELD_F128: u8 = 1;
const PROFILE_FAST128: u8 = 1;
const MERKLE_BLAKE3: u8 = 1;
const TRANSCRIPT_CHAINED_BLAKE3: u8 = 1;
const PROOF_CODEC_FLOCK_BINCODE_V1: u8 = 1;
const IMPLEMENTED_P3_LEAF_ONLY: u8 = 1;

pub const P3_VERIFIER_RELATION_MANIFEST_DOMAIN: &[u8; 8] = b"IXF2VR01";
const P3_VERIFIER_RELATION_MANIFEST_VERSION: u16 = 1;
const P3_VERIFIER_RELATION_BOUND_WORDS: usize = 14;
pub const P3_VERIFIER_RELATION_MANIFEST_BYTES: usize = 8
  + 2
  + 32
  + 32
  + 2 * 8
  + 32
  + 32
  + 2
  + 2
  + P3_VERIFIER_RELATION_BOUND_WORDS * 8;

/// Configuration identity for the first Flock Stage 2 implementation.
///
/// This is intentionally distinct from the historical Stage 3 configuration:
/// even though both currently use Fast128/F128/BLAKE3, they use different
/// transcript domains and have different accepted statements.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct FlockStage2ConfigV1;

impl FlockStage2ConfigV1 {
  pub fn to_bytes(self) -> Vec<u8> {
    let revision = FLOCK_UPSTREAM_REVISION.as_bytes();
    let transcript = FLOCK_STAGE2_P3_LEAF_TRANSCRIPT_DOMAIN;
    let mut bytes =
      Vec::with_capacity(8 + 2 + 2 + revision.len() + 6 + 2 + transcript.len());
    bytes.extend_from_slice(FLOCK_STAGE2_CONFIG_DOMAIN);
    bytes.extend_from_slice(&FLOCK_STAGE2_CONFIG_VERSION.to_le_bytes());
    bytes.extend_from_slice(
      &u16::try_from(revision.len()).expect("revision length").to_le_bytes(),
    );
    bytes.extend_from_slice(revision);
    bytes.extend_from_slice(&[
      FIELD_F128,
      PROFILE_FAST128,
      MERKLE_BLAKE3,
      TRANSCRIPT_CHAINED_BLAKE3,
      PROOF_CODEC_FLOCK_BINCODE_V1,
      IMPLEMENTED_P3_LEAF_ONLY,
    ]);
    bytes.extend_from_slice(
      &u16::try_from(transcript.len())
        .expect("transcript-domain length")
        .to_le_bytes(),
    );
    bytes.extend_from_slice(transcript);
    bytes
  }

  pub fn digest(self) -> [u8; 32] {
    *blake3::hash(&self.to_bytes()).as_bytes()
  }

  pub const fn leaf_profile(self) -> LigeritoProfile {
    LigeritoProfile::Fast128
  }

  pub const fn merkle_hash(self) -> HashKind {
    HashKind::Blake3
  }
}

/// Exact transport/profile bounds committed by one specialised leaf relation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct P3VerifierRelationBoundsV1 {
  pub verifying_key_bytes: u64,
  pub claims_bytes: u64,
  pub advice: P3AdviceProfileV1,
}

impl P3VerifierRelationBoundsV1 {
  fn for_prepared(prepared: &ValidatedP3ProofV1) -> Result<Self> {
    Ok(Self {
      verifying_key_bytes: as_u64(
        prepared.verifying_key_bytes().len(),
        "P3 verifying-key bytes",
      )?,
      claims_bytes: as_u64(prepared.claims_bytes().len(), "P3 claims bytes")?,
      advice: prepared.advice_profile().clone(),
    })
  }

  fn canonical_words(&self) -> [u64; P3_VERIFIER_RELATION_BOUND_WORDS] {
    [
      self.verifying_key_bytes,
      self.claims_bytes,
      self.advice.advice_bytes,
      self.advice.total_circuits,
      self.advice.active_circuits,
      self.advice.queries,
      self.advice.fri_rounds,
      self.advice.input_rounds_per_query,
      self.advice.commitment_cap_digests,
      self.advice.input_merkle_siblings,
      self.advice.fri_merkle_siblings,
      self.advice.opened_base_values,
      self.advice.fri_sibling_extension_values,
      self.advice.other_extension_values,
    ]
  }

  fn from_canonical_words(
    words: [u64; P3_VERIFIER_RELATION_BOUND_WORDS],
  ) -> Self {
    Self {
      verifying_key_bytes: words[0],
      claims_bytes: words[1],
      advice: P3AdviceProfileV1 {
        advice_bytes: words[2],
        total_circuits: words[3],
        active_circuits: words[4],
        queries: words[5],
        fri_rounds: words[6],
        input_rounds_per_query: words[7],
        commitment_cap_digests: words[8],
        input_merkle_siblings: words[9],
        fri_merkle_siblings: words[10],
        opened_base_values: words[11],
        fri_sibling_extension_values: words[12],
        other_extension_values: words[13],
      },
    }
  }

  fn ensure_accommodates(&self, prepared: &ValidatedP3ProofV1) -> Result<()> {
    let observed = Self::for_prepared(prepared)?;
    if observed.verifying_key_bytes != self.verifying_key_bytes {
      bail!("P3 verifying-key byte length differs from the leaf relation");
    }
    if observed.claims_bytes != self.claims_bytes {
      bail!("P3 claims byte length differs from the leaf relation");
    }
    if observed.advice.total_circuits != self.advice.total_circuits {
      bail!("P3 circuit count differs from the leaf relation");
    }
    if observed.advice.queries != self.advice.queries {
      bail!("P3 query count differs from the leaf relation");
    }

    let maxima = [
      (observed.advice.advice_bytes, self.advice.advice_bytes, "advice bytes"),
      (
        observed.advice.active_circuits,
        self.advice.active_circuits,
        "active circuits",
      ),
      (observed.advice.fri_rounds, self.advice.fri_rounds, "FRI rounds"),
      (
        observed.advice.input_rounds_per_query,
        self.advice.input_rounds_per_query,
        "input rounds per query",
      ),
      (
        observed.advice.commitment_cap_digests,
        self.advice.commitment_cap_digests,
        "commitment cap digests",
      ),
      (
        observed.advice.input_merkle_siblings,
        self.advice.input_merkle_siblings,
        "input Merkle siblings",
      ),
      (
        observed.advice.fri_merkle_siblings,
        self.advice.fri_merkle_siblings,
        "FRI Merkle siblings",
      ),
      (
        observed.advice.opened_base_values,
        self.advice.opened_base_values,
        "opened base values",
      ),
      (
        observed.advice.fri_sibling_extension_values,
        self.advice.fri_sibling_extension_values,
        "FRI sibling extension values",
      ),
      (
        observed.advice.other_extension_values,
        self.advice.other_extension_values,
        "other extension values",
      ),
    ];
    if let Some((observed, maximum, label)) =
      maxima.into_iter().find(|(observed, maximum, _)| observed > maximum)
    {
      bail!("P3 {label} ({observed}) exceeds leaf capacity ({maximum})");
    }
    Ok(())
  }
}

/// Canonical identity of one specialised complete P3-verifier relation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct P3VerifierRelationManifestV1 {
  p3_verifying_key_digest: [u8; 32],
  claim_layout: P3ClaimLayoutV1,
  typed_witness_layout_digest: [u8; 32],
  relation_program_digest: [u8; 32],
  bounds: P3VerifierRelationBoundsV1,
}

impl P3VerifierRelationManifestV1 {
  pub fn for_prepared(
    prepared: &ValidatedP3ProofV1,
    fri: &FriParameters,
  ) -> Result<Self> {
    let witness = Stage2AirPcsFriWitnessV1::from_p3(prepared, fri)?;
    let relation_program_digest = p3_verifier_leaf_circuit_digest(&witness)?;
    Self::for_prepared_and_program_digest(
      prepared,
      fri,
      relation_program_digest,
    )
  }

  pub(crate) fn for_prepared_and_program_digest(
    prepared: &ValidatedP3ProofV1,
    fri: &FriParameters,
    relation_program_digest: [u8; 32],
  ) -> Result<Self> {
    Stage3LoweringStatusV1::current().ensure_complete()?;
    if prepared.statement().fri_parameter_words() != &fri_parameter_words(fri) {
      bail!("P3 leaf manifest uses different FRI parameters");
    }
    let typed_witness = Stage3TypedProofWitnessV1::from_p3(prepared, fri)?;
    Ok(Self {
      p3_verifying_key_digest: *prepared.statement().verifying_key_digest(),
      claim_layout: prepared.statement().claim_layout(),
      typed_witness_layout_digest: typed_witness.layout_digest(),
      relation_program_digest,
      bounds: P3VerifierRelationBoundsV1::for_prepared(prepared)?,
    })
  }

  pub fn from_bytes(bytes: &[u8]) -> Result<Self> {
    if bytes.len() != P3_VERIFIER_RELATION_MANIFEST_BYTES {
      bail!(
        "P3 verifier relation manifest is {} bytes; expected {P3_VERIFIER_RELATION_MANIFEST_BYTES}",
        bytes.len()
      );
    }
    if &bytes[..8] != P3_VERIFIER_RELATION_MANIFEST_DOMAIN {
      bail!("invalid P3 verifier relation manifest domain");
    }
    let version = read_u16(bytes, 8);
    if version != P3_VERIFIER_RELATION_MANIFEST_VERSION {
      bail!("unsupported P3 verifier relation manifest version {version}");
    }
    if digest_at(bytes, 10) != FlockStage2ConfigV1.digest() {
      bail!("P3 verifier relation uses a different Flock Stage 2 config");
    }
    let p3_verifying_key_digest = digest_at(bytes, 42);
    let claim_layout = P3ClaimLayoutV1::from_descriptor_words([
      read_u64(bytes, 74),
      read_u64(bytes, 82),
    ])?;
    let typed_witness_layout_digest = digest_at(bytes, 90);
    let relation_program_digest = digest_at(bytes, 122);
    let status = Stage3LoweringStatusV1::current();
    let required_phase_mask = read_u16(bytes, 154);
    let implemented_phase_mask = read_u16(bytes, 156);
    if required_phase_mask != status.required_phase_mask()
      || implemented_phase_mask != status.implemented_phase_mask()
    {
      bail!("P3 verifier relation phase mask is not the complete V1 mask");
    }
    let mut words = [0u64; P3_VERIFIER_RELATION_BOUND_WORDS];
    for (index, word) in words.iter_mut().enumerate() {
      *word = read_u64(bytes, 158 + index * 8);
    }
    let manifest = Self {
      p3_verifying_key_digest,
      claim_layout,
      typed_witness_layout_digest,
      relation_program_digest,
      bounds: P3VerifierRelationBoundsV1::from_canonical_words(words),
    };
    if manifest.to_bytes() != bytes {
      bail!("P3 verifier relation manifest is not canonically encoded");
    }
    Ok(manifest)
  }

  pub fn to_bytes(&self) -> Vec<u8> {
    let status = Stage3LoweringStatusV1::current();
    let mut bytes = Vec::with_capacity(P3_VERIFIER_RELATION_MANIFEST_BYTES);
    bytes.extend_from_slice(P3_VERIFIER_RELATION_MANIFEST_DOMAIN);
    bytes
      .extend_from_slice(&P3_VERIFIER_RELATION_MANIFEST_VERSION.to_le_bytes());
    bytes.extend_from_slice(&FlockStage2ConfigV1.digest());
    bytes.extend_from_slice(&self.p3_verifying_key_digest);
    for word in self.claim_layout.descriptor_words() {
      bytes.extend_from_slice(&word.to_le_bytes());
    }
    bytes.extend_from_slice(&self.typed_witness_layout_digest);
    bytes.extend_from_slice(&self.relation_program_digest);
    bytes.extend_from_slice(&status.required_phase_mask().to_le_bytes());
    bytes.extend_from_slice(&status.implemented_phase_mask().to_le_bytes());
    for word in self.bounds.canonical_words() {
      bytes.extend_from_slice(&word.to_le_bytes());
    }
    debug_assert_eq!(bytes.len(), P3_VERIFIER_RELATION_MANIFEST_BYTES);
    bytes
  }

  pub fn relation_digest(&self) -> [u8; 32] {
    *blake3::hash(&self.to_bytes()).as_bytes()
  }

  pub fn ensure_accommodates(
    &self,
    prepared: &ValidatedP3ProofV1,
    fri: &FriParameters,
  ) -> Result<()> {
    if prepared.statement().verifying_key_digest()
      != &self.p3_verifying_key_digest
    {
      bail!("P3 verifying key differs from the specialised leaf relation");
    }
    if prepared.statement().claim_layout() != self.claim_layout {
      bail!("P3 claim layout differs from the specialised leaf relation");
    }
    let typed = Stage3TypedProofWitnessV1::from_p3(prepared, fri)?;
    if typed.layout_digest() != self.typed_witness_layout_digest {
      bail!("P3 typed witness layout differs from the leaf relation");
    }
    self.bounds.ensure_accommodates(prepared)
  }

  pub fn p3_verifying_key_digest(&self) -> &[u8; 32] {
    &self.p3_verifying_key_digest
  }

  pub const fn claim_layout(&self) -> P3ClaimLayoutV1 {
    self.claim_layout
  }

  pub fn typed_witness_layout_digest(&self) -> &[u8; 32] {
    &self.typed_witness_layout_digest
  }

  pub fn relation_program_digest(&self) -> &[u8; 32] {
    &self.relation_program_digest
  }

  pub fn bounds(&self) -> &P3VerifierRelationBoundsV1 {
    &self.bounds
  }
}

/// No-prove report for a complete ten-word IxVM verifier relation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FlockStage2LeafPreflightReportV1 {
  pub p3_statement_digest: [u8; 32],
  pub output_claim_digest: [u8; 32],
  pub relation_digest: [u8; 32],
  pub config_digest: [u8; 32],
  pub verifying_key_bytes: u64,
  pub claim_bytes: u64,
  pub compact_proof_bytes: u64,
  pub advice: P3AdviceProfileV1,
  pub relation: Stage3RelationCensusV1,
}

/// Timings for the verifier-core lower-bound benchmark.
///
/// Durations are integer nanoseconds so the FFI and benchmark JSON do not
/// lose precision or depend on a floating-point formatting convention.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FlockStage2VerifierCoreTimingsV1 {
  pub prepare_ns: u64,
  pub typed_witness_ns: u64,
  pub preflight_ns: u64,
  pub manifest_ns: u64,
  pub same_witness_prove_ns: u64,
  pub valid_verify_ns: u64,
  pub corrupt_reject_ns: u64,
  pub input_to_verified_output_ns: u64,
  pub wall_with_negative_check_ns: u64,
}

/// Structured result of proving the current verifier-only Stage 2 leaf.
///
/// This is deliberately named `verifier_core`: it proves every P3 verifier
/// phase but does not yet constrain the `CheckEnv` preimage or publish the
/// uniform aggregate claim required for a semantic P3-lift comparison.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FlockStage2VerifierCoreBenchmarkV1 {
  pub preflight: FlockStage2LeafPreflightReportV1,
  pub circuit_digest: [u8; 32],
  pub proof_bundle_digest: [u8; 32],
  pub proof_bundle_bytes: u64,
  pub timings: FlockStage2VerifierCoreTimingsV1,
}

/// Native transport/advice census for one canonical IxVM P3 proof.
///
/// This report performs no Flock circuit construction.  It is useful as the
/// cheap first checkpoint for a production proof before choosing a bounded
/// relation profile.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FlockStage2LeafProfileReportV1 {
  pub p3_statement_digest: [u8; 32],
  pub output_claim_digest: [u8; 32],
  pub config_digest: [u8; 32],
  pub verifying_key_bytes: u64,
  pub claim_bytes: u64,
  pub compact_proof_bytes: u64,
  pub advice: P3AdviceProfileV1,
}

impl fmt::Display for FlockStage2LeafProfileReportV1 {
  fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
    let hex = |digest| blake3::Hash::from_bytes(digest).to_hex();
    writeln!(formatter, "Flock Stage 2 profile accepted an IxVM P3 leaf")?;
    writeln!(formatter, "  P3 statement: {}", hex(self.p3_statement_digest))?;
    writeln!(formatter, "  output claim: {}", hex(self.output_claim_digest))?;
    writeln!(formatter, "  config:       {}", hex(self.config_digest))?;
    writeln!(
      formatter,
      "  transport: vk={} B, claim={} B, compact proof={} B, advice={} B",
      self.verifying_key_bytes,
      self.claim_bytes,
      self.compact_proof_bytes,
      self.advice.advice_bytes,
    )?;
    write!(
      formatter,
      "  P3 shape: circuits={} ({} active), queries={}, FRI rounds={}, input rounds/query={}, input siblings={}, FRI siblings={}, opened base={}, FRI sibling ext={}, other ext={}",
      self.advice.total_circuits,
      self.advice.active_circuits,
      self.advice.queries,
      self.advice.fri_rounds,
      self.advice.input_rounds_per_query,
      self.advice.input_merkle_siblings,
      self.advice.fri_merkle_siblings,
      self.advice.opened_base_values,
      self.advice.fri_sibling_extension_values,
      self.advice.other_extension_values,
    )
  }
}

/// Diagnostic no-prove census for a prefix of the PCS/FRI queries.
///
/// This intentionally omits AIR and cannot be converted into a Stage 2 leaf
/// artifact.  Its circuit digest identifies only the measured prefix shape.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FlockStage2PcsFriProfileReportV1 {
  pub leaf: FlockStage2LeafProfileReportV1,
  pub selected_queries: u64,
  pub total_queries: u64,
  pub relation: Stage3RelationCensusV1,
}

/// Sizing-only report captured before Flock circuit finalization.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FlockStage2SizingReportV1 {
  pub leaf: FlockStage2LeafProfileReportV1,
  pub sizing: Stage2RelationSizingV1,
  pub memory: Stage2RelationMemoryEstimateV1,
}

impl fmt::Display for FlockStage2SizingReportV1 {
  fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
    writeln!(formatter, "{}", self.leaf)?;
    let scope =
      if self.sizing.includes_air { "AIR + PCS/FRI" } else { "PCS/FRI" };
    writeln!(
      formatter,
      "  sizing-only {scope}: {}/{} queries, estimated nu={}, exact nu={}, capacity/table={}, max rows={}, total rows={}, inputs={}, public={}",
      self.sizing.selected_queries,
      self.leaf.advice.queries,
      self.sizing.estimated_nu,
      self.sizing.exact_nu,
      self.sizing.table_capacity,
      self.sizing.maximum_table_rows(),
      self.sizing.total_rows(),
      self.sizing.relation_inputs,
      self.sizing.public_values,
    )?;
    writeln!(
      formatter,
      "  sized rows: blake3={}, order={}, add={}, mul={}, repack={}, canonical={}, equality={}, zero={}, hash-sample={}, field-sample={}, split={}, window={}",
      self.sizing.blake3_rows,
      self.sizing.digest_order_rows,
      self.sizing.goldilocks_add_rows,
      self.sizing.goldilocks_mul_rows,
      self.sizing.lane_repack_rows,
      self.sizing.canonical_goldilocks_rows,
      self.sizing.equality_rows,
      self.sizing.zero_constraint_rows,
      self.sizing.hash_sample_rows,
      self.sizing.field_sample_rows,
      self.sizing.u64_split_rows,
      self.sizing.byte_window_rows,
    )?;
    writeln!(
      formatter,
      "  memory geometry: M={}, virtual witness buffers=3 x {} = {}, stripes={}, witness+stripes={}",
      self.memory.registry_m,
      binary_bytes(self.memory.padded_witness_buffer_virtual_bytes),
      binary_bytes(self.memory.three_padded_witness_buffers_virtual_bytes),
      binary_bytes(self.memory.stripe_buffers_virtual_bytes),
      binary_bytes(self.memory.witness_and_stripe_virtual_bytes),
    )?;
    writeln!(
      formatter,
      "  live payload: witness={} per buffer ({} words), stripes={}",
      binary_bytes(self.memory.live_witness_bytes_per_buffer),
      self.memory.live_witness_words_per_buffer,
      binary_bytes(self.memory.stripe_live_write_bytes),
    )?;
    writeln!(
      formatter,
      "  PCS commit: dense M={}, stack={}, lanes={}/{}, rate=1/2^{}, codeword={}, Merkle tree={}",
      self.memory.dense_m,
      binary_bytes(self.memory.committed_stack_bytes),
      self.memory.pcs_committed_lanes,
      self.memory.pcs_total_lanes,
      self.memory.pcs_log_inv_rate,
      binary_bytes(self.memory.initial_codeword_bytes),
      binary_bytes(self.memory.initial_merkle_tree_bytes),
    )?;
    writeln!(
      formatter,
      "  accounted commit-phase model: {} ({} with 25% arithmetic headroom); accounted virtual={}",
      binary_bytes(self.memory.accounted_commit_phase_bytes),
      binary_bytes(
        self.memory.accounted_commit_phase_with_25_percent_headroom_bytes
      ),
      binary_bytes(self.memory.accounted_virtual_reservation_bytes),
    )?;
    write!(
      formatter,
      "  memory-model exclusions: circuit/row arena, wiring GKR, PIOP/opening scratch, allocator metadata, retained scratch pools, runtime/OS"
    )
  }
}

impl fmt::Display for FlockStage2PcsFriProfileReportV1 {
  fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
    writeln!(formatter, "{}", self.leaf)?;
    writeln!(
      formatter,
      "  diagnostic PCS/FRI prefix: {}/{} queries",
      self.selected_queries, self.total_queries,
    )?;
    let digest =
      blake3::Hash::from_bytes(self.relation.circuit_digest).to_hex();
    writeln!(
      formatter,
      "  prefix relation: digest={digest}, nu={}, capacity/table={}, inputs={}, public={}, rows={}",
      self.relation.nu,
      self.relation.table_capacity,
      self.relation.relation_inputs,
      self.relation.public_values,
      self.relation.total_rows(),
    )?;
    write!(
      formatter,
      "  prefix rows: blake3={}, order={}, add={}, mul={}, repack={}, canonical={}, equality={}, zero={}, hash-sample={}, field-sample={}, split={}, window={}",
      self.relation.blake3_rows,
      self.relation.digest_order_rows,
      self.relation.goldilocks_add_rows,
      self.relation.goldilocks_mul_rows,
      self.relation.lane_repack_rows,
      self.relation.canonical_goldilocks_rows,
      self.relation.equality_rows,
      self.relation.zero_constraint_rows,
      self.relation.hash_sample_rows,
      self.relation.field_sample_rows,
      self.relation.u64_split_rows,
      self.relation.byte_window_rows,
    )
  }
}

impl fmt::Display for FlockStage2LeafPreflightReportV1 {
  fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
    let hex = |digest| blake3::Hash::from_bytes(digest).to_hex();
    writeln!(formatter, "Flock Stage 2 preflight accepted an IxVM P3 leaf")?;
    writeln!(formatter, "  P3 statement: {}", hex(self.p3_statement_digest))?;
    writeln!(formatter, "  output claim: {}", hex(self.output_claim_digest))?;
    writeln!(formatter, "  relation:     {}", hex(self.relation_digest))?;
    writeln!(formatter, "  config:       {}", hex(self.config_digest))?;
    writeln!(
      formatter,
      "  transport: vk={} B, claim={} B, compact proof={} B, advice={} B",
      self.verifying_key_bytes,
      self.claim_bytes,
      self.compact_proof_bytes,
      self.advice.advice_bytes,
    )?;
    write!(
      formatter,
      "  Flock relation: nu={}, capacity/table={}, inputs={}, public={}, rows={}",
      self.relation.nu,
      self.relation.table_capacity,
      self.relation.relation_inputs,
      self.relation.public_values,
      self.relation.total_rows(),
    )
  }
}

/// In-process Phase 1 leaf artifact.
///
/// The final Stage 2 root artifact has a separate strict wire codec and never
/// embeds this witness.  This type exists so the complete P3 verifier can be
/// proved, mutated, and benchmarked before the recursive outer format lands.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FlockStage2P3LeafArtifactV1 {
  statement: P3ProofStatementV1,
  relation_manifest: P3VerifierRelationManifestV1,
  flock_artifact: Stage2AirPcsFriArtifactV1,
}

impl FlockStage2P3LeafArtifactV1 {
  pub fn statement(&self) -> &P3ProofStatementV1 {
    &self.statement
  }

  pub fn relation_manifest(&self) -> &P3VerifierRelationManifestV1 {
    &self.relation_manifest
  }

  pub fn circuit_digest(&self) -> &[u8; 32] {
    self.flock_artifact.circuit_digest()
  }

  pub fn proof_bundle_bytes(&self) -> &[u8] {
    self.flock_artifact.proof_bundle_bytes()
  }

  #[cfg(test)]
  pub(crate) fn flock_artifact(&self) -> &Stage2AirPcsFriArtifactV1 {
    &self.flock_artifact
  }
}

/// Host facade for the incrementally built Flock Stage 2 backend.
#[derive(Clone, Copy, Debug, Default)]
pub struct FlockStage2Backend;

impl FlockStage2Backend {
  /// Natively validate and expand one canonical raw Stage 1 proof.
  pub fn prepare_ixvm_leaf(
    self,
    vk_bytes: &[u8],
    claim_bytes: &[u8],
    proof_bytes: &[u8],
    fri: &FriParameters,
    verify_claim_index: u64,
  ) -> Result<ValidatedP3ProofV1> {
    validate_and_expand_p3_inputs(
      vk_bytes,
      claim_bytes,
      proof_bytes,
      fri,
      P3ClaimLayoutV1::Ixvm { verify_claim_index },
    )
  }

  /// Validate the canonical proof and report its transport/advice geometry
  /// without constructing a Flock circuit.
  pub fn profile_ixvm_leaf(
    self,
    vk_bytes: &[u8],
    claim_bytes: &[u8],
    proof_bytes: &[u8],
    fri: &FriParameters,
    verify_claim_index: u64,
  ) -> Result<FlockStage2LeafProfileReportV1> {
    let prepared = self.prepare_ixvm_leaf(
      vk_bytes,
      claim_bytes,
      proof_bytes,
      fri,
      verify_claim_index,
    )?;
    leaf_profile_report(&prepared, vk_bytes, claim_bytes, proof_bytes)
  }

  /// Compile and evaluate the first `query_count` PCS/FRI openings, omitting
  /// AIR.  This is a profiling checkpoint and never creates a proof artifact.
  pub fn profile_ixvm_leaf_pcs_fri_prefix(
    self,
    vk_bytes: &[u8],
    claim_bytes: &[u8],
    proof_bytes: &[u8],
    fri: &FriParameters,
    verify_claim_index: u64,
    query_count: usize,
  ) -> Result<FlockStage2PcsFriProfileReportV1> {
    Stage3LoweringStatusV1::current().ensure_complete()?;
    let prepared = self.prepare_ixvm_leaf(
      vk_bytes,
      claim_bytes,
      proof_bytes,
      fri,
      verify_claim_index,
    )?;
    let leaf =
      leaf_profile_report(&prepared, vk_bytes, claim_bytes, proof_bytes)?;
    let witness = Stage2PcsFriWitnessV1::from_p3(&prepared, fri)?;
    let total_queries = witness.queries.len();
    let relation = preflight_stage2_pcs_fri_prefix(&witness, query_count)?;
    Ok(FlockStage2PcsFriProfileReportV1 {
      leaf,
      selected_queries: as_u64(query_count, "selected query count")?,
      total_queries: as_u64(total_queries, "total query count")?,
      relation,
    })
  }

  /// Emit a PCS/FRI query prefix and report exact slot capacities without
  /// finalizing or evaluating the padded Flock circuit.
  pub fn size_ixvm_leaf_pcs_fri_prefix(
    self,
    vk_bytes: &[u8],
    claim_bytes: &[u8],
    proof_bytes: &[u8],
    fri: &FriParameters,
    verify_claim_index: u64,
    query_count: usize,
  ) -> Result<FlockStage2SizingReportV1> {
    Stage3LoweringStatusV1::current().ensure_complete()?;
    let prepared = self.prepare_ixvm_leaf(
      vk_bytes,
      claim_bytes,
      proof_bytes,
      fri,
      verify_claim_index,
    )?;
    let leaf =
      leaf_profile_report(&prepared, vk_bytes, claim_bytes, proof_bytes)?;
    let witness = Stage2PcsFriWitnessV1::from_p3(&prepared, fri)?;
    let sizing = size_stage2_pcs_fri_prefix(&witness, query_count)?;
    let memory = sizing.memory_estimate()?;
    Ok(FlockStage2SizingReportV1 { leaf, sizing, memory })
  }

  /// Emit the complete AIR/PCS/FRI relation and report exact slot capacities
  /// without finalizing or evaluating the padded Flock circuit.
  pub fn size_ixvm_leaf(
    self,
    vk_bytes: &[u8],
    claim_bytes: &[u8],
    proof_bytes: &[u8],
    fri: &FriParameters,
    verify_claim_index: u64,
  ) -> Result<FlockStage2SizingReportV1> {
    Stage3LoweringStatusV1::current().ensure_complete()?;
    let prepared = self.prepare_ixvm_leaf(
      vk_bytes,
      claim_bytes,
      proof_bytes,
      fri,
      verify_claim_index,
    )?;
    let leaf =
      leaf_profile_report(&prepared, vk_bytes, claim_bytes, proof_bytes)?;
    let witness = Stage2AirPcsFriWitnessV1::from_p3(&prepared, fri)?;
    let sizing = size_p3_verifier_leaf(&witness)?;
    let memory = sizing.memory_estimate()?;
    Ok(FlockStage2SizingReportV1 { leaf, sizing, memory })
  }

  /// Compile and evaluate every P3 verifier gate without invoking Flock.
  pub fn preflight_ixvm_leaf(
    self,
    vk_bytes: &[u8],
    claim_bytes: &[u8],
    proof_bytes: &[u8],
    fri: &FriParameters,
    verify_claim_index: u64,
  ) -> Result<FlockStage2LeafPreflightReportV1> {
    Stage3LoweringStatusV1::current().ensure_complete()?;
    let prepared = self.prepare_ixvm_leaf(
      vk_bytes,
      claim_bytes,
      proof_bytes,
      fri,
      verify_claim_index,
    )?;
    let witness = Stage2AirPcsFriWitnessV1::from_p3(&prepared, fri)?;
    let relation = preflight_p3_verifier_leaf(&witness)?;
    let manifest =
      P3VerifierRelationManifestV1::for_prepared_and_program_digest(
        &prepared,
        fri,
        relation.circuit_digest,
      )?;
    Ok(FlockStage2LeafPreflightReportV1 {
      p3_statement_digest: prepared.statement().digest(),
      output_claim_digest: prepared.statement().ixvm_output_claim_digest()?,
      relation_digest: manifest.relation_digest(),
      config_digest: FlockStage2ConfigV1.digest(),
      verifying_key_bytes: as_u64(vk_bytes.len(), "verifying-key bytes")?,
      claim_bytes: as_u64(claim_bytes.len(), "claim bytes")?,
      compact_proof_bytes: as_u64(proof_bytes.len(), "compact-proof bytes")?,
      advice: prepared.advice_profile().clone(),
      relation,
    })
  }

  /// Run the production-shaped verifier-core benchmark with structured phase
  /// results. Preparation and typed-witness construction happen once. The
  /// preflight then installs the exact-witness in-process relation used by the
  /// following prove call; this is a diagnostic lower bound, not a reusable
  /// different-witness shape cache.
  pub fn benchmark_ixvm_verifier_core(
    self,
    vk_bytes: &[u8],
    claim_bytes: &[u8],
    proof_bytes: &[u8],
    fri: &FriParameters,
    verify_claim_index: u64,
  ) -> Result<FlockStage2VerifierCoreBenchmarkV1> {
    Stage3LoweringStatusV1::current().ensure_complete()?;
    let total_started = Instant::now();

    let phase_started = Instant::now();
    let prepared = self.prepare_ixvm_leaf(
      vk_bytes,
      claim_bytes,
      proof_bytes,
      fri,
      verify_claim_index,
    )?;
    let prepare_ns = elapsed_ns(phase_started);

    let phase_started = Instant::now();
    let witness = Stage2AirPcsFriWitnessV1::from_p3(&prepared, fri)?;
    let typed_witness_ns = elapsed_ns(phase_started);

    let phase_started = Instant::now();
    let relation = preflight_p3_verifier_leaf(&witness)?;
    let preflight_ns = elapsed_ns(phase_started);

    let phase_started = Instant::now();
    let relation_manifest =
      P3VerifierRelationManifestV1::for_prepared_and_program_digest(
        &prepared,
        fri,
        relation.circuit_digest,
      )?;
    let relation_digest = relation_manifest.relation_digest();
    let manifest_ns = elapsed_ns(phase_started);

    let preflight = FlockStage2LeafPreflightReportV1 {
      p3_statement_digest: prepared.statement().digest(),
      output_claim_digest: prepared.statement().ixvm_output_claim_digest()?,
      relation_digest,
      config_digest: FlockStage2ConfigV1.digest(),
      verifying_key_bytes: as_u64(vk_bytes.len(), "verifying-key bytes")?,
      claim_bytes: as_u64(claim_bytes.len(), "claim bytes")?,
      compact_proof_bytes: as_u64(proof_bytes.len(), "compact-proof bytes")?,
      advice: prepared.advice_profile().clone(),
      relation,
    };

    let phase_started = Instant::now();
    let flock_artifact = prove_p3_verifier_leaf(&witness)?;
    let same_witness_prove_ns = elapsed_ns(phase_started);
    if flock_artifact.circuit_digest() != &preflight.relation.circuit_digest {
      bail!("Flock verifier-core preflight and prover circuit digests differ");
    }
    let artifact = FlockStage2P3LeafArtifactV1 {
      statement: prepared.statement().clone(),
      relation_manifest: relation_manifest.clone(),
      flock_artifact,
    };

    let phase_started = Instant::now();
    self.verify_ixvm_leaf(
      &artifact,
      artifact.statement(),
      &preflight.relation_digest,
    )?;
    let valid_verify_ns = elapsed_ns(phase_started);
    let input_to_verified_output_ns = elapsed_ns(total_started);

    let inner = &artifact.flock_artifact;
    let mut corrupted_bundle = inner.proof_bundle_bytes().to_vec();
    let last = corrupted_bundle
      .len()
      .checked_sub(1)
      .ok_or_else(|| anyhow::anyhow!("Flock verifier-core proof is empty"))?;
    corrupted_bundle[last] ^= 1;
    let corrupted_inner = Stage2AirPcsFriArtifactV1::from_parts(
      inner.witness().clone(),
      *inner.circuit_digest(),
      corrupted_bundle,
    )?;
    let corrupted = FlockStage2P3LeafArtifactV1 {
      statement: artifact.statement.clone(),
      relation_manifest: artifact.relation_manifest.clone(),
      flock_artifact: corrupted_inner,
    };
    let phase_started = Instant::now();
    if self
      .verify_ixvm_leaf(
        &corrupted,
        corrupted.statement(),
        &preflight.relation_digest,
      )
      .is_ok()
    {
      bail!("corrupted Flock verifier-core proof was accepted");
    }
    let corrupt_reject_ns = elapsed_ns(phase_started);

    let proof_bundle_bytes =
      as_u64(artifact.proof_bundle_bytes().len(), "Flock proof-bundle bytes")?;
    Ok(FlockStage2VerifierCoreBenchmarkV1 {
      circuit_digest: *artifact.circuit_digest(),
      proof_bundle_digest: *blake3::hash(artifact.proof_bundle_bytes())
        .as_bytes(),
      proof_bundle_bytes,
      preflight,
      timings: FlockStage2VerifierCoreTimingsV1 {
        prepare_ns,
        typed_witness_ns,
        preflight_ns,
        manifest_ns,
        same_witness_prove_ns,
        valid_verify_ns,
        corrupt_reject_ns,
        input_to_verified_output_ns,
        wall_with_negative_check_ns: elapsed_ns(total_started),
      },
    })
  }

  /// Prove all eleven P3 verifier phases under the Stage 2 leaf transcript.
  pub fn prove_ixvm_leaf(
    self,
    vk_bytes: &[u8],
    claim_bytes: &[u8],
    proof_bytes: &[u8],
    fri: &FriParameters,
    verify_claim_index: u64,
  ) -> Result<FlockStage2P3LeafArtifactV1> {
    Stage3LoweringStatusV1::current().ensure_complete()?;
    let prepared = self.prepare_ixvm_leaf(
      vk_bytes,
      claim_bytes,
      proof_bytes,
      fri,
      verify_claim_index,
    )?;
    let witness = Stage2AirPcsFriWitnessV1::from_p3(&prepared, fri)?;
    let flock_artifact = prove_p3_verifier_leaf(&witness)?;
    let relation_manifest =
      P3VerifierRelationManifestV1::for_prepared_and_program_digest(
        &prepared,
        fri,
        *flock_artifact.circuit_digest(),
      )?;
    Ok(FlockStage2P3LeafArtifactV1 {
      statement: prepared.statement().clone(),
      relation_manifest,
      flock_artifact,
    })
  }

  /// Verify an in-process leaf against externally expected statement and
  /// relation identities.
  pub fn verify_ixvm_leaf(
    self,
    artifact: &FlockStage2P3LeafArtifactV1,
    expected_statement: &P3ProofStatementV1,
    expected_relation_digest: &[u8; 32],
  ) -> Result<()> {
    if artifact.statement != *expected_statement {
      bail!("Flock Stage 2 leaf targets a different P3 statement");
    }
    if artifact.relation_manifest.relation_digest() != *expected_relation_digest
    {
      bail!("Flock Stage 2 leaf uses a different relation manifest");
    }
    if artifact.relation_manifest.p3_verifying_key_digest()
      != expected_statement.verifying_key_digest()
      || artifact.relation_manifest.claim_layout()
        != expected_statement.claim_layout()
    {
      bail!("Flock Stage 2 leaf manifest targets a different P3 system");
    }
    if artifact.relation_manifest.relation_program_digest()
      != artifact.flock_artifact.circuit_digest()
    {
      bail!("Flock Stage 2 leaf circuit and relation manifest disagree");
    }
    if artifact.flock_artifact.witness().air.statement_digest
      != expected_statement.digest()
    {
      bail!("Flock Stage 2 leaf proof binds a different P3 statement");
    }
    if !matches!(
      expected_statement.claim_layout(),
      P3ClaimLayoutV1::Ixvm { .. }
    ) {
      bail!("Flock Stage 2 leaf requires the ten-word IxVM claim layout");
    }
    verify_p3_verifier_leaf(&artifact.flock_artifact)
  }
}

fn leaf_profile_report(
  prepared: &ValidatedP3ProofV1,
  vk_bytes: &[u8],
  claim_bytes: &[u8],
  proof_bytes: &[u8],
) -> Result<FlockStage2LeafProfileReportV1> {
  Ok(FlockStage2LeafProfileReportV1 {
    p3_statement_digest: prepared.statement().digest(),
    output_claim_digest: prepared.statement().ixvm_output_claim_digest()?,
    config_digest: FlockStage2ConfigV1.digest(),
    verifying_key_bytes: as_u64(vk_bytes.len(), "verifying-key bytes")?,
    claim_bytes: as_u64(claim_bytes.len(), "claim bytes")?,
    compact_proof_bytes: as_u64(proof_bytes.len(), "compact-proof bytes")?,
    advice: prepared.advice_profile().clone(),
  })
}

fn as_u64(value: usize, label: &str) -> Result<u64> {
  u64::try_from(value)
    .map_err(|error| anyhow::anyhow!("{label} exceeds u64: {error}"))
}

fn elapsed_ns(started: Instant) -> u64 {
  u64::try_from(started.elapsed().as_nanos()).unwrap_or(u64::MAX)
}

fn binary_bytes(bytes: u64) -> String {
  const GIB: f64 = 1024.0 * 1024.0 * 1024.0;
  if bytes >= 1024 * 1024 * 1024 {
    format!("{:.2} GiB", bytes as f64 / GIB)
  } else if bytes >= 1024 * 1024 {
    format!("{:.2} MiB", bytes as f64 / (1024.0 * 1024.0))
  } else if bytes >= 1024 {
    format!("{:.2} KiB", bytes as f64 / 1024.0)
  } else {
    format!("{bytes} B")
  }
}

fn digest_at(bytes: &[u8], offset: usize) -> [u8; 32] {
  bytes[offset..offset + 32].try_into().expect("digest slice")
}

fn read_u16(bytes: &[u8], offset: usize) -> u16 {
  u16::from_le_bytes(bytes[offset..offset + 2].try_into().expect("u16 slice"))
}

fn read_u64(bytes: &[u8], offset: usize) -> u64 {
  u64::from_le_bytes(bytes[offset..offset + 8].try_into().expect("u64 slice"))
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn stage2_config_is_distinct_and_domain_separated() {
    let bytes = FlockStage2ConfigV1.to_bytes();
    assert_eq!(&bytes[..8], FLOCK_STAGE2_CONFIG_DOMAIN);
    assert!(
      bytes
        .windows(FLOCK_UPSTREAM_REVISION.len())
        .any(|window| window == FLOCK_UPSTREAM_REVISION.as_bytes())
    );
    assert!(
      bytes
        .windows(FLOCK_STAGE2_P3_LEAF_TRANSCRIPT_DOMAIN.len())
        .any(|window| window == FLOCK_STAGE2_P3_LEAF_TRANSCRIPT_DOMAIN)
    );
    assert_ne!(FlockStage2ConfigV1.digest(), crate::FlockConfigV1.digest());
    assert_eq!(FlockStage2ConfigV1.leaf_profile(), LigeritoProfile::Fast128);
    assert_eq!(FlockStage2ConfigV1.merkle_hash(), HashKind::Blake3);
  }
}
