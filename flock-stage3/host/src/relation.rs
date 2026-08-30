use anyhow::{Result, bail};
use ix_terminal::{Stage2AdviceProfileV1, ValidatedStage2RootV1};
use multi_stark::types::FriParameters;

use crate::{
  FlockConfigV1, Stage2AirPcsFriWitnessV1, Stage3TypedProofWitnessV1,
  fri::stage2_air_pcs_fri_circuit_digest,
};

pub const STAGE3_RELATION_MANIFEST_DOMAIN: &[u8; 8] = b"IXFLKR01";
const STAGE3_RELATION_MANIFEST_VERSION: u16 = 1;

/// A semantic obligation that the production Flock relation must enforce.
///
/// These are deliberately coarser than individual helper functions, but fine
/// grained enough that a partial port cannot silently omit an entire verifier
/// phase. A phase bit may only be enabled together with tests that compare the
/// Flock lowering against the existing Aiur verifier.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Stage3VerifierPhaseV1 {
  TypedProofWitnessShape = 0,
  SpecializedVerifyingKeyBinding = 1,
  ClaimsDecodeAndCanonicality = 2,
  Stage2StatementBinding = 3,
  ShapeAndActivation = 4,
  LookupAccumulatorBalance = 5,
  FiatShamirReplay = 6,
  AirOodEvaluation = 7,
  PcsOpeningReduction = 8,
  MerkleMmcs = 9,
  FriGrindingFoldAndFinalPolynomial = 10,
}

pub const STAGE3_VERIFIER_PHASES_V1: [Stage3VerifierPhaseV1; 11] = [
  Stage3VerifierPhaseV1::TypedProofWitnessShape,
  Stage3VerifierPhaseV1::SpecializedVerifyingKeyBinding,
  Stage3VerifierPhaseV1::ClaimsDecodeAndCanonicality,
  Stage3VerifierPhaseV1::Stage2StatementBinding,
  Stage3VerifierPhaseV1::ShapeAndActivation,
  Stage3VerifierPhaseV1::LookupAccumulatorBalance,
  Stage3VerifierPhaseV1::FiatShamirReplay,
  Stage3VerifierPhaseV1::AirOodEvaluation,
  Stage3VerifierPhaseV1::PcsOpeningReduction,
  Stage3VerifierPhaseV1::MerkleMmcs,
  Stage3VerifierPhaseV1::FriGrindingFoldAndFinalPolynomial,
];

const REQUIRED_PHASE_MASK: u16 = (1 << STAGE3_VERIFIER_PHASES_V1.len()) - 1;

// Every phase is consumed by the single statement/AIR/PCS/FRI relation. The
// manifest still refuses to identify a deployable relation until the concrete
// compiled circuit digest has been installed.
const IMPLEMENTED_PHASE_MASK: u16 = REQUIRED_PHASE_MASK;

impl Stage3VerifierPhaseV1 {
  const fn bit(self) -> u16 {
    1 << self as u8
  }

  pub const fn name(self) -> &'static str {
    match self {
      Self::TypedProofWitnessShape => "typed-proof-witness-shape",
      Self::SpecializedVerifyingKeyBinding => {
        "specialized-verifying-key-binding"
      },
      Self::ClaimsDecodeAndCanonicality => "claims-decode-and-canonicality",
      Self::Stage2StatementBinding => "stage2-statement-binding",
      Self::ShapeAndActivation => "shape-and-activation",
      Self::LookupAccumulatorBalance => "lookup-accumulator-balance",
      Self::FiatShamirReplay => "fiat-shamir-replay",
      Self::AirOodEvaluation => "air-ood-evaluation",
      Self::PcsOpeningReduction => "pcs-opening-reduction",
      Self::MerkleMmcs => "merkle-mmcs",
      Self::FriGrindingFoldAndFinalPolynomial => {
        "fri-grinding-fold-and-final-polynomial"
      },
    }
  }
}

/// Auditable progress gate for the verifier lowering.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Stage3LoweringStatusV1 {
  implemented_phase_mask: u16,
}

impl Stage3LoweringStatusV1 {
  pub const fn current() -> Self {
    Self { implemented_phase_mask: IMPLEMENTED_PHASE_MASK }
  }

  pub const fn required_phase_mask(self) -> u16 {
    REQUIRED_PHASE_MASK
  }

  pub const fn implemented_phase_mask(self) -> u16 {
    self.implemented_phase_mask
  }

  pub const fn is_complete(self) -> bool {
    self.implemented_phase_mask == REQUIRED_PHASE_MASK
  }

  pub fn missing_phases(self) -> Vec<Stage3VerifierPhaseV1> {
    STAGE3_VERIFIER_PHASES_V1
      .into_iter()
      .filter(|phase| self.implemented_phase_mask & phase.bit() == 0)
      .collect()
  }

  pub fn ensure_complete(self) -> Result<()> {
    if self.is_complete() {
      return Ok(());
    }
    let missing = self
      .missing_phases()
      .into_iter()
      .map(Stage3VerifierPhaseV1::name)
      .collect::<Vec<_>>()
      .join(", ");
    bail!("Flock Stage 3 verifier lowering is incomplete; missing: {missing}")
  }
}

/// Fixed capacity of one compiled Stage 3 verifier relation.
///
/// `for_prepared` seeds every maximum from one measured root. That is useful
/// while developing the lowering, but it is not a production capacity study:
/// the final values must cover the intended corpus before the relation program
/// digest is frozen.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stage3RelationBoundsV1 {
  pub verifying_key_bytes: u64,
  pub claims_bytes: u64,
  pub advice: Stage2AdviceProfileV1,
}

impl Stage3RelationBoundsV1 {
  fn for_prepared(prepared: &ValidatedStage2RootV1) -> Result<Self> {
    Ok(Self {
      verifying_key_bytes: as_u64(
        prepared.verifying_key_bytes().len(),
        "verifying-key bytes",
      )?,
      claims_bytes: as_u64(prepared.claims_bytes().len(), "claims bytes")?,
      advice: prepared.advice_profile().clone(),
    })
  }

  fn canonical_words(&self) -> [u64; 14] {
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

  fn ensure_accommodates(
    &self,
    prepared: &ValidatedStage2RootV1,
  ) -> Result<()> {
    let observed = Self::for_prepared(prepared)?;
    if observed.verifying_key_bytes != self.verifying_key_bytes {
      bail!("Stage 2 verifying-key byte length differs from relation shape");
    }
    if observed.claims_bytes != self.claims_bytes {
      bail!("Stage 2 claims byte length differs from relation shape");
    }
    if observed.advice.total_circuits != self.advice.total_circuits {
      bail!("Stage 2 circuit count differs from relation shape");
    }
    if observed.advice.queries != self.advice.queries {
      bail!("Stage 2 query count differs from relation shape");
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
      bail!(
        "Stage 2 {label} ({observed}) exceeds relation capacity ({maximum})"
      );
    }
    Ok(())
  }
}

/// Canonical identity of a specialised Stage 3 verifier relation.
///
/// The constructor compiles the relation and installs its circuit digest.
/// `relation_digest` additionally binds the Flock configuration, specialised
/// Stage 2 key, witness layout, phase mask, and exact measured capacity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stage3RelationManifestV1 {
  stage2_verifying_key_digest: [u8; 32],
  typed_witness_layout_digest: [u8; 32],
  relation_program_digest: Option<[u8; 32]>,
  bounds: Stage3RelationBoundsV1,
  lowering_status: Stage3LoweringStatusV1,
}

impl Stage3RelationManifestV1 {
  pub fn for_prepared(prepared: &ValidatedStage2RootV1) -> Result<Self> {
    let fri = statement_fri_parameters(prepared)?;
    let witness = Stage2AirPcsFriWitnessV1::from_prepared(prepared, &fri)?;
    let relation_program_digest = stage2_air_pcs_fri_circuit_digest(&witness)?;
    Self::for_prepared_and_program_digest(prepared, relation_program_digest)
  }

  pub(crate) fn for_prepared_and_program_digest(
    prepared: &ValidatedStage2RootV1,
    relation_program_digest: [u8; 32],
  ) -> Result<Self> {
    let fri = statement_fri_parameters(prepared)?;
    let typed_witness =
      Stage3TypedProofWitnessV1::from_prepared(prepared, &fri)?;
    Ok(Self {
      stage2_verifying_key_digest: *prepared.statement().verifying_key_digest(),
      typed_witness_layout_digest: typed_witness.layout_digest(),
      relation_program_digest: Some(relation_program_digest),
      bounds: Stage3RelationBoundsV1::for_prepared(prepared)?,
      lowering_status: Stage3LoweringStatusV1::current(),
    })
  }

  pub fn stage2_verifying_key_digest(&self) -> &[u8; 32] {
    &self.stage2_verifying_key_digest
  }

  pub fn typed_witness_layout_digest(&self) -> &[u8; 32] {
    &self.typed_witness_layout_digest
  }

  pub fn bounds(&self) -> &Stage3RelationBoundsV1 {
    &self.bounds
  }

  pub const fn lowering_status(&self) -> Stage3LoweringStatusV1 {
    self.lowering_status
  }

  pub fn ensure_accommodates(
    &self,
    prepared: &ValidatedStage2RootV1,
  ) -> Result<()> {
    if prepared.statement().verifying_key_digest()
      != &self.stage2_verifying_key_digest
    {
      bail!("Stage 2 verifying key differs from the specialised relation");
    }
    self.bounds.ensure_accommodates(prepared)
  }

  /// Return the digest used in `Stage3StatementV1` for the complete,
  /// content-addressed relation program and its exact capacity.
  pub fn relation_digest(&self) -> Result<[u8; 32]> {
    self.lowering_status.ensure_complete()?;
    if self.relation_program_digest.is_none() {
      bail!("Flock Stage 3 relation program has not been built and digested");
    }
    Ok(*blake3::hash(&self.canonical_bytes()).as_bytes())
  }

  fn canonical_bytes(&self) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(8 + 2 + 32 * 4 + 2 + 2 + 14 * 8);
    bytes.extend_from_slice(STAGE3_RELATION_MANIFEST_DOMAIN);
    bytes.extend_from_slice(&STAGE3_RELATION_MANIFEST_VERSION.to_le_bytes());
    bytes.extend_from_slice(&FlockConfigV1.digest());
    bytes.extend_from_slice(&self.stage2_verifying_key_digest);
    bytes.extend_from_slice(&self.typed_witness_layout_digest);
    bytes.extend_from_slice(&self.relation_program_digest.unwrap_or([0; 32]));
    bytes.extend_from_slice(
      &self.lowering_status.required_phase_mask().to_le_bytes(),
    );
    bytes.extend_from_slice(
      &self.lowering_status.implemented_phase_mask().to_le_bytes(),
    );
    for word in self.bounds.canonical_words() {
      bytes.extend_from_slice(&word.to_le_bytes());
    }
    bytes
  }
}

fn statement_fri_parameters(
  prepared: &ValidatedStage2RootV1,
) -> Result<FriParameters> {
  let [log_final_poly_len, max_log_arity, num_queries, commit_pow, query_pow] =
    *prepared.statement().fri_parameter_words();
  let convert = |value, label| {
    usize::try_from(value).map_err(|error| {
      anyhow::anyhow!("Stage 2 {label} does not fit usize: {error}")
    })
  };
  Ok(FriParameters {
    log_final_poly_len: convert(log_final_poly_len, "final polynomial log")?,
    max_log_arity: convert(max_log_arity, "maximum FRI arity log")?,
    num_queries: convert(num_queries, "query count")?,
    commit_proof_of_work_bits: convert(commit_pow, "commit PoW bits")?,
    query_proof_of_work_bits: convert(query_pow, "query PoW bits")?,
  })
}

fn as_u64(value: usize, label: &str) -> Result<u64> {
  u64::try_from(value)
    .map_err(|error| anyhow::anyhow!("{label} exceeds u64: {error}"))
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn phase_registry_is_complete_and_unique() {
    let status = Stage3LoweringStatusV1::current();
    assert_eq!(status.required_phase_mask(), 0x07ff);
    assert_eq!(status.implemented_phase_mask(), 0x07ff);
    assert!(status.is_complete());
    assert!(status.missing_phases().is_empty());
    status.ensure_complete().unwrap();
  }
}
