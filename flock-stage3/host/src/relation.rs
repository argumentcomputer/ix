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

/// Exact transport and advice shape of one compiled Stage 3 verifier relation.
///
/// The current relation has no padding/activation layer that would make these
/// values reusable maxima. Every word therefore identifies the exact witness
/// shape used to compile the relation. A future capacity-based relation needs a
/// new manifest version and explicit in-circuit padding constraints.
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

  fn ensure_matches(&self, prepared: &ValidatedStage2RootV1) -> Result<()> {
    let observed = Self::for_prepared(prepared)?;
    self.ensure_same_shape(&observed)
  }

  fn ensure_same_shape(&self, observed: &Self) -> Result<()> {
    let labels = [
      "verifying-key bytes",
      "claims bytes",
      "advice bytes",
      "total circuits",
      "active circuits",
      "queries",
      "FRI rounds",
      "input rounds per query",
      "commitment cap digests",
      "input Merkle siblings",
      "FRI Merkle siblings",
      "opened base values",
      "FRI sibling extension values",
      "other extension values",
    ];
    let expected_words = self.canonical_words();
    let observed_words = observed.canonical_words();
    if let Some((label, (expected, observed))) = labels
      .into_iter()
      .zip(expected_words.into_iter().zip(observed_words))
      .find(|(_, (expected, observed))| expected != observed)
    {
      bail!(
        "Stage 2 {label} differs from the exact relation shape: expected {expected}, observed {observed}"
      );
    }
    Ok(())
  }
}

/// Canonical identity of a specialised Stage 3 verifier relation.
///
/// The constructor compiles the relation and installs its circuit digest.
/// `relation_digest` additionally binds the Flock configuration, specialised
/// Stage 2 key, witness layout, phase mask, and exact measured shape.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stage3RelationManifestV1 {
  stage2_verifying_key_digest: [u8; 32],
  typed_witness_layout_digest: [u8; 32],
  // These values are already bound by the compiled circuit digest. Retain
  // them here as well so reuse checks cover specialization, not just lengths.
  activation: Vec<bool>,
  log_degrees: Vec<u8>,
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
    Self::for_prepared_and_typed(
      prepared,
      &typed_witness,
      relation_program_digest,
    )
  }

  pub(crate) fn for_prepared_and_typed(
    prepared: &ValidatedStage2RootV1,
    typed_witness: &Stage3TypedProofWitnessV1,
    relation_program_digest: [u8; 32],
  ) -> Result<Self> {
    typed_witness.ensure_profile(prepared.advice_profile())?;
    Ok(Self {
      stage2_verifying_key_digest: *prepared.statement().verifying_key_digest(),
      typed_witness_layout_digest: typed_witness.layout_digest(),
      activation: typed_witness.active.clone(),
      log_degrees: typed_witness.log_degrees.clone(),
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

  pub fn ensure_matches(&self, prepared: &ValidatedStage2RootV1) -> Result<()> {
    if prepared.statement().verifying_key_digest()
      != &self.stage2_verifying_key_digest
    {
      bail!("Stage 2 verifying key differs from the specialised relation");
    }
    self.bounds.ensure_matches(prepared)?;

    let fri = statement_fri_parameters(prepared)?;
    let observed = Stage3TypedProofWitnessV1::from_prepared(prepared, &fri)?;
    self.ensure_layout_digest(observed.layout_digest())?;
    if observed.active != self.activation {
      bail!("Stage 2 activation pattern differs from the specialised relation");
    }
    if observed.log_degrees != self.log_degrees {
      bail!(
        "Stage 2 active trace heights differ from the specialised relation"
      );
    }
    Ok(())
  }

  /// Compatibility spelling retained for callers written against the earlier
  /// capacity terminology. The check is exact, not a less-than-or-equal test.
  pub fn ensure_accommodates(
    &self,
    prepared: &ValidatedStage2RootV1,
  ) -> Result<()> {
    self.ensure_matches(prepared)
  }

  fn ensure_layout_digest(&self, observed: [u8; 32]) -> Result<()> {
    if observed != self.typed_witness_layout_digest {
      bail!(
        "Stage 2 typed witness layout differs from the exact relation shape"
      );
    }
    Ok(())
  }

  /// Return the digest used in `Stage3StatementV1` for the complete,
  /// content-addressed relation program and its exact witness shape.
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
  use crate::test_support::interchangeable_root;

  #[test]
  fn manifest_reuse_checks_specialization_even_when_layout_matches() {
    for (first, second, message) in [
      ([4, 0], [0, 4], "activation pattern"),
      ([8, 4], [4, 8], "active trace heights"),
    ] {
      let first = interchangeable_root(first, 256);
      let second = interchangeable_root(second, 256);
      assert_eq!(first.advice_profile(), second.advice_profile());
      let manifest = Stage3RelationManifestV1::for_prepared(&first).unwrap();
      let fri = statement_fri_parameters(&second).unwrap();
      let typed =
        Stage3TypedProofWitnessV1::from_prepared(&second, &fri).unwrap();
      assert_eq!(
        manifest.typed_witness_layout_digest(),
        &typed.layout_digest()
      );
      assert!(
        manifest
          .ensure_matches(&second)
          .unwrap_err()
          .to_string()
          .contains(message)
      );
      assert!(
        crate::FlockStage3Backend
          .prepare_statement(&second, &manifest)
          .is_err()
      );
    }
  }

  #[test]
  fn different_claims_preserve_the_same_specialized_relation() {
    let first = interchangeable_root([4, 0], 256);
    let second = interchangeable_root([4, 0], 512);
    let first_manifest =
      Stage3RelationManifestV1::for_prepared(&first).unwrap();
    let second_manifest =
      Stage3RelationManifestV1::for_prepared(&second).unwrap();
    assert_ne!(first.statement(), second.statement());
    first_manifest.ensure_matches(&second).unwrap();
    assert_eq!(
      first_manifest.relation_digest().unwrap(),
      second_manifest.relation_digest().unwrap()
    );
  }

  fn relation_shape() -> Stage3RelationBoundsV1 {
    Stage3RelationBoundsV1 {
      verifying_key_bytes: 10,
      claims_bytes: 160,
      advice: Stage2AdviceProfileV1 {
        advice_bytes: 1_000,
        total_circuits: 8,
        active_circuits: 3,
        queries: 100,
        fri_rounds: 20,
        input_rounds_per_query: 4,
        commitment_cap_digests: 23,
        input_merkle_siblings: 2_400,
        fri_merkle_siblings: 19_000,
        opened_base_values: 12_000,
        fri_sibling_extension_values: 2_000,
        other_extension_values: 900,
      },
    }
  }

  #[test]
  fn phase_registry_is_complete_and_unique() {
    let status = Stage3LoweringStatusV1::current();
    assert_eq!(status.required_phase_mask(), 0x07ff);
    assert_eq!(status.implemented_phase_mask(), 0x07ff);
    assert!(status.is_complete());
    assert!(status.missing_phases().is_empty());
    status.ensure_complete().unwrap();
  }

  #[test]
  fn relation_shape_is_exact_instead_of_a_maximum() {
    let expected = relation_shape();
    assert!(expected.ensure_same_shape(&expected).is_ok());

    let mut smaller = expected.clone();
    smaller.advice.active_circuits -= 1;
    let error = expected.ensure_same_shape(&smaller).unwrap_err().to_string();
    assert!(error.contains("active circuits"));
    assert!(error.contains("expected 3, observed 2"));

    let mut larger = expected.clone();
    larger.advice.fri_merkle_siblings += 1;
    let error = expected.ensure_same_shape(&larger).unwrap_err().to_string();
    assert!(error.contains("FRI Merkle siblings"));
    assert!(error.contains("expected 19000, observed 19001"));
  }

  #[test]
  fn manifest_rejects_a_different_nested_layout_digest() {
    let manifest = Stage3RelationManifestV1 {
      stage2_verifying_key_digest: [0; 32],
      typed_witness_layout_digest: [1; 32],
      activation: vec![],
      log_degrees: vec![],
      relation_program_digest: Some([2; 32]),
      bounds: relation_shape(),
      lowering_status: Stage3LoweringStatusV1::current(),
    };
    assert!(manifest.ensure_layout_digest([1; 32]).is_ok());
    assert!(manifest.ensure_layout_digest([3; 32]).is_err());
  }
}
