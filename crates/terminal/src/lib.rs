//! Canonical boundary between the recursive Aiur aggregate and terminal
//! compression backends.
//!
//! SP1 and Flock must validate and bind exactly the same Stage 2 statement.
//! This crate owns that byte-level contract so terminal backends cannot drift.

use aiur::{G, synthesis::AiurProof, vk_codec::AiurVerifyingKey};
use anyhow::{Result, bail};
use bincode::{config, serde::decode_from_slice};
use multi_stark::{
  advice::AdviceProof,
  p3_field::{PrimeCharacteristicRing, PrimeField64},
  types::FriParameters,
};

/// Domain of the canonical Stage 2 aggregate-root statement.
///
/// This value is already used by the SP1 compressor and must not change
/// without introducing a new statement version.
pub const STAGE2_ROOT_DOMAIN: &[u8; 8] = b"IXROOT01";
/// Backwards-compatible name used by the SP1 public-values API.
pub const PUBLIC_VALUES_DOMAIN: &[u8; 8] = STAGE2_ROOT_DOMAIN;
pub const OUTER_CLAIM_ELEMENTS: usize = 18;
pub const FRI_PARAMETER_ELEMENTS: usize = 5;
pub const FRI_PARAMETERS_BYTES: usize = FRI_PARAMETER_ELEMENTS * 8;
pub const OUTER_CLAIM_BYTES: usize = OUTER_CLAIM_ELEMENTS * 8;
pub const STAGE2_CLAIMS_BYTES: usize = 8 + 8 + OUTER_CLAIM_BYTES;
pub const STAGE2_ROOT_STATEMENT_BYTES: usize =
  STAGE2_ROOT_DOMAIN.len() + 32 + FRI_PARAMETERS_BYTES + OUTER_CLAIM_BYTES;

const ADVICE_PROFILE_DOMAIN: &[u8; 8] = b"IXADVP01";

/// Versioned, canonical public statement asserted by a closed Stage 2 root.
///
/// Wire format:
/// `IXROOT01 || blake3(aiur_vk) || five FRI u64s LE || 18 Goldilocks u64s LE`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stage2RootStatementV1 {
  verifying_key_digest: [u8; 32],
  fri_parameters: [u64; FRI_PARAMETER_ELEMENTS],
  outer_claim: [u64; OUTER_CLAIM_ELEMENTS],
}

/// Shape census of the verified, per-query proof transport consumed by the
/// Flock verifier. This is diagnostic input to the Flock capacity model;
/// it is not itself a proof or a substitute for in-relation shape checks.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stage2AdviceProfileV1 {
  pub advice_bytes: u64,
  pub total_circuits: u64,
  pub active_circuits: u64,
  pub queries: u64,
  pub fri_rounds: u64,
  pub input_rounds_per_query: u64,
  pub commitment_cap_digests: u64,
  pub input_merkle_siblings: u64,
  pub fri_merkle_siblings: u64,
  pub opened_base_values: u64,
  pub fri_sibling_extension_values: u64,
  pub other_extension_values: u64,
}

impl Stage2AdviceProfileV1 {
  /// Parse the canonical Flock-verifier advice and census its fixed and
  /// capacity-driving dimensions. The parser requires exact byte consumption.
  pub fn from_advice_bytes(bytes: &[u8], fri: &FriParameters) -> Result<Self> {
    profile_advice(bytes, fri)
  }

  pub fn to_bytes(&self) -> Vec<u8> {
    let words = [
      self.advice_bytes,
      self.total_circuits,
      self.active_circuits,
      self.queries,
      self.fri_rounds,
      self.input_rounds_per_query,
      self.commitment_cap_digests,
      self.input_merkle_siblings,
      self.fri_merkle_siblings,
      self.opened_base_values,
      self.fri_sibling_extension_values,
      self.other_extension_values,
    ];
    let mut bytes =
      Vec::with_capacity(ADVICE_PROFILE_DOMAIN.len() + words.len() * 8);
    bytes.extend_from_slice(ADVICE_PROFILE_DOMAIN);
    for word in words {
      bytes.extend_from_slice(&word.to_le_bytes());
    }
    bytes
  }

  pub fn digest(&self) -> [u8; 32] {
    *blake3::hash(&self.to_bytes()).as_bytes()
  }
}

/// A compact proof that has been verified and expanded to the per-query advice
/// layout used by Flock Stage 3. The verifying key is retained for compiling a
/// specialised typed verifier witness; the claims remain the private words
/// bound by the Stage 2 statement inside that relation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ValidatedStage2RootV1 {
  statement: Stage2RootStatementV1,
  verifying_key_bytes: Vec<u8>,
  claims_bytes: Vec<u8>,
  advice_bytes: Vec<u8>,
  advice_profile: Stage2AdviceProfileV1,
}

impl ValidatedStage2RootV1 {
  pub fn statement(&self) -> &Stage2RootStatementV1 {
    &self.statement
  }

  pub fn verifying_key_bytes(&self) -> &[u8] {
    &self.verifying_key_bytes
  }

  pub fn claims_bytes(&self) -> &[u8] {
    &self.claims_bytes
  }

  pub fn advice_bytes(&self) -> &[u8] {
    &self.advice_bytes
  }

  pub fn advice_profile(&self) -> &Stage2AdviceProfileV1 {
    &self.advice_profile
  }
}

impl Stage2RootStatementV1 {
  /// Construct the statement while enforcing the exact claim shape and
  /// canonical Goldilocks encoding.
  pub fn new(
    vk_bytes: &[u8],
    claim_bytes: &[u8],
    fri: &FriParameters,
  ) -> Result<Self> {
    Ok(Self {
      verifying_key_digest: *blake3::hash(vk_bytes).as_bytes(),
      fri_parameters: fri_parameter_words(fri),
      outer_claim: decode_claim_words(claim_bytes)?,
    })
  }

  /// Parse the canonical format. Exact length, domain, and field encodings are
  /// checked; trailing bytes are rejected.
  pub fn from_bytes(bytes: &[u8]) -> Result<Self> {
    if bytes.len() != STAGE2_ROOT_STATEMENT_BYTES {
      bail!(
        "Stage 2 root statement is {} bytes; expected {STAGE2_ROOT_STATEMENT_BYTES}",
        bytes.len()
      );
    }
    if &bytes[..STAGE2_ROOT_DOMAIN.len()] != STAGE2_ROOT_DOMAIN {
      bail!("invalid Stage 2 root statement domain");
    }

    let mut verifying_key_digest = [0u8; 32];
    verifying_key_digest.copy_from_slice(&bytes[8..40]);

    let mut fri_parameters = [0u64; FRI_PARAMETER_ELEMENTS];
    for (word, chunk) in
      fri_parameters.iter_mut().zip(bytes[40..80].as_chunks::<8>().0)
    {
      *word = u64::from_le_bytes(*chunk);
    }

    Ok(Self {
      verifying_key_digest,
      fri_parameters,
      outer_claim: decode_claim_words(&bytes[80..])?,
    })
  }

  pub fn to_bytes(&self) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(STAGE2_ROOT_STATEMENT_BYTES);
    bytes.extend_from_slice(STAGE2_ROOT_DOMAIN);
    bytes.extend_from_slice(&self.verifying_key_digest);
    for word in self.fri_parameters {
      bytes.extend_from_slice(&word.to_le_bytes());
    }
    for word in self.outer_claim {
      bytes.extend_from_slice(&word.to_le_bytes());
    }
    debug_assert_eq!(bytes.len(), STAGE2_ROOT_STATEMENT_BYTES);
    bytes
  }

  /// BLAKE3 digest of the complete, domain-separated canonical statement.
  pub fn digest(&self) -> [u8; 32] {
    *blake3::hash(&self.to_bytes()).as_bytes()
  }

  pub fn verifying_key_digest(&self) -> &[u8; 32] {
    &self.verifying_key_digest
  }

  pub fn fri_parameter_words(&self) -> &[u64; FRI_PARAMETER_ELEMENTS] {
    &self.fri_parameters
  }

  pub fn outer_claim_words(&self) -> &[u64; OUTER_CLAIM_ELEMENTS] {
    &self.outer_claim
  }
}

pub fn fri_parameter_words(
  fri: &FriParameters,
) -> [u64; FRI_PARAMETER_ELEMENTS] {
  [
    fri.log_final_poly_len as u64,
    fri.max_log_arity as u64,
    fri.num_queries as u64,
    fri.commit_proof_of_work_bits as u64,
    fri.query_proof_of_work_bits as u64,
  ]
}

pub fn fri_parameters_to_bytes(fri: &FriParameters) -> Vec<u8> {
  fri_parameter_words(fri)
    .iter()
    .flat_map(|value| value.to_le_bytes())
    .collect()
}

/// Decode the exact 18-word outer claim and reject non-canonical Goldilocks
/// representatives.
pub fn decode_claim_words(
  claim_bytes: &[u8],
) -> Result<[u64; OUTER_CLAIM_ELEMENTS]> {
  if claim_bytes.len() != OUTER_CLAIM_BYTES {
    bail!(
      "ix_aggr outer claim is {} bytes; expected {OUTER_CLAIM_BYTES} (18 Goldilocks words)",
      claim_bytes.len()
    );
  }

  let mut words = [0u64; OUTER_CLAIM_ELEMENTS];
  for (index, (word_out, chunk)) in
    words.iter_mut().zip(claim_bytes.as_chunks::<8>().0).enumerate()
  {
    let word = u64::from_le_bytes(*chunk);
    let value = G::from_u64(word);
    if value.as_canonical_u64() != word {
      bail!("outer claim word {index} is not canonical Goldilocks");
    }
    *word_out = word;
  }
  Ok(words)
}

/// Canonical `&[&[Goldilocks]]` encoding consumed by the existing recursive
/// verifier: one claim, its 18-word length, then its little-endian words.
pub fn stage2_claims_bytes(claim_bytes: &[u8]) -> Result<Vec<u8>> {
  let words = decode_claim_words(claim_bytes)?;
  let mut bytes = Vec::with_capacity(STAGE2_CLAIMS_BYTES);
  bytes.extend_from_slice(&1u64.to_le_bytes());
  bytes.extend_from_slice(&(OUTER_CLAIM_ELEMENTS as u64).to_le_bytes());
  for word in words {
    bytes.extend_from_slice(&word.to_le_bytes());
  }
  Ok(bytes)
}

fn fri_matches(actual: &FriParameters, expected: &FriParameters) -> bool {
  fri_parameter_words(actual) == fri_parameter_words(expected)
}

struct DecodedRootInputs {
  statement: Stage2RootStatementV1,
  claim: Vec<G>,
  verifying_key: AiurVerifyingKey,
  proof: AiurProof,
}

fn decode_root_inputs(
  vk_bytes: &[u8],
  claim_bytes: &[u8],
  proof_bytes: &[u8],
  fri: &FriParameters,
) -> Result<DecodedRootInputs> {
  let statement = Stage2RootStatementV1::new(vk_bytes, claim_bytes, fri)?;
  let claim: Vec<G> =
    statement.outer_claim.iter().copied().map(G::from_u64).collect();
  let verifying_key = AiurVerifyingKey::from_bytes(vk_bytes)
    .map_err(|error| anyhow::anyhow!("invalid Aiur verifying key: {error}"))?;
  if verifying_key.to_bytes() != vk_bytes {
    bail!("Aiur verifying key is not canonically encoded");
  }
  if !fri_matches(&verifying_key.fri_parameters(), fri) {
    bail!("requested recursion FRI parameters do not match the Aiur vk");
  }
  let proof = AiurProof::from_bytes(proof_bytes)
    .map_err(|error| anyhow::anyhow!("invalid Aiur proof: {error}"))?;
  let canonical_proof = proof
    .to_bytes()
    .map_err(|error| anyhow::anyhow!("re-encode Aiur proof: {error}"))?;
  if canonical_proof != proof_bytes {
    bail!("Aiur proof is non-canonical or contains trailing bytes");
  }
  Ok(DecodedRootInputs { statement, claim, verifying_key, proof })
}

/// Validate a persisted aggregate root natively and return the exact public
/// statement terminal backends must prove. A backend circuit must repeat all
/// verification checks; this native pass is a cost and ergonomics guard.
pub fn validate_root_inputs(
  vk_bytes: &[u8],
  claim_bytes: &[u8],
  proof_bytes: &[u8],
  fri: &FriParameters,
) -> Result<Stage2RootStatementV1> {
  let decoded = decode_root_inputs(vk_bytes, claim_bytes, proof_bytes, fri)?;
  decoded.verifying_key.verify(&decoded.claim, &decoded.proof).map_err(
    |error| anyhow::anyhow!("aggregate root does not verify: {error:?}"),
  )?;
  Ok(decoded.statement)
}

/// Verify a compact Stage 2 root and expand its pruned Merkle multiproofs into
/// the per-query advice layout consumed by the Flock Stage 3 verifier.
/// No host-derived acceptance bit crosses the boundary: Stage 3 must parse and
/// re-check these retained vk, claim, and advice bytes inside its relation.
pub fn validate_and_expand_root_inputs(
  vk_bytes: &[u8],
  claim_bytes: &[u8],
  proof_bytes: &[u8],
  fri: &FriParameters,
) -> Result<ValidatedStage2RootV1> {
  let decoded = decode_root_inputs(vk_bytes, claim_bytes, proof_bytes, fri)?;
  let advice_bytes = decoded
    .verifying_key
    .proof_to_per_query_advice_bytes(&decoded.claim, &decoded.proof)
    .map_err(|error| anyhow::anyhow!("expand verified Aiur proof: {error}"))?;
  let advice_profile =
    Stage2AdviceProfileV1::from_advice_bytes(&advice_bytes, fri)?;
  Ok(ValidatedStage2RootV1 {
    statement: decoded.statement,
    verifying_key_bytes: vk_bytes.to_vec(),
    claims_bytes: stage2_claims_bytes(claim_bytes)?,
    advice_bytes,
    advice_profile,
  })
}

fn profile_advice(
  bytes: &[u8],
  fri: &FriParameters,
) -> Result<Stage2AdviceProfileV1> {
  let proof = decode_stage2_advice(bytes, fri)?;

  let input_rounds_per_query = proof
    .opening_proof
    .query_proofs
    .first()
    .map_or(0, |query| query.input_proof.len());
  let commitment_cap_digests = proof.commitments.stage_1_trace.roots().len()
    + proof.commitments.stage_2_trace.roots().len()
    + proof.commitments.quotient_chunks.roots().len()
    + proof
      .opening_proof
      .commit_phase_commits
      .iter()
      .map(|commitment| commitment.roots().len())
      .sum::<usize>();
  let input_merkle_siblings = proof
    .opening_proof
    .query_proofs
    .iter()
    .flat_map(|query| &query.input_proof)
    .map(|opening| opening.opening_proof.len())
    .sum();
  let fri_merkle_siblings = proof
    .opening_proof
    .query_proofs
    .iter()
    .flat_map(|query| &query.commit_phase_openings)
    .map(|opening| opening.opening_proof.len())
    .sum();
  let opened_base_values = proof
    .opening_proof
    .query_proofs
    .iter()
    .flat_map(|query| &query.input_proof)
    .flat_map(|opening| &opening.opened_values)
    .map(Vec::len)
    .sum();
  let fri_sibling_extension_values = proof
    .opening_proof
    .query_proofs
    .iter()
    .flat_map(|query| &query.commit_phase_openings)
    .map(|opening| opening.sibling_values.len())
    .sum();
  let other_extension_values = proof.intermediate_accumulators.len()
    + count_opened_values(&proof.quotient_opened_values)
    + proof
      .preprocessed_opened_values
      .as_ref()
      .map_or(0, |values| count_opened_values(values))
    + count_opened_values(&proof.stage_1_opened_values)
    + count_opened_values(&proof.stage_2_opened_values)
    + proof.opening_proof.final_poly.len();

  Ok(Stage2AdviceProfileV1 {
    advice_bytes: to_u64(bytes.len(), "advice bytes")?,
    total_circuits: to_u64(proof.active.len(), "circuit count")?,
    active_circuits: to_u64(
      proof.active.iter().filter(|&&active| active).count(),
      "active circuit count",
    )?,
    queries: to_u64(proof.opening_proof.query_proofs.len(), "query count")?,
    fri_rounds: to_u64(
      proof.opening_proof.commit_phase_commits.len(),
      "FRI round count",
    )?,
    input_rounds_per_query: to_u64(
      input_rounds_per_query,
      "input rounds per query",
    )?,
    commitment_cap_digests: to_u64(
      commitment_cap_digests,
      "commitment cap digests",
    )?,
    input_merkle_siblings: to_u64(
      input_merkle_siblings,
      "input Merkle siblings",
    )?,
    fri_merkle_siblings: to_u64(fri_merkle_siblings, "FRI Merkle siblings")?,
    opened_base_values: to_u64(opened_base_values, "opened base values")?,
    fri_sibling_extension_values: to_u64(
      fri_sibling_extension_values,
      "FRI sibling extension values",
    )?,
    other_extension_values: to_u64(
      other_extension_values,
      "other extension values",
    )?,
  })
}

/// Decode the canonical per-query Stage 2 proof transport into semantic proof
/// fields. The persisted bincode representation ends here: Flock backends
/// should lower this typed value, not reproduce byte parsing in their
/// relation.
pub fn decode_stage2_advice(
  bytes: &[u8],
  fri: &FriParameters,
) -> Result<AdviceProof> {
  let codec = config::standard().with_little_endian().with_fixed_int_encoding();
  let (proof, consumed): (AdviceProof, usize) = decode_from_slice(bytes, codec)
    .map_err(|error| {
      anyhow::anyhow!("decode canonical Stage 2 advice: {error}")
    })?;
  if consumed != bytes.len() {
    bail!("Stage 2 advice contains trailing bytes");
  }
  if proof.opening_proof.query_proofs.len() != fri.num_queries {
    bail!(
      "Stage 2 advice has {} queries; expected {}",
      proof.opening_proof.query_proofs.len(),
      fri.num_queries
    );
  }

  let input_rounds_per_query = proof
    .opening_proof
    .query_proofs
    .first()
    .map_or(0, |query| query.input_proof.len());
  if proof.opening_proof.query_proofs.iter().any(|query| {
    query.input_proof.len() != input_rounds_per_query
      || query.commit_phase_openings.len()
        != proof.opening_proof.commit_phase_commits.len()
  }) {
    bail!("Stage 2 advice has non-uniform per-query round counts");
  }
  Ok(proof)
}

fn count_opened_values<T>(values: &[Vec<Vec<T>>]) -> usize {
  values.iter().flat_map(|matrix| matrix.iter()).map(Vec::len).sum()
}

fn to_u64(value: usize, label: &str) -> Result<u64> {
  u64::try_from(value)
    .map_err(|error| anyhow::anyhow!("{label} exceeds u64: {error}"))
}

/// Backwards-compatible SP1 public-values constructor.
pub fn expected_public_values(
  vk_bytes: &[u8],
  claim_bytes: &[u8],
  fri: &FriParameters,
) -> Result<Vec<u8>> {
  Ok(Stage2RootStatementV1::new(vk_bytes, claim_bytes, fri)?.to_bytes())
}

#[cfg(test)]
mod tests {
  use super::*;
  use multi_stark::{
    advice::proof_to_advice_bytes,
    p3_matrix::dense::RowMajorMatrix,
    system::{CircuitInputs, System, SystemWitness},
    types::{CommitmentParameters, GoldilocksBlake3Config},
  };

  fn test_fri() -> FriParameters {
    FriParameters {
      log_final_poly_len: 0,
      max_log_arity: 1,
      num_queries: 100,
      commit_proof_of_work_bits: 0,
      query_proof_of_work_bits: 20,
    }
  }

  fn canonical_claim() -> Vec<u8> {
    (0..OUTER_CLAIM_ELEMENTS as u64).flat_map(u64::to_le_bytes).collect()
  }

  #[test]
  fn statement_round_trip_is_exact() {
    let statement =
      Stage2RootStatementV1::new(b"vk", &canonical_claim(), &test_fri())
        .expect("statement");
    let bytes = statement.to_bytes();
    assert_eq!(bytes.len(), STAGE2_ROOT_STATEMENT_BYTES);
    assert_eq!(&bytes[..8], STAGE2_ROOT_DOMAIN);
    assert_eq!(&bytes[8..40], blake3::hash(b"vk").as_bytes());
    assert_eq!(&bytes[40..80], fri_parameters_to_bytes(&test_fri()));
    assert_eq!(&bytes[80..], canonical_claim());
    assert_eq!(Stage2RootStatementV1::from_bytes(&bytes).unwrap(), statement);
    assert_eq!(
      blake3::Hash::from_bytes(statement.digest()).to_hex().as_str(),
      "f1e778aa3d903008a6e755daee2e4f36f1a7a168277cbb6625984602c12dbe4f"
    );
  }

  #[test]
  fn parser_rejects_domain_length_and_noncanonical_claim() {
    let mut bytes =
      Stage2RootStatementV1::new(b"vk", &canonical_claim(), &test_fri())
        .unwrap()
        .to_bytes();
    bytes[0] ^= 1;
    assert!(Stage2RootStatementV1::from_bytes(&bytes).is_err());

    let mut bytes =
      Stage2RootStatementV1::new(b"vk", &canonical_claim(), &test_fri())
        .unwrap()
        .to_bytes();
    bytes.extend_from_slice(&[0]);
    assert!(Stage2RootStatementV1::from_bytes(&bytes).is_err());

    let mut claim = canonical_claim();
    claim[..8].copy_from_slice(&u64::MAX.to_le_bytes());
    assert!(Stage2RootStatementV1::new(b"vk", &claim, &test_fri()).is_err());
  }

  #[test]
  fn claims_transport_is_the_recursive_verifier_wire_format() {
    let claim = canonical_claim();
    let bytes = stage2_claims_bytes(&claim).unwrap();
    assert_eq!(bytes.len(), STAGE2_CLAIMS_BYTES);
    assert_eq!(&bytes[..8], &1u64.to_le_bytes());
    assert_eq!(&bytes[8..16], &(OUTER_CLAIM_ELEMENTS as u64).to_le_bytes());
    assert_eq!(&bytes[16..], claim);
  }

  #[test]
  fn advice_profile_parses_a_real_proof_and_rejects_extensions() {
    let commitment = CommitmentParameters { log_blowup: 1, cap_height: 0 };
    let fri = FriParameters {
      log_final_poly_len: 0,
      max_log_arity: 1,
      num_queries: 2,
      commit_proof_of_work_bits: 0,
      query_proof_of_work_bits: 0,
    };
    let (system, key) = System::new(
      GoldilocksBlake3Config::new(commitment, fri),
      [
        CircuitInputs { main_width: 2, ..Default::default() },
        CircuitInputs { main_width: 3, ..Default::default() },
      ],
    );
    let trace_1 =
      RowMajorMatrix::new((0..16u32).map(G::from_u32).collect::<Vec<_>>(), 2);
    let trace_2 = RowMajorMatrix::new(
      (0..12u32).map(|value| G::from_u32(7 * value + 3)).collect(),
      3,
    );
    let witness = SystemWitness::from_stage_1(vec![trace_1, trace_2], &system);
    let proof = system.prove_multiple_claims(&key, &[], witness);
    let advice = proof_to_advice_bytes(&system, commitment, fri, &[], &proof)
      .expect("expand proof advice");

    let profile = Stage2AdviceProfileV1::from_advice_bytes(&advice, &fri)
      .expect("profile canonical advice");
    assert_eq!(profile.advice_bytes, advice.len() as u64);
    assert_eq!(profile.total_circuits, 2);
    assert_eq!(profile.active_circuits, 2);
    assert_eq!(profile.queries, 2);
    assert!(profile.input_rounds_per_query > 0);
    assert!(profile.input_merkle_siblings > 0);

    let mut extended = advice;
    extended.push(0);
    assert!(Stage2AdviceProfileV1::from_advice_bytes(&extended, &fri).is_err());
  }
}
