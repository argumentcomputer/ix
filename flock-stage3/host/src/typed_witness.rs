//! Owned, serialization-independent witness consumed by the Stage 3 lowering.
//!
//! The source advice uses bincode only as an off-circuit transport. This
//! module converts it once into primitive semantic values so the Flock
//! relation never depends on Rust layout or byte-parser execution.

use anyhow::{Result, bail};
use ix_terminal::{
  Stage2AdviceProfileV1, ValidatedP3ProofV1, ValidatedStage2RootV1,
  decode_p3_advice, fri_parameter_words,
};
use multi_stark::{
  advice::AdviceProof,
  p3_field::{BasedVectorSpace, PrimeField64},
  types::{ExtVal, FriParameters, Val},
};

pub const STAGE3_TYPED_WITNESS_LAYOUT_DOMAIN: &[u8; 8] = b"IXTYPW01";
const STAGE3_TYPED_WITNESS_LAYOUT_VERSION: u16 = 1;

pub type Stage3DigestV1 = [u8; 32];
pub type Stage3ExtensionValueV1 = [u64; 2];
pub type Stage3OpenedRoundV1 = Vec<Vec<Vec<Stage3ExtensionValueV1>>>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stage3TypedCommitmentsV1 {
  pub stage_1_trace: Vec<Stage3DigestV1>,
  pub stage_2_trace: Vec<Stage3DigestV1>,
  pub quotient_chunks: Vec<Stage3DigestV1>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stage3TypedBatchOpeningV1 {
  pub opened_values: Vec<Vec<u64>>,
  pub opening_proof: Vec<Stage3DigestV1>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stage3TypedCommitPhaseStepV1 {
  pub log_arity: u8,
  pub sibling_values: Vec<Stage3ExtensionValueV1>,
  pub opening_proof: Vec<Stage3DigestV1>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stage3TypedQueryProofV1 {
  pub input_proof: Vec<Stage3TypedBatchOpeningV1>,
  pub commit_phase_openings: Vec<Stage3TypedCommitPhaseStepV1>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stage3TypedFriProofV1 {
  pub commit_phase_commits: Vec<Vec<Stage3DigestV1>>,
  pub commit_pow_witnesses: Vec<u64>,
  pub query_proofs: Vec<Stage3TypedQueryProofV1>,
  pub final_poly: Vec<Stage3ExtensionValueV1>,
  pub query_pow_witness: u64,
}

/// Primitive, typed mirror of `multi_stark::advice::AdviceProof`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stage3TypedProofWitnessV1 {
  pub active: Vec<bool>,
  pub commitments: Stage3TypedCommitmentsV1,
  pub intermediate_accumulators: Vec<Stage3ExtensionValueV1>,
  pub log_degrees: Vec<u8>,
  pub opening_proof: Stage3TypedFriProofV1,
  pub quotient_opened_values: Stage3OpenedRoundV1,
  pub preprocessed_opened_values: Option<Stage3OpenedRoundV1>,
  pub stage_1_opened_values: Stage3OpenedRoundV1,
  pub stage_2_opened_values: Stage3OpenedRoundV1,
}

/// Counts that must agree with the independently recorded advice profile.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Stage3TypedProofCountsV1 {
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

impl Stage3TypedProofWitnessV1 {
  /// Decode the strict advice transport and immediately erase its serializer
  /// representation in favor of semantic primitive values.
  pub fn from_advice_bytes(bytes: &[u8], fri: &FriParameters) -> Result<Self> {
    Ok(Self::from_advice(decode_p3_advice(bytes, fri)?))
  }

  /// Prepare the typed proof attached to any already validated Aiur/P3 proof.
  pub fn from_p3(
    prepared: &ValidatedP3ProofV1,
    fri: &FriParameters,
  ) -> Result<Self> {
    if prepared.statement().fri_parameter_words() != &fri_parameter_words(fri) {
      bail!("typed P3 witness uses different FRI parameters");
    }
    let witness = Self::from_advice_bytes(prepared.advice_bytes(), fri)?;
    witness.ensure_profile(prepared.advice_profile())?;
    Ok(witness)
  }

  /// Prepare the typed proof attached to an already validated Stage 2 root.
  pub fn from_prepared(
    prepared: &ValidatedStage2RootV1,
    fri: &FriParameters,
  ) -> Result<Self> {
    Self::from_p3(prepared.p3_proof(), fri)
  }

  /// Digest of the exact nested vector/option layout, excluding witness
  /// values. It is a capacity/compiler input, not a proof-content commitment.
  pub fn layout_digest(&self) -> [u8; 32] {
    let mut bytes = Vec::new();
    bytes.extend_from_slice(STAGE3_TYPED_WITNESS_LAYOUT_DOMAIN);
    bytes.extend_from_slice(&STAGE3_TYPED_WITNESS_LAYOUT_VERSION.to_le_bytes());
    for word in self.layout_words() {
      bytes.extend_from_slice(&word.to_le_bytes());
    }
    *blake3::hash(&bytes).as_bytes()
  }

  pub fn counts(&self) -> Stage3TypedProofCountsV1 {
    let commitment_cap_digests = self.commitments.stage_1_trace.len()
      + self.commitments.stage_2_trace.len()
      + self.commitments.quotient_chunks.len()
      + self
        .opening_proof
        .commit_phase_commits
        .iter()
        .map(Vec::len)
        .sum::<usize>();
    let input_merkle_siblings = self
      .opening_proof
      .query_proofs
      .iter()
      .flat_map(|query| &query.input_proof)
      .map(|opening| opening.opening_proof.len())
      .sum();
    let fri_merkle_siblings = self
      .opening_proof
      .query_proofs
      .iter()
      .flat_map(|query| &query.commit_phase_openings)
      .map(|opening| opening.opening_proof.len())
      .sum();
    let opened_base_values = self
      .opening_proof
      .query_proofs
      .iter()
      .flat_map(|query| &query.input_proof)
      .flat_map(|opening| &opening.opened_values)
      .map(Vec::len)
      .sum();
    let fri_sibling_extension_values = self
      .opening_proof
      .query_proofs
      .iter()
      .flat_map(|query| &query.commit_phase_openings)
      .map(|opening| opening.sibling_values.len())
      .sum();
    let other_extension_values = self.intermediate_accumulators.len()
      + count_opened_values(&self.quotient_opened_values)
      + self.preprocessed_opened_values.as_ref().map_or(0, count_opened_values)
      + count_opened_values(&self.stage_1_opened_values)
      + count_opened_values(&self.stage_2_opened_values)
      + self.opening_proof.final_poly.len();
    let input_rounds_per_query = self
      .opening_proof
      .query_proofs
      .first()
      .map_or(0, |query| query.input_proof.len());

    Stage3TypedProofCountsV1 {
      total_circuits: as_u64(self.active.len()),
      active_circuits: as_u64(
        self.active.iter().filter(|&&active| active).count(),
      ),
      queries: as_u64(self.opening_proof.query_proofs.len()),
      fri_rounds: as_u64(self.opening_proof.commit_phase_commits.len()),
      input_rounds_per_query: as_u64(input_rounds_per_query),
      commitment_cap_digests: as_u64(commitment_cap_digests),
      input_merkle_siblings: as_u64(input_merkle_siblings),
      fri_merkle_siblings: as_u64(fri_merkle_siblings),
      opened_base_values: as_u64(opened_base_values),
      fri_sibling_extension_values: as_u64(fri_sibling_extension_values),
      other_extension_values: as_u64(other_extension_values),
    }
  }

  pub fn ensure_profile(&self, profile: &Stage2AdviceProfileV1) -> Result<()> {
    let expected = Stage3TypedProofCountsV1 {
      total_circuits: profile.total_circuits,
      active_circuits: profile.active_circuits,
      queries: profile.queries,
      fri_rounds: profile.fri_rounds,
      input_rounds_per_query: profile.input_rounds_per_query,
      commitment_cap_digests: profile.commitment_cap_digests,
      input_merkle_siblings: profile.input_merkle_siblings,
      fri_merkle_siblings: profile.fri_merkle_siblings,
      opened_base_values: profile.opened_base_values,
      fri_sibling_extension_values: profile.fri_sibling_extension_values,
      other_extension_values: profile.other_extension_values,
    };
    let observed = self.counts();
    if observed != expected {
      bail!(
        "typed Stage 3 witness counts differ from advice profile: expected {expected:?}, observed {observed:?}"
      );
    }
    Ok(())
  }

  /// Structural verifier step 2: the chained lookup accumulator must end at
  /// zero. The full relation will wire this value to the accumulator updates.
  pub fn last_accumulator_is_zero(&self) -> bool {
    self.intermediate_accumulators.last().is_some_and(|value| *value == [0, 0])
  }

  fn from_advice(proof: AdviceProof) -> Self {
    Self {
      active: proof.active,
      commitments: Stage3TypedCommitmentsV1 {
        stage_1_trace: proof.commitments.stage_1_trace.roots().to_vec(),
        stage_2_trace: proof.commitments.stage_2_trace.roots().to_vec(),
        quotient_chunks: proof.commitments.quotient_chunks.roots().to_vec(),
      },
      intermediate_accumulators: proof
        .intermediate_accumulators
        .into_iter()
        .map(extension_words)
        .collect(),
      log_degrees: proof.log_degrees,
      opening_proof: Stage3TypedFriProofV1 {
        commit_phase_commits: proof
          .opening_proof
          .commit_phase_commits
          .iter()
          .map(|commitment| commitment.roots().to_vec())
          .collect(),
        commit_pow_witnesses: proof
          .opening_proof
          .commit_pow_witnesses
          .into_iter()
          .map(base_word)
          .collect(),
        query_proofs: proof
          .opening_proof
          .query_proofs
          .into_iter()
          .map(|query| Stage3TypedQueryProofV1 {
            input_proof: query
              .input_proof
              .into_iter()
              .map(|opening| Stage3TypedBatchOpeningV1 {
                opened_values: opening
                  .opened_values
                  .into_iter()
                  .map(|row| row.into_iter().map(base_word).collect())
                  .collect(),
                opening_proof: opening.opening_proof,
              })
              .collect(),
            commit_phase_openings: query
              .commit_phase_openings
              .into_iter()
              .map(|step| Stage3TypedCommitPhaseStepV1 {
                log_arity: step.log_arity,
                sibling_values: step
                  .sibling_values
                  .into_iter()
                  .map(extension_words)
                  .collect(),
                opening_proof: step.opening_proof,
              })
              .collect(),
          })
          .collect(),
        final_poly: proof
          .opening_proof
          .final_poly
          .into_iter()
          .map(extension_words)
          .collect(),
        query_pow_witness: base_word(proof.opening_proof.query_pow_witness),
      },
      quotient_opened_values: opened_round(proof.quotient_opened_values),
      preprocessed_opened_values: proof
        .preprocessed_opened_values
        .map(opened_round),
      stage_1_opened_values: opened_round(proof.stage_1_opened_values),
      stage_2_opened_values: opened_round(proof.stage_2_opened_values),
    }
  }

  fn layout_words(&self) -> Vec<u64> {
    let mut words = Vec::new();
    push_len(&mut words, &self.active);
    push_len(&mut words, &self.commitments.stage_1_trace);
    push_len(&mut words, &self.commitments.stage_2_trace);
    push_len(&mut words, &self.commitments.quotient_chunks);
    push_len(&mut words, &self.intermediate_accumulators);
    push_len(&mut words, &self.log_degrees);
    push_len(&mut words, &self.opening_proof.commit_phase_commits);
    for cap in &self.opening_proof.commit_phase_commits {
      push_len(&mut words, cap);
    }
    push_len(&mut words, &self.opening_proof.commit_pow_witnesses);
    push_len(&mut words, &self.opening_proof.query_proofs);
    for query in &self.opening_proof.query_proofs {
      push_len(&mut words, &query.input_proof);
      for opening in &query.input_proof {
        push_len(&mut words, &opening.opened_values);
        for row in &opening.opened_values {
          push_len(&mut words, row);
        }
        push_len(&mut words, &opening.opening_proof);
      }
      push_len(&mut words, &query.commit_phase_openings);
      for step in &query.commit_phase_openings {
        words.push(u64::from(step.log_arity));
        push_len(&mut words, &step.sibling_values);
        push_len(&mut words, &step.opening_proof);
      }
    }
    push_len(&mut words, &self.opening_proof.final_poly);
    push_opened_round(&mut words, &self.quotient_opened_values);
    words.push(u64::from(self.preprocessed_opened_values.is_some()));
    if let Some(round) = &self.preprocessed_opened_values {
      push_opened_round(&mut words, round);
    }
    push_opened_round(&mut words, &self.stage_1_opened_values);
    push_opened_round(&mut words, &self.stage_2_opened_values);
    words
  }
}

fn base_word(value: Val) -> u64 {
  value.as_canonical_u64()
}

fn extension_words(value: ExtVal) -> Stage3ExtensionValueV1 {
  let coefficients = value.as_basis_coefficients_slice();
  [base_word(coefficients[0]), base_word(coefficients[1])]
}

fn opened_round(values: Vec<Vec<Vec<ExtVal>>>) -> Stage3OpenedRoundV1 {
  values
    .into_iter()
    .map(|matrix| {
      matrix
        .into_iter()
        .map(|point| point.into_iter().map(extension_words).collect())
        .collect()
    })
    .collect()
}

fn count_opened_values(values: &Stage3OpenedRoundV1) -> usize {
  values.iter().flat_map(|matrix| matrix.iter()).map(Vec::len).sum()
}

fn push_len<T>(words: &mut Vec<u64>, values: &[T]) {
  words.push(as_u64(values.len()));
}

fn push_opened_round(words: &mut Vec<u64>, values: &Stage3OpenedRoundV1) {
  push_len(words, values);
  for matrix in values {
    push_len(words, matrix);
    for point in matrix {
      push_len(words, point);
    }
  }
}

fn as_u64(value: usize) -> u64 {
  u64::try_from(value).expect("Stage 3 witness length fits u64")
}

#[cfg(test)]
mod tests {
  use multi_stark::{
    advice::proof_to_advice_bytes,
    p3_field::PrimeCharacteristicRing,
    p3_matrix::dense::RowMajorMatrix,
    system::{CircuitInputs, System, SystemWitness},
    types::{CommitmentParameters, GoldilocksBlake3Config},
  };

  use super::*;

  fn typed_fixture() -> (Stage3TypedProofWitnessV1, Stage2AdviceProfileV1) {
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
      RowMajorMatrix::new((0..16u32).map(Val::from_u32).collect::<Vec<_>>(), 2);
    let trace_2 = RowMajorMatrix::new(
      (0..12u32).map(|value| Val::from_u32(7 * value + 3)).collect(),
      3,
    );
    let proof = system.prove_multiple_claims(
      &key,
      &[],
      SystemWitness::from_stage_1(vec![trace_1, trace_2], &system),
    );
    let advice =
      proof_to_advice_bytes(&system, commitment, fri, &[], &proof).unwrap();
    let profile =
      Stage2AdviceProfileV1::from_advice_bytes(&advice, &fri).unwrap();
    let typed =
      Stage3TypedProofWitnessV1::from_advice_bytes(&advice, &fri).unwrap();
    (typed, profile)
  }

  #[test]
  fn typed_layout_preserves_every_profile_count() {
    let (typed, profile) = typed_fixture();
    typed.ensure_profile(&profile).unwrap();
    assert!(typed.last_accumulator_is_zero());
    assert_ne!(typed.layout_digest(), [0; 32]);
  }

  #[test]
  fn layout_digest_changes_with_nested_shape_not_values() {
    let (typed, _) = typed_fixture();
    let digest = typed.layout_digest();

    let mut value_change = typed.clone();
    value_change.opening_proof.query_pow_witness ^= 1;
    assert_eq!(value_change.layout_digest(), digest);

    let mut shape_change = typed;
    shape_change.opening_proof.query_proofs[0].input_proof[0]
      .opening_proof
      .pop();
    assert_ne!(shape_change.layout_digest(), digest);
  }
}
