use crate::{F128JaggedMatrixIdV1, F128MatrixFoldRoundV1};
use std::collections::BTreeSet;
use std::fmt;

const JAGGED_ACCUMULATOR_TOPOLOGY_DIGEST_DOMAIN: &[u8] =
  b"ix:stage4:flock-jagged-accumulator-topology:v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct F128JaggedComboTermBindingV1 {
  pub coefficient_observation: u64,
  pub address_observation: u64,
  pub address: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum F128JaggedRowBindingV1 {
  Eq {
    header_observation: u64,
    scale_observation: u64,
    point_observations: Vec<u64>,
  },
  Combo {
    header_observation: u64,
    terms: Vec<F128JaggedComboTermBindingV1>,
  },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128JaggedFoldClaimBindingV1 {
  pub claim: u64,
  pub row: F128JaggedRowBindingV1,
  pub column_point_observations: Vec<u64>,
  pub value_observation: u64,
}

/// Matrix-free replay of one digest-keyed jagged-layout fold.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128JaggedAccumulatorTraceV1 {
  pub matrix: F128JaggedMatrixIdV1,
  pub circuit_digest_payload: u64,
  /// Observation of `F128::new(k, claim_count)` at the fold prefix.
  pub shape_observation: u64,
  pub claims: Vec<F128JaggedFoldClaimBindingV1>,
  pub lambda_challenges: Vec<u64>,
  pub column_rounds: Vec<F128MatrixFoldRoundV1>,
  pub bridge_observations: Vec<u64>,
  pub mu_challenges: Vec<u64>,
  pub row_rounds: Vec<F128MatrixFoldRoundV1>,
  pub value_observation: u64,
}

impl F128JaggedAccumulatorTraceV1 {
  pub fn validate(
    &self,
    input_claims: usize,
    observed_values: usize,
    byte_payloads: usize,
    challenges: usize,
  ) -> Result<(), F128JaggedAccumulatorTraceError> {
    validate_index(self.circuit_digest_payload, byte_payloads).map_err(
      |(index, count)| F128JaggedAccumulatorTraceError::BytePayloadIndex {
        index,
        count,
      },
    )?;
    let row_variables = usize::try_from(self.matrix.row_variables)
      .map_err(|_| F128JaggedAccumulatorTraceError::DimensionOverflow)?;
    let column_variables = usize::try_from(self.matrix.column_variables)
      .map_err(|_| F128JaggedAccumulatorTraceError::DimensionOverflow)?;
    if self.claims.is_empty()
      || self.claims.len() != input_claims
      || self.lambda_challenges.len() != self.claims.len()
      || self.bridge_observations.len() != self.claims.len()
      || self.mu_challenges.len() != self.claims.len()
      || self.column_rounds.len() != column_variables
      || self.row_rounds.len() != row_variables
    {
      return Err(F128JaggedAccumulatorTraceError::Malformed {
        claims: self.claims.len(),
        row_variables: self.matrix.row_variables,
        column_variables: self.matrix.column_variables,
      });
    }

    let mut covered = BTreeSet::new();
    let mut observations = BTreeSet::new();
    validate_unique_observation(
      self.shape_observation,
      observed_values,
      &mut observations,
    )?;
    for binding in &self.claims {
      validate_index(binding.claim, input_claims).map_err(
        |(index, count)| F128JaggedAccumulatorTraceError::ClaimIndex {
          index,
          count,
        },
      )?;
      if !covered.insert(binding.claim) {
        return Err(F128JaggedAccumulatorTraceError::DuplicateClaim {
          claim: binding.claim,
        });
      }
      match &binding.row {
        F128JaggedRowBindingV1::Eq {
          header_observation,
          scale_observation,
          point_observations,
        } => {
          if point_observations.len() != row_variables {
            return Err(F128JaggedAccumulatorTraceError::ClaimShape {
              claim: binding.claim,
            });
          }
          for &observation in std::iter::once(header_observation)
            .chain(std::iter::once(scale_observation))
            .chain(point_observations)
          {
            validate_unique_observation(
              observation,
              observed_values,
              &mut observations,
            )?;
          }
        },
        F128JaggedRowBindingV1::Combo { header_observation, terms } => {
          if terms.is_empty()
            || terms.iter().any(|term| {
              usize::try_from(term.address).ok().is_none_or(|address| {
                1usize
                  .checked_shl(self.matrix.row_variables)
                  .is_none_or(|capacity| address >= capacity)
              })
            })
          {
            return Err(F128JaggedAccumulatorTraceError::ClaimShape {
              claim: binding.claim,
            });
          }
          validate_unique_observation(
            *header_observation,
            observed_values,
            &mut observations,
          )?;
          for term in terms {
            for observation in
              [term.coefficient_observation, term.address_observation]
            {
              validate_unique_observation(
                observation,
                observed_values,
                &mut observations,
              )?;
            }
          }
        },
      }
      if binding.column_point_observations.len() != column_variables {
        return Err(F128JaggedAccumulatorTraceError::ClaimShape {
          claim: binding.claim,
        });
      }
      for &observation in binding
        .column_point_observations
        .iter()
        .chain(std::iter::once(&binding.value_observation))
      {
        validate_unique_observation(
          observation,
          observed_values,
          &mut observations,
        )?;
      }
    }
    if covered.len() != input_claims {
      let claim = (0..input_claims)
        .find(|index| {
          !covered
            .contains(&u64::try_from(*index).expect("claim index fits u64"))
        })
        .expect("short coverage has a missing claim");
      return Err(F128JaggedAccumulatorTraceError::MissingClaim { claim });
    }
    for &observation in self
      .bridge_observations
      .iter()
      .chain(std::iter::once(&self.value_observation))
    {
      validate_unique_observation(
        observation,
        observed_values,
        &mut observations,
      )?;
    }
    let mut challenge_set = BTreeSet::new();
    for &challenge in self.lambda_challenges.iter().chain(&self.mu_challenges) {
      validate_unique_challenge(challenge, challenges, &mut challenge_set)?;
    }
    for round in self.column_rounds.iter().chain(&self.row_rounds) {
      for observation in [round.one_observation, round.infinity_observation] {
        validate_unique_observation(
          observation,
          observed_values,
          &mut observations,
        )?;
      }
      validate_unique_challenge(
        round.challenge,
        challenges,
        &mut challenge_set,
      )?;
    }
    Ok(())
  }

  #[must_use]
  pub fn census(&self) -> F128JaggedAccumulatorCensusV1 {
    let claim_observations = 1usize
      + self
        .claims
        .iter()
        .map(|claim| {
          let row = match &claim.row {
            F128JaggedRowBindingV1::Eq { point_observations, .. } => {
              2 + point_observations.len()
            },
            F128JaggedRowBindingV1::Combo { terms, .. } => 1 + 2 * terms.len(),
          };
          row + claim.column_point_observations.len() + 1
        })
        .sum::<usize>();
    F128JaggedAccumulatorCensusV1 {
      folds: 1,
      input_claims: self.claims.len().try_into().expect("claim count fits u64"),
      claim_observations: claim_observations
        .try_into()
        .expect("claim observation count fits u64"),
      bridge_observations: self
        .bridge_observations
        .len()
        .try_into()
        .expect("bridge count fits u64"),
      rounds: (self.column_rounds.len() + self.row_rounds.len())
        .try_into()
        .expect("round count fits u64"),
      challenges: (self.lambda_challenges.len()
        + self.column_rounds.len()
        + self.mu_challenges.len()
        + self.row_rounds.len())
      .try_into()
      .expect("challenge count fits u64"),
      root_claims: 1,
    }
  }

  #[must_use]
  pub fn topology_digest(&self) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(JAGGED_ACCUMULATOR_TOPOLOGY_DIGEST_DOMAIN);
    hasher.update(&self.matrix.circuit_digest);
    hasher.update(&self.matrix.row_variables.to_le_bytes());
    hasher.update(&self.matrix.column_variables.to_le_bytes());
    hash_u64(&mut hasher, self.circuit_digest_payload);
    hash_u64(&mut hasher, self.shape_observation);
    hash_len(&mut hasher, self.claims.len());
    for claim in &self.claims {
      hash_u64(&mut hasher, claim.claim);
      match &claim.row {
        F128JaggedRowBindingV1::Eq {
          header_observation,
          scale_observation,
          point_observations,
        } => {
          hasher.update(&[0]);
          hash_u64(&mut hasher, *header_observation);
          hash_u64(&mut hasher, *scale_observation);
          hash_indices(&mut hasher, point_observations);
        },
        F128JaggedRowBindingV1::Combo { header_observation, terms } => {
          hasher.update(&[1]);
          hash_u64(&mut hasher, *header_observation);
          hash_len(&mut hasher, terms.len());
          for term in terms {
            hash_u64(&mut hasher, term.coefficient_observation);
            hash_u64(&mut hasher, term.address_observation);
            hasher.update(&term.address.to_le_bytes());
          }
        },
      }
      hash_indices(&mut hasher, &claim.column_point_observations);
      hash_u64(&mut hasher, claim.value_observation);
    }
    hash_indices(&mut hasher, &self.lambda_challenges);
    hash_rounds(&mut hasher, &self.column_rounds);
    hash_indices(&mut hasher, &self.bridge_observations);
    hash_indices(&mut hasher, &self.mu_challenges);
    hash_rounds(&mut hasher, &self.row_rounds);
    hash_u64(&mut hasher, self.value_observation);
    *hasher.finalize().as_bytes()
  }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct F128JaggedAccumulatorCensusV1 {
  pub folds: u64,
  pub input_claims: u64,
  pub claim_observations: u64,
  pub bridge_observations: u64,
  pub rounds: u64,
  pub challenges: u64,
  pub root_claims: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum F128JaggedAccumulatorTraceError {
  BytePayloadIndex { index: u64, count: usize },
  DimensionOverflow,
  Malformed { claims: usize, row_variables: u32, column_variables: u32 },
  ClaimIndex { index: u64, count: usize },
  DuplicateClaim { claim: u64 },
  MissingClaim { claim: usize },
  ClaimShape { claim: u64 },
  ObservationIndex { index: u64, count: usize },
  DuplicateObservation { index: u64 },
  ChallengeIndex { index: u64, count: usize },
  DuplicateChallenge { index: u64 },
}

impl fmt::Display for F128JaggedAccumulatorTraceError {
  fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::BytePayloadIndex { index, count } => write!(
        formatter,
        "jagged accumulator digest payload {index} is outside {count} payloads",
      ),
      Self::DimensionOverflow => {
        write!(formatter, "jagged accumulator dimension overflow")
      },
      Self::Malformed { claims, row_variables, column_variables } => write!(
        formatter,
        "jagged accumulator is malformed: claims={claims}, row_variables={row_variables}, column_variables={column_variables}",
      ),
      Self::ClaimIndex { index, count } => write!(
        formatter,
        "jagged accumulator claim {index} is outside {count} claims",
      ),
      Self::DuplicateClaim { claim } => {
        write!(formatter, "jagged accumulator repeats claim {claim}")
      },
      Self::MissingClaim { claim } => {
        write!(formatter, "jagged accumulator omits claim {claim}")
      },
      Self::ClaimShape { claim } => {
        write!(
          formatter,
          "jagged accumulator claim {claim} has the wrong shape"
        )
      },
      Self::ObservationIndex { index, count } => write!(
        formatter,
        "jagged accumulator observation {index} is outside {count} values",
      ),
      Self::DuplicateObservation { index } => {
        write!(formatter, "jagged accumulator reuses observation {index}")
      },
      Self::ChallengeIndex { index, count } => write!(
        formatter,
        "jagged accumulator challenge {index} is outside {count} values",
      ),
      Self::DuplicateChallenge { index } => {
        write!(formatter, "jagged accumulator reuses challenge {index}")
      },
    }
  }
}

impl std::error::Error for F128JaggedAccumulatorTraceError {}

fn validate_index(index: u64, count: usize) -> Result<usize, (u64, usize)> {
  usize::try_from(index)
    .ok()
    .filter(|&index| index < count)
    .ok_or((index, count))
}

fn validate_unique_observation(
  index: u64,
  count: usize,
  used: &mut BTreeSet<u64>,
) -> Result<(), F128JaggedAccumulatorTraceError> {
  validate_index(index, count).map_err(|(index, count)| {
    F128JaggedAccumulatorTraceError::ObservationIndex { index, count }
  })?;
  if !used.insert(index) {
    return Err(F128JaggedAccumulatorTraceError::DuplicateObservation {
      index,
    });
  }
  Ok(())
}

fn validate_unique_challenge(
  index: u64,
  count: usize,
  used: &mut BTreeSet<u64>,
) -> Result<(), F128JaggedAccumulatorTraceError> {
  validate_index(index, count).map_err(|(index, count)| {
    F128JaggedAccumulatorTraceError::ChallengeIndex { index, count }
  })?;
  if !used.insert(index) {
    return Err(F128JaggedAccumulatorTraceError::DuplicateChallenge { index });
  }
  Ok(())
}

fn hash_len(hasher: &mut blake3::Hasher, length: usize) {
  hasher.update(&u64::try_from(length).expect("length fits u64").to_le_bytes());
}

fn hash_u64(hasher: &mut blake3::Hasher, value: u64) {
  hasher.update(&value.to_le_bytes());
}

fn hash_indices(hasher: &mut blake3::Hasher, values: &[u64]) {
  hash_len(hasher, values.len());
  for &value in values {
    hash_u64(hasher, value);
  }
}

fn hash_rounds(hasher: &mut blake3::Hasher, rounds: &[F128MatrixFoldRoundV1]) {
  hash_len(hasher, rounds.len());
  for round in rounds {
    for value in
      [round.one_observation, round.infinity_observation, round.challenge]
    {
      hash_u64(hasher, value);
    }
  }
}
