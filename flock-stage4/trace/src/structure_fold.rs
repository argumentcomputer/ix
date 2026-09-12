use crate::{
  F128CircuitStructureMatrixIdV1, F128MatrixFoldClaimBindingV1,
  F128MatrixFoldRoundV1,
};
use std::collections::BTreeSet;
use std::fmt;

const STRUCTURE_ACCUMULATOR_TOPOLOGY_DIGEST_DOMAIN: &[u8] =
  b"ix:stage4:flock-structure-accumulator-topology:v1";

/// Matrix-free replay of Flock's digest-keyed circuit-structure fold.
///
/// The input claims are emitted by Product-GKR. The fold batches them into
/// one plain matrix evaluation without reading the structure table inside the
/// recursive relation. `circuit_digest_payload` names the digest absorbed by
/// Flock's `flock-aggregate-sigma-v1` prefix before any fold challenge.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128CircuitStructureAccumulatorTraceV1 {
  pub matrix: F128CircuitStructureMatrixIdV1,
  pub circuit_digest_payload: u64,
  pub claims: Vec<F128MatrixFoldClaimBindingV1>,
  pub lambda_challenges: Vec<u64>,
  pub column_rounds: Vec<F128MatrixFoldRoundV1>,
  pub bridge_observations: Vec<u64>,
  pub mu_challenges: Vec<u64>,
  pub row_rounds: Vec<F128MatrixFoldRoundV1>,
  pub value_observation: u64,
}

impl F128CircuitStructureAccumulatorTraceV1 {
  pub fn validate(
    &self,
    input_claims: usize,
    observed_values: usize,
    byte_payloads: usize,
    challenges: usize,
  ) -> Result<(), F128CircuitStructureAccumulatorTraceError> {
    validate_index(self.circuit_digest_payload, byte_payloads).map_err(
      |(index, count)| {
        F128CircuitStructureAccumulatorTraceError::BytePayloadIndex {
          index,
          count,
        }
      },
    )?;
    let row_variables =
      usize::try_from(self.matrix.row_variables).map_err(|_| {
        F128CircuitStructureAccumulatorTraceError::DimensionOverflow
      })?;
    let column_variables = usize::try_from(self.matrix.column_variables)
      .map_err(|_| {
        F128CircuitStructureAccumulatorTraceError::DimensionOverflow
      })?;
    if self.claims.is_empty() {
      return Err(F128CircuitStructureAccumulatorTraceError::Empty);
    }
    if self.lambda_challenges.len() != self.claims.len()
      || self.bridge_observations.len() != self.claims.len()
      || self.mu_challenges.len() != self.claims.len()
      || self.column_rounds.len() != column_variables
      || self.row_rounds.len() != row_variables
    {
      return Err(F128CircuitStructureAccumulatorTraceError::Malformed {
        claims: self.claims.len(),
        row_variables: self.matrix.row_variables,
        column_variables: self.matrix.column_variables,
      });
    }

    let mut covered = BTreeSet::new();
    for binding in &self.claims {
      validate_index(binding.claim, input_claims).map_err(
        |(index, count)| {
          F128CircuitStructureAccumulatorTraceError::ClaimIndex { index, count }
        },
      )?;
      if !covered.insert(binding.claim) {
        return Err(
          F128CircuitStructureAccumulatorTraceError::DuplicateClaim {
            claim: binding.claim,
          },
        );
      }
      if binding.row_low_observations.len() != 1
        || binding.row_point_observations.len() != row_variables
        || binding.column_low_observations.len() != 1
        || binding.column_point_observations.len() != column_variables
      {
        return Err(F128CircuitStructureAccumulatorTraceError::ClaimShape {
          claim: binding.claim,
        });
      }
      for &observation in binding
        .row_low_observations
        .iter()
        .chain(&binding.row_point_observations)
        .chain(&binding.column_low_observations)
        .chain(&binding.column_point_observations)
        .chain(std::iter::once(&binding.value_observation))
      {
        validate_observation(observation, observed_values)?;
      }
    }
    if covered.len() != input_claims {
      let claim = (0..input_claims)
        .find(|index| {
          !covered
            .contains(&u64::try_from(*index).expect("claim index fits u64"))
        })
        .expect("short coverage has a missing claim");
      return Err(F128CircuitStructureAccumulatorTraceError::MissingClaim {
        claim,
      });
    }

    for &observation in self
      .bridge_observations
      .iter()
      .chain(std::iter::once(&self.value_observation))
    {
      validate_observation(observation, observed_values)?;
    }
    for &challenge in self.lambda_challenges.iter().chain(&self.mu_challenges) {
      validate_challenge(challenge, challenges)?;
    }
    for round in self.column_rounds.iter().chain(&self.row_rounds) {
      validate_observation(round.one_observation, observed_values)?;
      validate_observation(round.infinity_observation, observed_values)?;
      validate_challenge(round.challenge, challenges)?;
    }
    Ok(())
  }

  #[must_use]
  pub fn census(&self) -> F128CircuitStructureAccumulatorCensusV1 {
    F128CircuitStructureAccumulatorCensusV1 {
      folds: 1,
      input_claims: u64::try_from(self.claims.len())
        .expect("structure claim count fits u64"),
      claim_observations: self
        .claims
        .iter()
        .map(|claim| {
          1 + claim.row_low_observations.len()
            + claim.row_point_observations.len()
            + claim.column_low_observations.len()
            + claim.column_point_observations.len()
        })
        .map(|count| u64::try_from(count).expect("observation count fits u64"))
        .sum(),
      bridge_observations: u64::try_from(self.bridge_observations.len())
        .expect("bridge count fits u64"),
      rounds: u64::try_from(self.column_rounds.len() + self.row_rounds.len())
        .expect("round count fits u64"),
      challenges: u64::try_from(
        self.lambda_challenges.len()
          + self.mu_challenges.len()
          + self.column_rounds.len()
          + self.row_rounds.len(),
      )
      .expect("challenge count fits u64"),
      root_claims: 1,
    }
  }

  /// Content address of the value-independent fold wiring.
  #[must_use]
  pub fn topology_digest(&self) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(STRUCTURE_ACCUMULATOR_TOPOLOGY_DIGEST_DOMAIN);
    hasher.update(&self.matrix.circuit_digest);
    hasher.update(&self.matrix.row_variables.to_le_bytes());
    hasher.update(&self.matrix.column_variables.to_le_bytes());
    hash_u64(&mut hasher, self.circuit_digest_payload);
    hash_len(&mut hasher, self.claims.len());
    for claim in &self.claims {
      hash_u64(&mut hasher, claim.claim);
      hash_indices(&mut hasher, &claim.row_low_observations);
      hash_indices(&mut hasher, &claim.row_point_observations);
      hash_indices(&mut hasher, &claim.column_low_observations);
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
pub struct F128CircuitStructureAccumulatorCensusV1 {
  pub folds: u64,
  pub input_claims: u64,
  pub claim_observations: u64,
  pub bridge_observations: u64,
  pub rounds: u64,
  pub challenges: u64,
  pub root_claims: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum F128CircuitStructureAccumulatorTraceError {
  BytePayloadIndex { index: u64, count: usize },
  DimensionOverflow,
  Empty,
  Malformed { claims: usize, row_variables: u32, column_variables: u32 },
  ClaimIndex { index: u64, count: usize },
  DuplicateClaim { claim: u64 },
  MissingClaim { claim: usize },
  ClaimShape { claim: u64 },
  ObservationIndex { index: u64, count: usize },
  ChallengeIndex { index: u64, count: usize },
}

impl fmt::Display for F128CircuitStructureAccumulatorTraceError {
  fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::BytePayloadIndex { index, count } => write!(
        formatter,
        "structure accumulator digest payload {index} is outside {count} payloads",
      ),
      Self::DimensionOverflow => {
        write!(formatter, "structure accumulator dimension does not fit usize")
      },
      Self::Empty => {
        write!(formatter, "structure accumulator has no input claims")
      },
      Self::Malformed { claims, row_variables, column_variables } => write!(
        formatter,
        "structure accumulator has inconsistent vectors: claims={claims}, row_variables={row_variables}, column_variables={column_variables}",
      ),
      Self::ClaimIndex { index, count } => write!(
        formatter,
        "structure accumulator claim {index} is outside {count} claims",
      ),
      Self::DuplicateClaim { claim } => {
        write!(formatter, "structure accumulator repeats input claim {claim}")
      },
      Self::MissingClaim { claim } => {
        write!(formatter, "structure accumulator omits input claim {claim}")
      },
      Self::ClaimShape { claim } => write!(
        formatter,
        "structure accumulator input claim {claim} has malformed bindings",
      ),
      Self::ObservationIndex { index, count } => write!(
        formatter,
        "structure accumulator observation {index} is outside {count} values",
      ),
      Self::ChallengeIndex { index, count } => write!(
        formatter,
        "structure accumulator challenge {index} is outside {count} values",
      ),
    }
  }
}

impl std::error::Error for F128CircuitStructureAccumulatorTraceError {}

fn validate_observation(
  index: u64,
  count: usize,
) -> Result<(), F128CircuitStructureAccumulatorTraceError> {
  validate_index(index, count).map_err(|(index, count)| {
    F128CircuitStructureAccumulatorTraceError::ObservationIndex { index, count }
  })
}

fn validate_challenge(
  index: u64,
  count: usize,
) -> Result<(), F128CircuitStructureAccumulatorTraceError> {
  validate_index(index, count).map_err(|(index, count)| {
    F128CircuitStructureAccumulatorTraceError::ChallengeIndex { index, count }
  })
}

fn validate_index(index: u64, count: usize) -> Result<(), (u64, usize)> {
  if usize::try_from(index).ok().is_none_or(|index| index >= count) {
    return Err((index, count));
  }
  Ok(())
}

fn hash_rounds(hasher: &mut blake3::Hasher, rounds: &[F128MatrixFoldRoundV1]) {
  hash_len(hasher, rounds.len());
  for round in rounds {
    hash_u64(hasher, round.one_observation);
    hash_u64(hasher, round.infinity_observation);
    hash_u64(hasher, round.challenge);
  }
}

fn hash_indices(hasher: &mut blake3::Hasher, indices: &[u64]) {
  hash_len(hasher, indices.len());
  for &index in indices {
    hash_u64(hasher, index);
  }
}

fn hash_len(hasher: &mut blake3::Hasher, length: usize) {
  hash_u64(hasher, u64::try_from(length).expect("topology length fits u64"));
}

fn hash_u64(hasher: &mut blake3::Hasher, value: u64) {
  hasher.update(&value.to_le_bytes());
}

#[cfg(test)]
mod tests {
  use super::*;

  fn fixture() -> F128CircuitStructureAccumulatorTraceV1 {
    F128CircuitStructureAccumulatorTraceV1 {
      matrix: F128CircuitStructureMatrixIdV1 {
        circuit_digest: [9; 32],
        row_variables: 1,
        column_variables: 1,
      },
      circuit_digest_payload: 0,
      claims: vec![F128MatrixFoldClaimBindingV1 {
        claim: 0,
        row_low_observations: vec![0],
        row_point_observations: vec![1],
        column_low_observations: vec![2],
        column_point_observations: vec![3],
        value_observation: 4,
      }],
      lambda_challenges: vec![0],
      column_rounds: vec![F128MatrixFoldRoundV1 {
        one_observation: 5,
        infinity_observation: 6,
        challenge: 1,
      }],
      bridge_observations: vec![7],
      mu_challenges: vec![2],
      row_rounds: vec![F128MatrixFoldRoundV1 {
        one_observation: 8,
        infinity_observation: 9,
        challenge: 3,
      }],
      value_observation: 10,
    }
  }

  #[test]
  fn validates_rectangular_fold_and_counts_it() {
    let trace = fixture();
    trace.validate(1, 11, 1, 4).unwrap();
    assert_eq!(
      trace.census(),
      F128CircuitStructureAccumulatorCensusV1 {
        folds: 1,
        input_claims: 1,
        claim_observations: 5,
        bridge_observations: 1,
        rounds: 2,
        challenges: 4,
        root_claims: 1,
      },
    );
    assert_ne!(trace.topology_digest(), [0; 32]);
  }

  #[test]
  fn rejects_missing_claim_and_wrong_point_shape() {
    assert!(matches!(
      fixture().validate(2, 11, 1, 4),
      Err(F128CircuitStructureAccumulatorTraceError::MissingClaim { claim: 1 })
    ));
    let mut malformed = fixture();
    malformed.claims[0].column_point_observations.clear();
    assert!(matches!(
      malformed.validate(1, 11, 1, 4),
      Err(F128CircuitStructureAccumulatorTraceError::ClaimShape { .. })
    ));
  }
}
