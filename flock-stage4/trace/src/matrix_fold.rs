use crate::F128StaticMatrixIdV1;
use std::collections::BTreeSet;
use std::fmt;

const MATRIX_ACCUMULATOR_TOPOLOGY_DIGEST_DOMAIN: &[u8] =
  b"ix:stage4:flock-matrix-accumulator-topology:v1";

/// Transcript locations that bind one incoming static-matrix claim.
///
/// Flock observes all four weight components and the claimed value before it
/// samples the fold's batching coefficients.  Keeping those locations in the
/// neutral trace makes that binding part of the compiled relation rather than
/// an ordering convention in the host exporter.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128MatrixFoldClaimBindingV1 {
  pub claim: u64,
  pub row_low_observations: Vec<u64>,
  pub row_point_observations: Vec<u64>,
  pub column_low_observations: Vec<u64>,
  pub column_point_observations: Vec<u64>,
  pub value_observation: u64,
}

/// One Convention-A degree-two sumcheck round.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct F128MatrixFoldRoundV1 {
  pub one_observation: u64,
  pub infinity_observation: u64,
  pub challenge: u64,
}

/// Matrix-free replay data for one group of claims about the same matrix.
///
/// The fold verifies only a reduction. Its output remains conditional until
/// the returned plain evaluation claim is checked against the registry-static
/// matrix at the aggregation root.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128MatrixFoldTraceV1 {
  pub matrix: F128StaticMatrixIdV1,
  pub claims: Vec<F128MatrixFoldClaimBindingV1>,
  pub lambda_challenges: Vec<u64>,
  pub column_rounds: Vec<F128MatrixFoldRoundV1>,
  pub bridge_observations: Vec<u64>,
  pub mu_challenges: Vec<u64>,
  pub row_rounds: Vec<F128MatrixFoldRoundV1>,
  pub value_observation: u64,
}

/// Complete Boolean matrix accumulator replay for one registry.
///
/// `registry_digest_payload` and `prior_count_payload` name the two byte
/// payloads absorbed by Flock's `flock-aggregate-v0` prefix. Every input claim
/// must occur in exactly one fold, and every matrix key must occur at most
/// once, so a caller cannot silently drop or split deferred work.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128MatrixAccumulatorTraceV1 {
  pub registry_digest: [u8; 32],
  pub registry_digest_payload: u64,
  pub prior_count_payload: u64,
  pub prior_accumulators: u8,
  pub folds: Vec<F128MatrixFoldTraceV1>,
}

impl F128MatrixAccumulatorTraceV1 {
  pub fn validate(
    &self,
    claims: usize,
    observed_values: usize,
    byte_payloads: usize,
    challenges: usize,
  ) -> Result<(), F128MatrixAccumulatorTraceError> {
    validate_index(
      self.registry_digest_payload,
      byte_payloads,
      |index, count| F128MatrixAccumulatorTraceError::BytePayloadIndex {
        kind: "registry digest",
        index,
        count,
      },
    )?;
    validate_index(self.prior_count_payload, byte_payloads, |index, count| {
      F128MatrixAccumulatorTraceError::BytePayloadIndex {
        kind: "prior count",
        index,
        count,
      }
    })?;
    if self.registry_digest_payload == self.prior_count_payload {
      return Err(F128MatrixAccumulatorTraceError::AliasedBindingPayloads);
    }

    let mut covered_claims = BTreeSet::new();
    let mut matrices = BTreeSet::new();
    for (fold_index, fold) in self.folds.iter().enumerate() {
      if fold.matrix.registry_digest != self.registry_digest {
        return Err(F128MatrixAccumulatorTraceError::RegistryMismatch {
          fold: fold_index,
        });
      }
      if !matrices.insert(fold.matrix) {
        return Err(F128MatrixAccumulatorTraceError::DuplicateMatrix {
          fold: fold_index,
        });
      }
      if fold.claims.is_empty() {
        return Err(F128MatrixAccumulatorTraceError::EmptyFold {
          fold: fold_index,
        });
      }
      let arity = usize::try_from(fold.matrix.variables).map_err(|_| {
        F128MatrixAccumulatorTraceError::DimensionOverflow { fold: fold_index }
      })?;
      if fold.lambda_challenges.len() != fold.claims.len()
        || fold.bridge_observations.len() != fold.claims.len()
        || fold.mu_challenges.len() != fold.claims.len()
        || fold.column_rounds.len() != arity
        || fold.row_rounds.len() != arity
      {
        return Err(F128MatrixAccumulatorTraceError::MalformedFold {
          fold: fold_index,
          claims: fold.claims.len(),
          variables: fold.matrix.variables,
        });
      }

      for binding in &fold.claims {
        validate_index(binding.claim, claims, |index, count| {
          F128MatrixAccumulatorTraceError::ClaimIndex {
            fold: fold_index,
            index,
            count,
          }
        })?;
        if !covered_claims.insert(binding.claim) {
          return Err(F128MatrixAccumulatorTraceError::DuplicateClaim {
            fold: fold_index,
            claim: binding.claim,
          });
        }
        for observation in binding
          .row_low_observations
          .iter()
          .chain(&binding.row_point_observations)
          .chain(&binding.column_low_observations)
          .chain(&binding.column_point_observations)
          .chain(std::iter::once(&binding.value_observation))
        {
          validate_observation(*observation, observed_values, fold_index)?;
        }
      }
      for observation in fold
        .bridge_observations
        .iter()
        .chain(std::iter::once(&fold.value_observation))
      {
        validate_observation(*observation, observed_values, fold_index)?;
      }
      for challenge in fold.lambda_challenges.iter().chain(&fold.mu_challenges)
      {
        validate_challenge(*challenge, challenges, fold_index)?;
      }
      for round in fold.column_rounds.iter().chain(&fold.row_rounds) {
        validate_observation(
          round.one_observation,
          observed_values,
          fold_index,
        )?;
        validate_observation(
          round.infinity_observation,
          observed_values,
          fold_index,
        )?;
        validate_challenge(round.challenge, challenges, fold_index)?;
      }
    }

    if covered_claims.len() != claims {
      let missing = (0..claims)
        .find(|index| {
          !covered_claims
            .contains(&u64::try_from(*index).expect("claim index fits u64"))
        })
        .expect("a short coverage set has a missing claim");
      return Err(F128MatrixAccumulatorTraceError::MissingClaim {
        claim: missing,
      });
    }
    Ok(())
  }

  #[must_use]
  pub fn census(&self) -> F128MatrixAccumulatorCensusV1 {
    let mut census = F128MatrixAccumulatorCensusV1 {
      folds: u64::try_from(self.folds.len()).expect("fold count fits u64"),
      root_claims: u64::try_from(self.folds.len())
        .expect("root-claim count fits u64"),
      ..F128MatrixAccumulatorCensusV1::default()
    };
    for fold in &self.folds {
      census.input_claims +=
        u64::try_from(fold.claims.len()).expect("claim count fits u64");
      census.claim_observations += fold
        .claims
        .iter()
        .map(|claim| {
          1 + claim.row_low_observations.len()
            + claim.row_point_observations.len()
            + claim.column_low_observations.len()
            + claim.column_point_observations.len()
        })
        .map(|count| u64::try_from(count).expect("observation count fits u64"))
        .sum::<u64>();
      census.bridge_observations +=
        u64::try_from(fold.bridge_observations.len())
          .expect("bridge count fits u64");
      census.rounds +=
        u64::try_from(fold.column_rounds.len() + fold.row_rounds.len())
          .expect("round count fits u64");
      census.challenges += u64::try_from(
        fold.lambda_challenges.len()
          + fold.mu_challenges.len()
          + fold.column_rounds.len()
          + fold.row_rounds.len(),
      )
      .expect("challenge count fits u64");
    }
    census
  }

  /// Content address of the accumulator replay wiring, independent of values.
  #[must_use]
  pub fn topology_digest(&self) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(MATRIX_ACCUMULATOR_TOPOLOGY_DIGEST_DOMAIN);
    hasher.update(&self.registry_digest);
    hash_u64(&mut hasher, self.registry_digest_payload);
    hash_u64(&mut hasher, self.prior_count_payload);
    hasher.update(&[self.prior_accumulators]);
    hash_len(&mut hasher, self.folds.len());
    for fold in &self.folds {
      hash_matrix(&mut hasher, fold.matrix);
      hash_len(&mut hasher, fold.claims.len());
      for claim in &fold.claims {
        hash_u64(&mut hasher, claim.claim);
        hash_indices(&mut hasher, &claim.row_low_observations);
        hash_indices(&mut hasher, &claim.row_point_observations);
        hash_indices(&mut hasher, &claim.column_low_observations);
        hash_indices(&mut hasher, &claim.column_point_observations);
        hash_u64(&mut hasher, claim.value_observation);
      }
      hash_indices(&mut hasher, &fold.lambda_challenges);
      hash_rounds(&mut hasher, &fold.column_rounds);
      hash_indices(&mut hasher, &fold.bridge_observations);
      hash_indices(&mut hasher, &fold.mu_challenges);
      hash_rounds(&mut hasher, &fold.row_rounds);
      hash_u64(&mut hasher, fold.value_observation);
    }
    *hasher.finalize().as_bytes()
  }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct F128MatrixAccumulatorCensusV1 {
  pub folds: u64,
  pub input_claims: u64,
  pub claim_observations: u64,
  pub bridge_observations: u64,
  pub rounds: u64,
  pub challenges: u64,
  pub root_claims: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum F128MatrixAccumulatorTraceError {
  BytePayloadIndex { kind: &'static str, index: u64, count: usize },
  AliasedBindingPayloads,
  RegistryMismatch { fold: usize },
  DuplicateMatrix { fold: usize },
  EmptyFold { fold: usize },
  DimensionOverflow { fold: usize },
  MalformedFold { fold: usize, claims: usize, variables: u32 },
  ClaimIndex { fold: usize, index: u64, count: usize },
  DuplicateClaim { fold: usize, claim: u64 },
  MissingClaim { claim: usize },
  ObservationIndex { fold: usize, index: u64, count: usize },
  ChallengeIndex { fold: usize, index: u64, count: usize },
}

impl fmt::Display for F128MatrixAccumulatorTraceError {
  fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::BytePayloadIndex { kind, index, count } => write!(
        formatter,
        "matrix accumulator {kind} payload {index} is outside {count} payloads",
      ),
      Self::AliasedBindingPayloads => write!(
        formatter,
        "matrix accumulator registry and prior-count payloads alias",
      ),
      Self::RegistryMismatch { fold } => {
        write!(formatter, "matrix fold {fold} names a different registry")
      },
      Self::DuplicateMatrix { fold } => {
        write!(formatter, "matrix fold {fold} repeats a matrix key")
      },
      Self::EmptyFold { fold } => {
        write!(formatter, "matrix fold {fold} has no input claims")
      },
      Self::DimensionOverflow { fold } => {
        write!(formatter, "matrix fold {fold} dimension does not fit usize")
      },
      Self::MalformedFold { fold, claims, variables } => write!(
        formatter,
        "matrix fold {fold} has inconsistent vectors: claims={claims}, variables={variables}",
      ),
      Self::ClaimIndex { fold, index, count } => write!(
        formatter,
        "matrix fold {fold} claim index {index} is outside {count} claims",
      ),
      Self::DuplicateClaim { fold, claim } => {
        write!(formatter, "matrix fold {fold} repeats input claim {claim}",)
      },
      Self::MissingClaim { claim } => {
        write!(formatter, "matrix accumulator omits input claim {claim}")
      },
      Self::ObservationIndex { fold, index, count } => write!(
        formatter,
        "matrix fold {fold} observation {index} is outside {count} values",
      ),
      Self::ChallengeIndex { fold, index, count } => write!(
        formatter,
        "matrix fold {fold} challenge {index} is outside {count} values",
      ),
    }
  }
}

impl std::error::Error for F128MatrixAccumulatorTraceError {}

fn validate_observation(
  index: u64,
  count: usize,
  fold: usize,
) -> Result<(), F128MatrixAccumulatorTraceError> {
  validate_index(index, count, |index, count| {
    F128MatrixAccumulatorTraceError::ObservationIndex { fold, index, count }
  })
}

fn validate_challenge(
  index: u64,
  count: usize,
  fold: usize,
) -> Result<(), F128MatrixAccumulatorTraceError> {
  validate_index(index, count, |index, count| {
    F128MatrixAccumulatorTraceError::ChallengeIndex { fold, index, count }
  })
}

fn validate_index(
  index: u64,
  count: usize,
  error: impl FnOnce(u64, usize) -> F128MatrixAccumulatorTraceError,
) -> Result<(), F128MatrixAccumulatorTraceError> {
  if usize::try_from(index).ok().is_none_or(|index| index >= count) {
    return Err(error(index, count));
  }
  Ok(())
}

fn hash_matrix(hasher: &mut blake3::Hasher, matrix: F128StaticMatrixIdV1) {
  hasher.update(&matrix.registry_digest);
  hash_u64(hasher, matrix.table);
  hasher.update(&[matrix.side as u8]);
  hasher.update(&matrix.variables.to_le_bytes());
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
  use crate::F128MatrixSideV1;

  fn fixture() -> F128MatrixAccumulatorTraceV1 {
    let matrix = F128StaticMatrixIdV1 {
      registry_digest: [7; 32],
      table: 2,
      side: F128MatrixSideV1::A,
      variables: 1,
    };
    F128MatrixAccumulatorTraceV1 {
      registry_digest: matrix.registry_digest,
      registry_digest_payload: 0,
      prior_count_payload: 1,
      prior_accumulators: 0,
      folds: vec![F128MatrixFoldTraceV1 {
        matrix,
        claims: vec![F128MatrixFoldClaimBindingV1 {
          claim: 0,
          row_low_observations: vec![0, 1],
          row_point_observations: Vec::new(),
          column_low_observations: vec![2, 3],
          column_point_observations: Vec::new(),
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
      }],
    }
  }

  #[test]
  fn validates_total_claim_coverage_and_counts_fold_shape() {
    let trace = fixture();
    trace.validate(1, 11, 2, 4).unwrap();
    assert_eq!(
      trace.census(),
      F128MatrixAccumulatorCensusV1 {
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
  fn rejects_omitted_and_duplicated_claims() {
    assert!(matches!(
      fixture().validate(2, 11, 2, 4),
      Err(F128MatrixAccumulatorTraceError::MissingClaim { claim: 1 })
    ));

    let mut duplicate = fixture();
    let mut second = duplicate.folds[0].clone();
    second.matrix.side = F128MatrixSideV1::B;
    duplicate.folds.push(second);
    assert!(matches!(
      duplicate.validate(1, 11, 2, 4),
      Err(F128MatrixAccumulatorTraceError::DuplicateClaim { .. })
    ));
  }
}
