use std::collections::BTreeSet;
use std::fmt;

const MULTIPOINT_TOPOLOGY_DIGEST_DOMAIN: &[u8] =
  b"ix:stage4:flock-multipoint-twisted-assist:v1";

pub const F128_MULTIPOINT_RING_SWITCH_CLAIMS: usize = 2;
pub const F128_MULTIPOINT_DUAL_VALUES: usize = 128;
pub const F128_MULTIPOINT_SCALAR_GROUPS: usize = 1;
pub const F128_MULTIPOINT_JAGGED_CLAIMS: usize = 3;
pub const F128_FAMILY_H_CORRECTIONS: usize = 7;

/// Stable identity of Flock's count-dependent jagged layout table.
///
/// The digest names the child circuit whose fixed counts determine the
/// heights. Rows are the padded layout-column space; columns are the
/// interleaved boundary-pair space sampled by the anchor assist.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct F128JaggedMatrixIdV1 {
  pub circuit_digest: [u8; 32],
  pub row_variables: u32,
  pub column_variables: u32,
}

/// Universal GHASH trace-dual decomposition used by family H.
///
/// If `d_t` is inverse-Moore row zero, then
/// `d_t = geometric_origin * geometric_ratio^t` for `t >= 7`; the seven
/// entries below are the additive corrections for `t = 0..6`. Every other
/// inverse-Moore row is obtained by Frobenius powering these constants.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct F128FamilyHConstantsV1 {
  pub geometric_origin: [u8; 16],
  pub geometric_ratio: [u8; 16],
  pub low_corrections: [[u8; 16]; F128_FAMILY_H_CORRECTIONS],
}

/// One characteristic-two degree-two sumcheck round.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct F128MultipointRoundV1 {
  pub one_observation: u64,
  pub infinity_observation: u64,
  pub challenge: u64,
}

/// Value-independent replay of Flock's forked multipoint-twisted assist.
///
/// The production circuit has exactly two ring-switched claims and one
/// scalar group containing all wiring gathers. Its three private values are
/// the raw evaluations exported as claims on the digest-keyed jagged table;
/// they are accepted only after the auxiliary jagged fold reaches a terminal
/// root discharge.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128MultipointTwistedAssistTraceV1 {
  /// Pins this continuation to the exact merged-PCS frontend topology.
  pub frontend_topology_digest: [u8; 32],
  pub matrix: F128JaggedMatrixIdV1,
  /// Original jagged row-point arity (`JaggedParams::n`).
  pub witness_row_variables: u32,
  /// Dense-domain arity (`JaggedParams::m`).
  pub dense_variables: u32,
  pub family_h: F128FamilyHConstantsV1,
  /// Two vectors of 128 dual-form values, in ring-switch claim order.
  pub dual_value_observations: Vec<Vec<u64>>,
  /// Exactly one value for the production packed-direct scalar group.
  pub group_value_observations: Vec<u64>,
  pub gamma_challenge: u64,
  pub multipoint_rounds: Vec<F128MultipointRoundV1>,
  /// The anchor assist's claimed value, which must equal the multipoint
  /// sumcheck endpoint.
  pub anchor_value_observation: u64,
  pub anchor_rounds: Vec<F128MultipointRoundV1>,
  /// Boolean column addresses of the packed-direct claims, in claim order.
  pub group_column_addresses: Vec<u32>,
  /// Raw layout values in flattened assertion order: RS0, RS1, combo.
  pub jagged_claim_private_values: Vec<u64>,
}

impl F128MultipointTwistedAssistTraceV1 {
  pub fn validate(
    &self,
    observed_values: usize,
    challenges: usize,
    private_values: usize,
  ) -> Result<(), F128MultipointTraceError> {
    let dense_variables = usize::try_from(self.dense_variables)
      .map_err(|_| F128MultipointTraceError::DimensionOverflow)?;
    let expected_column_variables = dense_variables
      .checked_add(1)
      .and_then(|value| value.checked_mul(2))
      .ok_or(F128MultipointTraceError::DimensionOverflow)?;
    if usize::try_from(self.matrix.column_variables).ok()
      != Some(expected_column_variables)
    {
      return Err(F128MultipointTraceError::InvalidShape(
        "jagged matrix column arity is not 2(m + 1)",
      ));
    }
    if self.dual_value_observations.len() != F128_MULTIPOINT_RING_SWITCH_CLAIMS
      || self
        .dual_value_observations
        .iter()
        .any(|values| values.len() != F128_MULTIPOINT_DUAL_VALUES)
      || self.group_value_observations.len() != F128_MULTIPOINT_SCALAR_GROUPS
    {
      return Err(F128MultipointTraceError::InvalidShape(
        "multipoint value vectors have the wrong shape",
      ));
    }
    if self.multipoint_rounds.len() != dense_variables
      || self.anchor_rounds.len() != expected_column_variables
    {
      return Err(F128MultipointTraceError::InvalidShape(
        "multipoint or anchor sumcheck has the wrong round count",
      ));
    }
    if self.group_column_addresses.is_empty() {
      return Err(F128MultipointTraceError::InvalidShape(
        "the scalar group has no packed-direct members",
      ));
    }
    let address_capacity = 1usize
      .checked_shl(self.matrix.row_variables)
      .ok_or(F128MultipointTraceError::DimensionOverflow)?;
    if self.group_column_addresses.iter().any(|&address| {
      usize::try_from(address).map_or(true, |a| a >= address_capacity)
    }) {
      return Err(F128MultipointTraceError::InvalidShape(
        "a scalar-group address is outside the jagged row space",
      ));
    }
    if self.jagged_claim_private_values.len() != F128_MULTIPOINT_JAGGED_CLAIMS
      || private_values != F128_MULTIPOINT_JAGGED_CLAIMS
    {
      return Err(F128MultipointTraceError::InvalidShape(
        "the deferred jagged assertion must contain exactly three values",
      ));
    }

    let mut used_observations = BTreeSet::new();
    for &index in self
      .dual_value_observations
      .iter()
      .flatten()
      .chain(&self.group_value_observations)
      .chain(std::iter::once(&self.anchor_value_observation))
    {
      validate_unique_index(
        index,
        observed_values,
        "assist observation",
        &mut used_observations,
      )?;
    }
    for round in self.multipoint_rounds.iter().chain(&self.anchor_rounds) {
      for index in [round.one_observation, round.infinity_observation] {
        validate_unique_index(
          index,
          observed_values,
          "assist round observation",
          &mut used_observations,
        )?;
      }
    }

    let mut used_challenges = BTreeSet::new();
    validate_unique_index(
      self.gamma_challenge,
      challenges,
      "assist gamma challenge",
      &mut used_challenges,
    )?;
    for round in self.multipoint_rounds.iter().chain(&self.anchor_rounds) {
      validate_unique_index(
        round.challenge,
        challenges,
        "assist round challenge",
        &mut used_challenges,
      )?;
    }

    let mut used_private = BTreeSet::new();
    for &index in &self.jagged_claim_private_values {
      validate_unique_index(
        index,
        private_values,
        "jagged private value",
        &mut used_private,
      )?;
    }
    if used_private.len() != private_values {
      return Err(F128MultipointTraceError::InvalidShape(
        "the jagged private-value map is not exhaustive",
      ));
    }
    Ok(())
  }

  #[must_use]
  pub fn census(&self) -> F128MultipointTwistedAssistCensusV1 {
    F128MultipointTwistedAssistCensusV1 {
      dual_value_observations: self
        .dual_value_observations
        .iter()
        .map(Vec::len)
        .sum::<usize>()
        .try_into()
        .expect("dual-value count fits u64"),
      group_value_observations: self
        .group_value_observations
        .len()
        .try_into()
        .expect("group-value count fits u64"),
      batching_challenges: 1,
      multipoint_rounds: self
        .multipoint_rounds
        .len()
        .try_into()
        .expect("multipoint round count fits u64"),
      anchor_rounds: self
        .anchor_rounds
        .len()
        .try_into()
        .expect("anchor round count fits u64"),
      group_members: self
        .group_column_addresses
        .len()
        .try_into()
        .expect("group-member count fits u64"),
      jagged_claims: self
        .jagged_claim_private_values
        .len()
        .try_into()
        .expect("jagged-claim count fits u64"),
    }
  }

  /// Content address of the complete value-independent assist wiring.
  #[must_use]
  pub fn topology_digest(&self) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(MULTIPOINT_TOPOLOGY_DIGEST_DOMAIN);
    hasher.update(&self.frontend_topology_digest);
    hasher.update(&self.matrix.circuit_digest);
    for value in [
      self.matrix.row_variables,
      self.matrix.column_variables,
      self.witness_row_variables,
      self.dense_variables,
    ] {
      hasher.update(&value.to_le_bytes());
    }
    hasher.update(&self.family_h.geometric_origin);
    hasher.update(&self.family_h.geometric_ratio);
    for correction in &self.family_h.low_corrections {
      hasher.update(correction);
    }
    hash_nested_indices(&mut hasher, &self.dual_value_observations);
    hash_indices(&mut hasher, &self.group_value_observations);
    hasher.update(&self.gamma_challenge.to_le_bytes());
    hash_rounds(&mut hasher, &self.multipoint_rounds);
    hasher.update(&self.anchor_value_observation.to_le_bytes());
    hash_rounds(&mut hasher, &self.anchor_rounds);
    hash_len(&mut hasher, self.group_column_addresses.len());
    for address in &self.group_column_addresses {
      hasher.update(&address.to_le_bytes());
    }
    hash_indices(&mut hasher, &self.jagged_claim_private_values);
    *hasher.finalize().as_bytes()
  }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct F128MultipointTwistedAssistCensusV1 {
  pub dual_value_observations: u64,
  pub group_value_observations: u64,
  pub batching_challenges: u64,
  pub multipoint_rounds: u64,
  pub anchor_rounds: u64,
  pub group_members: u64,
  pub jagged_claims: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum F128MultipointTraceError {
  DimensionOverflow,
  InvalidShape(&'static str),
  InvalidIndex { kind: &'static str, index: u64, count: usize },
  DuplicateIndex { kind: &'static str, index: u64 },
}

impl fmt::Display for F128MultipointTraceError {
  fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::DimensionOverflow => {
        write!(formatter, "multipoint assist dimension overflow")
      },
      Self::InvalidShape(reason) => {
        write!(formatter, "invalid multipoint assist shape: {reason}")
      },
      Self::InvalidIndex { kind, index, count } => {
        write!(formatter, "{kind} index {index} is outside {count} values")
      },
      Self::DuplicateIndex { kind, index } => {
        write!(formatter, "{kind} index {index} is reused")
      },
    }
  }
}

impl std::error::Error for F128MultipointTraceError {}

fn validate_unique_index(
  index: u64,
  count: usize,
  kind: &'static str,
  used: &mut BTreeSet<u64>,
) -> Result<(), F128MultipointTraceError> {
  let valid = usize::try_from(index).ok().is_some_and(|index| index < count);
  if !valid {
    return Err(F128MultipointTraceError::InvalidIndex { kind, index, count });
  }
  if !used.insert(index) {
    return Err(F128MultipointTraceError::DuplicateIndex { kind, index });
  }
  Ok(())
}

fn hash_len(hasher: &mut blake3::Hasher, length: usize) {
  hasher.update(
    &u64::try_from(length).expect("trace length fits u64").to_le_bytes(),
  );
}

fn hash_indices(hasher: &mut blake3::Hasher, indices: &[u64]) {
  hash_len(hasher, indices.len());
  for index in indices {
    hasher.update(&index.to_le_bytes());
  }
}

fn hash_nested_indices(hasher: &mut blake3::Hasher, values: &[Vec<u64>]) {
  hash_len(hasher, values.len());
  for indices in values {
    hash_indices(hasher, indices);
  }
}

fn hash_rounds(hasher: &mut blake3::Hasher, rounds: &[F128MultipointRoundV1]) {
  hash_len(hasher, rounds.len());
  for round in rounds {
    for value in
      [round.one_observation, round.infinity_observation, round.challenge]
    {
      hasher.update(&value.to_le_bytes());
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  fn fixture() -> F128MultipointTwistedAssistTraceV1 {
    F128MultipointTwistedAssistTraceV1 {
      frontend_topology_digest: [1; 32],
      matrix: F128JaggedMatrixIdV1 {
        circuit_digest: [2; 32],
        row_variables: 1,
        column_variables: 6,
      },
      witness_row_variables: 2,
      dense_variables: 2,
      family_h: F128FamilyHConstantsV1 {
        geometric_origin: [3; 16],
        geometric_ratio: [4; 16],
        low_corrections: [[5; 16]; F128_FAMILY_H_CORRECTIONS],
      },
      dual_value_observations: vec![(0..128).collect(), (128..256).collect()],
      group_value_observations: vec![256],
      gamma_challenge: 0,
      multipoint_rounds: vec![
        F128MultipointRoundV1 {
          one_observation: 257,
          infinity_observation: 258,
          challenge: 1,
        },
        F128MultipointRoundV1 {
          one_observation: 259,
          infinity_observation: 260,
          challenge: 2,
        },
      ],
      anchor_value_observation: 261,
      anchor_rounds: (0..6)
        .map(|round| F128MultipointRoundV1 {
          one_observation: 262 + 2 * round,
          infinity_observation: 263 + 2 * round,
          challenge: 3 + round,
        })
        .collect(),
      group_column_addresses: vec![0, 1],
      jagged_claim_private_values: vec![0, 1, 2],
    }
  }

  #[test]
  fn validates_and_addresses_assist_topology() {
    let trace = fixture();
    trace.validate(274, 9, 3).expect("validate fixture");
    assert_eq!(trace.census().dual_value_observations, 256);
    assert_eq!(trace.census().jagged_claims, 3);
    assert_ne!(trace.topology_digest(), [0; 32]);
  }

  #[test]
  fn rejects_reused_child_challenge() {
    let mut trace = fixture();
    trace.anchor_rounds[0].challenge = trace.gamma_challenge;
    assert!(matches!(
      trace.validate(274, 9, 3),
      Err(F128MultipointTraceError::DuplicateIndex { .. })
    ));
  }
}
