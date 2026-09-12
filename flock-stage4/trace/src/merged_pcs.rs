use crate::F128ReferenceV1;
use crate::f128::{hash_reference, validate_reference};
use std::collections::BTreeSet;
use std::fmt;

const MERGED_PCS_TOPOLOGY_DIGEST_DOMAIN: &[u8] =
  b"ix:stage4:flock-merged-pcs-frontend:v1";

pub const F128_MERGED_PCS_BOOLEAN_CLAIMS: usize = 2;
pub const F128_RING_SWITCH_SKIP_WEIGHTS: usize = 64;
pub const F128_RING_SWITCH_SLICES: usize = 128;
pub const F128_RING_SWITCH_RANDOMIZERS: usize = 7;

/// One Boolean witness evaluation entering Flock's ring-switch reduction.
///
/// `x_outer` uses the native merged-opening convention: it is the complete
/// multilinear suffix following the six-coordinate univariate skip. Its
/// first coordinate is therefore the seventh packed bit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128MergedPcsBooleanClaimV1 {
  pub z_skip: F128ReferenceV1,
  pub skip_weights: Vec<F128ReferenceV1>,
  pub x_outer: Vec<F128ReferenceV1>,
  pub value: F128ReferenceV1,
}

/// Transcript locations for one succinct DP24 ring-switch proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128RingSwitchTraceV1 {
  pub s_hat_v_observations: Vec<u64>,
  pub r_dprime_challenges: Vec<u64>,
}

/// One degree-two round of the dense merged sumcheck.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct F128MergedPcsRoundV1 {
  pub one_observation: u64,
  pub infinity_observation: u64,
  pub challenge: u64,
}

/// Value-independent replay boundary for Flock's merged PCS opening.
///
/// This trace covers both Boolean ring switches, mixed claim batching, and
/// the complete dense sumcheck. Its outputs remain conditional on the
/// multipoint-twisted assist and the inner Ligerito opening.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128MergedPcsFrontendTraceV1 {
  /// Number of Boolean variables in the committed unpacked witness.
  pub commitment_variables: u32,
  /// The original commitment CAP byte payload absorbed by the main tape.
  pub commitment_cap_payload: u64,
  pub commitment_cap_nodes: u32,
  /// Jagged row dimension used by the assist.
  pub row_variables: u32,
  /// Jagged column dimension (`log2(jagged_heights.len())`).
  pub column_variables: u32,
  pub jagged_heights: Vec<u64>,
  pub boolean_claims: Vec<F128MergedPcsBooleanClaimV1>,
  pub ring_switches: Vec<F128RingSwitchTraceV1>,
  /// Value-only packed-direct intake, in the exact wiring-gather order.
  pub packed_direct_observations: Vec<u64>,
  /// Ring-switched coefficients first, then packed-direct coefficients.
  pub batching_challenges: Vec<u64>,
  pub merged_rounds: Vec<F128MergedPcsRoundV1>,
  /// The value later authenticated by the inner Ligerito opening at `rho`.
  pub q_eval_observation: u64,
}

impl F128MergedPcsFrontendTraceV1 {
  #[allow(clippy::too_many_arguments)]
  pub fn validate(
    &self,
    public_values: usize,
    observed_values: usize,
    challenges: usize,
    private_values: usize,
    algebra_operations: usize,
    payload_lengths: &[usize],
    packed_direct_point_variables: &[usize],
  ) -> Result<(), F128MergedPcsTraceError> {
    let commitment_variables = usize::try_from(self.commitment_variables)
      .map_err(|_| F128MergedPcsTraceError::DimensionOverflow)?;
    let row_variables = usize::try_from(self.row_variables)
      .map_err(|_| F128MergedPcsTraceError::DimensionOverflow)?;
    let column_variables = usize::try_from(self.column_variables)
      .map_err(|_| F128MergedPcsTraceError::DimensionOverflow)?;
    let dense_rounds = commitment_variables
      .checked_sub(F128_RING_SWITCH_RANDOMIZERS)
      .ok_or(F128MergedPcsTraceError::InvalidShape(
        "commitment dimension is smaller than the packing prefix",
      ))?;
    if self.merged_rounds.len() != dense_rounds {
      return Err(F128MergedPcsTraceError::InvalidShape(
        "merged-round count does not match the commitment dimension",
      ));
    }

    let expected_columns = 1usize
      .checked_shl(self.column_variables)
      .ok_or(F128MergedPcsTraceError::DimensionOverflow)?;
    if self.jagged_heights.len() != expected_columns {
      return Err(F128MergedPcsTraceError::InvalidShape(
        "jagged height count does not match the column dimension",
      ));
    }
    let row_capacity = 1u64
      .checked_shl(self.row_variables)
      .ok_or(F128MergedPcsTraceError::DimensionOverflow)?;
    if self.jagged_heights.iter().any(|&height| height > row_capacity) {
      return Err(F128MergedPcsTraceError::InvalidShape(
        "a jagged column exceeds the row domain",
      ));
    }
    let dense_capacity = 1u128
      .checked_shl(
        u32::try_from(dense_rounds)
          .map_err(|_| F128MergedPcsTraceError::DimensionOverflow)?,
      )
      .ok_or(F128MergedPcsTraceError::DimensionOverflow)?;
    let area = self
      .jagged_heights
      .iter()
      .try_fold(0u128, |area, &height| area.checked_add(u128::from(height)))
      .ok_or(F128MergedPcsTraceError::DimensionOverflow)?;
    if area > dense_capacity {
      return Err(F128MergedPcsTraceError::InvalidShape(
        "jagged area exceeds the committed dense stack",
      ));
    }

    let cap_nodes = usize::try_from(self.commitment_cap_nodes)
      .map_err(|_| F128MergedPcsTraceError::DimensionOverflow)?;
    if cap_nodes == 0 || !cap_nodes.is_power_of_two() {
      return Err(F128MergedPcsTraceError::InvalidShape(
        "commitment CAP node count is not a power of two",
      ));
    }
    let cap_payload = to_index(
      self.commitment_cap_payload,
      payload_lengths.len(),
      "commitment CAP payload",
    )?;
    let cap_bytes = cap_nodes
      .checked_mul(32)
      .ok_or(F128MergedPcsTraceError::DimensionOverflow)?;
    if payload_lengths[cap_payload] != cap_bytes {
      return Err(F128MergedPcsTraceError::PayloadLength {
        expected: cap_bytes,
        actual: payload_lengths[cap_payload],
      });
    }

    if self.boolean_claims.len() != F128_MERGED_PCS_BOOLEAN_CLAIMS
      || self.ring_switches.len() != F128_MERGED_PCS_BOOLEAN_CLAIMS
    {
      return Err(F128MergedPcsTraceError::InvalidShape(
        "merged frontend requires exactly the Boolean AB and C claims",
      ));
    }
    let suffix_variables = 1usize
      .checked_add(row_variables)
      .and_then(|value| value.checked_add(column_variables))
      .ok_or(F128MergedPcsTraceError::DimensionOverflow)?;
    for claim in &self.boolean_claims {
      if claim.skip_weights.len() != F128_RING_SWITCH_SKIP_WEIGHTS
        || claim.x_outer.len() != suffix_variables
      {
        return Err(F128MergedPcsTraceError::InvalidShape(
          "Boolean ring-switch claim has the wrong point shape",
        ));
      }
      for reference in std::iter::once(&claim.z_skip)
        .chain(&claim.skip_weights)
        .chain(&claim.x_outer)
        .chain(std::iter::once(&claim.value))
      {
        validate_reference(
          *reference,
          algebra_operations,
          public_values,
          observed_values,
          challenges,
          private_values,
        )
        .map_err(|error| {
          F128MergedPcsTraceError::Reference(error.to_string())
        })?;
      }
    }

    if self.packed_direct_observations.len()
      != packed_direct_point_variables.len()
      || packed_direct_point_variables
        .iter()
        .any(|&variables| variables != row_variables + column_variables)
    {
      return Err(F128MergedPcsTraceError::InvalidShape(
        "packed-direct claims have the wrong point shape",
      ));
    }
    if self.batching_challenges.len()
      != F128_MERGED_PCS_BOOLEAN_CLAIMS + self.packed_direct_observations.len()
    {
      return Err(F128MergedPcsTraceError::InvalidShape(
        "mixed batching challenge count does not match the claim count",
      ));
    }

    let mut used_observations = BTreeSet::new();
    for ring_switch in &self.ring_switches {
      if ring_switch.s_hat_v_observations.len() != F128_RING_SWITCH_SLICES
        || ring_switch.r_dprime_challenges.len() != F128_RING_SWITCH_RANDOMIZERS
      {
        return Err(F128MergedPcsTraceError::InvalidShape(
          "ring-switch transcript has the wrong shape",
        ));
      }
      for &index in &ring_switch.s_hat_v_observations {
        validate_unique_index(
          index,
          observed_values,
          "ring-switch observation",
          &mut used_observations,
        )?;
      }
    }
    for &index in &self.packed_direct_observations {
      validate_unique_index(
        index,
        observed_values,
        "packed-direct observation",
        &mut used_observations,
      )?;
    }
    for round in &self.merged_rounds {
      for index in [round.one_observation, round.infinity_observation] {
        validate_unique_index(
          index,
          observed_values,
          "merged-round observation",
          &mut used_observations,
        )?;
      }
    }
    validate_unique_index(
      self.q_eval_observation,
      observed_values,
      "q-evaluation observation",
      &mut used_observations,
    )?;

    let mut used_challenges = BTreeSet::new();
    for ring_switch in &self.ring_switches {
      for &index in &ring_switch.r_dprime_challenges {
        validate_unique_index(
          index,
          challenges,
          "ring-switch challenge",
          &mut used_challenges,
        )?;
      }
    }
    for &index in &self.batching_challenges {
      validate_unique_index(
        index,
        challenges,
        "batching challenge",
        &mut used_challenges,
      )?;
    }
    for round in &self.merged_rounds {
      validate_unique_index(
        round.challenge,
        challenges,
        "merged-round challenge",
        &mut used_challenges,
      )?;
    }
    Ok(())
  }

  #[must_use]
  pub fn census(&self) -> F128MergedPcsFrontendCensusV1 {
    F128MergedPcsFrontendCensusV1 {
      boolean_claims: u64::try_from(self.boolean_claims.len())
        .expect("Boolean claim count fits u64"),
      ring_switch_slice_observations: self
        .ring_switches
        .iter()
        .map(|trace| {
          u64::try_from(trace.s_hat_v_observations.len())
            .expect("ring-switch slice count fits u64")
        })
        .sum(),
      ring_switch_challenges: self
        .ring_switches
        .iter()
        .map(|trace| {
          u64::try_from(trace.r_dprime_challenges.len())
            .expect("ring-switch challenge count fits u64")
        })
        .sum(),
      packed_direct_claims: u64::try_from(
        self.packed_direct_observations.len(),
      )
      .expect("packed-direct claim count fits u64"),
      batching_challenges: u64::try_from(self.batching_challenges.len())
        .expect("batching challenge count fits u64"),
      merged_rounds: u64::try_from(self.merged_rounds.len())
        .expect("merged round count fits u64"),
      conditional_outputs: 2,
    }
  }

  /// Content address of the complete frontend topology, independent of proof
  /// values and transcript contents.
  #[must_use]
  pub fn topology_digest(&self) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(MERGED_PCS_TOPOLOGY_DIGEST_DOMAIN);
    for value in [
      u64::from(self.commitment_variables),
      self.commitment_cap_payload,
      u64::from(self.commitment_cap_nodes),
      u64::from(self.row_variables),
      u64::from(self.column_variables),
      self.q_eval_observation,
    ] {
      hasher.update(&value.to_le_bytes());
    }
    hash_u64s(&mut hasher, &self.jagged_heights);
    hash_len(&mut hasher, self.boolean_claims.len());
    for claim in &self.boolean_claims {
      hash_reference(&mut hasher, claim.z_skip);
      hash_references(&mut hasher, &claim.skip_weights);
      hash_references(&mut hasher, &claim.x_outer);
      hash_reference(&mut hasher, claim.value);
    }
    hash_len(&mut hasher, self.ring_switches.len());
    for ring_switch in &self.ring_switches {
      hash_u64s(&mut hasher, &ring_switch.s_hat_v_observations);
      hash_u64s(&mut hasher, &ring_switch.r_dprime_challenges);
    }
    hash_u64s(&mut hasher, &self.packed_direct_observations);
    hash_u64s(&mut hasher, &self.batching_challenges);
    hash_len(&mut hasher, self.merged_rounds.len());
    for round in &self.merged_rounds {
      for value in
        [round.one_observation, round.infinity_observation, round.challenge]
      {
        hasher.update(&value.to_le_bytes());
      }
    }
    *hasher.finalize().as_bytes()
  }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct F128MergedPcsFrontendCensusV1 {
  pub boolean_claims: u64,
  pub ring_switch_slice_observations: u64,
  pub ring_switch_challenges: u64,
  pub packed_direct_claims: u64,
  pub batching_challenges: u64,
  pub merged_rounds: u64,
  /// `running` for the assist identity and `(rho, q_eval)` for Ligerito.
  pub conditional_outputs: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum F128MergedPcsTraceError {
  DimensionOverflow,
  InvalidShape(&'static str),
  InvalidIndex { kind: &'static str, index: u64, count: usize },
  DuplicateIndex { kind: &'static str, index: u64 },
  PayloadLength { expected: usize, actual: usize },
  Reference(String),
}

impl fmt::Display for F128MergedPcsTraceError {
  fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::DimensionOverflow => {
        write!(formatter, "merged PCS dimension overflow")
      },
      Self::InvalidShape(reason) => {
        write!(formatter, "invalid merged PCS shape: {reason}")
      },
      Self::InvalidIndex { kind, index, count } => {
        write!(formatter, "{kind} index {index} is outside {count} values")
      },
      Self::DuplicateIndex { kind, index } => {
        write!(formatter, "{kind} index {index} is reused")
      },
      Self::PayloadLength { expected, actual } => write!(
        formatter,
        "commitment CAP payload has {actual} bytes; expected {expected}",
      ),
      Self::Reference(error) => {
        write!(formatter, "invalid merged PCS algebra reference: {error}")
      },
    }
  }
}

impl std::error::Error for F128MergedPcsTraceError {}

fn to_index(
  index: u64,
  count: usize,
  kind: &'static str,
) -> Result<usize, F128MergedPcsTraceError> {
  usize::try_from(index)
    .ok()
    .filter(|&index| index < count)
    .ok_or(F128MergedPcsTraceError::InvalidIndex { kind, index, count })
}

fn validate_unique_index(
  index: u64,
  count: usize,
  kind: &'static str,
  used: &mut BTreeSet<u64>,
) -> Result<(), F128MergedPcsTraceError> {
  to_index(index, count, kind)?;
  if !used.insert(index) {
    return Err(F128MergedPcsTraceError::DuplicateIndex { kind, index });
  }
  Ok(())
}

fn hash_len(hasher: &mut blake3::Hasher, length: usize) {
  hasher.update(
    &u64::try_from(length).expect("trace length fits u64").to_le_bytes(),
  );
}

fn hash_u64s(hasher: &mut blake3::Hasher, values: &[u64]) {
  hash_len(hasher, values.len());
  for value in values {
    hasher.update(&value.to_le_bytes());
  }
}

fn hash_references(
  hasher: &mut blake3::Hasher,
  references: &[F128ReferenceV1],
) {
  hash_len(hasher, references.len());
  for &reference in references {
    hash_reference(hasher, reference);
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::F128InputSourceV1;

  fn reference(index: u64) -> F128ReferenceV1 {
    F128ReferenceV1::Input(F128InputSourceV1::Challenge(index))
  }

  fn fixture() -> F128MergedPcsFrontendTraceV1 {
    let claim = F128MergedPcsBooleanClaimV1 {
      z_skip: reference(0),
      skip_weights: (0..64).map(reference).collect(),
      x_outer: vec![reference(0), reference(1), reference(2)],
      value: reference(0),
    };
    F128MergedPcsFrontendTraceV1 {
      commitment_variables: 9,
      commitment_cap_payload: 0,
      commitment_cap_nodes: 1,
      row_variables: 1,
      column_variables: 1,
      jagged_heights: vec![1, 2],
      boolean_claims: vec![claim.clone(), claim],
      ring_switches: vec![
        F128RingSwitchTraceV1 {
          s_hat_v_observations: (0..128).collect(),
          r_dprime_challenges: (64..71).collect(),
        },
        F128RingSwitchTraceV1 {
          s_hat_v_observations: (128..256).collect(),
          r_dprime_challenges: (71..78).collect(),
        },
      ],
      packed_direct_observations: vec![256],
      batching_challenges: vec![78, 79, 80],
      merged_rounds: vec![
        F128MergedPcsRoundV1 {
          one_observation: 257,
          infinity_observation: 258,
          challenge: 81,
        },
        F128MergedPcsRoundV1 {
          one_observation: 259,
          infinity_observation: 260,
          challenge: 82,
        },
      ],
      q_eval_observation: 261,
    }
  }

  #[test]
  fn validates_and_addresses_frontend_topology() {
    let trace = fixture();
    trace.validate(0, 262, 83, 0, 0, &[32], &[2]).expect("validate fixture");
    assert_eq!(trace.census().ring_switch_slice_observations, 256);
    assert_eq!(trace.census().conditional_outputs, 2);
    assert_ne!(trace.topology_digest(), [0; 32]);
  }

  #[test]
  fn rejects_reused_fiat_shamir_sources() {
    let mut trace = fixture();
    trace.merged_rounds[0].challenge = trace.batching_challenges[0];
    assert!(matches!(
      trace.validate(0, 262, 83, 0, 0, &[32], &[2]),
      Err(F128MergedPcsTraceError::DuplicateIndex { .. })
    ));
  }
}
