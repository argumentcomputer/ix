use crate::F128AlgebraTraceV1;
use std::collections::BTreeSet;
use std::fmt;

const WIRING_TOPOLOGY_DIGEST_DOMAIN: &[u8] =
  b"ix:stage4:flock-wiring-topology:v1";

/// The two verifier values whose truth is deferred to the circuit-structure
/// accumulator: `MLE(live * id)` and `MLE(live)` at the Product-GKR endpoint.
pub const F128_WIRING_PRIVATE_VALUES: usize = 2;

/// Stable identity of Flock's digest-keyed circuit-structure matrix.
///
/// Rows are the circuit's gate-row domain. Columns are the padded cell-slot
/// domain followed by Flock's three-bit plane selector. Unlike the Boolean
/// lincheck matrices, this matrix can be rectangular.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct F128CircuitStructureMatrixIdV1 {
  pub circuit_digest: [u8; 32],
  pub row_variables: u32,
  pub column_variables: u32,
}

/// Complete, value-independent replay of Flock's circuit wiring verifier.
///
/// `algebra` checks Product-GKR, both terminal input equations, the gather
/// recombination, fixed public words, and `f_eval == g_eval`. The remaining
/// fields identify the three circuit-static claims and every packed-direct
/// gather claim that must flow into later accumulator/PCS stages.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128WiringTraceV1 {
  pub circuit_digest: [u8; 32],
  pub public_value_count: u64,
  pub row_variables: u32,
  pub cell_variables: u32,
  pub packed_claim_variables: u32,
  pub structure_base_variables: u32,
  pub fixed_public_values: Vec<Option<[u8; 16]>>,
  pub rho_challenges: Vec<u64>,
  pub closing_digest_challenges: [u64; 2],
  pub masked_id_private_value: u64,
  pub live_private_value: u64,
  pub sigma_eval_observation: u64,
  pub gather_observations: Vec<u64>,
  pub gather_high_bits: Vec<Vec<bool>>,
  pub algebra: F128AlgebraTraceV1,
}

impl F128WiringTraceV1 {
  pub fn validate(
    &self,
    public_values: usize,
    observed_values: usize,
    challenges: usize,
    private_values: usize,
  ) -> Result<(), F128WiringTraceError> {
    let expected_public = usize::try_from(self.public_value_count)
      .map_err(|_| F128WiringTraceError::DimensionOverflow)?;
    if expected_public != public_values
      || self.fixed_public_values.len() != public_values
    {
      return Err(F128WiringTraceError::PublicValueCount {
        expected: expected_public,
        actual: public_values,
        fixed: self.fixed_public_values.len(),
      });
    }
    if private_values != F128_WIRING_PRIVATE_VALUES
      || self.masked_id_private_value == self.live_private_value
    {
      return Err(F128WiringTraceError::PrivateValueShape {
        count: private_values,
      });
    }
    for index in [self.masked_id_private_value, self.live_private_value] {
      validate_index(index, private_values, |index, count| {
        F128WiringTraceError::PrivateValueIndex { index, count }
      })?;
    }

    let row_variables = usize::try_from(self.row_variables)
      .map_err(|_| F128WiringTraceError::DimensionOverflow)?;
    let cell_variables = usize::try_from(self.cell_variables)
      .map_err(|_| F128WiringTraceError::DimensionOverflow)?;
    let packed_variables = usize::try_from(self.packed_claim_variables)
      .map_err(|_| F128WiringTraceError::DimensionOverflow)?;
    let base_variables = usize::try_from(self.structure_base_variables)
      .map_err(|_| F128WiringTraceError::DimensionOverflow)?;
    if row_variables > cell_variables || row_variables > packed_variables {
      return Err(F128WiringTraceError::VariableShape);
    }
    let slot_variables = cell_variables - row_variables;
    if base_variables < slot_variables {
      return Err(F128WiringTraceError::VariableShape);
    }
    let rows = 1usize
      .checked_shl(self.row_variables)
      .ok_or(F128WiringTraceError::DimensionOverflow)?;
    let slots = 1usize
      .checked_shl(
        u32::try_from(slot_variables)
          .map_err(|_| F128WiringTraceError::DimensionOverflow)?,
      )
      .ok_or(F128WiringTraceError::DimensionOverflow)?;
    let public_slots = public_values.div_ceil(rows);
    if self
      .gather_observations
      .len()
      .checked_add(public_slots)
      .is_none_or(|used| used > slots)
    {
      return Err(F128WiringTraceError::CellSpaceShape {
        gate_slots: self.gather_observations.len(),
        public_slots,
        slots,
      });
    }

    if self.rho_challenges.len() != cell_variables {
      return Err(F128WiringTraceError::RhoShape {
        expected: cell_variables,
        actual: self.rho_challenges.len(),
      });
    }
    let mut challenge_set = BTreeSet::new();
    for &index in
      self.rho_challenges.iter().chain(&self.closing_digest_challenges)
    {
      validate_index(index, challenges, |index, count| {
        F128WiringTraceError::ChallengeIndex { index, count }
      })?;
      if !challenge_set.insert(index) {
        return Err(F128WiringTraceError::DuplicateChallenge { index });
      }
    }

    if self.gather_observations.len() != self.gather_high_bits.len() {
      return Err(F128WiringTraceError::GatherCount {
        observations: self.gather_observations.len(),
        points: self.gather_high_bits.len(),
      });
    }
    let high_variables = packed_variables - row_variables;
    let mut observation_set = BTreeSet::new();
    for &index in std::iter::once(&self.sigma_eval_observation)
      .chain(&self.gather_observations)
    {
      validate_index(index, observed_values, |index, count| {
        F128WiringTraceError::ObservationIndex { index, count }
      })?;
      if !observation_set.insert(index) {
        return Err(F128WiringTraceError::DuplicateObservation { index });
      }
    }
    for (claim, bits) in self.gather_high_bits.iter().enumerate() {
      if bits.len() != high_variables {
        return Err(F128WiringTraceError::GatherPointShape {
          claim,
          expected: high_variables,
          actual: bits.len(),
        });
      }
    }
    if !self.algebra.deferred_matrix_claims.is_empty() {
      return Err(F128WiringTraceError::DeferredAlgebraClaims {
        count: self.algebra.deferred_matrix_claims.len(),
      });
    }
    self
      .algebra
      .validate(public_values, observed_values, challenges, private_values)
      .map_err(|error| F128WiringTraceError::Algebra(error.to_string()))?;
    Ok(())
  }

  #[must_use]
  pub const fn structure_matrix(&self) -> F128CircuitStructureMatrixIdV1 {
    F128CircuitStructureMatrixIdV1 {
      circuit_digest: self.circuit_digest,
      row_variables: self.row_variables,
      column_variables: self.structure_base_variables + 3,
    }
  }

  #[must_use]
  pub fn census(&self) -> F128WiringCensusV1 {
    let algebra = self.algebra.census();
    F128WiringCensusV1 {
      product_layers: u64::from(self.cell_variables),
      product_rounds: u64::from(self.cell_variables)
        * u64::from(self.cell_variables.saturating_sub(1))
        / 2,
      gather_claims: u64::try_from(self.gather_observations.len())
        .expect("gather count fits u64"),
      fixed_public_values: u64::try_from(
        self.fixed_public_values.iter().filter(|value| value.is_some()).count(),
      )
      .expect("fixed-public count fits u64"),
      operations: algebra.operations,
      additions: algebra.additions,
      multiplications: algebra.multiplications,
      inversions: algebra.inversions,
      equalities: algebra.equalities,
      circuit_structure_claims: 3,
    }
  }

  /// Content address of the complete wiring replay, independent of values.
  #[must_use]
  pub fn topology_digest(&self) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(WIRING_TOPOLOGY_DIGEST_DOMAIN);
    hasher.update(&self.circuit_digest);
    for value in [
      self.public_value_count,
      u64::from(self.row_variables),
      u64::from(self.cell_variables),
      u64::from(self.packed_claim_variables),
      u64::from(self.structure_base_variables),
      self.masked_id_private_value,
      self.live_private_value,
      self.sigma_eval_observation,
    ] {
      hasher.update(&value.to_le_bytes());
    }
    hash_len(&mut hasher, self.fixed_public_values.len());
    for value in &self.fixed_public_values {
      match value {
        Some(value) => {
          hasher.update(&[1]);
          hasher.update(value);
        },
        None => {
          hasher.update(&[0]);
        },
      }
    }
    hash_indices(&mut hasher, &self.rho_challenges);
    hash_indices(&mut hasher, &self.closing_digest_challenges);
    hash_indices(&mut hasher, &self.gather_observations);
    hash_len(&mut hasher, self.gather_high_bits.len());
    for bits in &self.gather_high_bits {
      hash_len(&mut hasher, bits.len());
      for chunk in bits.chunks(8) {
        let byte = chunk
          .iter()
          .enumerate()
          .fold(0u8, |byte, (bit, value)| byte | (u8::from(*value) << bit));
        hasher.update(&[byte]);
      }
    }
    hasher.update(&self.algebra.topology_digest());
    *hasher.finalize().as_bytes()
  }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct F128WiringCensusV1 {
  pub product_layers: u64,
  pub product_rounds: u64,
  pub gather_claims: u64,
  pub fixed_public_values: u64,
  pub operations: u64,
  pub additions: u64,
  pub multiplications: u64,
  pub inversions: u64,
  pub equalities: u64,
  pub circuit_structure_claims: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum F128WiringTraceError {
  PublicValueCount { expected: usize, actual: usize, fixed: usize },
  PrivateValueShape { count: usize },
  PrivateValueIndex { index: u64, count: usize },
  DimensionOverflow,
  VariableShape,
  CellSpaceShape { gate_slots: usize, public_slots: usize, slots: usize },
  RhoShape { expected: usize, actual: usize },
  ChallengeIndex { index: u64, count: usize },
  DuplicateChallenge { index: u64 },
  ObservationIndex { index: u64, count: usize },
  DuplicateObservation { index: u64 },
  GatherCount { observations: usize, points: usize },
  GatherPointShape { claim: usize, expected: usize, actual: usize },
  DeferredAlgebraClaims { count: usize },
  Algebra(String),
}

impl fmt::Display for F128WiringTraceError {
  fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::PublicValueCount { expected, actual, fixed } => write!(
        formatter,
        "wiring has {actual} public values and {fixed} fixed-value entries; expected {expected}",
      ),
      Self::PrivateValueShape { count } => write!(
        formatter,
        "wiring has {count} private helper values; expected {F128_WIRING_PRIVATE_VALUES}",
      ),
      Self::PrivateValueIndex { index, count } => write!(
        formatter,
        "wiring private-value index {index} is outside {count} values",
      ),
      Self::DimensionOverflow => write!(formatter, "wiring dimension overflow"),
      Self::VariableShape => {
        write!(formatter, "wiring variable dimensions are inconsistent")
      },
      Self::CellSpaceShape { gate_slots, public_slots, slots } => write!(
        formatter,
        "wiring cell space has {slots} slots but needs {gate_slots} gate and {public_slots} public slots",
      ),
      Self::RhoShape { expected, actual } => write!(
        formatter,
        "wiring endpoint has {actual} coordinates; expected {expected}",
      ),
      Self::ChallengeIndex { index, count } => write!(
        formatter,
        "wiring challenge index {index} is outside {count} challenges",
      ),
      Self::DuplicateChallenge { index } => {
        write!(formatter, "wiring repeats challenge index {index}")
      },
      Self::ObservationIndex { index, count } => write!(
        formatter,
        "wiring observation index {index} is outside {count} values",
      ),
      Self::DuplicateObservation { index } => {
        write!(formatter, "wiring repeats observation index {index}")
      },
      Self::GatherCount { observations, points } => write!(
        formatter,
        "wiring has {observations} gather observations and {points} claim points",
      ),
      Self::GatherPointShape { claim, expected, actual } => write!(
        formatter,
        "wiring gather {claim} has {actual} fixed point bits; expected {expected}",
      ),
      Self::DeferredAlgebraClaims { count } => write!(
        formatter,
        "wiring algebra unexpectedly contains {count} deferred matrix claims",
      ),
      Self::Algebra(error) => {
        write!(formatter, "invalid wiring algebra: {error}")
      },
    }
  }
}

impl std::error::Error for F128WiringTraceError {}

fn validate_index(
  index: u64,
  count: usize,
  error: impl FnOnce(u64, usize) -> F128WiringTraceError,
) -> Result<(), F128WiringTraceError> {
  if usize::try_from(index).ok().is_none_or(|index| index >= count) {
    return Err(error(index, count));
  }
  Ok(())
}

fn hash_indices(hasher: &mut blake3::Hasher, indices: &[u64]) {
  hash_len(hasher, indices.len());
  for &index in indices {
    hasher.update(&index.to_le_bytes());
  }
}

fn hash_len(hasher: &mut blake3::Hasher, length: usize) {
  hasher.update(
    &u64::try_from(length)
      .expect("wiring topology length fits u64")
      .to_le_bytes(),
  );
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::{
    F128EqualityV1, F128InputSourceV1, F128ReferenceV1, F128VerifierPhaseV1,
  };

  fn fixture() -> F128WiringTraceV1 {
    F128WiringTraceV1 {
      circuit_digest: [9; 32],
      public_value_count: 1,
      row_variables: 1,
      cell_variables: 2,
      packed_claim_variables: 2,
      structure_base_variables: 1,
      fixed_public_values: vec![Some(7u128.to_le_bytes())],
      rho_challenges: vec![0, 1],
      closing_digest_challenges: [2, 3],
      masked_id_private_value: 0,
      live_private_value: 1,
      sigma_eval_observation: 0,
      gather_observations: vec![1],
      gather_high_bits: vec![vec![false]],
      algebra: F128AlgebraTraceV1 {
        operations: Vec::new(),
        equalities: vec![F128EqualityV1 {
          phase: F128VerifierPhaseV1::Wiring,
          left: F128ReferenceV1::Input(F128InputSourceV1::PublicValue(0)),
          right: F128ReferenceV1::Input(F128InputSourceV1::Constant(
            7u128.to_le_bytes(),
          )),
        }],
        deferred_matrix_claims: Vec::new(),
      },
    }
  }

  #[test]
  fn validates_conditional_wiring_boundary() {
    let trace = fixture();
    trace.validate(1, 2, 4, 2).unwrap();
    assert_eq!(trace.structure_matrix().column_variables, 4);
    assert_eq!(trace.census().circuit_structure_claims, 3);
    assert_ne!(trace.topology_digest(), [0; 32]);
  }

  #[test]
  fn rejects_aliased_terminal_inputs_and_bad_points() {
    let mut trace = fixture();
    trace.gather_observations[0] = trace.sigma_eval_observation;
    assert!(matches!(
      trace.validate(1, 2, 4, 2),
      Err(F128WiringTraceError::DuplicateObservation { .. })
    ));

    let mut trace = fixture();
    trace.gather_high_bits[0].push(true);
    assert!(matches!(
      trace.validate(1, 2, 4, 2),
      Err(F128WiringTraceError::GatherPointShape { .. })
    ));
  }
}
