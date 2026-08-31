use std::collections::BTreeSet;
use std::fmt;

const LIGERITO_TOPOLOGY_DIGEST_DOMAIN: &[u8] =
  b"ix:stage4:flock-inner-ligerito-topology:v1";

/// Transcript indices of one canonical `GF(2^256)` value, in `(c0, c1)`
/// order over Flock's `GF(2^128)` base field.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct F256IndexPairV1 {
  pub c0: u64,
  pub c1: u64,
}

/// One quadratic sumcheck message `(u_0, u_2)` in `GF(2^256)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct F256LigeritoMessageV1 {
  pub u_0: F256IndexPairV1,
  pub u_2: F256IndexPairV1,
}

/// One OOD evaluation mixed into the running Ligerito claim.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128LigeritoOodClaimV1 {
  pub point_challenges: Vec<u64>,
  pub value_observation: u64,
  /// Recursive commitments introduce their OOD claim with a quadratic;
  /// L0 adds its base-table claim before the first quadratic exists.
  pub intro_message: Option<F256LigeritoMessageV1>,
  pub beta_challenge: u64,
}

/// One opened commitment in the recursive Ligerito ladder.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128LigeritoLevelV1 {
  /// Byte payload containing this level's complete Merkle cap.
  pub cap_payload: u64,
  pub cap_nodes: u32,
  /// `log2` of the committed codeword-position count.
  pub block_variables: u32,
  /// Number of base-field words in each opened row. L0 may use a non-power-
  /// of-two live-lane count; recursive levels are powers of two.
  pub lane_count: u32,
  /// Dimension of the additive-code message indexed by a query.
  pub log_message_columns: u32,
  /// Canonical binary-decomposition schedule, in descending depth order.
  pub summand_depths: Vec<u32>,
  /// One transcript challenge word per query, in schedule order.
  pub query_challenges: Vec<u64>,
  /// Private F128 indices for each opened row, in query/lane order.
  pub opened_rows: Vec<Vec<u64>>,
  /// Private 32-byte digest indices for each capped Merkle path.
  pub merkle_paths: Vec<Vec<u64>>,
  /// Challenge point which folds the row lanes. Each entry consumes two
  /// consecutive base-field challenge words as one F256 coordinate.
  pub lane_challenges: Vec<F256IndexPairV1>,
  /// The next quadratic message observed after each lane-fold challenge.
  pub round_messages: Vec<F256LigeritoMessageV1>,
  /// Base-field equality point which batches the queried rows.
  pub alpha_challenges: Vec<u64>,
  pub ood_claims: Vec<F128LigeritoOodClaimV1>,
  /// Present for every level except the final clear residual.
  pub intro_message: Option<F256LigeritoMessageV1>,
  pub beta_challenge: u64,
}

/// Value-independent replay boundary for the packed-direct inner opening of
/// Flock's merged PCS. Opened rows and Merkle siblings are private witness;
/// every cap, message, OOD value, and challenge names the already-constrained
/// main transcript.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128InnerLigeritoTraceV1 {
  pub frontend_topology_digest: [u8; 32],
  pub commitment_variables: u32,
  /// Re-observation of the frontend's `q_eval` in the one-claim inner batch.
  pub q_eval_observation: u64,
  pub batching_challenge: u64,
  /// Re-observation of `batching_challenge * q_eval` at Ligerito entry.
  pub target_observation: u64,
  pub first_message: F256LigeritoMessageV1,
  pub levels: Vec<F128LigeritoLevelV1>,
  /// Final `GF(2^256)` residual polynomial, observed in clear as interleaved
  /// pairs of `GF(2^128)` coordinates.
  pub final_yr_observations: Vec<u64>,
}

impl F128InnerLigeritoTraceV1 {
  pub fn validate(
    &self,
    observed_values: usize,
    challenges: usize,
    payload_lengths: &[usize],
    private_values: usize,
    private_digests: usize,
  ) -> Result<(), F128InnerLigeritoTraceError> {
    let log_n = usize::try_from(self.commitment_variables)
      .map_err(|_| F128InnerLigeritoTraceError::DimensionOverflow)?
      .checked_sub(7)
      .ok_or(F128InnerLigeritoTraceError::InvalidShape(
        "commitment dimension is below the packing width",
      ))?;
    if self.levels.len() < 2 {
      return Err(F128InnerLigeritoTraceError::InvalidShape(
        "the recursive ladder must contain at least two commitments",
      ));
    }

    let mut used_observations = BTreeSet::new();
    let mut used_challenges = BTreeSet::new();
    let mut used_payloads = BTreeSet::new();
    let mut used_private_values = BTreeSet::new();
    let mut used_private_digests = BTreeSet::new();

    validate_unique(
      self.q_eval_observation,
      observed_values,
      "q-evaluation observation",
      &mut used_observations,
    )?;
    validate_unique(
      self.target_observation,
      observed_values,
      "target observation",
      &mut used_observations,
    )?;
    validate_message(
      self.first_message,
      observed_values,
      &mut used_observations,
    )?;
    validate_unique(
      self.batching_challenge,
      challenges,
      "batching challenge",
      &mut used_challenges,
    )?;

    let mut prior_columns = log_n;
    for (level_index, level) in self.levels.iter().enumerate() {
      let block_variables = usize::try_from(level.block_variables)
        .map_err(|_| F128InnerLigeritoTraceError::DimensionOverflow)?;
      let lane_count = usize::try_from(level.lane_count)
        .map_err(|_| F128InnerLigeritoTraceError::DimensionOverflow)?;
      let log_columns = usize::try_from(level.log_message_columns)
        .map_err(|_| F128InnerLigeritoTraceError::DimensionOverflow)?;
      let lane_variables = level.lane_challenges.len();
      if lane_count == 0
        || lane_count > checked_pow2(lane_variables)?
        || level.round_messages.len() != lane_variables
        || prior_columns < lane_variables
        || prior_columns - lane_variables != log_columns
      {
        return Err(F128InnerLigeritoTraceError::InvalidLevelShape {
          level: level_index,
          reason: "lane fold does not reach the declared message dimension",
        });
      }
      if level_index != 0 && lane_count != checked_pow2(lane_variables)? {
        return Err(F128InnerLigeritoTraceError::InvalidLevelShape {
          level: level_index,
          reason: "a recursive commitment has a non-power-of-two lane count",
        });
      }
      if block_variables < log_columns {
        return Err(F128InnerLigeritoTraceError::InvalidLevelShape {
          level: level_index,
          reason: "codeword dimension is below its message dimension",
        });
      }
      prior_columns = log_columns
        .checked_add(1)
        .ok_or(F128InnerLigeritoTraceError::DimensionOverflow)?;

      let query_shape = validate_schedule(level_index, level)?;
      if level.opened_rows.len() != query_shape.queries
        || level.merkle_paths.len() != query_shape.queries
        || level.query_challenges.len() != query_shape.queries
        || level.opened_rows.iter().any(|row| row.len() != lane_count)
        || level
          .merkle_paths
          .iter()
          .any(|path| path.len() != query_shape.path_length)
      {
        return Err(F128InnerLigeritoTraceError::InvalidLevelShape {
          level: level_index,
          reason: "query, row, or Merkle-path dimensions differ",
        });
      }
      if level.alpha_challenges.len() != ceil_log2(query_shape.queries) {
        return Err(F128InnerLigeritoTraceError::InvalidLevelShape {
          level: level_index,
          reason: "query-batching point has the wrong dimension",
        });
      }
      if level_index == 0 {
        if level.ood_claims.iter().any(|claim| {
          claim.point_challenges.len() != log_n || claim.intro_message.is_some()
        }) {
          return Err(F128InnerLigeritoTraceError::InvalidLevelShape {
            level: level_index,
            reason: "L0 OOD claim has the wrong point or an intro message",
          });
        }
      } else if level.ood_claims.iter().any(|claim| {
        claim.point_challenges.len()
          != usize::try_from(self.levels[level_index - 1].log_message_columns)
            .expect("validated dimension fits usize")
            + 1
          || claim.intro_message.is_none()
      }) {
        return Err(F128InnerLigeritoTraceError::InvalidLevelShape {
          level: level_index,
          reason: "recursive OOD claim has the wrong point or intro message",
        });
      }
      let is_final = level_index + 1 == self.levels.len();
      if level.intro_message.is_some() == is_final {
        return Err(F128InnerLigeritoTraceError::InvalidLevelShape {
          level: level_index,
          reason: "only non-final levels carry a consistency intro message",
        });
      }

      let cap_payload = validate_index(
        level.cap_payload,
        payload_lengths.len(),
        "cap payload",
      )?;
      if !used_payloads.insert(cap_payload)
        || payload_lengths[cap_payload]
          != usize::try_from(level.cap_nodes)
            .map_err(|_| F128InnerLigeritoTraceError::DimensionOverflow)?
            .checked_mul(32)
            .ok_or(F128InnerLigeritoTraceError::DimensionOverflow)?
        || usize::try_from(level.cap_nodes).ok()
          != Some(checked_pow2(query_shape.cap_depth)?)
      {
        return Err(F128InnerLigeritoTraceError::InvalidLevelShape {
          level: level_index,
          reason: "cap payload or cap depth is inconsistent",
        });
      }

      for pair in &level.lane_challenges {
        validate_pair(*pair, challenges, &mut used_challenges)?;
      }
      for &message in &level.round_messages {
        validate_message(message, observed_values, &mut used_observations)?;
      }
      for &index in &level.query_challenges {
        validate_unique(
          index,
          challenges,
          "query challenge",
          &mut used_challenges,
        )?;
      }
      for &index in &level.alpha_challenges {
        validate_unique(
          index,
          challenges,
          "alpha challenge",
          &mut used_challenges,
        )?;
      }
      validate_unique(
        level.beta_challenge,
        challenges,
        "level beta challenge",
        &mut used_challenges,
      )?;
      if let Some(message) = level.intro_message {
        validate_message(message, observed_values, &mut used_observations)?;
      }
      for claim in &level.ood_claims {
        for &index in &claim.point_challenges {
          validate_unique(
            index,
            challenges,
            "OOD point challenge",
            &mut used_challenges,
          )?;
        }
        validate_unique(
          claim.beta_challenge,
          challenges,
          "OOD beta challenge",
          &mut used_challenges,
        )?;
        validate_unique(
          claim.value_observation,
          observed_values,
          "OOD value observation",
          &mut used_observations,
        )?;
        if let Some(message) = claim.intro_message {
          validate_message(message, observed_values, &mut used_observations)?;
        }
      }
      for row in &level.opened_rows {
        for &index in row {
          validate_unique(
            index,
            private_values,
            "opened-row private value",
            &mut used_private_values,
          )?;
        }
      }
      for path in &level.merkle_paths {
        for &index in path {
          validate_unique(
            index,
            private_digests,
            "Merkle-path private digest",
            &mut used_private_digests,
          )?;
        }
      }
    }

    let final_columns = usize::try_from(
      self.levels.last().expect("at least two levels").log_message_columns,
    )
    .map_err(|_| F128InnerLigeritoTraceError::DimensionOverflow)?;
    let final_coordinate_columns = final_columns
      .checked_add(1)
      .ok_or(F128InnerLigeritoTraceError::DimensionOverflow)?;
    if self.final_yr_observations.len()
      != checked_pow2(final_coordinate_columns)?
    {
      return Err(F128InnerLigeritoTraceError::InvalidShape(
        "the final split-coordinate polynomial has the wrong length",
      ));
    }
    for &index in &self.final_yr_observations {
      validate_unique(
        index,
        observed_values,
        "final polynomial observation",
        &mut used_observations,
      )?;
    }
    if used_private_values.len() != private_values
      || used_private_digests.len() != private_digests
    {
      return Err(F128InnerLigeritoTraceError::InvalidShape(
        "the private row/path maps are not exhaustive",
      ));
    }
    Ok(())
  }

  #[must_use]
  pub fn census(&self) -> F128InnerLigeritoCensusV1 {
    let mut census = F128InnerLigeritoCensusV1 {
      levels: self.levels.len().try_into().expect("level count fits u64"),
      ..F128InnerLigeritoCensusV1::default()
    };
    census.messages = 1;
    census.observed_values = 2 + 4;
    census.challenges = 1;
    census.final_words = self
      .final_yr_observations
      .len()
      .try_into()
      .expect("final word count fits u64");
    census.observed_values += census.final_words;
    for level in &self.levels {
      census.cap_nodes += u64::from(level.cap_nodes);
      census.queries += u64::try_from(level.query_challenges.len())
        .expect("query count fits u64");
      census.opened_values +=
        u64::try_from(level.opened_rows.iter().map(Vec::len).sum::<usize>())
          .expect("opened value count fits u64");
      census.path_digests +=
        u64::try_from(level.merkle_paths.iter().map(Vec::len).sum::<usize>())
          .expect("path digest count fits u64");
      census.f256_fold_challenges += u64::try_from(level.lane_challenges.len())
        .expect("fold challenge count fits u64");
      census.alpha_challenges += u64::try_from(level.alpha_challenges.len())
        .expect("alpha challenge count fits u64");
      census.ood_claims +=
        u64::try_from(level.ood_claims.len()).expect("OOD count fits u64");
      census.challenges += 2 * level.lane_challenges.len() as u64
        + level.query_challenges.len() as u64
        + level.alpha_challenges.len() as u64
        + 1;
      if level.intro_message.is_some() {
        census.messages += 1;
        census.observed_values += 4;
      }
      for claim in &level.ood_claims {
        census.challenges += claim.point_challenges.len() as u64 + 1;
        census.observed_values += 1;
        if claim.intro_message.is_some() {
          census.messages += 1;
          census.observed_values += 4;
        }
      }
    }
    census.messages += census.f256_fold_challenges;
    census.observed_values += 4 * census.f256_fold_challenges;
    census
  }

  #[must_use]
  pub fn topology_digest(&self) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(LIGERITO_TOPOLOGY_DIGEST_DOMAIN);
    hasher.update(&self.frontend_topology_digest);
    hash_u64(&mut hasher, u64::from(self.commitment_variables));
    hash_u64(&mut hasher, self.q_eval_observation);
    hash_u64(&mut hasher, self.batching_challenge);
    hash_u64(&mut hasher, self.target_observation);
    hash_message(&mut hasher, self.first_message);
    hash_u64(&mut hasher, self.levels.len() as u64);
    for level in &self.levels {
      hash_u64(&mut hasher, level.cap_payload);
      for value in [
        level.cap_nodes,
        level.block_variables,
        level.lane_count,
        level.log_message_columns,
      ] {
        hash_u64(&mut hasher, u64::from(value));
      }
      hash_u32s(&mut hasher, &level.summand_depths);
      hash_indices(&mut hasher, &level.query_challenges);
      hash_nested_indices(&mut hasher, &level.opened_rows);
      hash_nested_indices(&mut hasher, &level.merkle_paths);
      hash_pairs(&mut hasher, &level.lane_challenges);
      hash_u64(&mut hasher, level.round_messages.len() as u64);
      for &message in &level.round_messages {
        hash_message(&mut hasher, message);
      }
      hash_indices(&mut hasher, &level.alpha_challenges);
      hash_u64(&mut hasher, level.ood_claims.len() as u64);
      for claim in &level.ood_claims {
        hash_indices(&mut hasher, &claim.point_challenges);
        hash_u64(&mut hasher, claim.value_observation);
        hash_optional_message(&mut hasher, claim.intro_message);
        hash_u64(&mut hasher, claim.beta_challenge);
      }
      hash_optional_message(&mut hasher, level.intro_message);
      hash_u64(&mut hasher, level.beta_challenge);
    }
    hash_indices(&mut hasher, &self.final_yr_observations);
    *hasher.finalize().as_bytes()
  }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct F128InnerLigeritoCensusV1 {
  pub levels: u64,
  pub cap_nodes: u64,
  pub queries: u64,
  pub opened_values: u64,
  pub path_digests: u64,
  pub messages: u64,
  pub f256_fold_challenges: u64,
  pub alpha_challenges: u64,
  pub ood_claims: u64,
  pub final_words: u64,
  pub observed_values: u64,
  pub challenges: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum F128InnerLigeritoTraceError {
  DimensionOverflow,
  InvalidShape(&'static str),
  InvalidLevelShape { level: usize, reason: &'static str },
  InvalidIndex { kind: &'static str, index: u64, count: usize },
  DuplicateIndex { kind: &'static str, index: usize },
}

impl fmt::Display for F128InnerLigeritoTraceError {
  fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::DimensionOverflow => {
        write!(formatter, "inner Ligerito dimension overflow")
      },
      Self::InvalidShape(reason) => {
        write!(formatter, "invalid inner Ligerito shape: {reason}")
      },
      Self::InvalidLevelShape { level, reason } => {
        write!(formatter, "invalid inner Ligerito level {level}: {reason}")
      },
      Self::InvalidIndex { kind, index, count } => {
        write!(
          formatter,
          "inner Ligerito {kind} {index} is outside {count} values"
        )
      },
      Self::DuplicateIndex { kind, index } => {
        write!(formatter, "inner Ligerito reuses {kind} {index}")
      },
    }
  }
}

impl std::error::Error for F128InnerLigeritoTraceError {}

#[derive(Clone, Copy)]
struct QueryShape {
  queries: usize,
  cap_depth: usize,
  path_length: usize,
}

fn validate_schedule(
  level_index: usize,
  level: &F128LigeritoLevelV1,
) -> Result<QueryShape, F128InnerLigeritoTraceError> {
  let block_variables = usize::try_from(level.block_variables)
    .map_err(|_| F128InnerLigeritoTraceError::DimensionOverflow)?;
  if level.summand_depths.is_empty() {
    return Err(F128InnerLigeritoTraceError::InvalidLevelShape {
      level: level_index,
      reason: "query schedule is empty",
    });
  }
  let mut prior = usize::MAX;
  let mut queries = 0usize;
  for &depth in &level.summand_depths {
    let depth = usize::try_from(depth)
      .map_err(|_| F128InnerLigeritoTraceError::DimensionOverflow)?;
    if depth > block_variables || depth >= prior {
      return Err(F128InnerLigeritoTraceError::InvalidLevelShape {
        level: level_index,
        reason: "query summand depths are not canonical descending depths",
      });
    }
    prior = depth;
    queries = queries
      .checked_add(checked_pow2(depth)?)
      .ok_or(F128InnerLigeritoTraceError::DimensionOverflow)?;
  }
  let cap_depth = usize::try_from(level.summand_depths[0])
    .map_err(|_| F128InnerLigeritoTraceError::DimensionOverflow)?;
  Ok(QueryShape {
    queries,
    cap_depth,
    path_length: block_variables - cap_depth,
  })
}

fn validate_message(
  message: F256LigeritoMessageV1,
  count: usize,
  used: &mut BTreeSet<usize>,
) -> Result<(), F128InnerLigeritoTraceError> {
  for pair in [message.u_0, message.u_2] {
    for index in [pair.c0, pair.c1] {
      validate_unique(index, count, "message observation", used)?;
    }
  }
  Ok(())
}

fn validate_pair(
  pair: F256IndexPairV1,
  count: usize,
  used: &mut BTreeSet<usize>,
) -> Result<(), F128InnerLigeritoTraceError> {
  for index in [pair.c0, pair.c1] {
    validate_unique(index, count, "F256 challenge", used)?;
  }
  Ok(())
}

fn validate_unique(
  index: u64,
  count: usize,
  kind: &'static str,
  used: &mut BTreeSet<usize>,
) -> Result<(), F128InnerLigeritoTraceError> {
  let index = validate_index(index, count, kind)?;
  if !used.insert(index) {
    return Err(F128InnerLigeritoTraceError::DuplicateIndex { kind, index });
  }
  Ok(())
}

fn validate_index(
  index: u64,
  count: usize,
  kind: &'static str,
) -> Result<usize, F128InnerLigeritoTraceError> {
  usize::try_from(index)
    .ok()
    .filter(|&index| index < count)
    .ok_or(F128InnerLigeritoTraceError::InvalidIndex { kind, index, count })
}

fn checked_pow2(exponent: usize) -> Result<usize, F128InnerLigeritoTraceError> {
  1usize
    .checked_shl(
      u32::try_from(exponent)
        .map_err(|_| F128InnerLigeritoTraceError::DimensionOverflow)?,
    )
    .ok_or(F128InnerLigeritoTraceError::DimensionOverflow)
}

fn ceil_log2(value: usize) -> usize {
  if value <= 1 {
    0
  } else {
    usize::BITS as usize - (value - 1).leading_zeros() as usize
  }
}

fn hash_u64(hasher: &mut blake3::Hasher, value: u64) {
  hasher.update(&value.to_le_bytes());
}

fn hash_indices(hasher: &mut blake3::Hasher, values: &[u64]) {
  hash_u64(hasher, values.len() as u64);
  for &value in values {
    hash_u64(hasher, value);
  }
}

fn hash_u32s(hasher: &mut blake3::Hasher, values: &[u32]) {
  hash_u64(hasher, values.len() as u64);
  for &value in values {
    hash_u64(hasher, u64::from(value));
  }
}

fn hash_nested_indices(hasher: &mut blake3::Hasher, values: &[Vec<u64>]) {
  hash_u64(hasher, values.len() as u64);
  for value in values {
    hash_indices(hasher, value);
  }
}

fn hash_pair(hasher: &mut blake3::Hasher, pair: F256IndexPairV1) {
  hash_u64(hasher, pair.c0);
  hash_u64(hasher, pair.c1);
}

fn hash_pairs(hasher: &mut blake3::Hasher, pairs: &[F256IndexPairV1]) {
  hash_u64(hasher, pairs.len() as u64);
  for &pair in pairs {
    hash_pair(hasher, pair);
  }
}

fn hash_message(hasher: &mut blake3::Hasher, message: F256LigeritoMessageV1) {
  hash_pair(hasher, message.u_0);
  hash_pair(hasher, message.u_2);
}

fn hash_optional_message(
  hasher: &mut blake3::Hasher,
  message: Option<F256LigeritoMessageV1>,
) {
  hash_u64(hasher, u64::from(message.is_some()));
  if let Some(message) = message {
    hash_message(hasher, message);
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  fn pair(start: u64) -> F256IndexPairV1 {
    F256IndexPairV1 { c0: start, c1: start + 1 }
  }

  fn message(start: u64) -> F256LigeritoMessageV1 {
    F256LigeritoMessageV1 { u_0: pair(start), u_2: pair(start + 2) }
  }

  fn fixture() -> F128InnerLigeritoTraceV1 {
    F128InnerLigeritoTraceV1 {
      frontend_topology_digest: [7; 32],
      commitment_variables: 10,
      q_eval_observation: 0,
      batching_challenge: 0,
      target_observation: 1,
      first_message: message(2),
      levels: vec![
        F128LigeritoLevelV1 {
          cap_payload: 0,
          cap_nodes: 2,
          block_variables: 2,
          lane_count: 2,
          log_message_columns: 2,
          summand_depths: vec![1],
          query_challenges: vec![1, 2],
          opened_rows: vec![vec![0, 1], vec![2, 3]],
          merkle_paths: vec![vec![0], vec![1]],
          lane_challenges: vec![pair(3)],
          round_messages: vec![message(12)],
          alpha_challenges: vec![5],
          ood_claims: vec![],
          intro_message: Some(message(6)),
          beta_challenge: 6,
        },
        F128LigeritoLevelV1 {
          cap_payload: 1,
          cap_nodes: 1,
          block_variables: 2,
          lane_count: 4,
          log_message_columns: 1,
          summand_depths: vec![0],
          query_challenges: vec![11],
          opened_rows: vec![vec![4, 5, 6, 7]],
          merkle_paths: vec![vec![2, 3]],
          lane_challenges: vec![pair(7), pair(9)],
          round_messages: vec![message(16), message(20)],
          alpha_challenges: vec![],
          ood_claims: vec![],
          intro_message: None,
          beta_challenge: 12,
        },
      ],
      final_yr_observations: vec![10, 11, 24, 25],
    }
  }

  #[test]
  fn validates_and_counts_a_small_ladder() {
    let trace = fixture();
    trace.validate(26, 13, &[64, 32], 8, 4).unwrap();
    let census = trace.census();
    assert_eq!(census.levels, 2);
    assert_eq!(census.queries, 3);
    assert_eq!(census.opened_values, 8);
    assert_eq!(census.path_digests, 4);
    assert_ne!(trace.topology_digest(), [0; 32]);
  }

  #[test]
  fn rejects_reused_private_value() {
    let mut trace = fixture();
    trace.levels[1].opened_rows[0][0] = 0;
    assert!(matches!(
      trace.validate(26, 13, &[64, 32], 8, 4),
      Err(F128InnerLigeritoTraceError::DuplicateIndex { .. })
    ));
  }
}
