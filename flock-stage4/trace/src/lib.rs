//! Backend-neutral trace schema at the Flock-to-Stage-4 boundary.
//!
//! The pinned Flock verifier produces this trace by running its real
//! recording challenger. The terminal circuit consumes it without importing
//! Flock's field, proof serialization, or circuit implementation.

mod f128;
mod jagged_fold;
mod ligerito;
mod matrix_fold;
mod merged_pcs;
mod multipoint;
mod statement;
mod structure_fold;
mod wiring;

pub use f128::{
  F128AlgebraCensusV1, F128AlgebraTraceError, F128AlgebraTraceV1,
  F128DeferredMatrixClaimV1, F128EqualityV1, F128InputSourceV1,
  F128MatrixSideV1, F128OperationV1, F128ReferenceV1, F128StaticMatrixIdV1,
  F128StructuredWeightV1, F128VerifierPhaseV1,
};
pub use jagged_fold::{
  F128JaggedAccumulatorCensusV1, F128JaggedAccumulatorTraceError,
  F128JaggedAccumulatorTraceV1, F128JaggedComboTermBindingV1,
  F128JaggedFoldClaimBindingV1, F128JaggedRowBindingV1,
};
pub use ligerito::{
  F128InnerLigeritoCensusV1, F128InnerLigeritoTraceError,
  F128InnerLigeritoTraceV1, F128LigeritoLevelV1, F128LigeritoOodClaimV1,
  F256IndexPairV1, F256LigeritoMessageV1,
};
pub use matrix_fold::{
  F128MatrixAccumulatorCensusV1, F128MatrixAccumulatorTraceError,
  F128MatrixAccumulatorTraceV1, F128MatrixFoldClaimBindingV1,
  F128MatrixFoldRoundV1, F128MatrixFoldTraceV1,
};
pub use merged_pcs::{
  F128_MERGED_PCS_BOOLEAN_CLAIMS, F128_RING_SWITCH_RANDOMIZERS,
  F128_RING_SWITCH_SKIP_WEIGHTS, F128_RING_SWITCH_SLICES,
  F128MergedPcsBooleanClaimV1, F128MergedPcsFrontendCensusV1,
  F128MergedPcsFrontendTraceV1, F128MergedPcsRoundV1, F128MergedPcsTraceError,
  F128RingSwitchTraceV1,
};
pub use multipoint::{
  F128_FAMILY_H_CORRECTIONS, F128_MULTIPOINT_DUAL_VALUES,
  F128_MULTIPOINT_JAGGED_CLAIMS, F128_MULTIPOINT_RING_SWITCH_CLAIMS,
  F128_MULTIPOINT_SCALAR_GROUPS, F128FamilyHConstantsV1, F128JaggedMatrixIdV1,
  F128MultipointRoundV1, F128MultipointTraceError,
  F128MultipointTwistedAssistCensusV1, F128MultipointTwistedAssistTraceV1,
};
pub use statement::{
  F128StatementBindingTraceError, F128StatementBindingTraceV1,
};
pub use structure_fold::{
  F128CircuitStructureAccumulatorCensusV1,
  F128CircuitStructureAccumulatorTraceError,
  F128CircuitStructureAccumulatorTraceV1,
};
pub use wiring::{
  F128_WIRING_PRIVATE_VALUES, F128CircuitStructureMatrixIdV1,
  F128WiringCensusV1, F128WiringTraceError, F128WiringTraceV1,
};

use std::fmt;

const TOPOLOGY_DIGEST_DOMAIN: &[u8] = b"ix:stage4:flock-transcript-topology:v1";
const POW_SQUEEZE_COUNTER_TAG: u64 = 0xf10c_5000_0000_0000;

/// Origin of one 16-byte word absorbed by a chained-BLAKE3 transcript.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StreamWordSourceV1 {
  Constant([u8; 16]),
  ObservedValue(u64),
  BytePayload { payload: u64, word: u64 },
}

/// Source of one compression row's 256-bit chaining value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ChainingValueSourceV1 {
  Iv,
  Row(u64),
  RowHigh(u64),
}

/// Structural links from one BLAKE3 compression to earlier rows.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CompressionLinkV1 {
  pub chaining_value: ChainingValueSourceV1,
  pub right: Option<u64>,
  pub repeats: Option<u64>,
}

/// Concrete witness for one BLAKE3 compression plus its structural wiring.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CompressionRowV1 {
  pub chaining_value: [u32; 8],
  pub message: [u32; 16],
  pub counter: u64,
  pub block_length: u32,
  pub flags: u32,
  pub link: CompressionLinkV1,
  pub stream_offset: Option<u64>,
  pub stream_word_count: u8,
}

/// One 128-bit word selected from a compression's 512-bit output.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CompressionOutputWordV1 {
  pub row: u64,
  pub word: u8,
}

/// One independent chained-BLAKE3 transcript.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChainedBlake3ChainV1 {
  pub stream_words: Vec<StreamWordSourceV1>,
  pub finalize_after: Vec<u64>,
  pub compression_rows: Vec<CompressionRowV1>,
  pub squeeze_words: Vec<Vec<CompressionOutputWordV1>>,
}

/// A forked child transcript and the exact links to its parent.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChainedBlake3ChildV1 {
  pub label: Vec<u8>,
  pub chain: ChainedBlake3ChainV1,
  pub parent_seed_squeeze: u64,
  pub child_seed_word: u64,
  pub child_digest_squeeze: u64,
  pub parent_digest_word: u64,
}

/// Location of one recorded F128 challenge in a chain's squeeze outputs.
///
/// Chain zero is the parent; chain `n + 1` is child `n`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ChainedBlake3ChallengeSourceV1 {
  pub chain: u64,
  pub squeeze: u64,
  pub squeeze_word: u64,
}

/// Fused proof-of-work predicate reserved in one compression output.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ChainedBlake3PowConstraintV1 {
  pub chain: u64,
  pub row: u64,
  pub bits: u32,
}

/// Complete parent/child topology generated from a Flock transcript tape.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChainedBlake3TranscriptV1 {
  pub domain: Vec<u8>,
  pub parent: ChainedBlake3ChainV1,
  pub children: Vec<ChainedBlake3ChildV1>,
  pub challenge_sources: Vec<ChainedBlake3ChallengeSourceV1>,
  pub pow_constraints: Vec<ChainedBlake3PowConstraintV1>,
}

/// Deterministic trace-size report.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ChainedBlake3CensusV1 {
  pub chains: u64,
  pub stream_words: u64,
  pub compression_rows: u64,
  pub squeezes: u64,
  pub squeeze_words: u64,
  pub challenges: u64,
  pub pow_constraints: u64,
}

impl ChainedBlake3TranscriptV1 {
  /// Validate topology and all indices into the external witness tables.
  pub fn validate(
    &self,
    observed_values: usize,
    payload_lengths: &[usize],
  ) -> Result<(), TraceValidationError> {
    validate_chain(&self.parent, "parent", observed_values, payload_lengths)?;
    for (child_index, child) in self.children.iter().enumerate() {
      let name = format!("child {child_index}");
      validate_chain(&child.chain, &name, observed_values, payload_lengths)?;
      validate_cross_links(&self.parent, child, child_index)?;
    }
    for (challenge_index, source) in self.challenge_sources.iter().enumerate() {
      let chain = self.chain(source.chain).ok_or_else(|| {
        TraceValidationError::new(format!(
          "challenge {challenge_index} references missing chain {}",
          source.chain,
        ))
      })?;
      let squeeze = to_usize(source.squeeze, "challenge", "squeeze index")?;
      let squeeze_word =
        to_usize(source.squeeze_word, "challenge", "squeeze word")?;
      if chain
        .squeeze_words
        .get(squeeze)
        .and_then(|words| words.get(squeeze_word))
        .is_none()
      {
        return Err(TraceValidationError::new(format!(
          "challenge {challenge_index} has an invalid squeeze source",
        )));
      }
    }
    for (pow_index, pow) in self.pow_constraints.iter().enumerate() {
      if pow.bits > 128 {
        return Err(TraceValidationError::new(format!(
          "PoW {pow_index} exceeds the 128-bit fused predicate",
        )));
      }
      let chain = self.chain(pow.chain).ok_or_else(|| {
        TraceValidationError::new(format!(
          "PoW {pow_index} references missing chain {}",
          pow.chain,
        ))
      })?;
      let row = to_usize(pow.row, "PoW", "row")?;
      let Some(compression) = chain.compression_rows.get(row) else {
        return Err(TraceValidationError::new(format!(
          "PoW {pow_index} references missing row {row}",
        )));
      };
      let message_length = u64::from(compression.stream_word_count) * 16;
      let expected_counter =
        POW_SQUEEZE_COUNTER_TAG | (message_length << 32) | u64::from(pow.bits);
      if compression.counter != expected_counter
        || compression.block_length != 64
        || compression.flags != 1 << 7
        || compression.stream_offset.is_none()
        || compression.stream_word_count == 0
      {
        return Err(TraceValidationError::new(format!(
          "PoW {pow_index} does not name a canonical fused squeeze row",
        )));
      }
    }
    Ok(())
  }

  /// Content address of the value-independent transcript topology.
  #[must_use]
  pub fn topology_digest(&self) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(TOPOLOGY_DIGEST_DOMAIN);
    hash_bytes(&mut hasher, &self.domain);
    hash_chain(&mut hasher, &self.parent);
    hash_u64(&mut hasher, self.children.len());
    for child in &self.children {
      hash_bytes(&mut hasher, &child.label);
      hash_u64(&mut hasher, child.parent_seed_squeeze);
      hash_u64(&mut hasher, child.child_seed_word);
      hash_u64(&mut hasher, child.child_digest_squeeze);
      hash_u64(&mut hasher, child.parent_digest_word);
      hash_chain(&mut hasher, &child.chain);
    }
    hash_u64(&mut hasher, self.challenge_sources.len());
    for source in &self.challenge_sources {
      hash_u64(&mut hasher, source.chain);
      hash_u64(&mut hasher, source.squeeze);
      hash_u64(&mut hasher, source.squeeze_word);
    }
    hash_u64(&mut hasher, self.pow_constraints.len());
    for pow in &self.pow_constraints {
      hash_u64(&mut hasher, pow.chain);
      hash_u64(&mut hasher, pow.row);
      hasher.update(&pow.bits.to_le_bytes());
    }
    *hasher.finalize().as_bytes()
  }

  #[must_use]
  pub fn census(&self) -> ChainedBlake3CensusV1 {
    let mut census = ChainedBlake3CensusV1::default();
    add_chain_census(&mut census, &self.parent);
    for child in &self.children {
      add_chain_census(&mut census, &child.chain);
    }
    census.challenges = u64::try_from(self.challenge_sources.len())
      .expect("challenge count fits u64");
    census.pow_constraints =
      u64::try_from(self.pow_constraints.len()).expect("PoW count fits u64");
    census
  }

  fn chain(&self, chain: u64) -> Option<&ChainedBlake3ChainV1> {
    if chain == 0 {
      Some(&self.parent)
    } else {
      usize::try_from(chain - 1)
        .ok()
        .and_then(|index| self.children.get(index))
        .map(|child| &child.chain)
    }
  }
}

/// Structural error in an exported transcript trace.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TraceValidationError {
  message: String,
}

impl TraceValidationError {
  fn new(message: impl Into<String>) -> Self {
    Self { message: message.into() }
  }
}

impl fmt::Display for TraceValidationError {
  fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
    formatter.write_str(&self.message)
  }
}

impl std::error::Error for TraceValidationError {}

fn validate_chain(
  chain: &ChainedBlake3ChainV1,
  name: &str,
  observed_values: usize,
  payload_lengths: &[usize],
) -> Result<(), TraceValidationError> {
  for (word_index, source) in chain.stream_words.iter().enumerate() {
    match *source {
      StreamWordSourceV1::Constant(_) => {},
      StreamWordSourceV1::ObservedValue(index) => {
        let index = usize::try_from(index).map_err(|_| {
          TraceValidationError::new(format!(
            "{name} stream word {word_index} has an oversized value index",
          ))
        })?;
        if index >= observed_values {
          return Err(TraceValidationError::new(format!(
            "{name} stream word {word_index} references value {index}, but only {observed_values} exist",
          )));
        }
      },
      StreamWordSourceV1::BytePayload { payload, word } => {
        let payload = usize::try_from(payload).map_err(|_| {
          TraceValidationError::new(format!(
            "{name} stream word {word_index} has an oversized payload index",
          ))
        })?;
        let word = usize::try_from(word).map_err(|_| {
          TraceValidationError::new(format!(
            "{name} stream word {word_index} has an oversized payload word",
          ))
        })?;
        let Some(&length) = payload_lengths.get(payload) else {
          return Err(TraceValidationError::new(format!(
            "{name} stream word {word_index} references missing payload {payload}",
          )));
        };
        if word >= length.div_ceil(16) {
          return Err(TraceValidationError::new(format!(
            "{name} stream word {word_index} references word {word} outside payload {payload}",
          )));
        }
      },
    }
  }

  if chain.finalize_after.len() != chain.squeeze_words.len() {
    return Err(TraceValidationError::new(format!(
      "{name} has {} finalize points but {} squeeze maps",
      chain.finalize_after.len(),
      chain.squeeze_words.len(),
    )));
  }
  let mut previous = 0usize;
  for (index, &position) in chain.finalize_after.iter().enumerate() {
    let position = to_usize(position, name, "finalize position")?;
    if position < previous || position > chain.stream_words.len() {
      return Err(TraceValidationError::new(format!(
        "{name} finalize {index} is outside the ordered stream",
      )));
    }
    previous = position;
  }

  for (row_index, row) in chain.compression_rows.iter().enumerate() {
    if row.block_length > 64 {
      return Err(TraceValidationError::new(format!(
        "{name} row {row_index} has block length {}",
        row.block_length,
      )));
    }
    if row.stream_word_count > 4 {
      return Err(TraceValidationError::new(format!(
        "{name} row {row_index} consumes more than four stream words",
      )));
    }
    validate_prior_source(row.link.chaining_value, row_index, name)?;
    validate_prior_optional(row.link.right, row_index, name, "right")?;
    validate_prior_optional(row.link.repeats, row_index, name, "repeat")?;
    match row.stream_offset {
      Some(offset) => {
        if offset % 16 != 0 {
          return Err(TraceValidationError::new(format!(
            "{name} row {row_index} has a non-word-aligned stream offset",
          )));
        }
        let start = to_usize(offset / 16, name, "stream offset")?;
        let end = start
          .checked_add(usize::from(row.stream_word_count))
          .ok_or_else(|| TraceValidationError::new("stream range overflow"))?;
        if end > chain.stream_words.len() {
          return Err(TraceValidationError::new(format!(
            "{name} row {row_index} reads beyond the stream",
          )));
        }
      },
      None if row.stream_word_count != 0 => {
        return Err(TraceValidationError::new(format!(
          "{name} row {row_index} has stream words without an offset",
        )));
      },
      None => {},
    }
  }

  for (squeeze_index, sources) in chain.squeeze_words.iter().enumerate() {
    if sources.is_empty() {
      return Err(TraceValidationError::new(format!(
        "{name} squeeze {squeeze_index} has no output words",
      )));
    }
    for source in sources {
      let row = to_usize(source.row, name, "squeeze row")?;
      if row >= chain.compression_rows.len() || source.word >= 4 {
        return Err(TraceValidationError::new(format!(
          "{name} squeeze {squeeze_index} has an invalid output source",
        )));
      }
    }
  }
  Ok(())
}

fn validate_cross_links(
  parent: &ChainedBlake3ChainV1,
  child: &ChainedBlake3ChildV1,
  child_index: usize,
) -> Result<(), TraceValidationError> {
  let seed =
    to_usize(child.parent_seed_squeeze, "child", "parent seed squeeze")?;
  let digest =
    to_usize(child.child_digest_squeeze, "child", "child digest squeeze")?;
  if parent.squeeze_words.get(seed).and_then(|words| words.first()).is_none()
    || parent
      .squeeze_words
      .get(seed + 1)
      .and_then(|words| words.first())
      .is_none()
  {
    return Err(TraceValidationError::new(format!(
      "child {child_index} has an invalid parent seed squeeze",
    )));
  }
  if child
    .chain
    .squeeze_words
    .get(digest)
    .and_then(|words| words.first())
    .is_none()
    || child
      .chain
      .squeeze_words
      .get(digest + 1)
      .and_then(|words| words.first())
      .is_none()
  {
    return Err(TraceValidationError::new(format!(
      "child {child_index} has an invalid digest squeeze",
    )));
  }
  let child_seed = to_usize(child.child_seed_word, "child", "seed word")?;
  if !has_two_observed_words(&child.chain, child_seed) {
    return Err(TraceValidationError::new(format!(
      "child {child_index} seed words are outside its stream",
    )));
  }
  let parent_digest =
    to_usize(child.parent_digest_word, "child", "parent digest word")?;
  if !has_two_observed_words(parent, parent_digest) {
    return Err(TraceValidationError::new(format!(
      "child {child_index} digest words are outside the parent stream",
    )));
  }
  Ok(())
}

fn has_two_observed_words(chain: &ChainedBlake3ChainV1, first: usize) -> bool {
  matches!(
    chain.stream_words.get(first),
    Some(StreamWordSourceV1::ObservedValue(_))
  ) && chain
    .stream_words
    .iter()
    .skip(first + 1)
    .any(|source| matches!(source, StreamWordSourceV1::ObservedValue(_)))
}

fn validate_prior_source(
  source: ChainingValueSourceV1,
  row: usize,
  name: &str,
) -> Result<(), TraceValidationError> {
  match source {
    ChainingValueSourceV1::Iv => Ok(()),
    ChainingValueSourceV1::Row(source)
    | ChainingValueSourceV1::RowHigh(source) => {
      validate_prior_optional(Some(source), row, name, "chaining-value")
    },
  }
}

fn validate_prior_optional(
  source: Option<u64>,
  row: usize,
  name: &str,
  kind: &str,
) -> Result<(), TraceValidationError> {
  if let Some(source) = source {
    let source = to_usize(source, name, kind)?;
    if source >= row {
      return Err(TraceValidationError::new(format!(
        "{name} row {row} has a non-prior {kind} link to row {source}",
      )));
    }
  }
  Ok(())
}

fn to_usize(
  value: u64,
  name: &str,
  kind: &str,
) -> Result<usize, TraceValidationError> {
  usize::try_from(value).map_err(|_| {
    TraceValidationError::new(format!("{name} has an oversized {kind}"))
  })
}

fn hash_chain(hasher: &mut blake3::Hasher, chain: &ChainedBlake3ChainV1) {
  hash_u64(hasher, chain.stream_words.len());
  for source in &chain.stream_words {
    match source {
      StreamWordSourceV1::Constant(value) => {
        hasher.update(&[0]);
        hasher.update(value);
      },
      StreamWordSourceV1::ObservedValue(index) => {
        hasher.update(&[1]);
        hash_u64(hasher, *index);
      },
      StreamWordSourceV1::BytePayload { payload, word } => {
        hasher.update(&[2]);
        hash_u64(hasher, *payload);
        hash_u64(hasher, *word);
      },
    }
  }
  hash_u64(hasher, chain.finalize_after.len());
  for &position in &chain.finalize_after {
    hash_u64(hasher, position);
  }
  hash_u64(hasher, chain.compression_rows.len());
  for row in &chain.compression_rows {
    hash_chaining_source(hasher, row.link.chaining_value);
    hash_option_u64(hasher, row.link.right);
    hash_option_u64(hasher, row.link.repeats);
    hash_option_u64(hasher, row.stream_offset);
    hasher.update(&[row.stream_word_count]);
    hash_u64(hasher, row.counter);
    hasher.update(&row.block_length.to_le_bytes());
    hasher.update(&row.flags.to_le_bytes());
  }
  hash_u64(hasher, chain.squeeze_words.len());
  for squeeze in &chain.squeeze_words {
    hash_u64(hasher, squeeze.len());
    for source in squeeze {
      hash_u64(hasher, source.row);
      hasher.update(&[source.word]);
    }
  }
}

fn hash_chaining_source(
  hasher: &mut blake3::Hasher,
  source: ChainingValueSourceV1,
) {
  match source {
    ChainingValueSourceV1::Iv => {
      hasher.update(&[0]);
    },
    ChainingValueSourceV1::Row(row) => {
      hasher.update(&[1]);
      hash_u64(hasher, row);
    },
    ChainingValueSourceV1::RowHigh(row) => {
      hasher.update(&[2]);
      hash_u64(hasher, row);
    },
  }
}

fn hash_option_u64(hasher: &mut blake3::Hasher, value: Option<u64>) {
  match value {
    Some(value) => {
      hasher.update(&[1]);
      hash_u64(hasher, value);
    },
    None => {
      hasher.update(&[0]);
    },
  }
}

fn hash_bytes(hasher: &mut blake3::Hasher, bytes: &[u8]) {
  hash_u64(hasher, bytes.len());
  hasher.update(bytes);
}

fn hash_u64(hasher: &mut blake3::Hasher, value: impl TryInto<u64>) {
  let value = value.try_into().ok().expect("trace length fits u64");
  hasher.update(&value.to_le_bytes());
}

fn add_chain_census(
  census: &mut ChainedBlake3CensusV1,
  chain: &ChainedBlake3ChainV1,
) {
  census.chains += 1;
  census.stream_words +=
    u64::try_from(chain.stream_words.len()).expect("stream length fits u64");
  census.compression_rows += u64::try_from(chain.compression_rows.len())
    .expect("compression count fits u64");
  census.squeezes +=
    u64::try_from(chain.squeeze_words.len()).expect("squeeze count fits u64");
  census.squeeze_words += chain
    .squeeze_words
    .iter()
    .map(|words| u64::try_from(words.len()).expect("word count fits u64"))
    .sum::<u64>();
}

#[cfg(test)]
mod tests {
  use super::*;

  fn one_row_chain() -> ChainedBlake3ChainV1 {
    ChainedBlake3ChainV1 {
      stream_words: vec![StreamWordSourceV1::ObservedValue(0)],
      finalize_after: vec![1],
      compression_rows: vec![CompressionRowV1 {
        chaining_value: [0; 8],
        message: [0; 16],
        counter: 0,
        block_length: 16,
        flags: 1 << 7,
        link: CompressionLinkV1 {
          chaining_value: ChainingValueSourceV1::Iv,
          right: None,
          repeats: None,
        },
        stream_offset: Some(0),
        stream_word_count: 1,
      }],
      squeeze_words: vec![vec![CompressionOutputWordV1 { row: 0, word: 0 }]],
    }
  }

  #[test]
  fn topology_digest_excludes_compression_witness_values() {
    let first = ChainedBlake3TranscriptV1 {
      domain: b"test".to_vec(),
      parent: one_row_chain(),
      children: Vec::new(),
      challenge_sources: vec![ChainedBlake3ChallengeSourceV1 {
        chain: 0,
        squeeze: 0,
        squeeze_word: 0,
      }],
      pow_constraints: Vec::new(),
    };
    let mut second = first.clone();
    second.parent.compression_rows[0].message[0] = 17;
    second.parent.compression_rows[0].chaining_value[0] = 19;
    assert_eq!(first.topology_digest(), second.topology_digest());
    first.validate(1, &[]).unwrap();
  }

  #[test]
  fn validation_rejects_forward_row_link() {
    let mut trace = ChainedBlake3TranscriptV1 {
      domain: b"test".to_vec(),
      parent: one_row_chain(),
      children: Vec::new(),
      challenge_sources: Vec::new(),
      pow_constraints: Vec::new(),
    };
    trace.parent.compression_rows[0].link.chaining_value =
      ChainingValueSourceV1::Row(0);
    assert!(trace.validate(1, &[]).is_err());
  }
}
