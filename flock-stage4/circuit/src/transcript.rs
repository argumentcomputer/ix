use crate::blake3::{
  BLAKE3_IV, Word32, alloc_word_prefix, constrain_compression,
};
use crate::{
  CanonicalR1csV1, F128VariablesV1, LinearCombination, R1csBuilder, R1csError,
  R1csProjectionV1, Witness,
};
use ix_stage4_trace::{
  ChainedBlake3ChainV1, ChainedBlake3ChildV1, ChainedBlake3TranscriptV1,
  ChainingValueSourceV1, StreamWordSourceV1,
};
use std::fmt;

const WORDS_PER_F128: usize = 4;
const BITS_PER_WORD: usize = 32;

type Word128 = [Word32; WORDS_PER_F128];

/// R1CS wires carrying one little-endian F128 transcript value.
pub type F128TranscriptVariablesV1 = F128VariablesV1;

/// One zero-padded 16-byte transcript payload word.
///
/// Unlike a squeezed F128 value, a short byte payload has constant padding
/// bits. Keeping linear expressions here avoids allocating dummy variables
/// merely to expose those already-constrained bytes to protocol consumers.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128TranscriptWordV1 {
  value: [u8; 16],
  bit_expressions: [LinearCombination; 128],
}

impl F128TranscriptWordV1 {
  pub const fn value(&self) -> &[u8; 16] {
    &self.value
  }

  pub fn bit_expressions(&self) -> &[LinearCombination; 128] {
    &self.bit_expressions
  }

  pub fn from_f128_variables(value: &F128VariablesV1) -> Self {
    Self {
      value: *value.value(),
      bit_expressions: value
        .bit_variables()
        .map(LinearCombination::from_variable),
    }
  }
}

/// Wires exposed by the compiled chained-BLAKE3 transcript.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChainedBlake3CircuitOutputV1 {
  pub topology_digest: [u8; 32],
  pub observed_values: Vec<F128TranscriptVariablesV1>,
  /// Zero-padded 16-byte words for every `observe_bytes` payload.
  ///
  /// Consumers use these wires to bind protocol metadata (for example the
  /// matrix registry digest) to the same bytes absorbed by the transcript.
  pub byte_payloads: Vec<Vec<F128TranscriptWordV1>>,
  pub challenges: Vec<F128TranscriptVariablesV1>,
}

/// Failure while lowering an exported transcript into canonical R1CS.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TranscriptCircuitError {
  InvalidTrace(String),
  R1cs(R1csError),
  MissingIndex(&'static str),
  UnsupportedTopology(&'static str),
  CompressionWitnessMismatch { chain: usize, row: usize },
  ChallengeCount { expected: usize, actual: usize },
  ChallengeMismatch { challenge: usize },
}

impl fmt::Display for TranscriptCircuitError {
  fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::InvalidTrace(error) => {
        write!(formatter, "invalid transcript trace: {error}")
      },
      Self::R1cs(error) => write!(formatter, "transcript R1CS: {error}"),
      Self::MissingIndex(kind) => {
        write!(formatter, "missing transcript {kind}")
      },
      Self::UnsupportedTopology(kind) => {
        write!(formatter, "unsupported transcript topology: {kind}")
      },
      Self::CompressionWitnessMismatch { chain, row } => write!(
        formatter,
        "compression witness mismatch in chain {chain}, row {row}",
      ),
      Self::ChallengeCount { expected, actual } => write!(
        formatter,
        "transcript has {actual} challenges; expected {expected}",
      ),
      Self::ChallengeMismatch { challenge } => {
        write!(formatter, "transcript challenge {challenge} is inconsistent")
      },
    }
  }
}

impl std::error::Error for TranscriptCircuitError {}

impl From<R1csError> for TranscriptCircuitError {
  fn from(error: R1csError) -> Self {
    Self::R1cs(error)
  }
}

/// Compile one exported Flock transcript into a standalone canonical R1CS.
pub fn build_chained_blake3_transcript_r1cs(
  trace: &ChainedBlake3TranscriptV1,
  observed_values: &[[u8; 16]],
  byte_payloads: &[Vec<u8>],
  challenges: &[[u8; 16]],
) -> Result<
  (CanonicalR1csV1, Witness, ChainedBlake3CircuitOutputV1),
  TranscriptCircuitError,
> {
  let mut builder = R1csBuilder::new();
  let output = constrain_chained_blake3_transcript(
    &mut builder,
    trace,
    observed_values,
    byte_payloads,
    challenges,
  )?;
  let (r1cs, witness) = builder.finish()?;
  Ok((r1cs, witness, output))
}

/// Stream the expanded transcript relation into an exact digest and census
/// without retaining matrices or a full assignment.
pub fn project_chained_blake3_transcript_r1cs(
  trace: &ChainedBlake3TranscriptV1,
  observed_values: &[[u8; 16]],
  byte_payloads: &[Vec<u8>],
  challenges: &[[u8; 16]],
) -> Result<R1csProjectionV1, TranscriptCircuitError> {
  let mut builder = R1csBuilder::new_projection();
  constrain_chained_blake3_transcript(
    &mut builder,
    trace,
    observed_values,
    byte_payloads,
    challenges,
  )?;
  Ok(builder.finish_projection()?)
}

/// Add one exported Flock transcript to an existing Stage 4 relation.
pub fn constrain_chained_blake3_transcript(
  builder: &mut R1csBuilder,
  trace: &ChainedBlake3TranscriptV1,
  observed_values: &[[u8; 16]],
  byte_payloads: &[Vec<u8>],
  challenges: &[[u8; 16]],
) -> Result<ChainedBlake3CircuitOutputV1, TranscriptCircuitError> {
  let payload_lengths = byte_payloads.iter().map(Vec::len).collect::<Vec<_>>();
  trace
    .validate(observed_values.len(), &payload_lengths)
    .map_err(|error| TranscriptCircuitError::InvalidTrace(error.to_string()))?;
  if challenges.len() != trace.challenge_sources.len() {
    return Err(TranscriptCircuitError::ChallengeCount {
      expected: trace.challenge_sources.len(),
      actual: challenges.len(),
    });
  }

  let tables =
    WitnessTables::allocate(builder, observed_values, byte_payloads)?;
  let parent = compile_chain(builder, &trace.parent, &tables, 0)?;
  let children = trace
    .children
    .iter()
    .enumerate()
    .map(|(index, child)| {
      compile_chain(builder, &child.chain, &tables, index + 1)
    })
    .collect::<Result<Vec<_>, _>>()?;

  for (index, child) in trace.children.iter().enumerate() {
    enforce_child_links(
      builder,
      &trace.parent,
      &parent,
      child,
      &children[index],
    )?;
  }
  enforce_pow_constraints(builder, trace, &parent, &children)?;

  let challenge_words = trace
    .challenge_sources
    .iter()
    .map(|source| {
      let chain = compiled_chain(source.chain, &parent, &children)?;
      let squeeze = to_usize(source.squeeze, "challenge squeeze")?;
      let word = to_usize(source.squeeze_word, "challenge squeeze word")?;
      chain
        .squeeze_words
        .get(squeeze)
        .and_then(|words| words.get(word))
        .cloned()
        .ok_or(TranscriptCircuitError::MissingIndex("challenge source"))
    })
    .collect::<Result<Vec<_>, _>>()?;
  for (index, (word, expected)) in
    challenge_words.iter().zip(challenges).enumerate()
  {
    if word128_bytes(word) != *expected {
      return Err(TranscriptCircuitError::ChallengeMismatch {
        challenge: index,
      });
    }
  }

  Ok(ChainedBlake3CircuitOutputV1 {
    topology_digest: trace.topology_digest(),
    observed_values: tables
      .observed_values
      .iter()
      .map(export_f128_variables)
      .collect(),
    byte_payloads: tables
      .byte_payloads
      .iter()
      .map(|payload| payload.iter().map(export_transcript_word).collect())
      .collect(),
    challenges: challenge_words.iter().map(export_f128_variables).collect(),
  })
}

struct WitnessTables {
  observed_values: Vec<Word128>,
  byte_payloads: Vec<Vec<Word128>>,
}

impl WitnessTables {
  fn allocate(
    builder: &mut R1csBuilder,
    observed_values: &[[u8; 16]],
    byte_payloads: &[Vec<u8>],
  ) -> Result<Self, R1csError> {
    let observed_values = observed_values
      .iter()
      .map(|value| alloc_word128_prefix(builder, value))
      .collect::<Result<Vec<_>, _>>()?;
    let byte_payloads = byte_payloads
      .iter()
      .map(|payload| {
        payload
          .chunks(16)
          .map(|word| alloc_word128_prefix(builder, word))
          .collect::<Result<Vec<_>, _>>()
      })
      .collect::<Result<Vec<_>, _>>()?;
    Ok(Self { observed_values, byte_payloads })
  }

  fn resolve(
    &self,
    source: StreamWordSourceV1,
  ) -> Result<Word128, TranscriptCircuitError> {
    match source {
      StreamWordSourceV1::Constant(value) => Ok(constant_word128(&value)),
      StreamWordSourceV1::ObservedValue(index) => self
        .observed_values
        .get(to_usize(index, "observed value")?)
        .cloned()
        .ok_or(TranscriptCircuitError::MissingIndex("observed value")),
      StreamWordSourceV1::BytePayload { payload, word } => self
        .byte_payloads
        .get(to_usize(payload, "byte payload")?)
        .and_then(|payload| {
          to_usize(word, "payload word").ok().and_then(|word| payload.get(word))
        })
        .cloned()
        .ok_or(TranscriptCircuitError::MissingIndex("payload word")),
    }
  }
}

struct CompiledChain {
  stream_words: Vec<Word128>,
  outputs: Vec<[Word32; 16]>,
  squeeze_words: Vec<Vec<Word128>>,
}

fn compile_chain(
  builder: &mut R1csBuilder,
  chain: &ChainedBlake3ChainV1,
  tables: &WitnessTables,
  chain_index: usize,
) -> Result<CompiledChain, TranscriptCircuitError> {
  let stream_words = chain
    .stream_words
    .iter()
    .copied()
    .map(|source| tables.resolve(source))
    .collect::<Result<Vec<_>, _>>()?;
  let mut outputs = Vec::with_capacity(chain.compression_rows.len());
  for (row_index, row) in chain.compression_rows.iter().enumerate() {
    if row.link.right.is_some() || row.link.repeats.is_some() {
      return Err(TranscriptCircuitError::UnsupportedTopology(
        "tree-BLAKE3 row in chained transcript",
      ));
    }
    let chaining_value: [Word32; 8] = match row.link.chaining_value {
      ChainingValueSourceV1::Iv => BLAKE3_IV.map(Word32::constant),
      ChainingValueSourceV1::Row(source) => {
        output_half(&outputs, source, false)?
      },
      ChainingValueSourceV1::RowHigh(source) => {
        output_half(&outputs, source, true)?
      },
    };
    let mut message = core::array::from_fn(|_| Word32::constant(0));
    if let Some(offset) = row.stream_offset {
      let start = to_usize(offset / 16, "compression stream offset")?;
      for word in 0..usize::from(row.stream_word_count) {
        let source = stream_words.get(start + word).ok_or(
          TranscriptCircuitError::MissingIndex("compression stream word"),
        )?;
        for limb in 0..WORDS_PER_F128 {
          message[word * WORDS_PER_F128 + limb] = source[limb].clone();
        }
      }
    }
    if chaining_value.each_ref().map(|word| word.value) != row.chaining_value
      || message.each_ref().map(|word| word.value) != row.message
    {
      return Err(TranscriptCircuitError::CompressionWitnessMismatch {
        chain: chain_index,
        row: row_index,
      });
    }
    outputs.push(constrain_compression(
      builder,
      chaining_value,
      message,
      row.counter,
      row.block_length,
      row.flags,
    )?);
  }
  let squeeze_words = chain
    .squeeze_words
    .iter()
    .map(|sources| {
      sources
        .iter()
        .map(|source| output_word(&outputs, source.row, source.word))
        .collect::<Result<Vec<_>, _>>()
    })
    .collect::<Result<Vec<_>, _>>()?;
  Ok(CompiledChain { stream_words, outputs, squeeze_words })
}

fn output_half(
  outputs: &[[Word32; 16]],
  row: u64,
  high: bool,
) -> Result<[Word32; 8], TranscriptCircuitError> {
  let row = outputs
    .get(to_usize(row, "chaining-value row")?)
    .ok_or(TranscriptCircuitError::MissingIndex("chaining-value row"))?;
  let start = usize::from(high) * 8;
  row[start..start + 8]
    .to_vec()
    .try_into()
    .map_err(|_| TranscriptCircuitError::MissingIndex("chaining-value half"))
}

fn output_word(
  outputs: &[[Word32; 16]],
  row: u64,
  word: u8,
) -> Result<Word128, TranscriptCircuitError> {
  let row = outputs
    .get(to_usize(row, "output row")?)
    .ok_or(TranscriptCircuitError::MissingIndex("output row"))?;
  let start = usize::from(word) * WORDS_PER_F128;
  row
    .get(start..start + WORDS_PER_F128)
    .ok_or(TranscriptCircuitError::MissingIndex("output word"))?
    .to_vec()
    .try_into()
    .map_err(|_| TranscriptCircuitError::MissingIndex("output word"))
}

fn enforce_child_links(
  builder: &mut R1csBuilder,
  parent_schema: &ChainedBlake3ChainV1,
  parent: &CompiledChain,
  child_schema: &ChainedBlake3ChildV1,
  child: &CompiledChain,
) -> Result<(), TranscriptCircuitError> {
  let seed = to_usize(child_schema.parent_seed_squeeze, "parent seed squeeze")?;
  let digest =
    to_usize(child_schema.child_digest_squeeze, "child digest squeeze")?;
  let child_seed =
    observed_pair(&child_schema.chain, child, child_schema.child_seed_word)?;
  let parent_digest =
    observed_pair(parent_schema, parent, child_schema.parent_digest_word)?;
  enforce_word128_equal(builder, squeeze_first(parent, seed)?, &child_seed[0]);
  enforce_word128_equal(
    builder,
    squeeze_first(parent, seed + 1)?,
    &child_seed[1],
  );
  enforce_word128_equal(
    builder,
    squeeze_first(child, digest)?,
    &parent_digest[0],
  );
  enforce_word128_equal(
    builder,
    squeeze_first(child, digest + 1)?,
    &parent_digest[1],
  );
  Ok(())
}

fn observed_pair(
  schema: &ChainedBlake3ChainV1,
  compiled: &CompiledChain,
  first: u64,
) -> Result<[Word128; 2], TranscriptCircuitError> {
  let first = to_usize(first, "cross-link stream word")?;
  if !matches!(
    schema.stream_words.get(first),
    Some(StreamWordSourceV1::ObservedValue(_))
  ) {
    return Err(TranscriptCircuitError::MissingIndex("first cross-link value"));
  }
  let second = schema
    .stream_words
    .iter()
    .enumerate()
    .skip(first + 1)
    .find_map(|(index, source)| {
      matches!(source, StreamWordSourceV1::ObservedValue(_)).then_some(index)
    })
    .ok_or(TranscriptCircuitError::MissingIndex("second cross-link value"))?;
  Ok([
    compiled.stream_words[first].clone(),
    compiled.stream_words[second].clone(),
  ])
}

fn squeeze_first(
  chain: &CompiledChain,
  squeeze: usize,
) -> Result<&Word128, TranscriptCircuitError> {
  chain
    .squeeze_words
    .get(squeeze)
    .and_then(|words| words.first())
    .ok_or(TranscriptCircuitError::MissingIndex("cross-link squeeze"))
}

fn enforce_word128_equal(
  builder: &mut R1csBuilder,
  left: &Word128,
  right: &Word128,
) {
  for (left, right) in left.iter().zip(right) {
    left.enforce_equal(builder, right);
  }
}

fn enforce_pow_constraints(
  builder: &mut R1csBuilder,
  trace: &ChainedBlake3TranscriptV1,
  parent: &CompiledChain,
  children: &[CompiledChain],
) -> Result<(), TranscriptCircuitError> {
  for pow in &trace.pow_constraints {
    let chain = compiled_chain(pow.chain, parent, children)?;
    let row_index = to_usize(pow.row, "PoW row")?;
    let output = chain
      .outputs
      .get(row_index)
      .ok_or(TranscriptCircuitError::MissingIndex("PoW row"))?;
    if pow.bits == 0 {
      let row = trace_chain(pow.chain, trace)?
        .compression_rows
        .get(row_index)
        .ok_or(TranscriptCircuitError::MissingIndex("PoW trace row"))?;
      let start = to_usize(
        row
          .stream_offset
          .ok_or(TranscriptCircuitError::MissingIndex("PoW stream offset"))?
          / 16,
        "PoW stream offset",
      )?;
      let nonce = chain
        .stream_words
        .get(start + usize::from(row.stream_word_count) - 1)
        .ok_or(TranscriptCircuitError::MissingIndex("PoW nonce"))?;
      for word in &nonce[..2] {
        for bit in 0..BITS_PER_WORD {
          word.enforce_bit_zero(builder, bit);
        }
      }
      continue;
    }
    let predicate = &output[4..8];
    let full_bytes = usize::try_from(pow.bits / 8)
      .map_err(|_| TranscriptCircuitError::MissingIndex("PoW bit count"))?;
    let extra = usize::try_from(pow.bits % 8)
      .map_err(|_| TranscriptCircuitError::MissingIndex("PoW bit count"))?;
    for byte in 0..full_bytes {
      enforce_predicate_byte(builder, predicate, byte, 0);
    }
    if extra != 0 {
      enforce_predicate_byte(builder, predicate, full_bytes, 8 - extra);
    }
  }
  Ok(())
}

fn enforce_predicate_byte(
  builder: &mut R1csBuilder,
  predicate: &[Word32],
  byte: usize,
  first_bit: usize,
) {
  let word = byte / 4;
  let bit_base = (byte % 4) * 8;
  for bit in first_bit..8 {
    predicate[word].enforce_bit_zero(builder, bit_base + bit);
  }
}

fn compiled_chain<'a>(
  chain: u64,
  parent: &'a CompiledChain,
  children: &'a [CompiledChain],
) -> Result<&'a CompiledChain, TranscriptCircuitError> {
  if chain == 0 {
    Ok(parent)
  } else {
    children
      .get(to_usize(chain - 1, "child chain")?)
      .ok_or(TranscriptCircuitError::MissingIndex("child chain"))
  }
}

fn trace_chain(
  chain: u64,
  trace: &ChainedBlake3TranscriptV1,
) -> Result<&ChainedBlake3ChainV1, TranscriptCircuitError> {
  if chain == 0 {
    Ok(&trace.parent)
  } else {
    trace
      .children
      .get(to_usize(chain - 1, "child trace")?)
      .map(|child| &child.chain)
      .ok_or(TranscriptCircuitError::MissingIndex("child trace"))
  }
}

fn alloc_word128_prefix(
  builder: &mut R1csBuilder,
  bytes: &[u8],
) -> Result<Word128, R1csError> {
  if bytes.len() > 16 {
    return Err(R1csError::InternalShape);
  }
  (0..WORDS_PER_F128)
    .map(|word| {
      let start = word * 4;
      let length = bytes.len().saturating_sub(start).min(4);
      let mut encoded = [0_u8; 4];
      if length != 0 {
        encoded[..length].copy_from_slice(&bytes[start..start + length]);
      }
      alloc_word_prefix(builder, u32::from_le_bytes(encoded), length * 8)
    })
    .collect::<Result<Vec<_>, _>>()?
    .try_into()
    .map_err(|_| R1csError::InternalShape)
}

fn constant_word128(bytes: &[u8; 16]) -> Word128 {
  core::array::from_fn(|word| {
    Word32::constant(u32::from_le_bytes(
      bytes[4 * word..4 * word + 4].try_into().expect("four-byte word"),
    ))
  })
}

fn word128_bytes(word: &Word128) -> [u8; 16] {
  let mut bytes = [0_u8; 16];
  for (index, limb) in word.iter().enumerate() {
    bytes[4 * index..4 * index + 4].copy_from_slice(&limb.value.to_le_bytes());
  }
  bytes
}

fn export_f128_variables(word: &Word128) -> F128TranscriptVariablesV1 {
  let words = word.each_ref().map(Word32::variables);
  let bit_variables =
    core::array::from_fn(|bit| words[bit / BITS_PER_WORD][bit % BITS_PER_WORD]);
  F128VariablesV1::from_constrained_bits(word128_bytes(word), bit_variables)
}

fn export_transcript_word(word: &Word128) -> F128TranscriptWordV1 {
  let words = word.each_ref().map(Word32::expressions);
  let bit_expressions = core::array::from_fn(|bit| {
    words[bit / BITS_PER_WORD][bit % BITS_PER_WORD].clone()
  });
  F128TranscriptWordV1 { value: word128_bytes(word), bit_expressions }
}

fn to_usize(
  value: u64,
  kind: &'static str,
) -> Result<usize, TranscriptCircuitError> {
  usize::try_from(value).map_err(|_| TranscriptCircuitError::MissingIndex(kind))
}

#[cfg(test)]
mod tests {
  use super::*;
  use ix_stage4_trace::{
    ChainedBlake3ChallengeSourceV1, CompressionLinkV1, CompressionOutputWordV1,
    CompressionRowV1,
  };

  const CHUNK_START: u32 = 1 << 0;
  const CHUNK_END: u32 = 1 << 1;
  const ROOT: u32 = 1 << 3;

  fn one_block_fixture(
    message: [u8; 16],
  ) -> (ChainedBlake3TranscriptV1, Vec<Vec<u8>>, Vec<[u8; 16]>) {
    let words: [u32; 4] = core::array::from_fn(|index| {
      u32::from_le_bytes(
        message[4 * index..4 * index + 4].try_into().expect("four-byte word"),
      )
    });
    let mut block = [0_u32; 16];
    block[..4].copy_from_slice(&words);
    let digest = blake3::hash(&message);
    let challenge = digest.as_bytes()[..16].try_into().unwrap();
    (
      ChainedBlake3TranscriptV1 {
        domain: b"unit-test".to_vec(),
        parent: ChainedBlake3ChainV1 {
          stream_words: vec![StreamWordSourceV1::BytePayload {
            payload: 0,
            word: 0,
          }],
          finalize_after: vec![1],
          compression_rows: vec![CompressionRowV1 {
            chaining_value: BLAKE3_IV,
            message: block,
            counter: 0,
            block_length: 16,
            flags: CHUNK_START | CHUNK_END | ROOT,
            link: CompressionLinkV1 {
              chaining_value: ChainingValueSourceV1::Iv,
              right: None,
              repeats: None,
            },
            stream_offset: Some(0),
            stream_word_count: 1,
          }],
          squeeze_words: vec![vec![CompressionOutputWordV1 {
            row: 0,
            word: 0,
          }]],
        },
        children: Vec::new(),
        challenge_sources: vec![ChainedBlake3ChallengeSourceV1 {
          chain: 0,
          squeeze: 0,
          squeeze_word: 0,
        }],
        pow_constraints: Vec::new(),
      },
      vec![message.to_vec()],
      vec![challenge],
    )
  }

  #[test]
  fn one_block_trace_compiles_and_matches_challenge() {
    let (trace, payloads, challenges) = one_block_fixture(*b"0123456789abcdef");
    let (r1cs, witness, output) =
      build_chained_blake3_transcript_r1cs(&trace, &[], &payloads, &challenges)
        .unwrap();
    r1cs.check(&witness).unwrap();
    assert_eq!(output.challenges[0].value(), &challenges[0]);
    assert_eq!(output.byte_payloads[0][0].value(), &payloads[0][..16]);
    assert_eq!(output.topology_digest, trace.topology_digest());
    let projected = project_chained_blake3_transcript_r1cs(
      &trace,
      &[],
      &payloads,
      &challenges,
    )
    .unwrap();
    assert_eq!(projected.census(), &r1cs.census());
  }

  #[test]
  fn trace_circuit_shape_is_value_independent() {
    let (first_trace, first_payloads, first_challenges) =
      one_block_fixture(*b"0123456789abcdef");
    let (second_trace, second_payloads, second_challenges) =
      one_block_fixture(*b"fedcba9876543210");
    assert_eq!(first_trace.topology_digest(), second_trace.topology_digest());
    let (first, _, _) = build_chained_blake3_transcript_r1cs(
      &first_trace,
      &[],
      &first_payloads,
      &first_challenges,
    )
    .unwrap();
    let (second, _, _) = build_chained_blake3_transcript_r1cs(
      &second_trace,
      &[],
      &second_payloads,
      &second_challenges,
    )
    .unwrap();
    assert_eq!(first.digest(), second.digest());
  }

  #[test]
  fn mismatched_compression_witness_is_rejected_before_r1cs() {
    let (mut trace, payloads, challenges) =
      one_block_fixture(*b"0123456789abcdef");
    trace.parent.compression_rows[0].message[0] ^= 1;
    assert!(matches!(
      build_chained_blake3_transcript_r1cs(&trace, &[], &payloads, &challenges,),
      Err(TranscriptCircuitError::CompressionWitnessMismatch { .. })
    ));
  }
}
