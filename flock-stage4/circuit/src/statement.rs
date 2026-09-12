use crate::blake3::{
  BLAKE3_IV, Word32, alloc_word_in_phase, constrain_compression_in_phase,
};
use crate::f128::alloc_f128_private;
use crate::public_inputs::{
  Stage4PublicInputVariablesV1, constrain_stage4_public_input_expressions,
};
use crate::{
  ConstraintPhase, F128TranscriptWordV1, F128VariablesV1, LinearCombination,
  R1csBuilder, R1csError,
};
use ark_bls12_381::Fr;
use ix_stage4_trace::F128StatementBindingTraceV1;
use std::fmt;

pub const STAGE4_STAGE3_STATEMENT_BYTES: usize = 104;
const WORD_BYTES: usize = 4;
const BLOCK_BYTES: usize = 64;
const BLOCK_WORDS: usize = BLOCK_BYTES / WORD_BYTES;
const PUBLIC_CHUNK_BYTES: usize = 1024;
const PUBLIC_CHUNK_F128: usize = PUBLIC_CHUNK_BYTES / 16;
const CHUNK_START: u32 = 1 << 0;
const CHUNK_END: u32 = 1 << 1;
const PARENT: u32 = 1 << 2;
const ROOT: u32 = 1 << 3;

/// Private values connected to Flock's statement transcript and the two
/// terminal public digest limbs.
#[derive(Clone, Copy)]
pub struct F128StatementCircuitInputsV1<'a> {
  pub stage3_statement: &'a [u8; STAGE4_STAGE3_STATEMENT_BYTES],
  pub public_values: &'a [[u8; 16]],
  pub byte_payloads: &'a [Vec<F128TranscriptWordV1>],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct F128StatementCircuitOutputV1 {
  pub topology_digest: [u8; 32],
  /// Constrained Flock public words, retained for the wiring verifier.
  pub public_values: Vec<F128VariablesV1>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum F128StatementCircuitError {
  InvalidTrace(String),
  R1cs(R1csError),
  MissingPayload(&'static str),
  PayloadShape { kind: &'static str, expected: usize, actual: usize },
  PayloadMismatch(&'static str),
  StatementConstantMismatch(&'static str),
  Stage2PublicValueMismatch(usize),
  InternalShape(&'static str),
}

impl fmt::Display for F128StatementCircuitError {
  fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::InvalidTrace(error) => {
        write!(formatter, "invalid statement-binding trace: {error}")
      },
      Self::R1cs(error) => write!(formatter, "statement-binding R1CS: {error}"),
      Self::MissingPayload(kind) => {
        write!(formatter, "missing statement {kind} payload")
      },
      Self::PayloadShape { kind, expected, actual } => write!(
        formatter,
        "statement {kind} payload has {actual} words; expected {expected}",
      ),
      Self::PayloadMismatch(kind) => {
        write!(formatter, "statement {kind} payload is inconsistent")
      },
      Self::StatementConstantMismatch(kind) => {
        write!(formatter, "Stage 3 statement {kind} is inconsistent")
      },
      Self::Stage2PublicValueMismatch(position) => write!(
        formatter,
        "Stage 2 digest half {position} disagrees with the Flock public vector",
      ),
      Self::InternalShape(kind) => {
        write!(formatter, "malformed statement circuit {kind}")
      },
    }
  }
}

impl std::error::Error for F128StatementCircuitError {}

impl From<R1csError> for F128StatementCircuitError {
  fn from(error: R1csError) -> Self {
    Self::R1cs(error)
  }
}

/// Bind the complete terminal statement to Flock's circuit-statement prefix.
///
/// This recomputes Flock's chunked commitment to every public word, binds it
/// and the fixed circuit digest to the exact byte payloads absorbed before
/// Fiat--Shamir, connects the embedded Stage 2 root digest, and finally hashes
/// the 104-byte Stage 3 statement into the two terminal public `Fr` limbs.
pub fn constrain_f128_statement_binding(
  builder: &mut R1csBuilder,
  public_inputs: Stage4PublicInputVariablesV1,
  trace: &F128StatementBindingTraceV1,
  inputs: F128StatementCircuitInputsV1<'_>,
) -> Result<F128StatementCircuitOutputV1, F128StatementCircuitError> {
  trace
    .validate(inputs.public_values.len(), inputs.byte_payloads.len())
    .map_err(|error| {
      F128StatementCircuitError::InvalidTrace(error.to_string())
    })?;
  validate_statement_constants(trace, inputs.stage3_statement)?;

  let circuit_payload = payload(
    inputs.byte_payloads,
    trace.circuit_digest_payload,
    "circuit digest",
  )?;
  bind_constant_digest(
    builder,
    circuit_payload,
    trace.circuit_digest,
    "circuit digest",
  )?;

  let public_values = inputs
    .public_values
    .iter()
    .copied()
    .map(|value| alloc_f128_private(builder, value, ConstraintPhase::Wiring))
    .collect::<Result<Vec<_>, _>>()?;
  let public_digest = constrain_public_values_digest(builder, &public_values)?;
  let expected_public_digest =
    native_public_values_digest(inputs.public_values);
  if digest_bytes(&public_digest) != expected_public_digest {
    return Err(F128StatementCircuitError::InternalShape(
      "public-values digest",
    ));
  }
  let public_payload = payload(
    inputs.byte_payloads,
    trace.public_values_digest_payload,
    "public-values digest",
  )?;
  bind_computed_digest(
    builder,
    &public_digest,
    public_payload,
    expected_public_digest,
    "public-values digest",
    ConstraintPhase::Wiring,
  )?;

  let statement_words = inputs
    .stage3_statement
    .as_chunks::<WORD_BYTES>()
    .0
    .iter()
    .map(|bytes| {
      alloc_word_in_phase(
        builder,
        u32::from_le_bytes(*bytes),
        ConstraintPhase::Statement,
      )
    })
    .collect::<Result<Vec<_>, _>>()?;
  bind_statement_constants(builder, trace, &statement_words);
  for (position, &index) in trace.stage2_digest_public_values.iter().enumerate()
  {
    let start = 2 + 4 * position;
    let statement_value = statement_f128(
      &statement_words[start..start + 4],
      inputs.stage3_statement[8 + 16 * position..24 + 16 * position]
        .try_into()
        .expect("Stage 2 digest half has 16 bytes"),
    )?;
    let public_value = public_values
      .get(usize::try_from(index).expect("u64 fits usize"))
      .ok_or(F128StatementCircuitError::Stage2PublicValueMismatch(position))?;
    if statement_value.value() != public_value.value() {
      return Err(F128StatementCircuitError::Stage2PublicValueMismatch(
        position,
      ));
    }
    crate::enforce_f128_equal(
      builder,
      &statement_value,
      public_value,
      ConstraintPhase::Statement,
    );
  }

  let statement_digest = constrain_chunk(
    builder,
    &statement_words,
    STAGE4_STAGE3_STATEMENT_BYTES,
    true,
    ConstraintPhase::Statement,
  )?;
  if digest_bytes(&statement_digest)
    != *blake3::hash(inputs.stage3_statement).as_bytes()
  {
    return Err(F128StatementCircuitError::InternalShape(
      "Stage 3 statement digest",
    ));
  }
  let digest_bits = statement_digest
    .iter()
    .flat_map(Word32::expressions)
    .collect::<Vec<_>>()
    .try_into()
    .map_err(|_| {
      F128StatementCircuitError::InternalShape("statement digest bits")
    })?;
  constrain_stage4_public_input_expressions(
    builder,
    public_inputs,
    &digest_bits,
  );

  Ok(F128StatementCircuitOutputV1 {
    topology_digest: trace.topology_digest(),
    public_values,
  })
}

fn validate_statement_constants(
  trace: &F128StatementBindingTraceV1,
  statement: &[u8; STAGE4_STAGE3_STATEMENT_BYTES],
) -> Result<(), F128StatementCircuitError> {
  for (kind, actual, expected) in [
    ("domain", &statement[..8], trace.statement_domain.as_slice()),
    ("relation digest", &statement[40..72], trace.relation_digest.as_slice()),
    ("config digest", &statement[72..104], trace.config_digest.as_slice()),
  ] {
    if actual != expected {
      return Err(F128StatementCircuitError::StatementConstantMismatch(kind));
    }
  }
  Ok(())
}

fn bind_statement_constants(
  builder: &mut R1csBuilder,
  trace: &F128StatementBindingTraceV1,
  words: &[Word32],
) {
  let expected = trace
    .statement_domain
    .into_iter()
    .chain(trace.relation_digest)
    .chain(trace.config_digest)
    .collect::<Vec<_>>();
  let selected = words[..2].iter().chain(&words[10..]);
  for (word, bytes) in selected.zip(expected.as_chunks::<4>().0) {
    word.enforce_equal_in_phase(
      builder,
      &Word32::constant(u32::from_le_bytes(*bytes)),
      ConstraintPhase::Statement,
    );
  }
}

fn statement_f128(
  words: &[Word32],
  value: [u8; 16],
) -> Result<F128VariablesV1, F128StatementCircuitError> {
  let variables = words
    .iter()
    .flat_map(Word32::variables)
    .collect::<Vec<_>>()
    .try_into()
    .map_err(|_| {
      F128StatementCircuitError::InternalShape("Stage 2 digest word")
    })?;
  Ok(F128VariablesV1::from_constrained_bits(value, variables))
}

fn payload<'a>(
  payloads: &'a [Vec<F128TranscriptWordV1>],
  index: u64,
  kind: &'static str,
) -> Result<&'a [F128TranscriptWordV1], F128StatementCircuitError> {
  payloads
    .get(usize::try_from(index).expect("u64 fits usize"))
    .map(Vec::as_slice)
    .ok_or(F128StatementCircuitError::MissingPayload(kind))
}

fn bind_constant_digest(
  builder: &mut R1csBuilder,
  payload: &[F128TranscriptWordV1],
  expected: [u8; 32],
  kind: &'static str,
) -> Result<(), F128StatementCircuitError> {
  if payload.len() != 2 {
    return Err(F128StatementCircuitError::PayloadShape {
      kind,
      expected: 2,
      actual: payload.len(),
    });
  }
  if payload.iter().flat_map(|word| word.value()).copied().collect::<Vec<_>>()
    != expected
  {
    return Err(F128StatementCircuitError::PayloadMismatch(kind));
  }
  for (word, expected) in payload.iter().zip(expected.as_chunks::<16>().0) {
    for (expression, bit) in word.bit_expressions().iter().zip(bits(expected)) {
      builder.enforce_zero(
        ConstraintPhase::Wiring,
        expression
          .clone()
          .minus(&LinearCombination::from_constant(Fr::from(u64::from(bit)))),
      );
    }
  }
  Ok(())
}

fn bind_computed_digest(
  builder: &mut R1csBuilder,
  computed: &[Word32; 8],
  payload: &[F128TranscriptWordV1],
  expected: [u8; 32],
  kind: &'static str,
  phase: ConstraintPhase,
) -> Result<(), F128StatementCircuitError> {
  if payload.len() != 2 {
    return Err(F128StatementCircuitError::PayloadShape {
      kind,
      expected: 2,
      actual: payload.len(),
    });
  }
  let actual =
    payload.iter().flat_map(|word| word.value()).copied().collect::<Vec<_>>();
  if actual != expected {
    return Err(F128StatementCircuitError::PayloadMismatch(kind));
  }
  for (word, payload_word) in computed.iter().enumerate() {
    for (bit, expression) in payload[word / 4].bit_expressions()
      [32 * (word % 4)..32 * (word % 4 + 1)]
      .iter()
      .enumerate()
    {
      builder.enforce_zero(
        phase,
        payload_word.expressions()[bit].clone().minus(expression),
      );
    }
  }
  Ok(())
}

fn constrain_public_values_digest(
  builder: &mut R1csBuilder,
  public_values: &[F128VariablesV1],
) -> Result<[Word32; 8], F128StatementCircuitError> {
  let mut chunks = public_values.chunks(PUBLIC_CHUNK_F128);
  let first = chunks
    .next()
    .ok_or(F128StatementCircuitError::InternalShape("empty public vector"))?;
  let mut digest = constrain_chunk(
    builder,
    &f128_words(first),
    16 * first.len(),
    false,
    ConstraintPhase::Wiring,
  )?;
  for chunk in chunks {
    let right = constrain_chunk(
      builder,
      &f128_words(chunk),
      16 * chunk.len(),
      false,
      ConstraintPhase::Wiring,
    )?;
    digest = constrain_parent(builder, digest, right)?;
  }
  Ok(digest)
}

fn f128_words(values: &[F128VariablesV1]) -> Vec<Word32> {
  values
    .iter()
    .flat_map(|value| {
      let variables = value.bit_variables();
      value.value().as_chunks::<4>().0.iter().enumerate().map(
        move |(word, bytes)| {
          Word32::from_variables(
            u32::from_le_bytes(*bytes),
            variables[32 * word..32 * (word + 1)]
              .try_into()
              .expect("F128 word has 32 bits"),
          )
        },
      )
    })
    .collect()
}

fn constrain_chunk(
  builder: &mut R1csBuilder,
  words: &[Word32],
  byte_length: usize,
  root: bool,
  phase: ConstraintPhase,
) -> Result<[Word32; 8], F128StatementCircuitError> {
  if byte_length == 0 || words.len() != byte_length.div_ceil(WORD_BYTES) {
    return Err(F128StatementCircuitError::InternalShape("BLAKE3 chunk"));
  }
  let blocks = byte_length.div_ceil(BLOCK_BYTES);
  let mut chaining_value = BLAKE3_IV.map(Word32::constant);
  for block in 0..blocks {
    let start = block * BLOCK_WORDS;
    let mut message = core::array::from_fn(|_| Word32::constant(0));
    for (target, source) in message.iter_mut().zip(&words[start..]) {
      *target = source.clone();
    }
    let final_block = block + 1 == blocks;
    let block_length =
      if final_block { byte_length - block * BLOCK_BYTES } else { BLOCK_BYTES };
    let mut flags = 0;
    if block == 0 {
      flags |= CHUNK_START;
    }
    if final_block {
      flags |= CHUNK_END;
      if root {
        flags |= ROOT;
      }
    }
    let output = constrain_compression_in_phase(
      builder,
      chaining_value,
      message,
      0,
      u32::try_from(block_length).expect("BLAKE3 block length fits u32"),
      flags,
      phase,
    )?;
    chaining_value = output[..8]
      .to_vec()
      .try_into()
      .map_err(|_| F128StatementCircuitError::InternalShape("BLAKE3 CV"))?;
  }
  Ok(chaining_value)
}

fn constrain_parent(
  builder: &mut R1csBuilder,
  left: [Word32; 8],
  right: [Word32; 8],
) -> Result<[Word32; 8], F128StatementCircuitError> {
  let message = left
    .into_iter()
    .chain(right)
    .collect::<Vec<_>>()
    .try_into()
    .map_err(|_| F128StatementCircuitError::InternalShape("BLAKE3 parent"))?;
  let output = constrain_compression_in_phase(
    builder,
    BLAKE3_IV.map(Word32::constant),
    message,
    0,
    64,
    PARENT,
    ConstraintPhase::Wiring,
  )?;
  output[..8]
    .to_vec()
    .try_into()
    .map_err(|_| F128StatementCircuitError::InternalShape("BLAKE3 parent CV"))
}

fn digest_bytes(words: &[Word32; 8]) -> [u8; 32] {
  let mut output = [0; 32];
  for (index, word) in words.iter().enumerate() {
    output[4 * index..4 * index + 4].copy_from_slice(&word.value.to_le_bytes());
  }
  output
}

fn native_public_values_digest(public_values: &[[u8; 16]]) -> [u8; 32] {
  use blake3::hazmat::{HasherExt, Mode, merge_subtrees_non_root};

  let bytes = public_values.iter().flatten().copied().collect::<Vec<_>>();
  let mut chunks = bytes.chunks(PUBLIC_CHUNK_BYTES);
  let first = chunks.next().expect("statement trace requires public values");
  let mut digest = blake3::Hasher::new().update(first).finalize_non_root();
  for chunk in chunks {
    let right = blake3::Hasher::new().update(chunk).finalize_non_root();
    digest = merge_subtrees_non_root(&digest, &right, Mode::Hash);
  }
  digest
}

fn bits(bytes: &[u8]) -> impl Iterator<Item = bool> + '_ {
  bytes.iter().flat_map(|byte| (0..8).map(move |bit| (byte >> bit) & 1 == 1))
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::{
    Stage4PublicInputsV1, alloc_f128_private, alloc_stage4_public_inputs,
  };
  use ark_bls12_381::Fr;

  fn fixture() -> (
    [u8; STAGE4_STAGE3_STATEMENT_BYTES],
    Vec<[u8; 16]>,
    F128StatementBindingTraceV1,
  ) {
    let mut statement = [0; STAGE4_STAGE3_STATEMENT_BYTES];
    statement[..8].copy_from_slice(b"IXFLK301");
    statement[8..40].copy_from_slice(&[9; 32]);
    statement[40..72].copy_from_slice(&[7; 32]);
    statement[72..].copy_from_slice(&[5; 32]);
    let public_values = vec![[1; 16], [9; 16], [9; 16]];
    let trace = F128StatementBindingTraceV1 {
      statement_domain: *b"IXFLK301",
      relation_digest: [7; 32],
      config_digest: [5; 32],
      circuit_digest: [3; 32],
      circuit_digest_payload: 0,
      public_values_digest_payload: 1,
      stage2_digest_public_values: [1, 2],
      public_value_count: 3,
    };
    (statement, public_values, trace)
  }

  fn compile_with(
    root_byte: u8,
    first_public_byte: u8,
  ) -> Result<(crate::CanonicalR1csV1, crate::Witness), F128StatementCircuitError>
  {
    let (mut statement, mut public_values, trace) = fixture();
    statement[8..40].fill(root_byte);
    public_values[0].fill(first_public_byte);
    public_values[1].fill(root_byte);
    public_values[2].fill(root_byte);
    let mut builder = R1csBuilder::new();
    let terminal = alloc_stage4_public_inputs(
      &mut builder,
      Stage4PublicInputsV1::from_statement_digest(
        *blake3::hash(&statement).as_bytes(),
      ),
    )?;
    let public_digest = native_public_values_digest(&public_values);
    let payload_values = [trace.circuit_digest, public_digest];
    let payloads = payload_values
      .iter()
      .map(|digest| {
        digest
          .as_chunks::<16>()
          .0
          .iter()
          .map(|word| {
            alloc_f128_private(&mut builder, *word, ConstraintPhase::Transcript)
              .map(|word| F128TranscriptWordV1::from_f128_variables(&word))
          })
          .collect::<Result<Vec<_>, _>>()
      })
      .collect::<Result<Vec<_>, _>>()?;
    constrain_f128_statement_binding(
      &mut builder,
      terminal,
      &trace,
      F128StatementCircuitInputsV1 {
        stage3_statement: &statement,
        public_values: &public_values,
        byte_payloads: &payloads,
      },
    )?;
    Ok(builder.finish()?)
  }

  fn compile()
  -> Result<(crate::CanonicalR1csV1, crate::Witness), F128StatementCircuitError>
  {
    compile_with(9, 1)
  }

  #[test]
  fn binds_statement_public_vector_and_transcript_payloads() {
    let (r1cs, witness) = compile().unwrap();
    r1cs.check(&witness).unwrap();
    assert_eq!(r1cs.census().public_variables, 2);
    assert!(
      r1cs
        .census()
        .constraints_by_phase
        .contains_key(&ConstraintPhase::Statement)
    );
    assert!(
      r1cs.census().constraints_by_phase.contains_key(&ConstraintPhase::Wiring)
    );
  }

  #[test]
  fn terminal_digest_mutation_breaks_the_relation() {
    let (r1cs, mut witness) = compile().unwrap();
    witness.set(crate::Variable::from_index(1), Fr::from(4u64)).unwrap();
    assert!(matches!(r1cs.check(&witness), Err(R1csError::Unsatisfied { .. })));
  }

  #[test]
  fn relation_shape_is_independent_of_dynamic_statement_and_public_values() {
    let (first, _) = compile_with(9, 1).unwrap();
    let (second, _) = compile_with(11, 2).unwrap();
    assert_eq!(first.digest(), second.digest());
  }
}
