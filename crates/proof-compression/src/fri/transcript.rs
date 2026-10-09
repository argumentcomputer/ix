use std::collections::HashMap;

use p3_field::{PrimeCharacteristicRing, PrimeField64};
use p3_goldilocks::Goldilocks;

use super::AlgebraicInputs;
use super::ByteGadgets;
use super::ByteValue;
use super::QuadraticValue;
use super::blake3;
use multi_stark::plonkish::Bool;
use multi_stark::plonkish::CircuitBuilder;
use multi_stark::plonkish::Value;
use multi_stark::system::System;
use multi_stark::types::GoldilocksBlake3Config;

#[cfg(test)]
#[path = "transcript_tests.rs"]
mod tests;

/// Constrained reference Goldilocks/BLAKE3 challenger. Observation invalidates
/// buffered output; each flush chains its digest; sampling pops bytes from
/// the END of that digest, matching p3's HashChallenger exactly.
///
/// Field sampling selects the FIRST canonical candidate, with a fixed retry
/// budget. Exhaustion is rejected; no modular reduction or skipped valid
/// candidates are allowed. Conditional buffer updates are circuit relations.
pub struct Blake3Challenger {
  input: Vec<ByteValue>,
  output: Vec<ByteValue>,
  encodings: HashMap<Value, [ByteValue; 8]>,
  dynamic: Option<BufferedOutput>,
  max_field_retries: usize,
}

pub const DEFAULT_FIELD_RETRIES: usize = 2;

/// Bytes in consumption order, and a one-hot remaining-byte count. This
/// representation lets retries consume a witness-dependent number of bytes
/// without changing the circuit's layout or trusting a host-selected cursor.
#[derive(Clone)]
struct BufferedOutput {
  queue: [ByteValue; 32],
  remaining: [Bool; 33],
}

impl Blake3Challenger {
  /// Exact reference grinding check; zero bits do not observe the witness.
  pub fn check_witness(
    &mut self,
    b: &mut CircuitBuilder<Goldilocks>,
    bytes: &ByteGadgets,
    bits: usize,
    witness: Value,
  ) {
    if bits != 0 {
      self.observe_field(b, bytes, witness);
      for bit in self.sample_bits(b, bytes, bits) {
        b.assert_zero(bit.value());
      }
    }
  }
  /// Low bits of the next little-endian u64. Native sample_bits always
  /// consumes eight bytes, even for zero bits, and does not reject >= p.
  pub fn sample_bits(
    &mut self,
    b: &mut CircuitBuilder<Goldilocks>,
    bytes: &ByteGadgets,
    count: usize,
  ) -> Vec<Bool> {
    assert!(count < 64 && (1u64 << count) < Goldilocks::ORDER_U64);
    let sampled = self.sample_chunk::<8>(b, bytes);
    sampled[..count.div_ceil(8)]
      .iter()
      .flat_map(|&byte| bytes.bits(b, byte))
      .take(count)
      .collect()
  }

  pub fn new(
    b: &mut CircuitBuilder<Goldilocks>,
    bytes: &ByteGadgets,
    seed: &[u8],
  ) -> Self {
    Self::with_retry_limit(b, bytes, seed, DEFAULT_FIELD_RETRIES)
  }

  /// The retry limit is a circuit constant, never prover advice. Zero
  /// retains the original no-retry subset. Larger limits cost more gates.
  pub fn with_retry_limit(
    b: &mut CircuitBuilder<Goldilocks>,
    bytes: &ByteGadgets,
    seed: &[u8],
    max_field_retries: usize,
  ) -> Self {
    Self {
      input: seed.iter().map(|&x| bytes.constant(b, x)).collect(),
      output: vec![],
      encodings: HashMap::new(),
      dynamic: None,
      max_field_retries,
    }
  }

  pub fn observe_bytes(&mut self, values: &[ByteValue]) {
    // Native observe_slice([]) performs no byte observations, so it
    // must not discard partially consumed output.
    if !values.is_empty() {
      self.output.clear();
      self.dynamic = None;
    }
    self.input.extend_from_slice(values);
  }

  pub fn observe_field(
    &mut self,
    b: &mut CircuitBuilder<Goldilocks>,
    bytes: &ByteGadgets,
    value: Value,
  ) {
    let encoding = *self
      .encodings
      .entry(value)
      .or_insert_with(|| bytes.encode_field64(b, value));
    self.observe_bytes(&encoding);
  }

  pub fn observe_extension(
    &mut self,
    b: &mut CircuitBuilder<Goldilocks>,
    bytes: &ByteGadgets,
    value: QuadraticValue,
  ) {
    for coordinate in value.0 {
      self.observe_field(b, bytes, coordinate);
    }
  }

  pub fn sample_byte(
    &mut self,
    b: &mut CircuitBuilder<Goldilocks>,
    bytes: &ByteGadgets,
  ) -> ByteValue {
    self.sample_chunk::<1>(b, bytes)[0]
  }

  fn sample_chunk<const N: usize>(
    &mut self,
    b: &mut CircuitBuilder<Goldilocks>,
    bytes: &ByteGadgets,
  ) -> [ByteValue; N] {
    assert!((1..=32).contains(&N));
    let Some(old) = self.dynamic.take() else {
      return std::array::from_fn(|_| {
        if self.output.is_empty() {
          let digest = blake3(b, bytes, &self.input);
          self.input = digest.to_vec();
          self.output = digest.to_vec();
        }
        self.output.pop().unwrap()
      });
    };
    assert_eq!(self.input.len(), 32);
    // At most one digest boundary can be crossed by a <=32-byte read.
    // Hashing speculatively is safe: state advances only when required.
    let digest = blake3(b, bytes, &self.input);
    let fresh: [_; 32] = std::array::from_fn(|i| digest[31 - i]);
    let terms: Vec<_> = old.remaining[..N]
      .iter()
      .map(|bit| (Goldilocks::ONE, bit.value()))
      .collect();
    let refill = b.linear_combination(&terms, Goldilocks::ZERO);
    let refill = b.assert_bool(refill);
    let sampled = std::array::from_fn(|i| {
      let mut value = old.queue[i];
      for r in 0..=i {
        value = bytes.select(b, old.remaining[r], fresh[i - r], value);
      }
      value
    });
    let zero = bytes.constant(b, 0);
    let queue = std::array::from_fn(|i| {
      let mut value = old.queue.get(i + N).copied().unwrap_or(zero);
      for r in 0..N {
        let candidate = fresh.get(i + N - r).copied().unwrap_or(zero);
        value = bytes.select(b, old.remaining[r], candidate, value);
      }
      value
    });
    let remaining = std::array::from_fn(|count| {
      let terms: Vec<_> = (0..=32)
        .filter(|&r| (if r >= N { r - N } else { 32 - N + r }) == count)
        .map(|r| (Goldilocks::ONE, old.remaining[r].value()))
        .collect();
      let value = b.linear_combination(&terms, Goldilocks::ZERO);
      b.assert_bool(value)
    });
    for (value, fresh) in self.input.iter_mut().zip(digest) {
      *value = bytes.select(b, refill, fresh, *value);
    }
    self.dynamic = Some(BufferedOutput { queue, remaining });
    sampled
  }

  fn buffer(
    &self,
    b: &mut CircuitBuilder<Goldilocks>,
    bytes: &ByteGadgets,
  ) -> BufferedOutput {
    self.dynamic.clone().unwrap_or_else(|| {
      let zero = bytes.constant(b, 0);
      BufferedOutput {
        queue: std::array::from_fn(|i| {
          self.output.iter().rev().nth(i).copied().unwrap_or(zero)
        }),
        remaining: std::array::from_fn(|i| {
          let value = b.constant(Goldilocks::from_bool(i == self.output.len()));
          b.assert_bool(value)
        }),
      }
    })
  }

  fn retain_state_if(
    &mut self,
    b: &mut CircuitBuilder<Goldilocks>,
    bytes: &ByteGadgets,
    retain: Bool,
    input: &[ByteValue],
    before: &BufferedOutput,
  ) {
    assert_eq!(self.input.len(), 32);
    assert_eq!(input.len(), 32);
    let after = self.buffer(b, bytes);
    let queue = std::array::from_fn(|i| {
      bytes.select(b, retain, before.queue[i], after.queue[i])
    });
    let remaining = std::array::from_fn(|i| {
      let value = b.select(
        retain,
        before.remaining[i].value(),
        after.remaining[i].value(),
      );
      b.assert_bool(value)
    });
    for (value, &old) in self.input.iter_mut().zip(input) {
      *value = bytes.select(b, retain, old, *value);
    }
    self.output.clear();
    self.dynamic = Some(BufferedOutput { queue, remaining });
  }

  pub fn sample_field(
    &mut self,
    b: &mut CircuitBuilder<Goldilocks>,
    bytes: &ByteGadgets,
  ) -> Value {
    let mut candidate = self.sample_chunk::<8>(b, bytes);
    let mut accepted =
      bytes.is_at_most_u64(b, candidate, Goldilocks::ORDER_U64 - 1);
    let one = b.constant(Goldilocks::ONE);
    for _ in 0..self.max_field_retries {
      let before = self.buffer(b, bytes);
      let input = self.input.clone();
      let next = self.sample_chunk::<8>(b, bytes);
      self.retain_state_if(b, bytes, accepted, &input, &before);
      candidate = std::array::from_fn(|i| {
        bytes.select(b, accepted, candidate[i], next[i])
      });
      let valid = bytes.is_at_most_u64(b, next, Goldilocks::ORDER_U64 - 1);
      let done = b.select(accepted, one, valid.value());
      accepted = b.assert_bool(done);
    }
    b.assert_equal(accepted.value(), one);
    let value = bytes.pack_u64(b, candidate);
    self.encodings.insert(value, candidate);
    value
  }

  pub fn sample_extension(
    &mut self,
    b: &mut CircuitBuilder<Goldilocks>,
    bytes: &ByteGadgets,
  ) -> QuadraticValue {
    QuadraticValue(std::array::from_fn(|_| self.sample_field(b, bytes)))
  }

  /// Observe a fixed integer through the same canonical field encoding.
  pub fn observe_constant(
    &mut self,
    b: &mut CircuitBuilder<Goldilocks>,
    bytes: &ByteGadgets,
    value: usize,
  ) {
    let value = b.constant(Goldilocks::from_usize(value));
    self.observe_field(b, bytes, value);
  }
}

/// Single-root commitments (cap height zero) supplied as constrained bytes.
/// The PCS gadget authenticates its openings against these wires.
pub struct TranscriptCommitments {
  pub stage1: [ByteValue; 32],
  pub stage2: [ByteValue; 32],
  pub quotient: [ByteValue; 32],
}

impl TranscriptCommitments {
  pub fn allocate(
    b: &mut CircuitBuilder<Goldilocks>,
    bytes: &ByteGadgets,
  ) -> Self {
    let mut root =
      |label| std::array::from_fn(|i| bytes.input(b, &format!("{label}[{i}]")));
    Self {
      stage1: root("stage1 root"),
      stage2: root("stage2 root"),
      quotient: root("quotient root"),
    }
  }
}

/// Constrain the reference multi-stark transcript through OOD challenge zeta
/// and bind all four challenge wires consumed by the algebraic verifier.
///
/// Scope: all circuits active, fixed heights, cap height zero, Goldilocks,
/// quadratic challenges, and bounded rejection-sampling retries. System metadata,
/// preprocessing commitment, and protocol seed are trusted circuit constants.
/// PCS/Merkle/FRI authentication is NOT performed by this function.
/// Returns the constrained challenger state for the PCS continuation.
pub fn constrain_transcript(
  b: &mut CircuitBuilder<Goldilocks>,
  bytes: &ByteGadgets,
  system: &System<GoldilocksBlake3Config>,
  log_degrees: &[u8],
  inputs: &AlgebraicInputs,
  commitments: &TranscriptCommitments,
) -> Blake3Challenger {
  constrain_active_transcript(
    b,
    bytes,
    system,
    &vec![true; system.circuits.len()],
    log_degrees,
    inputs,
    commitments,
    DEFAULT_FIELD_RETRIES,
  )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn constrain_active_transcript(
  b: &mut CircuitBuilder<Goldilocks>,
  bytes: &ByteGadgets,
  system: &System<GoldilocksBlake3Config>,
  active: &[bool],
  log_degrees: &[u8],
  inputs: &AlgebraicInputs,
  commitments: &TranscriptCommitments,
  max_field_retries: usize,
) -> Blake3Challenger {
  assert_eq!(
    system.config.cap_height(),
    0,
    "only cap height zero is supported"
  );
  assert!(!system.circuits.is_empty());
  assert_eq!(system.circuits.len(), active.len());
  assert_eq!(active.iter().filter(|&&a| a).count(), log_degrees.len());
  assert_eq!(log_degrees.len(), inputs.openings.len());
  let mut challenger = Blake3Challenger::with_retry_limit(
    b,
    bytes,
    system.config.challenger_seed(),
    max_field_retries,
  );
  challenger.observe_constant(b, bytes, system.circuits.len());
  for circuit in &system.circuits {
    for item in [
      circuit.constraint_count(),
      circuit.max_constraint_degree(),
      circuit.preprocessed_height,
      circuit.preprocessed_width,
      circuit.main_width,
      circuit.stage_2_width,
      circuit.lookup_group_size,
    ] {
      challenger.observe_constant(b, bytes, item);
    }
  }
  for &enabled in active {
    challenger.observe_constant(b, bytes, usize::from(enabled));
  }
  if let Some(commitment) = &system.preprocessed_commit {
    assert_eq!(
      commitment.roots().len(),
      1,
      "only cap height zero is supported"
    );
    let root = commitment.roots()[0].map(|x| bytes.constant(b, x));
    challenger.observe_bytes(&root);
  }
  challenger.observe_bytes(&commitments.stage1);
  for &log_degree in log_degrees {
    challenger.observe_constant(b, bytes, usize::from(log_degree));
  }
  challenger.observe_constant(b, bytes, inputs.claims.len());
  for claim in &inputs.claims {
    challenger.observe_constant(b, bytes, claim.len());
    for &value in claim {
      challenger.observe_field(b, bytes, value);
    }
  }
  let beta = challenger.sample_extension(b, bytes);
  beta.assert_equal(b, inputs.challenges.beta);
  challenger.observe_extension(b, bytes, beta);
  let gamma = challenger.sample_extension(b, bytes);
  gamma.assert_equal(b, inputs.challenges.gamma);
  challenger.observe_extension(b, bytes, gamma);
  challenger.observe_bytes(&commitments.stage2);
  for opening in &inputs.openings {
    challenger.observe_extension(b, bytes, opening.accumulator);
  }
  let alpha = challenger.sample_extension(b, bytes);
  alpha.assert_equal(b, inputs.challenges.alpha);
  challenger.observe_bytes(&commitments.quotient);
  let zeta = challenger.sample_extension(b, bytes);
  zeta.assert_equal(b, inputs.challenges.zeta);
  challenger
}
