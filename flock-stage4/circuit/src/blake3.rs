use crate::{
  CanonicalR1csV1, ConstraintPhase, LinearCombination, R1csBuilder, R1csError,
  Variable, Witness,
};
use ark_bls12_381::Fr;
use ark_ff::{AdditiveGroup, Field};

const WORD_BITS: usize = 32;
const ROUNDS: usize = 7;

pub const BLAKE3_IV: [u32; 8] = [
  0x6a09_e667,
  0xbb67_ae85,
  0x3c6e_f372,
  0xa54f_f53a,
  0x510e_527f,
  0x9b05_688c,
  0x1f83_d9ab,
  0x5be0_cd19,
];

const MSG_PERMUTATION: [usize; 16] =
  [2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8];

const G_LANES: [[usize; 4]; 8] = [
  [0, 4, 8, 12],
  [1, 5, 9, 13],
  [2, 6, 10, 14],
  [3, 7, 11, 15],
  [0, 5, 10, 15],
  [1, 6, 11, 12],
  [2, 7, 8, 13],
  [3, 4, 9, 14],
];

const G_MESSAGE_INDICES: [[usize; 2]; 8] =
  [[0, 1], [2, 3], [4, 5], [6, 7], [8, 9], [10, 11], [12, 13], [14, 15]];

/// One raw BLAKE3 compression invocation used by the Flock transcript.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Blake3CompressionInputV1 {
  pub chaining_value: [u32; 8],
  pub message: [u32; 16],
  pub counter: u64,
  pub block_length: u32,
  pub flags: u32,
}

/// Values and R1CS variables for the full 512-bit compression output.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Blake3CompressionOutputV1 {
  pub words: [u32; 16],
  pub bit_variables: [[Variable; WORD_BITS]; 16],
}

/// Build a standalone canonical R1CS for one transcript compression.
///
/// The chaining value and message are private bits. Counter, block length,
/// and flags are topology constants, matching their use in a compiled Flock
/// transcript.
pub fn build_blake3_compression_r1cs(
  input: Blake3CompressionInputV1,
) -> Result<(CanonicalR1csV1, Witness, Blake3CompressionOutputV1), R1csError> {
  let mut builder = R1csBuilder::new();
  let chaining_value = alloc_words(&mut builder, input.chaining_value)?;
  let message = alloc_words(&mut builder, input.message)?;
  let output = constrain_compression(
    &mut builder,
    chaining_value,
    message,
    input.counter,
    input.block_length,
    input.flags,
  )?;
  let exported = Blake3CompressionOutputV1 {
    words: output.each_ref().map(|word| word.value),
    bit_variables: output.each_ref().map(Word32::variables),
  };
  let (r1cs, witness) = builder.finish()?;
  Ok((r1cs, witness, exported))
}

#[derive(Clone, Debug)]
struct BitWire {
  value: bool,
  expression: LinearCombination,
  variable: Option<Variable>,
  constant: bool,
}

impl BitWire {
  fn constant(value: bool) -> Self {
    Self {
      value,
      expression: LinearCombination::from_constant(Fr::from(u64::from(value))),
      variable: None,
      constant: true,
    }
  }

  fn not(&self) -> Self {
    Self {
      value: !self.value,
      expression: LinearCombination::one().minus(&self.expression),
      variable: None,
      constant: self.constant,
    }
  }
}

#[derive(Clone, Debug)]
pub(crate) struct Word32 {
  pub(crate) value: u32,
  bits: [BitWire; WORD_BITS],
}

impl Word32 {
  pub(crate) fn constant(value: u32) -> Self {
    Self {
      value,
      bits: core::array::from_fn(|bit| {
        BitWire::constant((value >> bit) & 1 == 1)
      }),
    }
  }

  pub(crate) fn from_variables(
    value: u32,
    variables: [Variable; WORD_BITS],
  ) -> Self {
    Self {
      value,
      bits: variables.map(|variable| BitWire {
        value: false,
        expression: LinearCombination::from_variable(variable),
        variable: Some(variable),
        constant: false,
      }),
    }
    .with_variable_values()
  }

  pub(crate) fn from_expressions(
    value: u32,
    expressions: [LinearCombination; WORD_BITS],
  ) -> Self {
    Self {
      value,
      bits: core::array::from_fn(|bit| BitWire {
        value: (value >> bit) & 1 == 1,
        expression: expressions[bit].clone(),
        variable: None,
        constant: expressions[bit].terms().is_empty()
          || expressions[bit].terms() == [(Variable::ONE, Fr::ONE)],
      }),
    }
  }

  fn with_variable_values(mut self) -> Self {
    for (bit, wire) in self.bits.iter_mut().enumerate() {
      wire.value = (self.value >> bit) & 1 == 1;
    }
    self
  }

  fn rotate_right(&self, distance: usize) -> Self {
    Self {
      value: self.value.rotate_right(
        u32::try_from(distance).expect("BLAKE3 rotation fits u32"),
      ),
      bits: core::array::from_fn(|bit| {
        self.bits[(bit + distance) % WORD_BITS].clone()
      }),
    }
  }

  fn packed(&self) -> LinearCombination {
    let mut packed = LinearCombination::zero();
    let mut coefficient = Fr::ONE;
    for bit in &self.bits {
      packed = packed.plus(&bit.expression.clone().scale(coefficient));
      coefficient.double_in_place();
    }
    packed
  }

  pub(crate) fn variables(&self) -> [Variable; WORD_BITS] {
    self.bits.each_ref().map(|bit| {
      bit.variable.expect("compression outputs are allocated variables")
    })
  }

  pub(crate) fn expressions(&self) -> [LinearCombination; WORD_BITS] {
    self.bits.each_ref().map(|bit| bit.expression.clone())
  }

  pub(crate) fn enforce_equal(&self, builder: &mut R1csBuilder, other: &Self) {
    self.enforce_equal_in_phase(builder, other, ConstraintPhase::Transcript);
  }

  pub(crate) fn enforce_equal_in_phase(
    &self,
    builder: &mut R1csBuilder,
    other: &Self,
    phase: ConstraintPhase,
  ) {
    for (left, right) in self.bits.iter().zip(&other.bits) {
      builder
        .enforce_zero(phase, left.expression.clone().minus(&right.expression));
    }
  }

  pub(crate) fn enforce_bit_zero(&self, builder: &mut R1csBuilder, bit: usize) {
    self.enforce_bit_zero_in_phase(builder, bit, ConstraintPhase::Transcript);
  }

  pub(crate) fn enforce_bit_zero_in_phase(
    &self,
    builder: &mut R1csBuilder,
    bit: usize,
    phase: ConstraintPhase,
  ) {
    builder.enforce_zero(phase, self.bits[bit].expression.clone());
  }
}

/// Select one word without branching the constraint topology on the selector.
/// `false_word` is returned for selector zero and `true_word` for selector one.
pub(crate) fn select_word_in_phase(
  builder: &mut R1csBuilder,
  selector: Variable,
  selector_value: bool,
  false_word: &Word32,
  true_word: &Word32,
  phase: ConstraintPhase,
) -> Result<Word32, R1csError> {
  let selector = LinearCombination::from_variable(selector);
  let bits = false_word
    .bits
    .iter()
    .zip(&true_word.bits)
    .map(|(false_bit, true_bit)| {
      let output = alloc_derived_bit(
        builder,
        if selector_value { true_bit.value } else { false_bit.value },
      )?;
      builder.enforce(
        phase,
        selector.clone(),
        true_bit.expression.clone().minus(&false_bit.expression),
        output.expression.clone().minus(&false_bit.expression),
      );
      Ok(output)
    })
    .collect::<Result<Vec<_>, R1csError>>()?
    .try_into()
    .map_err(|_| R1csError::InternalShape)?;
  Ok(Word32 {
    value: if selector_value { true_word.value } else { false_word.value },
    bits,
  })
}

pub(crate) fn alloc_words<const N: usize>(
  builder: &mut R1csBuilder,
  values: [u32; N],
) -> Result<[Word32; N], R1csError> {
  alloc_words_in_phase(builder, values, ConstraintPhase::Transcript)
}

pub(crate) fn alloc_words_in_phase<const N: usize>(
  builder: &mut R1csBuilder,
  values: [u32; N],
  phase: ConstraintPhase,
) -> Result<[Word32; N], R1csError> {
  values
    .into_iter()
    .map(|value| alloc_word_in_phase(builder, value, phase))
    .collect::<Result<Vec<_>, _>>()?
    .try_into()
    .map_err(|_| R1csError::InternalShape)
}

pub(crate) fn alloc_word_in_phase(
  builder: &mut R1csBuilder,
  value: u32,
  phase: ConstraintPhase,
) -> Result<Word32, R1csError> {
  alloc_word_prefix_in_phase(builder, value, WORD_BITS, phase)
}

pub(crate) fn alloc_word_prefix(
  builder: &mut R1csBuilder,
  value: u32,
  private_bits: usize,
) -> Result<Word32, R1csError> {
  alloc_word_prefix_in_phase(
    builder,
    value,
    private_bits,
    ConstraintPhase::Transcript,
  )
}

pub(crate) fn alloc_word_prefix_in_phase(
  builder: &mut R1csBuilder,
  value: u32,
  private_bits: usize,
  phase: ConstraintPhase,
) -> Result<Word32, R1csError> {
  if private_bits > WORD_BITS {
    return Err(R1csError::InternalShape);
  }
  let bits = (0..WORD_BITS)
    .map(|bit| {
      let value = (value >> bit) & 1 == 1;
      if bit < private_bits {
        alloc_checked_bit(builder, value, phase)
      } else {
        Ok(BitWire::constant(value))
      }
    })
    .collect::<Result<Vec<_>, _>>()?
    .try_into()
    .map_err(|_| R1csError::InternalShape)?;
  Ok(Word32 { value, bits })
}

fn alloc_checked_bit(
  builder: &mut R1csBuilder,
  value: bool,
  phase: ConstraintPhase,
) -> Result<BitWire, R1csError> {
  let variable = builder.alloc_private(Fr::from(u64::from(value)))?;
  builder.enforce_boolean(phase, variable);
  Ok(BitWire {
    value,
    expression: LinearCombination::from_variable(variable),
    variable: Some(variable),
    constant: false,
  })
}

fn alloc_derived_bit(
  builder: &mut R1csBuilder,
  value: bool,
) -> Result<BitWire, R1csError> {
  let variable = builder.alloc_private(Fr::from(u64::from(value)))?;
  Ok(BitWire {
    value,
    expression: LinearCombination::from_variable(variable),
    variable: Some(variable),
    constant: false,
  })
}

fn xor_bit(
  builder: &mut R1csBuilder,
  left: &BitWire,
  right: &BitWire,
  phase: ConstraintPhase,
) -> Result<BitWire, R1csError> {
  if left.constant {
    return Ok(if left.value { right.not() } else { right.clone() });
  }
  if right.constant {
    return Ok(if right.value { left.not() } else { left.clone() });
  }
  let output = alloc_derived_bit(builder, left.value ^ right.value)?;
  let inverse_two =
    Fr::from(2_u64).inverse().expect("two is invertible in BLS12-381 Fr");
  let right_hand_side = left
    .expression
    .clone()
    .plus(&right.expression)
    .minus(&output.expression)
    .scale(inverse_two);
  builder.enforce(
    phase,
    left.expression.clone(),
    right.expression.clone(),
    right_hand_side,
  );
  Ok(output)
}

fn xor_word(
  builder: &mut R1csBuilder,
  left: &Word32,
  right: &Word32,
  phase: ConstraintPhase,
) -> Result<Word32, R1csError> {
  let bits = left
    .bits
    .iter()
    .zip(&right.bits)
    .map(|(left, right)| xor_bit(builder, left, right, phase))
    .collect::<Result<Vec<_>, _>>()?
    .try_into()
    .map_err(|_| R1csError::InternalShape)?;
  Ok(Word32 { value: left.value ^ right.value, bits })
}

fn add_two(
  builder: &mut R1csBuilder,
  left: &Word32,
  right: &Word32,
  phase: ConstraintPhase,
) -> Result<Word32, R1csError> {
  let total = u64::from(left.value) + u64::from(right.value);
  let sum = alloc_word_in_phase(builder, low_u32(total), phase)?;
  let overflow = alloc_checked_bit(builder, total >> WORD_BITS != 0, phase)?;
  let equation = left
    .packed()
    .plus(&right.packed())
    .minus(&sum.packed())
    .minus(&overflow.expression.clone().scale(Fr::from(1_u64 << WORD_BITS)));
  builder.enforce_zero(phase, equation);
  Ok(sum)
}

fn add_three(
  builder: &mut R1csBuilder,
  first: &Word32,
  second: &Word32,
  third: &Word32,
  phase: ConstraintPhase,
) -> Result<Word32, R1csError> {
  let total =
    u64::from(first.value) + u64::from(second.value) + u64::from(third.value);
  let sum = alloc_word_in_phase(builder, low_u32(total), phase)?;
  let overflow_value = total >> WORD_BITS;
  let overflow_low =
    alloc_checked_bit(builder, overflow_value & 1 == 1, phase)?;
  let overflow_high =
    alloc_checked_bit(builder, overflow_value & 2 == 2, phase)?;
  builder.enforce(
    phase,
    overflow_low.expression.clone(),
    overflow_high.expression.clone(),
    LinearCombination::zero(),
  );
  let overflow = overflow_low
    .expression
    .clone()
    .plus(&overflow_high.expression.clone().scale(Fr::from(2_u64)))
    .scale(Fr::from(1_u64 << WORD_BITS));
  let equation = first
    .packed()
    .plus(&second.packed())
    .plus(&third.packed())
    .minus(&sum.packed())
    .minus(&overflow);
  builder.enforce_zero(phase, equation);
  Ok(sum)
}

pub(crate) fn constrain_compression(
  builder: &mut R1csBuilder,
  chaining_value: [Word32; 8],
  message: [Word32; 16],
  counter: u64,
  block_length: u32,
  flags: u32,
) -> Result<[Word32; 16], R1csError> {
  constrain_compression_in_phase(
    builder,
    chaining_value,
    message,
    counter,
    block_length,
    flags,
    ConstraintPhase::Transcript,
  )
}

pub(crate) fn constrain_compression_in_phase(
  builder: &mut R1csBuilder,
  chaining_value: [Word32; 8],
  message: [Word32; 16],
  counter: u64,
  block_length: u32,
  flags: u32,
  phase: ConstraintPhase,
) -> Result<[Word32; 16], R1csError> {
  let original_chaining_value = chaining_value.clone();
  let mut state: [Word32; 16] = chaining_value
    .into_iter()
    .chain(BLAKE3_IV[..4].iter().copied().map(Word32::constant))
    .chain(
      [low_u32(counter), high_u32(counter), block_length, flags]
        .map(Word32::constant),
    )
    .collect::<Vec<_>>()
    .try_into()
    .map_err(|_| R1csError::InternalShape)?;

  let mut scheduled_message = message;
  for _ in 0..ROUNDS {
    for (lanes, indices) in G_LANES.into_iter().zip(G_MESSAGE_INDICES) {
      apply_g(
        builder,
        &mut state,
        lanes,
        &scheduled_message[indices[0]],
        &scheduled_message[indices[1]],
        phase,
      )?;
    }
    scheduled_message = core::array::from_fn(|index| {
      scheduled_message[MSG_PERMUTATION[index]].clone()
    });
  }

  let mut output = Vec::with_capacity(16);
  for index in 0..8 {
    output.push(xor_word(builder, &state[index], &state[index + 8], phase)?);
  }
  for index in 0..8 {
    output.push(xor_word(
      builder,
      &state[index + 8],
      &original_chaining_value[index],
      phase,
    )?);
  }
  output.try_into().map_err(|_| R1csError::InternalShape)
}

fn low_u32(value: u64) -> u32 {
  u32::from_le_bytes(
    value.to_le_bytes()[..4].try_into().expect("four low bytes"),
  )
}

fn high_u32(value: u64) -> u32 {
  u32::from_le_bytes(
    value.to_le_bytes()[4..].try_into().expect("four high bytes"),
  )
}

fn apply_g(
  builder: &mut R1csBuilder,
  state: &mut [Word32; 16],
  lanes: [usize; 4],
  message_x: &Word32,
  message_y: &Word32,
  phase: ConstraintPhase,
) -> Result<(), R1csError> {
  let [a_index, b_index, c_index, d_index] = lanes;
  let mut a = state[a_index].clone();
  let mut b = state[b_index].clone();
  let mut c = state[c_index].clone();
  let mut d = state[d_index].clone();

  a = add_three(builder, &a, &b, message_x, phase)?;
  d = xor_word(builder, &d, &a, phase)?.rotate_right(16);
  c = add_two(builder, &c, &d, phase)?;
  b = xor_word(builder, &b, &c, phase)?.rotate_right(12);
  a = add_three(builder, &a, &b, message_y, phase)?;
  d = xor_word(builder, &d, &a, phase)?.rotate_right(8);
  c = add_two(builder, &c, &d, phase)?;
  b = xor_word(builder, &b, &c, phase)?.rotate_right(7);

  state[a_index] = a;
  state[b_index] = b;
  state[c_index] = c;
  state[d_index] = d;
  Ok(())
}

#[cfg(test)]
mod tests {
  use super::*;

  const CHUNK_START: u32 = 1 << 0;
  const CHUNK_END: u32 = 1 << 1;
  const ROOT: u32 = 1 << 3;

  fn hash_input(message: &[u8]) -> Blake3CompressionInputV1 {
    assert!(message.len() <= 64);
    let mut block = [0_u8; 64];
    block[..message.len()].copy_from_slice(message);
    Blake3CompressionInputV1 {
      chaining_value: BLAKE3_IV,
      message: core::array::from_fn(|index| {
        u32::from_le_bytes(
          block[4 * index..4 * index + 4].try_into().expect("four-byte word"),
        )
      }),
      counter: 0,
      block_length: u32::try_from(message.len()).unwrap(),
      flags: CHUNK_START | CHUNK_END | ROOT,
    }
  }

  fn output_digest(output: &Blake3CompressionOutputV1) -> [u8; 32] {
    let mut digest = [0_u8; 32];
    for (index, word) in output.words[..8].iter().enumerate() {
      digest[4 * index..4 * index + 4].copy_from_slice(&word.to_le_bytes());
    }
    digest
  }

  #[test]
  fn compression_matches_reference_blake3() {
    for message in [b"".as_slice(), b"abc".as_slice()] {
      let (r1cs, witness, output) =
        build_blake3_compression_r1cs(hash_input(message)).unwrap();
      r1cs.check(&witness).unwrap();
      assert_eq!(r1cs.private_variables(), 15_824);
      assert_eq!(r1cs.census().constraints, 16_160);
      assert_eq!(output_digest(&output), *blake3::hash(message).as_bytes());
      assert_eq!(
        r1cs.census().constraints_by_phase.get(&ConstraintPhase::Transcript),
        Some(&r1cs.census().constraints),
      );
    }
  }

  #[test]
  fn output_tampering_breaks_the_relation() {
    let (r1cs, mut witness, output) =
      build_blake3_compression_r1cs(hash_input(b"tamper")).unwrap();
    witness.set(output.bit_variables[0][0], Fr::ONE).unwrap();
    if output.words[0] & 1 == 1 {
      witness.set(output.bit_variables[0][0], Fr::from(0_u64)).unwrap();
    }
    assert!(matches!(r1cs.check(&witness), Err(R1csError::Unsatisfied { .. })));
  }

  #[test]
  fn compression_shape_is_value_independent() {
    let (first, _, _) =
      build_blake3_compression_r1cs(hash_input(b"first")).unwrap();
    let (second, _, _) =
      build_blake3_compression_r1cs(hash_input(b"other")).unwrap();
    assert_eq!(first.digest(), second.digest());
  }
}
