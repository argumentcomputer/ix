//! BLAKE3 uses the existing Boolean compression gate. Bit references
//! remain views until a mask, selection, or permutation needs decomposition.
use crate::{
  ConstraintPhase, LinearCombination, R1csBuilder, R1csError, Variable,
};
use flock_prover::field::F128;
pub(crate) const BLAKE3_IV: [u32; 8] = ixby_flock::hash::IV;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Word32 {
  pub(crate) value: u32,
  bits: [Variable; 32],
}
impl Word32 {
  pub(crate) fn constant(value: u32) -> Self {
    Self {
      value,
      bits: std::array::from_fn(|i| Variable::Constant((value >> i) & 1 != 0)),
    }
  }
  pub(crate) fn from_variables(value: u32, bits: [Variable; 32]) -> Self {
    Self { value, bits }
  }
  pub(crate) fn from_expressions(
    value: u32,
    bits: [LinearCombination; 32],
  ) -> Self {
    Self { value, bits }
  }
  pub(crate) fn variables(&self) -> [Variable; 32] {
    self.bits
  }
  pub(crate) fn expressions(&self) -> [LinearCombination; 32] {
    self.bits
  }
  fn word(&self, b: &mut R1csBuilder) -> usize {
    b.pack(&std::array::from_fn(|i| {
      if i < 32 { self.bits[i] } else { Variable::Constant(false) }
    }))
  }
  pub(crate) fn enforce_equal(&self, b: &mut R1csBuilder, other: &Self) {
    self.enforce_equal_in_phase(b, other, ConstraintPhase::Transcript);
  }
  pub(crate) fn enforce_equal_in_phase(
    &self,
    b: &mut R1csBuilder,
    other: &Self,
    _: ConstraintPhase,
  ) {
    let a = self.word(b);
    let c = other.word(b);
    b.equal(a, c);
  }
  pub(crate) fn enforce_bit_zero(&self, b: &mut R1csBuilder, bit: usize) {
    let a = b.bit(self.bits[bit]);
    let zero = b.constant(F128::ZERO);
    b.equal(a, zero);
  }
}

pub(crate) fn alloc_words_in_phase<const N: usize>(
  b: &mut R1csBuilder,
  words: [u32; N],
  _: ConstraintPhase,
) -> Result<[Word32; N], R1csError> {
  // Keep complete four-limb words together so compression input packing is a
  // wire alias and does not introduce unnecessary decompositions.
  let mut result = Vec::with_capacity(N);
  for chunk in words.chunks(4) {
    let packed = std::array::from_fn(|i| chunk.get(i).copied().unwrap_or(0));
    let index = b.alloc(ixby_flock::hash::pack4(packed));
    for (limb, &value) in chunk.iter().enumerate() {
      result.push(Word32 {
        value,
        bits: std::array::from_fn(|i| Variable::Word {
          word: index,
          bit: u8::try_from(32 * limb + i).expect("bit below 128"),
        }),
      });
    }
  }
  result.try_into().map_err(|_| R1csError::InternalShape)
}
pub(crate) fn constrain_compression(
  b: &mut R1csBuilder,
  cv: [Word32; 8],
  message: [Word32; 16],
  counter: u64,
  length: u32,
  flags: u32,
) -> Result<[Word32; 16], R1csError> {
  constrain_compression_in_phase(
    b,
    cv,
    message,
    counter,
    length,
    flags,
    ConstraintPhase::Transcript,
  )
}
pub(crate) fn constrain_compression_in_phase(
  b: &mut R1csBuilder,
  cv: [Word32; 8],
  message: [Word32; 16],
  counter: u64,
  length: u32,
  flags: u32,
  _: ConstraintPhase,
) -> Result<[Word32; 16], R1csError> {
  let mut input = Vec::with_capacity(7);
  for words in cv.as_slice().chunks(4).chain(message.as_slice().chunks(4)) {
    input.push(b.pack(&std::array::from_fn(|i| words[i / 32].bits[i % 32])));
  }
  input.push(b.constant(ixby_flock::hash::pack_params(counter, length, flags)));
  let output = b.compress(input.try_into().unwrap());
  Ok(std::array::from_fn(|i| {
    let word = output[i / 4];
    Word32 {
      value: ixby_flock::hash::unpack4(b.values[word])[i % 4],
      bits: std::array::from_fn(|bit| Variable::Word {
        word,
        bit: u8::try_from(32 * (i % 4) + bit).expect("bit below 128"),
      }),
    }
  }))
}

pub(crate) fn select_digest(
  b: &mut R1csBuilder,
  selector: Variable,
  left: &[Word32; 8],
  right: &[Word32; 8],
) -> [Word32; 8] {
  let selector = b.bit(selector);
  let output: [usize; 2] = std::array::from_fn(|half| {
    let left =
      b.pack(&std::array::from_fn(|i| left[4 * half + i / 32].bits[i % 32]));
    let right =
      b.pack(&std::array::from_fn(|i| right[4 * half + i / 32].bits[i % 32]));
    let delta = b.add(left, right);
    let output = b.alloc(b.values[left] + b.values[selector] * b.values[delta]);
    b.graph.macs.push([selector, delta, left, output]);
    output
  });
  std::array::from_fn(|i| {
    let word = output[i / 4];
    Word32 {
      value: ixby_flock::hash::unpack4(b.values[word])[i % 4],
      bits: std::array::from_fn(|bit| Variable::Word {
        word,
        bit: u8::try_from(32 * (i % 4) + bit).expect("bit below 128"),
      }),
    }
  })
}
