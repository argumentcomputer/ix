//! Boolean synthesis helpers. Every reference names a constrained bit; `one`
//! must be the table's count-aware Flock constant pin, not free advice.

use crate::boolean::{BooleanR1csBuilder, BooleanR1csPlan, write_f128};
use flock_prover::field::F128;

pub(super) fn fill_words(words: &[F128], bits: &mut [bool]) {
  for (word, value) in words.iter().enumerate() {
    write_f128(bits, word * 128, *value);
  }
}

pub(super) fn read_words(
  bits: &[bool],
  start: usize,
  count: usize,
) -> Vec<F128> {
  (start..start + count)
    .map(|word| {
      let mut value = F128::ZERO;
      for bit in 0..64 {
        value.lo |= u64::from(bits[word * 128 + bit]) << bit;
        value.hi |= u64::from(bits[word * 128 + 64 + bit]) << bit;
      }
      value
    })
    .collect()
}

/// Total untrusted witness evaluation, not a verifier/host admission test.
pub(super) fn evaluate_words(
  plan: &BooleanR1csPlan,
  input: &[F128],
  outputs: usize,
) -> Vec<F128> {
  let mut bits = vec![false; plan.k()];
  plan.fill_row(&mut bits, |bits| fill_words(input, bits));
  read_words(&bits, input.len(), outputs)
}

pub(super) fn not(b: &mut BooleanR1csBuilder, one: usize, bit: usize) -> usize {
  b.xor(&[bit, one], one)
}

pub(super) fn or(
  b: &mut BooleanR1csBuilder,
  one: usize,
  x: usize,
  y: usize,
) -> usize {
  let product = b.and(x, y);
  b.xor(&[x, y, product], one)
}

pub(super) fn any(
  b: &mut BooleanR1csBuilder,
  one: usize,
  bits: &[usize],
) -> usize {
  let mut none = one;
  for bit in bits {
    none = b.product_of_parities(&[none], &[*bit, one]);
  }
  not(b, one, none)
}

pub(super) fn equal_constant(
  b: &mut BooleanR1csBuilder,
  one: usize,
  bits: &[usize],
  value: u64,
) -> usize {
  assert!(bits.len() <= 64);
  assert!(bits.len() == 64 || value < (1u64 << bits.len()));
  let mut equal = one;
  for (position, bit) in bits.iter().enumerate() {
    equal = if value & (1 << position) != 0 {
      b.and(equal, *bit)
    } else {
      b.product_of_parities(&[equal], &[*bit, one])
    };
  }
  equal
}

/// Little-endian subtraction with a final unsigned borrow, without wrapping
/// the comparison itself. The two borrow products are mutually exclusive.
pub(super) fn subtract(
  b: &mut BooleanR1csBuilder,
  one: usize,
  zero: usize,
  x: &[usize],
  y: &[usize],
) -> (Vec<usize>, usize) {
  assert_eq!(x.len(), y.len());
  let mut borrow = zero;
  let mut difference = Vec::with_capacity(x.len());
  for (&x, &y) in x.iter().zip(y) {
    difference.push(b.xor(&[x, y, borrow], one));
    let first = b.product_of_parities(&[x, one], &[y]);
    let second = b.product_of_parities(&[x, y, one], &[borrow]);
    borrow = b.xor(&[first, second], one);
  }
  (difference, borrow)
}

pub(super) fn constant_bits(one: usize, zero: usize, value: u32) -> Vec<usize> {
  (0..32).map(|bit| if value & (1 << bit) == 0 { zero } else { one }).collect()
}

pub(super) fn equal(
  b: &mut BooleanR1csBuilder,
  one: usize,
  a: &[usize],
  rhs: &[usize],
) -> usize {
  assert_eq!(a.len(), rhs.len());
  let mut result = one;
  for (a, rhs) in a.iter().zip(rhs) {
    result = b.product_of_parities(&[result], &[*a, *rhs, one]);
  }
  result
}

/// The caller derives mutually exclusive selectors, never free advice bits.
pub(super) fn select(
  b: &mut BooleanR1csBuilder,
  one: usize,
  zero: usize,
  sources: &[(usize, usize)],
  width: usize,
) -> Vec<usize> {
  (0..width)
    .map(|bit| {
      let products: Vec<_> =
        sources.iter().map(|(flag, base)| b.and(*flag, base + bit)).collect();
      if products.is_empty() { zero } else { b.xor(&products, one) }
    })
    .collect()
}

pub(super) fn require(
  b: &mut BooleanR1csBuilder,
  one: usize,
  violations: &mut Vec<usize>,
  enabled: usize,
  good: usize,
) {
  let bad = not(b, one, good);
  violations.push(b.and(enabled, bad));
}

pub(super) fn require_zero(
  b: &mut BooleanR1csBuilder,
  one: usize,
  violations: &mut Vec<usize>,
  enabled: usize,
  bits: &[usize],
) {
  let nonzero = any(b, one, bits);
  violations.push(b.and(enabled, nonzero));
}

/// Little-endian addition with the carry retained separately. The two carry
/// products are mutually exclusive, so their XOR is the ordinary carry bit.
pub(super) fn add(
  b: &mut BooleanR1csBuilder,
  one: usize,
  zero: usize,
  x: &[usize],
  y: &[usize],
) -> (Vec<usize>, usize) {
  assert_eq!(x.len(), y.len());
  let mut carry = zero;
  let mut sum = Vec::with_capacity(x.len());
  for (&x, &y) in x.iter().zip(y) {
    sum.push(b.xor(&[x, y, carry], one));
    let first = b.and(x, y);
    let second = b.product_of_parities(&[x, y], &[carry]);
    carry = b.xor(&[first, second], one);
  }
  (sum, carry)
}
