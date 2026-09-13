//! Boolean synthesis helpers. Every reference names a constrained bit; `one`
//! must be the table's count-aware Flock constant pin, not free advice.

use crate::boolean::BooleanR1csBuilder;

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
