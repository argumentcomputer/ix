//! Integer algorithms over constrained Boolean wires. In particular neither
//! F128 field addition nor Word32 wrapping implements these Nat operations.
use super::bits::Synthesis;
use crate::ixby::bits::{add, any, equal, subtract};

/// Full 2n-bit product. Keeping the upper half makes overflow unambiguous.
fn multiply(s: &mut Synthesis, a: &[usize], b: &[usize]) -> Vec<usize> {
  let mut product = vec![s.zero; 2 * a.len()];
  for (shift, bit) in b.iter().enumerate() {
    let mut partial = vec![s.zero; 2 * a.len()];
    for (index, a) in a.iter().enumerate() {
      partial[shift + index] = s.and(*bit, *a);
    }
    product = add(&mut s.b, s.one, s.zero, &product, &partial).0;
  }
  product
}

/// Restoring division retains n+1 remainder bits before subtraction. A
/// zero divisor explicitly disables every quotient bit, giving q=0, r=a.
/// No quotient/remainder or acceptance flag is provided as host advice.
fn divide(
  s: &mut Synthesis,
  a: &[usize],
  b: &[usize],
) -> (Vec<usize>, Vec<usize>) {
  let n = a.len();
  let nonzero = any(&mut s.b, s.one, b);
  let mut divisor = b.to_vec();
  divisor.push(s.zero);
  let mut remainder = vec![s.zero; n + 1];
  let mut quotient = vec![s.zero; n];
  for bit in (0..n).rev() {
    remainder.rotate_right(1);
    remainder[0] = a[bit];
    let (difference, borrow) =
      subtract(&mut s.b, s.one, s.zero, &remainder, &divisor);
    let enough = s.not(borrow);
    let take = s.and(nonzero, enough);
    quotient[bit] = take;
    remainder = s.mux(take, &difference, &remainder);
  }
  (quotient, remainder[..n].to_vec())
}

pub(super) struct Arithmetic {
  pub magnitude: Vec<usize>,
  pub comparison: usize,
  pub predecessor: Vec<usize>,
  pub nonzero: usize,
}

pub(super) fn evaluate(
  s: &mut Synthesis,
  a: &[usize],
  b: &[usize],
  selected: &[usize; 7],
  admitted: [bool; 7],
) -> Arithmetic {
  assert_eq!(a.len(), b.len());
  let n = a.len();
  let empty = vec![s.zero; n];
  let mut results = vec![empty.clone(); 5];
  if admitted[0] {
    let (sum, carry) = add(&mut s.b, s.one, s.zero, a, b);
    let bad = s.and(selected[0], carry);
    s.violations.push(bad);
    results[0] = sum;
  }
  let (difference, borrow) = subtract(&mut s.b, s.one, s.zero, a, b);
  if admitted[1] {
    let positive = s.not(borrow);
    results[1] = s.mask(positive, &difference);
  }
  if admitted[2] {
    let product = multiply(s, a, b);
    s.require_zero(selected[2], &product[n..]);
    results[2] = product[..n].to_vec();
  }
  if admitted[3] || admitted[4] {
    let (quotient, remainder) = divide(s, a, b);
    results[3] = quotient;
    results[4] = remainder;
  }
  let terms: Vec<_> = results
    .iter()
    .zip(selected)
    .map(|(bits, flag)| (*flag, bits.as_slice()))
    .collect();
  let magnitude = s.choose(&terms);
  let same = equal(&mut s.b, s.one, a, b);
  let eq = s.and(selected[5], same);
  let lt = s.and(selected[6], borrow);
  let comparison = s.sum(&[eq, lt]);
  let nonzero = any(&mut s.b, s.one, a);
  let one = s.constant(n, 1);
  let predecessor = subtract(&mut s.b, s.one, s.zero, a, &one).0;
  Arithmetic { magnitude, comparison, predecessor, nonzero }
}

pub(super) fn magnitude_length(
  s: &mut Synthesis,
  bits: &[usize],
) -> Vec<usize> {
  let mut length = vec![s.zero; 32];
  let mut higher_zero = s.one;
  for (byte, bits) in bits.chunks(8).enumerate().rev() {
    let nonzero = any(&mut s.b, s.one, bits);
    let last = s.and(higher_zero, nonzero);
    for (bit, target) in length.iter_mut().enumerate() {
      if (byte + 1) & (1usize << bit) != 0 {
        *target = s.sum(&[*target, last]);
      }
    }
    let empty = s.not(nonzero);
    higher_zero = s.and(higher_zero, empty);
  }
  length
}
