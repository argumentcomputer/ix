//! Bit-constrained arithmetic for the remaining existing crypto-v0 word
//! opcodes. No result or partial product is supplied as witness advice.

use crate::{
  boolean::BooleanR1csBuilder,
  ixby::bits::{add, any, not, subtract},
};

/// Results in EXTRA_WORD_PRIMITIVES order: sub, mul, shl, shr, rotr.
pub(super) fn operations(
  b: &mut BooleanR1csBuilder,
  one: usize,
  zero: usize,
  a: &[usize],
  c: &[usize],
) -> [Vec<usize>; 5] {
  assert_eq!(a.len(), 32);
  assert_eq!(c.len(), 32);
  let sub = subtract(b, one, zero, a, c).0;
  // Schoolbook multiplication modulo 2^32. Bits below each shifted partial
  // product cannot change; carries above bit 31 are deliberately discarded.
  let mut mul: Vec<_> = a.iter().map(|bit| b.and(*bit, c[0])).collect();
  for shift in 1..32 {
    let partial: Vec<_> =
      a[..32 - shift].iter().map(|bit| b.and(*bit, c[shift])).collect();
    let sum = add(b, one, zero, &mul[shift..], &partial).0;
    mul[shift..].copy_from_slice(&sum);
  }
  let mut shl = barrel(b, one, zero, a, c, false, false);
  let mut shr = barrel(b, one, zero, a, c, true, false);
  let rotr = barrel(b, one, zero, a, c, true, true);
  // Unlike rotate, the reference shifts do not mask the count modulo 32.
  let high = any(b, one, &c[5..]);
  let in_range = not(b, one, high);
  for bit in shl.iter_mut().chain(&mut shr) {
    *bit = b.and(in_range, *bit);
  }
  [sub, mul, shl, shr, rotr]
}

fn barrel(
  b: &mut BooleanR1csBuilder,
  one: usize,
  zero: usize,
  a: &[usize],
  count: &[usize],
  right: bool,
  rotate: bool,
) -> Vec<usize> {
  let mut current = a.to_vec();
  for (stage, flag) in count[..5].iter().enumerate() {
    let distance = 1usize << stage;
    current = (0..32)
      .map(|index| {
        let source =
          if right { index + distance } else { index + 32 - distance };
        let shifted =
          if rotate || (if right { source < 32 } else { source >= 32 }) {
            current[source % 32]
          } else {
            zero
          };
        let difference = b.xor(&[current[index], shifted], one);
        let selected = b.and(*flag, difference);
        b.xor(&[current[index], selected], one)
      })
      .collect();
  }
  current
}
