use super::{AFTER, BEFORE, OrderKind, PAD, SEAL, SEED};
use crate::{
  boolean::{BooleanR1csBuilder as Builder, BooleanR1csPlan},
  ixby::bits::{any, equal, equal_constant, not, require, require_zero},
};

fn word(i: usize) -> Vec<usize> {
  (128 * i..128 * (i + 1)).collect()
}
fn constant(b: &mut Builder, one: usize, i: usize, value: u64) -> usize {
  let bits = word(i);
  let lo = equal_constant(b, one, &bits[..64], value);
  let hi = equal_constant(b, one, &bits[64..], 0);
  b.and(lo, hi)
}
fn increment(
  b: &mut Builder,
  one: usize,
  bits: &[usize],
) -> (Vec<usize>, usize) {
  let mut carry = one;
  let result = bits
    .iter()
    .map(|&bit| {
      let sum = b.xor(&[bit, carry], one);
      carry = b.and(bit, carry);
      sum
    })
    .collect();
  (result, carry)
}
fn output(b: &mut Builder, one: usize, zero: usize, at: usize, bits: &[usize]) {
  for i in 0..128 {
    b.write_xor(at * 128 + i, &[bits.get(i).copied().unwrap_or(zero)], one);
  }
}
fn masked(b: &mut Builder, flag: usize, bits: &[usize]) -> Vec<usize> {
  bits.iter().map(|&x| b.and(flag, x)).collect()
}
pub(super) fn build(kind: OrderKind) -> BooleanR1csPlan {
  let (inputs, outputs, k) = match kind {
    OrderKind::Prepare(n) => (2 + 2 * n, 5, 16),
    OrderKind::Audit(n) => (2 * (n + 2) + 2, 1, 16),
    OrderKind::Access => (7, 6, 14),
  };
  let mut b = Builder::new(k, (inputs + outputs) * 128);
  for bit in 0..inputs * 128 {
    b.free_boolean_at(bit);
  }
  let one = b.alloc_constant_one();
  let zero = b.xor(&[one, one], one);
  let mut bad = Vec::new();
  match kind {
    OrderKind::Prepare(n) => {
      let enabled = 0;
      let disabled = not(&mut b, one, enabled);
      bad.extend(1..128);
      bad.extend(128 + 64..256);
      require_zero(
        &mut b,
        one,
        &mut bad,
        disabled,
        &(128..(2 + 2 * n) * 128).collect::<Vec<_>>(),
      );
      let (next, overflow) = increment(&mut b, one, &word(1)[..64]);
      require_zero(&mut b, one, &mut bad, enabled, &[overflow]);
      let before = masked(&mut b, enabled, &word(1));
      let after = masked(&mut b, enabled, &next);
      output(&mut b, one, zero, inputs, &before);
      output(&mut b, one, zero, inputs + 1, &[zero, enabled, disabled]);
      output(&mut b, one, zero, inputs + 2, &after);
      output(&mut b, one, zero, inputs + 3, &[enabled, zero, disabled]);
    },
    OrderKind::Audit(n) => {
      let width = n + 2;
      let current = width;
      let first = 2 * width * 128;
      let last = first + 128;
      bad.extend(first + 1..first + 128);
      bad.extend(last + 1..last + 128);
      bad.extend(current * 128 + 64..(current + 1) * 128);
      let pk =
        [SEED, AFTER, BEFORE, SEAL, PAD].map(|v| constant(&mut b, one, 1, v));
      let ck = [SEED, AFTER, BEFORE, SEAL, PAD]
        .map(|v| constant(&mut b, one, current + 1, v));
      let valid = any(&mut b, one, &ck);
      require(&mut b, one, &mut bad, one, valid);
      let [seed, after, before, seal, pad] = ck;
      require_zero(&mut b, one, &mut bad, pad, &word(current));
      for i in 2..width {
        require_zero(&mut b, one, &mut bad, pad, &word(current + i));
      }
      require(&mut b, one, &mut bad, first, seed);
      let final_kind = any(&mut b, one, &[seal, pad]);
      require(&mut b, one, &mut bad, last, final_kind);
      let following = not(&mut b, one, first);
      // Seed->Before, Before->After, After->Before/Seal, Seal->Pad, Pad->Pad.
      let ab = any(&mut b, one, &[before, seal]);
      let allowed = [
        (pk[0], before),
        (pk[2], after),
        (pk[1], ab),
        (pk[3], pad),
        (pk[4], pad),
      ]
      .map(|(p, c)| b.and(p, c));
      let allowed = any(&mut b, one, &allowed);
      require(&mut b, one, &mut bad, following, allowed);
      let same = any(&mut b, one, &[pk[0], pk[1]]);
      let same = b.and(following, same);
      let clocks_equal = equal(&mut b, one, &word(0), &word(current));
      require(&mut b, one, &mut bad, same, clocks_equal);
      for i in 2..width {
        let eq = equal(&mut b, one, &word(i), &word(current + i));
        require(&mut b, one, &mut bad, same, eq);
      }
      let step = b.and(following, pk[2]);
      let (next, overflow) = increment(&mut b, one, &word(0)[..64]);
      let next_equal = equal(&mut b, one, &next, &word(current)[..64]);
      require(&mut b, one, &mut bad, step, next_equal);
      require_zero(&mut b, one, &mut bad, step, &[overflow]);
    },
    OrderKind::Access => {
      let enabled = 0;
      let disabled = not(&mut b, one, enabled);
      bad.extend(1..128);
      bad.extend(128 + 59..256);
      bad.extend(256 + 5..384);
      bad.extend(384 + 64..512);
      bad.extend(512 + 1..640);
      let clock_max =
        equal_constant(&mut b, one, &word(1)[..59], (1u64 << 59) - 1);
      require_zero(&mut b, one, &mut bad, enabled, &[clock_max]);
      for i in [1, 3, 4, 5, 6] {
        require_zero(&mut b, one, &mut bad, disabled, &word(i));
      }
      let packed =
        word(2)[..5].iter().chain(&word(1)[..59]).copied().collect::<Vec<_>>();
      let (time, _) = increment(&mut b, one, &packed);
      let time = masked(&mut b, enabled, &time);
      let address = masked(&mut b, enabled, &word(3));
      output(&mut b, one, zero, inputs, &address);
      output(&mut b, one, zero, inputs + 1, &time);
      let write = b.and(enabled, 512);
      let read = b.xor(&[enabled, write], one);
      output(&mut b, one, zero, inputs + 2, &[read, write, disabled]);
      for i in 0..2 {
        let value = masked(&mut b, enabled, &word(5 + i));
        output(&mut b, one, zero, inputs + 3 + i, &value);
      }
    },
  }
  let invalid = any(&mut b, one, &bad);
  output(&mut b, one, zero, inputs + outputs - 1, &[invalid]);
  b.finish()
}
