use crate::{
  boolean::{BooleanR1csBuilder, BooleanR1csPlan},
  ixby::bits::{any, equal, equal_constant, not, require, require_zero},
};

pub(super) type Bits = Vec<usize>;

pub(super) struct Builder {
  pub(super) b: BooleanR1csBuilder,
  pub(super) one: usize,
  pub(super) zero: usize,
  pub(super) violations: Vec<usize>,
}

pub(super) struct Natural {
  pub(super) value: Bits,
  pub(super) consumed: Bits,
  pub(super) live: Bits,
}

impl Builder {
  pub(super) fn new(inputs: usize, outputs: usize, columns: usize) -> Self {
    let mut b = BooleanR1csBuilder::new(
      columns.next_power_of_two().ilog2() as usize,
      128 * (inputs + outputs),
    );
    for bit in 0..inputs * 128 {
      b.free_boolean_at(bit);
    }
    let one = b.alloc_constant_one();
    let zero = b.xor(&[one, one], one);
    Self { b, one, zero, violations: Vec::new() }
  }

  pub(super) fn constant(&self, width: usize, value: u64) -> Bits {
    assert!(width >= 64 || value < 1u64 << width);
    (0..width)
      .map(|bit| {
        if bit < 64 && value & (1 << bit) != 0 { self.one } else { self.zero }
      })
      .collect()
  }

  pub(super) fn not(&mut self, bit: usize) -> usize {
    not(&mut self.b, self.one, bit)
  }

  pub(super) fn any(&mut self, bits: &[usize]) -> usize {
    any(&mut self.b, self.one, bits)
  }

  pub(super) fn sum(&mut self, bits: &[usize]) -> usize {
    if bits.is_empty() { self.zero } else { self.b.xor(bits, self.one) }
  }

  pub(super) fn equal(&mut self, first: &[usize], second: &[usize]) -> usize {
    equal(&mut self.b, self.one, first, second)
  }

  pub(super) fn eq_const(&mut self, bits: &[usize], value: u64) -> usize {
    equal_constant(&mut self.b, self.one, bits, value)
  }

  pub(super) fn require(&mut self, enabled: usize, good: usize) {
    require(&mut self.b, self.one, &mut self.violations, enabled, good);
  }

  pub(super) fn require_zero(&mut self, enabled: usize, bits: &[usize]) {
    require_zero(&mut self.b, self.one, &mut self.violations, enabled, bits);
  }

  pub(super) fn write(&mut self, word: usize, bits: &[usize]) {
    assert!(bits.len() <= 128);
    for bit in 0..128 {
      self.b.write_xor(
        128 * word + bit,
        &[bits.get(bit).copied().unwrap_or(self.zero)],
        self.one,
      );
    }
  }

  /// First-terminator decoding of a fixed lookahead window. Every live flag
  /// comes from the preceding continuation bit. Following fields are ignored,
  /// not incorrectly required to be zero. A whole-payload caller additionally
  /// checks exact consumed length and zeroes bytes outside the live prefix.
  pub(super) fn natural(
    &mut self,
    bytes: &[usize],
    enabled: usize,
    bits: usize,
  ) -> Natural {
    let count = bits.div_ceil(7).max(1);
    assert_eq!(bytes.len(), count * 8);
    let mut live = enabled;
    let mut value = vec![self.zero; bits];
    let mut lives = Vec::with_capacity(count);
    let mut ends = Vec::with_capacity(count);
    for (index, byte) in bytes.as_chunks::<8>().0.iter().enumerate() {
      lives.push(live);
      let last = self.not(byte[7]);
      let end = self.b.and(live, last);
      ends.push(end);
      if index != 0 {
        let nonzero = self.any(&byte[..7]);
        self.require(end, nonzero);
      }
      for (bit, source) in byte[..7].iter().enumerate() {
        let target = 7 * index + bit;
        if target < bits {
          value[target] = self.b.and(live, *source);
        } else {
          self.require_zero(live, &[*source]);
        }
      }
      live = self.b.and(live, byte[7]);
    }
    // An active natural must terminate within the admitted bit capacity.
    self.violations.push(live);
    let consumed = (0..64)
      .map(|bit| {
        let set: Vec<_> = ends
          .iter()
          .enumerate()
          .filter_map(|(index, flag)| {
            ((index as u64 + 1) & (1u64 << bit) != 0).then_some(*flag)
          })
          .collect();
        self.sum(&set)
      })
      .collect();
    Natural { value, consumed, live: lives }
  }

  pub(super) fn finish(mut self, residual_word: usize) -> BooleanR1csPlan {
    let residual = self.any(&self.violations.clone());
    self.write(residual_word, &[residual]);
    self.b.finish()
  }
}
