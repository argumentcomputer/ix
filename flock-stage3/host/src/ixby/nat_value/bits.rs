use crate::{
  boolean::{BooleanR1csBuilder, BooleanR1csPlan},
  ixby::bits::{any, equal_constant, not, require, require_zero},
};

pub(super) struct Synthesis {
  pub b: BooleanR1csBuilder,
  pub one: usize,
  pub zero: usize,
  pub violations: Vec<usize>,
}

impl Synthesis {
  pub(super) fn new(inputs: usize, outputs: usize, extra: usize) -> Self {
    let reserved = 128 * (inputs + outputs);
    let mut b = BooleanR1csBuilder::new(
      (reserved + extra).next_power_of_two().ilog2() as usize,
      reserved,
    );
    for bit in 0..128 * inputs {
      b.free_boolean_at(bit);
    }
    let one = b.alloc_constant_one();
    let zero = b.xor(&[one, one], one);
    Self { b, one, zero, violations: Vec::new() }
  }
  pub(super) fn constant(&self, width: usize, value: u64) -> Vec<usize> {
    (0..width)
      .map(|bit| {
        if bit < 64 && value & (1u64 << bit) != 0 {
          self.one
        } else {
          self.zero
        }
      })
      .collect()
  }
  pub(super) fn and(&mut self, a: usize, b: usize) -> usize {
    self.b.and(a, b)
  }
  pub(super) fn not(&mut self, bit: usize) -> usize {
    not(&mut self.b, self.one, bit)
  }
  pub(super) fn sum(&mut self, bits: &[usize]) -> usize {
    if bits.is_empty() { self.zero } else { self.b.xor(bits, self.one) }
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
  pub(super) fn mask(&mut self, enabled: usize, bits: &[usize]) -> Vec<usize> {
    bits.iter().map(|bit| self.and(enabled, *bit)).collect()
  }
  pub(super) fn choose(&mut self, sources: &[(usize, &[usize])]) -> Vec<usize> {
    assert!(!sources.is_empty());
    assert!(sources.iter().all(|(_, bits)| bits.len() == sources[0].1.len()));
    (0..sources[0].1.len())
      .map(|bit| {
        let products: Vec<_> = sources
          .iter()
          .map(|(flag, bits)| self.and(*flag, bits[bit]))
          .collect();
        self.sum(&products)
      })
      .collect()
  }
  pub(super) fn mux(
    &mut self,
    flag: usize,
    yes: &[usize],
    no: &[usize],
  ) -> Vec<usize> {
    assert_eq!(yes.len(), no.len());
    yes
      .iter()
      .zip(no)
      .map(|(yes, no)| {
        let delta = self.b.product_of_parities(&[flag], &[*yes, *no]);
        self.sum(&[*no, delta])
      })
      .collect()
  }
  pub(super) fn write(&mut self, start: usize, bits: &[usize]) {
    for (bit, source) in bits.iter().enumerate() {
      self.b.write_xor(start + bit, &[*source], self.one);
    }
  }
  pub(super) fn finish(mut self, residual: usize) -> BooleanR1csPlan {
    let violation = any(&mut self.b, self.one, &self.violations);
    self.b.write_xor(residual, &[violation], self.one);
    self.b.finish()
  }
}
