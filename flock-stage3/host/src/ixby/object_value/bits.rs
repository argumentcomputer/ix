use super::ObjectLayout;
use crate::{
  boolean::{BooleanR1csBuilder, BooleanR1csPlan},
  ixby::{
    bits::{
      any, bounded_prefix, constant_bits, equal, equal_constant, not, require,
      require_zero, select, subtract,
    },
    value::{cell_with_nat_handles, cell_with_object_handles},
  },
};

pub(super) struct Synthesis {
  pub b: BooleanR1csBuilder,
  pub one: usize,
  pub zero: usize,
  pub violations: Vec<usize>,
  pub layout: ObjectLayout,
}

impl Synthesis {
  pub(super) fn new(
    inputs: usize,
    outputs: usize,
    extra: usize,
    layout: ObjectLayout,
  ) -> Self {
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
    Self { b, one, zero, violations: Vec::new(), layout }
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
  pub(super) fn equal(&mut self, a: &[usize], b: &[usize]) -> usize {
    equal(&mut self.b, self.one, a, b)
  }
  pub(super) fn require(&mut self, enabled: usize, good: usize) {
    require(&mut self.b, self.one, &mut self.violations, enabled, good);
  }
  pub(super) fn require_zero(&mut self, enabled: usize, bits: &[usize]) {
    require_zero(&mut self.b, self.one, &mut self.violations, enabled, bits);
  }
  pub(super) fn less(&mut self, a: &[usize], b: &[usize]) -> usize {
    subtract(&mut self.b, self.one, self.zero, a, b).1
  }
  pub(super) fn mask(&mut self, enabled: usize, bits: &[usize]) -> Vec<usize> {
    bits.iter().map(|bit| self.and(enabled, *bit)).collect()
  }
  pub(super) fn choose(&mut self, sources: &[(usize, &[usize])]) -> Vec<usize> {
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
  pub(super) fn prefix(&mut self, length: &[usize], max: usize) -> Vec<usize> {
    bounded_prefix(&mut self.b, self.one, &mut self.violations, length, max)
  }
  pub(super) fn cell(&mut self, enabled: usize, value: &[usize]) -> [usize; 8] {
    if self.layout.nat_capacity.is_some() {
      return cell_with_nat_handles(
        &mut self.b,
        self.one,
        &mut self.violations,
        enabled,
        value,
        self.layout.byte_entries(),
        Some(self.layout.entries()),
      );
    }
    let f = cell_with_object_handles(
      &mut self.b,
      self.one,
      &mut self.violations,
      enabled,
      value,
      self.layout.byte_entries(),
      self.layout.entries(),
    );
    [f[0], f[1], f[2], f[3], f[4], f[5], f[6], self.zero]
  }
  pub(super) fn select(
    &mut self,
    sources: &[(usize, usize)],
    width: usize,
  ) -> Vec<usize> {
    select(&mut self.b, self.one, self.zero, sources, width)
  }
  pub(super) fn declaration(
    &mut self,
    index: &[usize],
    enabled: usize,
    base: usize,
  ) -> Vec<usize> {
    let in_range = self.less(index, &(base..base + 32).collect::<Vec<_>>());
    self.require(enabled, in_range);
    let sources: Vec<_> = (0..self.layout.capacity.constructors())
      .map(|i| {
        let matched = self.eq_const(index, i as u64);
        (self.and(enabled, matched), base + 128 * (1 + 4 * i))
      })
      .collect();
    let decl = self.select(&sources, 512);
    self.require(enabled, decl[416]);
    decl
  }
  pub(super) fn record(
    &mut self,
    value: &[usize],
    enabled: usize,
    arena: usize,
    declarations: usize,
  ) -> Vec<usize> {
    let cell = self.cell(enabled, value);
    self.require(enabled, cell[6]);
    let width = 128 * self.layout.record_words();
    let sources: Vec<_> = (0..self.layout.entries())
      .map(|i| {
        let matched = self.eq_const(&value[128..160], i as u64);
        (self.and(enabled, matched), arena + i * width)
      })
      .collect();
    let record = self.select(&sources, width);
    self.require(enabled, record[64]);
    self.require_zero(self.one, &record[65..128]);
    let decl = self.declaration(&record[..32], enabled, declarations);
    let same = self.equal(&record[32..64], &decl[384..416]);
    self.require(enabled, same);
    let live = self.prefix(&record[32..64], self.layout.fields);
    for (index, flag) in live.iter().enumerate() {
      self.cell(*flag, &record[128 + 256 * index..384 + 256 * index]);
    }
    record
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
  pub(super) fn bounded_constant(
    &mut self,
    bits: &[usize],
    maximum: usize,
    enabled: usize,
  ) {
    let limit = constant_bits(self.one, self.zero, maximum as u32 + 1);
    let valid = self.less(bits, &limit);
    self.require(enabled, valid);
  }
}
