use crate::boolean::{BooleanR1csBuilder, BooleanR1csPlan};
use crate::ixby::bits::{add, any, equal_constant, not, subtract};

pub(super) type Bits = Vec<usize>;

/// Capacity-only upper bound, including range checks and full padding. The
/// source window has at most 248 bits, selected from fixed 16-byte words;
/// four binary shifts replace a free one-hot byte-window selector.
pub(super) fn columns_bound(
  bytes: usize,
  reads: usize,
  extra: usize,
  reserved: usize,
) -> usize {
  reserved
    + 128 * (bytes + 1)
    + reads * (320 * bytes.div_ceil(16) + 4096)
    + extra
}

pub(super) struct Decoder {
  pub b: BooleanR1csBuilder,
  pub one: usize,
  pub zero: usize,
  data_words: usize,
  length: Bits,
  cursor: Bits,
  violations: Vec<usize>,
}

impl Decoder {
  pub(super) fn new(
    capacity: usize,
    input_words: usize,
    output_words: usize,
    reads: usize,
    extra: usize,
  ) -> Self {
    let reserved = 128 * (input_words + output_words);
    let columns =
      columns_bound(capacity, reads, extra, reserved).next_power_of_two();
    let mut b = BooleanR1csBuilder::new(columns.ilog2() as usize, reserved);
    for bit in 0..input_words * 128 {
      b.free_boolean_at(bit);
    }
    let one = b.alloc_constant_one();
    let zero = b.xor(&[one, one], one);
    let mut decoder = Self {
      b,
      one,
      zero,
      data_words: capacity.div_ceil(16),
      length: (0..32).collect(),
      cursor: vec![zero; 32],
      violations: (32..128).collect(),
    };
    let lengths = decoder.bounded(&decoder.length.clone(), capacity, one);
    for byte in 0..decoder.data_words * 16 {
      let live =
        if byte < capacity { decoder.sum(&lengths[byte + 1..]) } else { zero };
      let inactive = decoder.not(live);
      let value: Vec<_> = (128 + 8 * byte..136 + 8 * byte).collect();
      let nonzero = decoder.any(&value);
      let bad = decoder.and(inactive, nonzero);
      decoder.violate(bad);
    }
    decoder
  }

  pub(super) fn constant(&self, width: usize, value: u64) -> Bits {
    assert!(width >= 64 || value < 1u64 << width);
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
  pub(super) fn not(&mut self, a: usize) -> usize {
    not(&mut self.b, self.one, a)
  }
  pub(super) fn any(&mut self, bits: &[usize]) -> usize {
    any(&mut self.b, self.one, bits)
  }
  /// Only for mutually exclusive terms (or explicitly GF(2) bit arithmetic).
  pub(super) fn sum(&mut self, bits: &[usize]) -> usize {
    if bits.is_empty() { self.zero } else { self.b.xor(bits, self.one) }
  }
  pub(super) fn eq_const(&mut self, bits: &[usize], value: u64) -> usize {
    equal_constant(&mut self.b, self.one, bits, value)
  }
  pub(super) fn equal(&mut self, first: &[usize], second: &[usize]) -> usize {
    assert_eq!(first.len(), second.len());
    let mut equal = self.one;
    for (a, b) in first.iter().zip(second) {
      equal = self.b.product_of_parities(&[equal], &[*a, *b, self.one]);
    }
    equal
  }
  pub(super) fn less(&mut self, first: &[usize], second: &[usize]) -> usize {
    subtract(&mut self.b, self.one, self.zero, first, second).1
  }
  pub(super) fn violate(&mut self, bad: usize) {
    self.violations.push(bad);
  }
  pub(super) fn require(&mut self, enabled: usize, good: usize) {
    let bad = self.not(good);
    let bad = self.and(enabled, bad);
    self.violate(bad);
  }
  pub(super) fn require_zero(&mut self, enabled: usize, bits: &[usize]) {
    let nonzero = self.any(bits);
    let bad = self.and(enabled, nonzero);
    self.violate(bad);
  }
  pub(super) fn bounded(
    &mut self,
    bits: &[usize],
    maximum: usize,
    enabled: usize,
  ) -> Bits {
    let equal: Vec<_> =
      (0..=maximum).map(|value| self.eq_const(bits, value as u64)).collect();
    let valid = self.sum(&equal);
    self.require(enabled, valid);
    equal
  }
  pub(super) fn live(
    &mut self,
    counts: &[usize],
    index: usize,
    enabled: usize,
  ) -> usize {
    let live = self.sum(&counts[index + 1..]);
    self.and(enabled, live)
  }
  pub(super) fn choose(&mut self, terms: &[(usize, &[usize])]) -> Bits {
    assert!(!terms.is_empty());
    let width = terms[0].1.len();
    assert!(terms.iter().all(|(_, bits)| bits.len() == width));
    (0..width)
      .map(|bit| {
        let products: Vec<_> =
          terms.iter().map(|(flag, bits)| self.and(*flag, bits[bit])).collect();
        self.sum(&products)
      })
      .collect()
  }
  pub(super) fn pack(&self, lanes: &[&[usize]]) -> Bits {
    assert!(lanes.len() <= 4);
    let mut output = vec![self.zero; 128];
    for (index, lane) in lanes.iter().enumerate() {
      assert!(lane.len() <= 32);
      output[index * 32..index * 32 + lane.len()].copy_from_slice(lane);
    }
    output
  }
  pub(super) fn write(&mut self, word: usize, bits: &[usize]) {
    assert!(bits.len() <= 128);
    for bit in 0..128 {
      self.b.write_xor(
        word * 128 + bit,
        &[bits.get(bit).copied().unwrap_or(self.zero)],
        self.one,
      );
    }
  }

  fn window(&mut self, width: usize) -> Bits {
    assert!(matches!(width, 8 | 32 | 64 | 128));
    let address = self.cursor[4..].to_vec();
    let selected: Vec<_> = (0..self.data_words)
      .map(|word| self.eq_const(&address, word as u64))
      .collect();
    let mut source: Vec<_> = (0..120 + width)
      .map(|bit| {
        let products: Vec<_> = selected
          .iter()
          .enumerate()
          .filter_map(|(word, flag)| {
            let source_word = word + bit / 128;
            (source_word < self.data_words)
              .then(|| self.and(*flag, 128 + source_word * 128 + bit % 128))
          })
          .collect();
        self.sum(&products)
      })
      .collect();
    for shift_bit in 0..4 {
      let shift = 8 << shift_bit;
      source = (0..source.len() - shift)
        .map(|bit| {
          let delta = self.b.product_of_parities(
            &[self.cursor[shift_bit]],
            &[source[bit], source[bit + shift]],
          );
          self.sum(&[source[bit], delta])
        })
        .collect();
    }
    assert_eq!(source.len(), width);
    source
  }

  /// Disjoint flags select a byte width. Disabled fields consume no bytes and
  /// produce zero. The surrounding buffer's following bytes are not padding
  /// of this field: they are masked out, not incorrectly forced to zero.
  pub(super) fn read(
    &mut self,
    width: usize,
    choices: &[(usize, usize)],
  ) -> Bits {
    assert!(choices.iter().all(|(_, bytes)| 8 * bytes <= width));
    let source = self.window(width);
    let output: Vec<_> = (0..width)
      .map(|bit| {
        let enabled: Vec<_> = choices
          .iter()
          .filter(|(_, bytes)| bit < 8 * bytes)
          .map(|(flag, _)| *flag)
          .collect();
        let enabled = self.sum(&enabled);
        self.and(enabled, source[bit])
      })
      .collect();
    let increment: Vec<_> = (0..32)
      .map(|bit| {
        let set: Vec<_> = choices
          .iter()
          .filter(|(_, bytes)| bytes & (1usize << bit) != 0)
          .map(|(flag, _)| *flag)
          .collect();
        self.sum(&set)
      })
      .collect();
    let (next, carry) =
      add(&mut self.b, self.one, self.zero, &self.cursor, &increment);
    self.violate(carry);
    let overflow = self.less(&self.length.clone(), &next);
    self.violate(overflow);
    self.cursor = next;
    output
  }
  pub(super) fn byte(&mut self, enabled: usize) -> Bits {
    self.read(8, &[(enabled, 1)])
  }
  pub(super) fn u32(&mut self, enabled: usize) -> Bits {
    self.read(32, &[(enabled, 4)])
  }
  pub(super) fn header(&mut self, magic: &[u8; 4]) {
    let word = self.u32(self.one);
    let matched = self.eq_const(&word, u32::from_le_bytes(*magic) as u64);
    self.require(self.one, matched);
    let version = self.u32(self.one);
    self.require_zero(self.one, &version);
  }
  pub(super) fn finish(mut self, residual_word: usize) -> BooleanR1csPlan {
    let consumed = self.equal(&self.cursor.clone(), &self.length.clone());
    self.require(self.one, consumed);
    let violation = self.any(&self.violations.clone());
    self.write(residual_word, &[violation]);
    self.b.finish()
  }
}
