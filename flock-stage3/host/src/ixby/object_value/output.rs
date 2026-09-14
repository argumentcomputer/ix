//! Derive canonical output bytes by a bounded preorder traversal. All selected
//! records come from the wired immutable arenas; no serialization is advice.
use super::{ObjectLayout, bits::Synthesis};
use crate::{
  boolean::BooleanR1csPlan,
  ixby::{bits::add, byte_value::ByteCapacity, control::ControlCapacities},
};

struct Encoder {
  s: Synthesis,
  bytes: ByteCapacity,
  capacity: usize,
  declarations: usize,
  arena: usize,
  byte_arena: usize,
  cursor: Vec<usize>,
  nodes: Vec<usize>,
  output: Vec<usize>,
}

impl Encoder {
  fn buffer(&mut self, value: &[usize], enabled: usize) -> Vec<usize> {
    let width = 128 * self.bytes.record_words();
    let sources: Vec<_> = (0..self.s.layout.byte_entries())
      .map(|index| {
        let matched = self.s.eq_const(&value[128..160], index as u64);
        (self.s.and(enabled, matched), self.byte_arena + index * width)
      })
      .collect();
    let record = self.s.select(&sources, width);
    self.s.require(enabled, record[32]);
    self.s.require_zero(self.s.one, &record[33..128]);
    self.s.bounded_constant(&record[..32], self.bytes.bytes(), enabled);
    for byte in 0..16 * self.bytes.data_words() {
      let boundary = self.s.constant(32, byte as u64);
      let live = self.s.less(&boundary, &record[..32]);
      let padding = self.s.not(live);
      self.s.require_zero(padding, &record[128 + 8 * byte..136 + 8 * byte]);
    }
    record
  }

  fn append(&mut self, prefix: &[usize], length: &[usize]) {
    let (next, carry) =
      add(&mut self.s.b, self.s.one, self.s.zero, &self.cursor, length);
    self.s.violations.push(carry);
    self.s.bounded_constant(&next, self.capacity, self.s.one);
    // Full output-width zero-fill shifts. Range checks above exclude high
    // cursor bits, and canonical prefix padding excludes overlapping writes.
    let mut shifted = prefix.to_vec();
    shifted.resize(8 * self.capacity.next_power_of_two(), self.s.zero);
    shifted.truncate(8 * self.capacity.next_power_of_two());
    for stage in 0..self.capacity.next_power_of_two().ilog2() as usize {
      let distance = 8usize << stage;
      shifted = (0..shifted.len())
        .map(|bit| {
          let moved =
            if bit >= distance { shifted[bit - distance] } else { self.s.zero };
          let difference = self.s.sum(&[shifted[bit], moved]);
          let delta = self.s.and(self.cursor[stage], difference);
          self.s.sum(&[shifted[bit], delta])
        })
        .collect();
    }
    for (target, source) in self.output.iter_mut().zip(shifted) {
      *target = self.s.sum(&[*target, source]);
    }
    self.cursor = next;
  }

  fn value(&mut self, value: &[usize], enabled: usize, depth: usize) {
    let flags = self.s.cell(enabled, value);
    let [boolean, word, field, extension, erased, bytes, ctor, nat, pap] =
      flags;
    let stored = if self.s.layout.nat_capacity.is_some() {
      self.s.sum(&[bytes, nat])
    } else {
      bytes
    };
    let masked = self.s.mask(ctor, value);
    let mut record =
      self.s.record(&masked, ctor, self.arena, self.declarations);
    let decl = self.s.declaration(&record[..32], ctor, self.declarations);
    if self.s.layout.applications {
      let masked = self.s.mask(pap, value);
      let (pap_record, _) = self.s.pap_record(
        &masked,
        pap,
        self.arena,
        self.declarations + 128 * self.s.layout.declaration_words(),
      );
      record =
        self.s.choose(&[(self.s.one, &record), (self.s.one, &pap_record)]);
    }
    let aggregate =
      if self.s.layout.applications { self.s.sum(&[ctor, pap]) } else { ctor };
    let buffer = self.buffer(value, stored);
    if let Some(capacity) = self.s.layout.nat_capacity {
      crate::ixby::nat_value::canonical_magnitude(
        &mut self.s.b,
        self.s.one,
        self.s.zero,
        &mut self.s.violations,
        nat,
        capacity,
        &buffer,
      );
    }
    let mut increment = vec![self.s.zero; 32];
    increment[0] = enabled;
    let (nodes, carry) =
      add(&mut self.s.b, self.s.one, self.s.zero, &self.nodes, &increment);
    self.s.violations.push(carry);
    self.nodes = nodes;
    let prefix_bytes = 45.max(6 + 16 * self.bytes.data_words());
    let mut prefix = vec![self.s.zero; 8 * prefix_bytes];
    prefix[0] = self.s.sum(&[ctor, erased]);
    prefix[1] = erased;
    if self.s.layout.applications {
      prefix[1] = self.s.sum(&[erased, pap]);
    }
    prefix[8] = self.s.sum(&[word, extension]);
    if self.s.layout.nat_capacity.is_some() {
      prefix[8] = self.s.sum(&[prefix[8], nat]);
    }
    prefix[9] = self.s.sum(&[field, extension]);
    prefix[10] = stored;
    let scalar = self.s.sum(&[boolean, word, field, extension]);
    for bit in 0..128 {
      prefix[16 + bit] = self.s.and(scalar, value[128 + bit]);
    }
    for bit in 0..320 {
      let source = self.s.and(ctor, decl[bit]);
      prefix[8 + bit] = self.s.sum(&[prefix[8 + bit], source]);
    }
    for bit in 0..32 {
      prefix[328 + bit] = self.s.and(ctor, record[32 + bit]);
      let source = self.s.and(stored, buffer[bit]);
      prefix[16 + bit] = self.s.sum(&[prefix[16 + bit], source]);
      if self.s.layout.applications {
        let function = self.s.and(pap, record[bit]);
        let captured = self.s.and(pap, record[32 + bit]);
        prefix[8 + bit] = self.s.sum(&[prefix[8 + bit], function]);
        prefix[40 + bit] = self.s.sum(&[prefix[40 + bit], captured]);
      }
    }
    for bit in 0..128 * self.bytes.data_words() {
      let source = self.s.and(stored, buffer[128 + bit]);
      prefix[48 + bit] = self.s.sum(&[prefix[48 + bit], source]);
    }
    let mut sizes: Vec<_> = [
      (boolean, 3),
      (word, 6),
      (field, 10),
      (extension, 18),
      (erased, 1),
      (ctor, 45),
    ]
    .map(|(flag, length)| (flag, self.s.constant(32, length)))
    .into();
    if self.s.layout.applications {
      sizes.push((pap, self.s.constant(32, 9)));
    }
    let mut sources: Vec<_> =
      sizes.iter().map(|(flag, bits)| (*flag, bits.as_slice())).collect();
    let six = self.s.constant(32, 6);
    let (byte_length, carry) =
      add(&mut self.s.b, self.s.one, self.s.zero, &buffer[..32], &six);
    let bad = self.s.and(stored, carry);
    self.s.violations.push(bad);
    sources.push((stored, &byte_length));
    let length = self.s.choose(&sources);
    self.append(&prefix, &length);
    if depth == 1 {
      self.s.require_zero(aggregate, &record[32..64]);
    } else {
      let live = self.s.prefix(&record[32..64], self.s.layout.fields);
      for (field, flag) in live.into_iter().enumerate() {
        self.value(
          &record[128 + 256 * field..384 + 256 * field],
          flag,
          depth - 1,
        );
      }
    }
  }
}

pub(crate) fn build(
  control: ControlCapacities,
  capacity: usize,
  layout: ObjectLayout,
  bytes: ByteCapacity,
) -> BooleanR1csPlan {
  let input_words = control.state_words()
    + layout.value_table_words()
    + layout.entries() * layout.record_words()
    + layout.byte_entries() * bytes.record_words();
  let data_words = capacity.div_ceil(16);
  let nodes = layout.tree_slots(layout.capacity.depth());
  let extra = 32768
    + 128 * input_words
    + nodes
      * (32768
        + 256 * layout.entries() * layout.record_words()
        + 256 * layout.byte_entries() * bytes.record_words()
        + 8
          * capacity.next_power_of_two()
          * (3 * capacity.next_power_of_two().ilog2() as usize + 4));
  let mut s = Synthesis::new(input_words, data_words + 2, extra, layout);
  let halted = s.eq_const(&(0..32).collect::<Vec<_>>(), 2);
  s.require(s.one, halted);
  s.require_zero(s.one, &(64..128).collect::<Vec<_>>());
  let value_base = 128 * (1 + control.frame_words());
  s.require_zero(s.one, &(128..value_base).collect::<Vec<_>>());
  s.require_zero(
    s.one,
    &(value_base + 256..128 * control.state_words()).collect::<Vec<_>>(),
  );
  let declarations = 128 * control.state_words();
  let arena = declarations + 128 * layout.value_table_words();
  let byte_arena = arena + 128 * layout.entries() * layout.record_words();
  let mut output = vec![s.zero; 128 * data_words];
  for (byte, value) in b"IXBO\0\0\0\0".iter().enumerate() {
    for bit in 0..8 {
      if value & (1 << bit) != 0 {
        output[8 * byte + bit] = s.one;
      }
    }
  }
  let mut encoder = Encoder {
    cursor: s.constant(32, 8),
    nodes: vec![s.zero; 32],
    s,
    bytes,
    capacity,
    declarations,
    arena,
    byte_arena,
    output,
  };
  if layout.nat_capacity.is_some() {
    encoder.output[32] = encoder.s.one;
  }
  encoder.value(
    &(value_base..value_base + 256).collect::<Vec<_>>(),
    encoder.s.one,
    layout.capacity.depth(),
  );
  encoder.s.bounded_constant(
    &encoder.nodes,
    layout.capacity.nodes(),
    encoder.s.one,
  );
  encoder.s.write(128 * input_words, &encoder.cursor);
  encoder.s.write(128 * (input_words + 1), &encoder.output);
  encoder.s.finish(128 * (input_words + data_words + 1))
}
