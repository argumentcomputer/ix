use crate::{
  boolean::{
    BooleanR1csBuilder, BooleanR1csPlan, generate_boolean_witness_into,
  },
  ixby::{
    bits::{
      add, any, constant_bits, equal_constant, evaluate_words, fill_words, not,
      require, require_zero, subtract,
    },
    byte_value::ByteCapacity,
    control::{ControlCapacities, ControlStepGate},
    object_value::ObjectLayout,
    value::{cell_with_byte_handles, cell_with_nat_handles, scalar_cell},
  },
  sizing::{CircuitEmitter, CountedGate},
};
use anyhow::{Result, ensure};
use flock_prover::{
  circuit::builder::{GateType, SlotId, SlotWitness, Wire},
  field::F128,
  r1cs::BlockR1cs,
  schedule::{IoWord, TableType},
  union::SlotWitnessDest,
};
use std::sync::{Arc, OnceLock};

#[cfg(test)]
#[path = "output_nat_tests.rs"]
mod nat_tests;
#[cfg(test)]
#[path = "object_output_tests.rs"]
mod object_tests;

#[derive(Clone, Debug)]
pub struct OutputEncodeGate {
  nu: usize,
  control: ControlCapacities,
  bytes: usize,
  byte_values: Option<(ByteCapacity, usize)>,
  object_values: Option<(ObjectLayout, ByteCapacity)>,
  nat_capacity: Option<crate::ixby::nat_value::NatCapacity>,
  pub(super) plan: Arc<OnceLock<BooleanR1csPlan>>,
}
#[derive(Clone, Debug)]
pub struct OutputEncodeRow(pub(super) Vec<F128>);
impl OutputEncodeGate {
  pub fn new(
    nu: usize,
    control: ControlCapacities,
    bytes: usize,
  ) -> Result<Self> {
    ControlStepGate::new(nu, control)?;
    ensure!((1..=512).contains(&bytes), "output byte capacity");
    Ok(Self {
      nu,
      control,
      bytes,
      byte_values: None,
      object_values: None,
      nat_capacity: None,
      plan: Arc::new(OnceLock::new()),
    })
  }
  pub(crate) fn with_byte_values(
    mut self,
    capacity: ByteCapacity,
    entries: usize,
  ) -> Result<Self> {
    crate::ixby::byte_value::validate_entries(entries)?;
    self.byte_values = Some((capacity, entries));
    self.plan = Arc::new(OnceLock::new());
    Ok(self)
  }
  pub fn data_words(&self) -> usize {
    self.bytes.div_ceil(16)
  }
  pub(crate) fn with_nat_values(
    mut self,
    capacity: crate::ixby::nat_value::NatCapacity,
  ) -> Result<Self> {
    ensure!(
      self
        .byte_values
        .is_some_and(|(bytes, _)| bytes.bytes() >= capacity.bytes()),
      "Nat output magnitude capacity"
    );
    self.nat_capacity = Some(capacity);
    self.plan = Arc::new(OnceLock::new());
    Ok(self)
  }
  pub(crate) fn with_objects(
    mut self,
    layout: ObjectLayout,
    bytes: ByteCapacity,
  ) -> Self {
    self.object_values = Some((layout, bytes));
    self.plan = Arc::new(OnceLock::new());
    self
  }
  pub(super) fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(|| match self.object_values {
      None => build(self),
      Some((layout, bytes)) => crate::ixby::object_value::build_output(
        self.control,
        self.bytes,
        layout,
        bytes,
      ),
    })
  }
  pub fn r1cs(&self) -> BlockR1cs {
    self.plan().block_r1cs(self.nu)
  }
  pub fn generate_witness_into(
    &self,
    rows: &[OutputEncodeRow],
    mut dst: SlotWitnessDest<'_>,
  ) -> Vec<u8> {
    dst.elide_padding_writes = false;
    generate_boolean_witness_into(
      self.plan(),
      rows,
      self.nu,
      dst,
      |row, bits| fill_words(&row.0, bits),
    )
  }
}
impl CountedGate for OutputEncodeGate {
  fn input_count(&self) -> usize {
    if let Some((layout, bytes)) = self.object_values {
      return self.control.state_words()
        + layout.value_table_words()
        + layout.entries() * layout.record_words()
        + layout.byte_entries() * bytes.record_words();
    }
    self.control.state_words()
      + self.byte_values.map_or(0, |(capacity, _)| capacity.record_words())
  }
  fn output_count(&self) -> usize {
    2 + self.data_words()
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut gate = self.clone();
    gate.nu = nu;
    gate.table()
  }
}
impl GateType for OutputEncodeGate {
  type Row = OutputEncodeRow;
  type Hint = ();
  fn table(&self) -> TableType {
    let mut schema: Vec<_> =
      (0..self.input_count()).map(IoWord::input).collect();
    schema.extend(
      (self.input_count()..self.input_count() + self.output_count())
        .map(IoWord::output),
    );
    crate::boolean::table_from_block_r1cs(self.r1cs()).with_io_schema(schema)
  }
  fn eval(&self, input: &[F128], _: &(), outputs: &mut Vec<F128>) -> Self::Row {
    assert_eq!(input.len(), self.input_count());
    outputs.extend(evaluate_words(self.plan(), input, self.output_count()));
    OutputEncodeRow(input.to_vec())
  }
  fn witness(&self, _: &[Self::Row], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}
#[derive(Clone, Copy, Debug)]
pub struct OutputEncodeSlot {
  slot: SlotId,
  zero: Wire,
  state_words: usize,
  buffer_words: usize,
  data_words: usize,
}
impl OutputEncodeSlot {
  pub fn declare(b: &mut impl CircuitEmitter, gate: OutputEncodeGate) -> Self {
    let (state_words, data_words) =
      (gate.control.state_words(), gate.data_words());
    let buffer_words = gate.input_count() - state_words;
    Self {
      slot: b.slot(gate),
      zero: b.fixed_public_input(F128::ZERO),
      state_words,
      buffer_words,
      data_words,
    }
  }
  pub fn slot(&self) -> SlotId {
    self.slot
  }
  /// Canonical length and padded byte words derived from the final state.
  pub fn encode(
    &self,
    b: &mut impl CircuitEmitter,
    state: &[Wire],
  ) -> Vec<Wire> {
    assert_eq!(
      self.buffer_words, 0,
      "byte output requires a constrained dereference"
    );
    self.encode_with_bytes(b, state, &[])
  }
  pub(crate) fn encode_with_bytes(
    &self,
    b: &mut impl CircuitEmitter,
    state: &[Wire],
    bytes: &[Wire],
  ) -> Vec<Wire> {
    assert_eq!(state.len(), self.state_words);
    assert_eq!(bytes.len(), self.buffer_words);
    let mut inputs = state.to_vec();
    inputs.extend_from_slice(bytes);
    let output = b.gate(self.slot, &inputs);
    b.connect(output[self.data_words + 1], self.zero);
    output[..self.data_words + 1].to_vec()
  }
}
fn build(gate: &OutputEncodeGate) -> BooleanR1csPlan {
  let reserved = 128 * (gate.input_count() + gate.output_count());
  let columns = reserved
    + if gate.nat_capacity.is_some() { 8192 } else { 0 }
    + 2048
    + 128 * gate.input_count()
    + gate
      .byte_values
      .map_or(0, |(capacity, _)| 4096 + 256 * (capacity.bytes() + 1));
  let mut b = BooleanR1csBuilder::new(
    columns.next_power_of_two().ilog2() as usize,
    reserved,
  );
  for bit in 0..128 * gate.input_count() {
    b.free_boolean_at(bit);
  }
  let one = b.alloc_constant_one();
  let zero = b.xor(&[one, one], one);
  let mut violations: Vec<_> = (64..128).collect();
  let halted = equal_constant(&mut b, one, &(0..32).collect::<Vec<_>>(), 2);
  require(&mut b, one, &mut violations, one, halted);
  let value_base = 128 * (1 + gate.control.frame_words());
  violations.extend(128..value_base);
  violations.extend(value_base + 256..128 * gate.control.state_words());
  let value: Vec<_> = (value_base..value_base + 256).collect();
  let mut nat_flag = zero;
  let (flags, byte_flag) = match gate.byte_values {
    None => (scalar_cell(&mut b, one, &mut violations, one, &value), zero),
    Some((_, entries)) => {
      if gate.nat_capacity.is_some() {
        let flags = cell_with_nat_handles(
          &mut b,
          one,
          &mut violations,
          one,
          &value,
          entries,
          None,
        );
        nat_flag = flags[7];
        (flags[..5].try_into().unwrap(), b.xor(&[flags[5], nat_flag], one))
      } else {
        let flags = cell_with_byte_handles(
          &mut b,
          one,
          &mut violations,
          one,
          &value,
          entries,
        );
        (flags[..5].try_into().unwrap(), flags[5])
      }
    },
  };
  let [boolean, word, field, extension, erased] = flags;
  let mut length = vec![zero; 32];
  for (size, flag) in
    [(11, boolean), (14, word), (18, field), (26, extension), (9, erased)]
  {
    for (bit, target) in length.iter_mut().enumerate().take(5) {
      if size & (1 << bit) != 0 {
        *target = b.xor(&[*target, flag], one);
      }
    }
  }
  let byte_base = 128 * gate.control.state_words();
  if let Some((capacity, _)) = gate.byte_values {
    let buffer: Vec<_> = (byte_base..128 * gate.input_count()).collect();
    let nonbyte = not(&mut b, one, byte_flag);
    require_zero(&mut b, one, &mut violations, nonbyte, &buffer);
    require_zero(&mut b, one, &mut violations, one, &buffer[32..128]);
    if let Some(capacity) = gate.nat_capacity {
      crate::ixby::nat_value::canonical_magnitude(
        &mut b,
        one,
        zero,
        &mut violations,
        nat_flag,
        capacity,
        &buffer,
      );
    }
    let maximum = constant_bits(one, zero, (capacity.bytes() + 1) as u32);
    let in_range = subtract(&mut b, one, zero, &buffer[..32], &maximum).1;
    require(&mut b, one, &mut violations, one, in_range);
    for byte in 0..capacity.data_words() * 16 {
      let boundary = constant_bits(one, zero, byte as u32);
      let live = subtract(&mut b, one, zero, &boundary, &buffer[..32]).1;
      let padding = not(&mut b, one, live);
      require_zero(
        &mut b,
        one,
        &mut violations,
        padding,
        &buffer[128 + 8 * byte..136 + 8 * byte],
      );
    }
    let header = constant_bits(one, zero, 14);
    let (total, overflow) = add(&mut b, one, zero, &buffer[..32], &header);
    violations.push(b.and(byte_flag, overflow));
    for (target, source) in length.iter_mut().zip(total) {
      let source = b.and(byte_flag, source);
      *target = b.xor(&[*target, source], one);
    }
  }
  let maximum = constant_bits(one, zero, (gate.bytes + 1) as u32);
  let in_range = subtract(&mut b, one, zero, &length, &maximum).1;
  require(&mut b, one, &mut violations, one, in_range);
  let mut bytes = vec![zero; 128 * gate.data_words()];
  for (index, byte) in b"IXBO\0\0\0\0".iter().enumerate() {
    for bit in 0..8 {
      if byte & (1 << bit) != 0 {
        bytes[index * 8 + bit] = one;
      }
    }
  }
  bytes[64] = erased;
  bytes[65] = erased;
  bytes[72] = b.xor(&[word, extension], one);
  if gate.nat_capacity.is_some() {
    bytes[32] = one; // revision 1 in the ordinary IXBO envelope
    bytes[72] = b.xor(&[bytes[72], nat_flag], one); // scalar Nat tag 5
  }
  bytes[73] = b.xor(&[field, extension], one);
  if gate.byte_values.is_some() {
    bytes[74] = byte_flag;
  }
  let nonbyte =
    if gate.byte_values.is_some() { not(&mut b, one, byte_flag) } else { one };
  for (bit, target) in bytes.iter_mut().skip(80).take(128).enumerate() {
    *target = if gate.byte_values.is_some() {
      b.and(nonbyte, value[128 + bit])
    } else {
      value[128 + bit]
    };
  }
  if let Some((capacity, _)) = gate.byte_values {
    for (bit, target) in bytes.iter_mut().enumerate().skip(80) {
      let source = if bit < 112 {
        Some(byte_base + bit - 80)
      } else if bit - 112 < 128 * capacity.data_words() {
        Some(byte_base + 128 + bit - 112)
      } else {
        None
      };
      if let Some(source) = source {
        let byte = b.and(byte_flag, source);
        *target = b.xor(&[*target, byte], one);
      }
    }
  }
  for (bit, source) in length.iter().enumerate() {
    b.write_xor(128 * gate.input_count() + bit, &[*source], one);
  }
  for (bit, source) in bytes.iter().enumerate() {
    b.write_xor(128 * (gate.input_count() + 1) + bit, &[*source], one);
  }
  let violation = any(&mut b, one, &violations);
  b.write_xor(
    128 * (gate.input_count() + gate.data_words() + 1),
    &[violation],
    one,
  );
  b.finish()
}
