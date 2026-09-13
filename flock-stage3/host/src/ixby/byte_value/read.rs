use super::{ByteCapacity, validate_entries};
use crate::{
  boolean::{
    BooleanR1csBuilder, BooleanR1csPlan, generate_boolean_witness_into,
  },
  ixby::{
    bits::{
      any, constant_bits, equal_constant, evaluate_words, fill_words, not,
      require, require_zero, select, subtract,
    },
    value::{
      cell_with_byte_handles, cell_with_nat_handles, cell_with_object_handles,
    },
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

/// Derive a byte buffer from a typed handle and a fixed bank of immutable
/// record wires. Non-byte cells return the zero buffer. A byte read requires
/// a present record, canonical length/padding and the entire u32 index.
/// Unselected records are not authenticated here: the executor owns all
/// record-producing wires and constrains each allocation at its producer.
#[derive(Clone, Debug)]
pub struct ByteReadGate {
  nu: usize,
  capacity: ByteCapacity,
  entries: usize,
  object_entries: Option<usize>,
  nat_capacity: Option<crate::ixby::nat_value::NatCapacity>,
  plan: Arc<OnceLock<BooleanR1csPlan>>,
}

#[derive(Clone, Debug)]
pub struct ByteReadRow(pub(super) Vec<F128>);

#[cfg(test)]
impl ByteReadRow {
  pub(crate) fn inputs(&self) -> &[F128] {
    &self.0
  }
}

impl ByteReadGate {
  pub fn new(
    nu: usize,
    capacity: ByteCapacity,
    entries: usize,
  ) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "byte-read row-domain admission");
    validate_entries(entries)?;
    ensure!(
      entries * capacity.record_words() <= 32768,
      "prototype byte-read bank word capacity"
    );
    Ok(Self {
      nu,
      capacity,
      entries,
      object_entries: None,
      nat_capacity: None,
      plan: Arc::new(OnceLock::new()),
    })
  }
  pub(crate) fn with_object_handles(mut self, entries: usize) -> Self {
    assert!((1..=128).contains(&entries));
    self.object_entries = Some(entries);
    self.plan = Arc::new(OnceLock::new());
    self
  }
  pub fn capacity(&self) -> ByteCapacity {
    self.capacity
  }
  pub(crate) fn with_nat_capacity(
    mut self,
    capacity: crate::ixby::nat_value::NatCapacity,
  ) -> Result<Self> {
    ensure!(
      capacity.bytes() <= self.capacity.bytes(),
      "Nat read magnitude capacity"
    );
    self.nat_capacity = Some(capacity);
    self.plan = Arc::new(OnceLock::new());
    Ok(self)
  }
  pub fn entries(&self) -> usize {
    self.entries
  }
  pub(super) fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(|| build(self))
  }
  pub fn r1cs(&self) -> BlockR1cs {
    self.plan().block_r1cs(self.nu)
  }
  pub fn generate_witness_into(
    &self,
    rows: &[ByteReadRow],
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

impl CountedGate for ByteReadGate {
  fn input_count(&self) -> usize {
    2 + self.entries * self.capacity.record_words()
  }
  fn output_count(&self) -> usize {
    self.capacity.record_words() + 1
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut gate = self.clone();
    gate.nu = nu;
    gate.table()
  }
}

impl GateType for ByteReadGate {
  type Row = ByteReadRow;
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
  fn eval(
    &self,
    inputs: &[F128],
    _: &(),
    outputs: &mut Vec<F128>,
  ) -> Self::Row {
    assert_eq!(inputs.len(), self.input_count());
    outputs.extend(evaluate_words(self.plan(), inputs, self.output_count()));
    ByteReadRow(inputs.to_vec())
  }
  fn witness(&self, _: &[Self::Row], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}

#[derive(Clone, Copy, Debug)]
pub struct ByteReadSlot {
  slot: SlotId,
  zero: Wire,
  capacity: ByteCapacity,
  entries: usize,
}

impl ByteReadSlot {
  pub fn declare(b: &mut impl CircuitEmitter, gate: ByteReadGate) -> Self {
    Self {
      capacity: gate.capacity,
      entries: gate.entries,
      slot: b.slot(gate),
      zero: b.fixed_public_input(F128::ZERO),
    }
  }
  pub fn slot(&self) -> SlotId {
    self.slot
  }
  /// Returns a length word and the complete padded data bank. There is no
  /// free enable/one-hot vector, selected record, length, or returned byte.
  pub fn read(
    &self,
    b: &mut impl CircuitEmitter,
    value: &[Wire],
    records: &[Wire],
  ) -> Vec<Wire> {
    assert_eq!(value.len(), 2);
    assert_eq!(records.len(), self.entries * self.capacity.record_words());
    let mut inputs = value.to_vec();
    inputs.extend_from_slice(records);
    let output = b.gate(self.slot, &inputs);
    b.connect(output[self.capacity.record_words()], self.zero);
    output[..self.capacity.record_words()].to_vec()
  }
}

fn build(gate: &ByteReadGate) -> BooleanR1csPlan {
  let width = 128 * gate.capacity.record_words();
  let reserved = 128 * (gate.input_count() + gate.output_count());
  let columns = reserved
    + if gate.nat_capacity.is_some() {
      4096 + 256 * gate.capacity.bytes()
    } else {
      0
    }
    + 4096
    + 128 * gate.entries
    + (gate.entries + 4) * width
    + 160 * gate.capacity.bytes()
    + gate.object_entries.map_or(0, |_| 2048);
  let mut b = BooleanR1csBuilder::new(
    columns.next_power_of_two().ilog2() as usize,
    reserved,
  );
  for bit in 0..128 * gate.input_count() {
    b.free_boolean_at(bit);
  }
  let one = b.alloc_constant_one();
  let zero = b.xor(&[one, one], one);
  let mut violations = Vec::new();
  let enabled = any(&mut b, one, &(0..128).collect::<Vec<_>>());
  let mut nat = zero;
  let bytes = match gate.object_entries {
    objects if gate.nat_capacity.is_some() => {
      let flags = cell_with_nat_handles(
        &mut b,
        one,
        &mut violations,
        enabled,
        &(0..256).collect::<Vec<_>>(),
        gate.entries,
        objects,
      );
      nat = flags[7];
      b.xor(&[flags[5], nat], one)
    },
    None => cell_with_byte_handles(
      &mut b,
      one,
      &mut violations,
      enabled,
      &(0..256).collect::<Vec<_>>(),
      gate.entries,
    )[5],
    Some(objects) => cell_with_object_handles(
      &mut b,
      one,
      &mut violations,
      enabled,
      &(0..256).collect::<Vec<_>>(),
      gate.entries,
      objects,
    )[5],
  };
  let index: Vec<_> = (128..160).collect();
  let selectors: Vec<_> = (0..gate.entries)
    .map(|entry| {
      let equal = equal_constant(&mut b, one, &index, entry as u64);
      (b.and(bytes, equal), 256 + entry * width)
    })
    .collect();
  let record = select(&mut b, one, zero, &selectors, width);
  require(&mut b, one, &mut violations, bytes, record[32]);
  require_zero(&mut b, one, &mut violations, one, &record[33..128]);
  let maximum = constant_bits(one, zero, (gate.capacity.bytes() + 1) as u32);
  let in_range = subtract(&mut b, one, zero, &record[..32], &maximum).1;
  require(&mut b, one, &mut violations, one, in_range);
  for byte in 0..16 * gate.capacity.data_words() {
    let boundary = constant_bits(one, zero, byte as u32);
    let live = subtract(&mut b, one, zero, &boundary, &record[..32]).1;
    let padding = not(&mut b, one, live);
    require_zero(
      &mut b,
      one,
      &mut violations,
      padding,
      &record[128 + 8 * byte..136 + 8 * byte],
    );
  }
  let mut buffer = record;
  buffer[32] = zero; // presence is not part of a byte-buffer length
  if let Some(capacity) = gate.nat_capacity {
    crate::ixby::nat_value::canonical_magnitude(
      &mut b,
      one,
      zero,
      &mut violations,
      nat,
      capacity,
      &buffer,
    );
  }
  for (bit, source) in buffer.iter().enumerate() {
    b.write_xor(128 * gate.input_count() + bit, &[*source], one);
  }
  let violation = any(&mut b, one, &violations);
  b.write_xor(
    128 * (gate.input_count() + gate.capacity.record_words()),
    &[violation],
    one,
  );
  b.finish()
}
