use super::{bytes::Decoder, evaluate, fill_words};
use crate::{
  boolean::{BooleanR1csPlan, generate_boolean_witness_into},
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
#[path = "input_tests.rs"]
mod tests;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InputCapacities {
  pub bytes: usize,
  pub values: usize,
}

impl InputCapacities {
  pub fn data_words(self) -> usize {
    self.bytes.div_ceil(16)
  }
  /// Full u32 count followed by a canonically padded bank of scalar cells.
  pub fn value_words(self) -> usize {
    1 + 2 * self.values
  }
}

#[derive(Clone, Debug)]
pub struct InputDecodeGate {
  nu: usize,
  capacity: InputCapacities,
  plan: Arc<OnceLock<BooleanR1csPlan>>,
}

#[derive(Clone, Debug)]
pub struct InputDecodeRow(Vec<F128>);

impl InputDecodeGate {
  pub fn new(nu: usize, capacity: InputCapacities) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "input decoder row-domain admission");
    ensure!(
      (1..=512).contains(&capacity.bytes),
      "prototype input byte capacity"
    );
    ensure!(capacity.values <= 16, "prototype input value capacity");
    Ok(Self { nu, capacity, plan: Arc::new(OnceLock::new()) })
  }
  pub fn capacity(&self) -> InputCapacities {
    self.capacity
  }
  fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(|| {
      let c = self.capacity;
      let output = self.input_count();
      let mut d = Decoder::new(
        c.bytes,
        output,
        self.output_count(),
        3 + 3 * c.values,
        4096,
      );
      d.header(b"IXBI");
      let count = d.u32(d.one);
      let counts = d.bounded(&count, c.values, d.one);
      d.write(output, &count);
      for value in 0..c.values {
        let enabled = d.live(&counts, value, d.one);
        let scalar = d.value(enabled);
        d.write(output + 1 + value * 2, &scalar.tag);
        d.write(output + 2 + value * 2, &scalar.payload);
      }
      d.finish(output + c.value_words())
    })
  }
  pub fn r1cs(&self) -> BlockR1cs {
    self.plan().block_r1cs(self.nu)
  }
  pub fn generate_witness_into(
    &self,
    rows: &[InputDecodeRow],
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

impl CountedGate for InputDecodeGate {
  fn input_count(&self) -> usize {
    1 + self.capacity.data_words()
  }
  fn output_count(&self) -> usize {
    self.capacity.value_words() + 1
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut gate = self.clone();
    gate.nu = nu;
    gate.table()
  }
}

impl GateType for InputDecodeGate {
  type Row = InputDecodeRow;
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
    outputs.extend(evaluate(self.plan(), inputs, self.output_count()));
    InputDecodeRow(inputs.to_vec())
  }
  fn witness(&self, _: &[Self::Row], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}

#[derive(Clone, Copy, Debug)]
pub struct InputDecodeSlot {
  slot: SlotId,
  zero: Wire,
  capacity: InputCapacities,
}

impl InputDecodeSlot {
  pub fn declare(b: &mut impl CircuitEmitter, gate: InputDecodeGate) -> Self {
    let capacity = gate.capacity;
    Self {
      slot: b.slot(gate),
      zero: b.fixed_public_input(F128::ZERO),
      capacity,
    }
  }
  pub fn slot(&self) -> SlotId {
    self.slot
  }
  pub fn decode(
    &self,
    b: &mut impl CircuitEmitter,
    length: Wire,
    data: &[Wire],
  ) -> Vec<Wire> {
    assert_eq!(data.len(), self.capacity.data_words());
    let mut input = vec![length];
    input.extend_from_slice(data);
    let output = b.gate(self.slot, &input);
    b.connect(output[self.capacity.value_words()], self.zero);
    output[..self.capacity.value_words()].to_vec()
  }
}
