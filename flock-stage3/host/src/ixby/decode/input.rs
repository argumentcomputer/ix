use super::{bytes::Decoder, evaluate, fill_words};
use crate::{
  boolean::{BooleanR1csPlan, generate_boolean_witness_into},
  ixby::{byte_value::ByteDecodeLayout, object_value::ObjectLayout},
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
#[path = "input_nat_tests.rs"]
mod nat_tests;
#[cfg(test)]
#[path = "input_object_tests.rs"]
mod object_tests;
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
  byte_layout: Option<ByteDecodeLayout>,
  object_layout: Option<ObjectLayout>,
  nat_capacity: Option<crate::ixby::nat_value::NatCapacity>,
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
    Ok(Self {
      nu,
      capacity,
      byte_layout: None,
      object_layout: None,
      nat_capacity: None,
      plan: Arc::new(OnceLock::new()),
    })
  }
  pub(crate) fn with_byte_values(
    mut self,
    layout: ByteDecodeLayout,
  ) -> Result<Self> {
    layout.validate(self.capacity.values)?;
    self.byte_layout = Some(layout);
    self.plan = Arc::new(OnceLock::new());
    Ok(self)
  }
  pub fn decoded_words(&self) -> usize {
    self.capacity.value_words()
      + self.byte_layout.map_or(0, |layout| {
        self.byte_records() * layout.capacity.record_words()
      })
      + self
        .object_layout
        .map_or(0, |layout| layout.input_slots() * layout.record_words())
  }
  pub(crate) fn with_objects(mut self, layout: ObjectLayout) -> Result<Self> {
    ensure!(
      self.byte_layout.is_some(),
      "object inputs require the byte-capable codec"
    );
    self.byte_layout.unwrap().validate(layout.input_slots())?;
    self.object_layout = Some(layout);
    self.plan = Arc::new(OnceLock::new());
    Ok(self)
  }
  pub(crate) fn byte_records(&self) -> usize {
    self.object_layout.map_or(self.capacity.values, ObjectLayout::input_slots)
  }
  pub(crate) fn with_nat_values(
    mut self,
    capacity: crate::ixby::nat_value::NatCapacity,
  ) -> Result<Self> {
    ensure!(
      self
        .byte_layout
        .is_some_and(|bytes| bytes.capacity.bytes() >= capacity.bytes()),
      "Nat input magnitude capacity"
    );
    self.nat_capacity = Some(capacity);
    self.plan = Arc::new(OnceLock::new());
    Ok(self)
  }
  pub fn capacity(&self) -> InputCapacities {
    self.capacity
  }
  fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(|| {
      if let Some(layout) = self.object_layout {
        return self.object_plan(layout);
      }
      let c = self.capacity;
      let output = self.input_count();
      let mut d = Decoder::new(
        c.bytes,
        output,
        self.output_count(),
        3 + 3 * c.values
          + self
            .byte_layout
            .map_or(0, |layout| c.values * (1 + layout.capacity.data_words())),
        4096
          + self
            .byte_layout
            .map_or(0, |layout| 256 * c.values * (layout.capacity.bytes() + 1)),
      );
      d.nat_capacity = self.nat_capacity;
      d.header(b"IXBI");
      let count = d.u32(d.one);
      let counts = d.bounded(&count, c.values, d.one);
      d.write(output, &count);
      for value in 0..c.values {
        let enabled = d.live(&counts, value, d.one);
        let scalar = match self.byte_layout {
          None => d.value(enabled),
          Some(layout) => d.value_with_bytes(enabled, layout, value),
        };
        d.write(output + 1 + value * 2, &scalar.tag);
        d.write(output + 2 + value * 2, &scalar.payload);
        if let Some(layout) = self.byte_layout {
          for (word, bits) in scalar.bytes.iter().enumerate() {
            d.write(
              output
                + c.value_words()
                + value * layout.capacity.record_words()
                + word,
              bits,
            );
          }
        }
      }
      d.finish(output + self.decoded_words())
    })
  }
  fn object_plan(&self, layout: ObjectLayout) -> BooleanR1csPlan {
    use super::tree::TreeContext;
    use crate::ixby::bits::add;
    let c = self.capacity;
    let bytes = self.byte_layout.unwrap();
    let output = self.input_count();
    let slots = layout.input_slots();
    let mut d = Decoder::new(
      c.bytes,
      output,
      self.output_count(),
      3 + slots * (9 + bytes.capacity.data_words()),
      4096 + slots * (8192 + 256 * (bytes.capacity.bytes() + 1)),
    );
    let declarations: Vec<Vec<_>> = (1 + c.data_words()..self.input_count())
      .map(|word| (128 * word..128 * (word + 1)).collect())
      .collect();
    let context = TreeContext { layout, bytes, declarations: &declarations };
    d.nat_capacity = self.nat_capacity;
    d.header(b"IXBI");
    let count = d.u32(d.one);
    let counts = d.bounded(&count, c.values, d.one);
    d.write(output, &count);
    let mut total = vec![d.zero; 32];
    for root in 0..c.values {
      let enabled = d.live(&counts, root, d.one);
      let slot = root * layout.tree_slots(layout.capacity.depth());
      let tree = d.tree(enabled, layout.capacity.depth(), slot, &context);
      d.write(output + 1 + root * 2, &tree.value.tag);
      d.write(output + 2 + root * 2, &tree.value.payload);
      for (word, bits) in tree.bytes.iter().enumerate() {
        d.write(
          output
            + c.value_words()
            + slot * bytes.capacity.record_words()
            + word,
          bits,
        );
      }
      for (word, bits) in tree.objects.iter().enumerate() {
        d.write(
          output
            + c.value_words()
            + slots * bytes.capacity.record_words()
            + slot * layout.record_words()
            + word,
          bits,
        );
      }
      for flag in tree.nodes {
        let mut increment = vec![d.zero; 32];
        increment[0] = flag;
        let (next, carry) = add(&mut d.b, d.one, d.zero, &total, &increment);
        d.violate(carry);
        total = next;
      }
    }
    d.bounded(&total, layout.capacity.nodes(), d.one);
    d.finish(output + self.decoded_words())
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
      + self.object_layout.map_or(0, ObjectLayout::declaration_words)
  }
  fn output_count(&self) -> usize {
    self.decoded_words() + 1
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
  words: usize,
  declarations: usize,
}

impl InputDecodeSlot {
  pub fn declare(b: &mut impl CircuitEmitter, gate: InputDecodeGate) -> Self {
    let capacity = gate.capacity;
    let words = gate.decoded_words();
    let declarations =
      gate.object_layout.map_or(0, ObjectLayout::declaration_words);
    Self {
      slot: b.slot(gate),
      zero: b.fixed_public_input(F128::ZERO),
      capacity,
      words,
      declarations,
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
    assert_eq!(
      self.declarations, 0,
      "object inputs require authenticated declarations"
    );
    self.decode_with_objects(b, length, data, &[])
  }
  pub(crate) fn decode_with_objects(
    &self,
    b: &mut impl CircuitEmitter,
    length: Wire,
    data: &[Wire],
    declarations: &[Wire],
  ) -> Vec<Wire> {
    assert_eq!(data.len(), self.capacity.data_words());
    assert_eq!(declarations.len(), self.declarations);
    let mut input = vec![length];
    input.extend_from_slice(data);
    input.extend_from_slice(declarations);
    let output = b.gate(self.slot, &input);
    b.connect(output[self.words], self.zero);
    output[..self.words].to_vec()
  }
}
