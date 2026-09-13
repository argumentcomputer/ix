use crate::{
  boolean::{
    BooleanR1csBuilder, BooleanR1csPlan, generate_boolean_witness_into,
  },
  ixby::{
    bits::{
      any, constant_bits, equal_constant, evaluate_words, fill_words, require,
      subtract,
    },
    control::{ControlCapacities, ControlStepGate},
    value::scalar_cell,
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

#[derive(Clone, Debug)]
pub struct OutputEncodeGate {
  nu: usize,
  control: ControlCapacities,
  bytes: usize,
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
    Ok(Self { nu, control, bytes, plan: Arc::new(OnceLock::new()) })
  }
  pub fn data_words(&self) -> usize {
    self.bytes.div_ceil(16)
  }
  pub(super) fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(|| build(self))
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
    self.control.state_words()
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
  data_words: usize,
}
impl OutputEncodeSlot {
  pub fn declare(b: &mut impl CircuitEmitter, gate: OutputEncodeGate) -> Self {
    let (state_words, data_words) = (gate.input_count(), gate.data_words());
    Self {
      slot: b.slot(gate),
      zero: b.fixed_public_input(F128::ZERO),
      state_words,
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
    assert_eq!(state.len(), self.state_words);
    let output = b.gate(self.slot, state);
    b.connect(output[self.data_words + 1], self.zero);
    output[..self.data_words + 1].to_vec()
  }
}
fn build(gate: &OutputEncodeGate) -> BooleanR1csPlan {
  let reserved = 128 * (gate.input_count() + gate.output_count());
  let columns = reserved + 2048 + 128 * gate.input_count();
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
  violations.extend(value_base + 256..128 * gate.input_count());
  let value: Vec<_> = (value_base..value_base + 256).collect();
  let flags = scalar_cell(&mut b, one, &mut violations, one, &value);
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
  bytes[73] = b.xor(&[field, extension], one);
  for (bit, target) in bytes.iter_mut().skip(80).take(128).enumerate() {
    *target = value[128 + bit];
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
