use crate::{
  boolean::{
    BooleanR1csBuilder, BooleanR1csPlan, generate_boolean_witness_into,
  },
  ixby::{
    bits::{
      any, bounded_prefix, constant_bits, equal, equal_constant,
      evaluate_words, fill_words, require, select, subtract,
    },
    control::{ControlCapacities, ControlStepGate},
    value::{
      cell_with_byte_handles, cell_with_nat_handles, cell_with_object_handles,
      scalar_cell,
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

#[derive(Clone, Debug)]
pub struct InitialStateGate {
  nu: usize,
  control: ControlCapacities,
  functions: usize,
  inputs: usize,
  fuel: u32,
  byte_entries: Option<usize>,
  object_entries: Option<usize>,
  nat_values: bool,
  pub(super) plan: Arc<OnceLock<BooleanR1csPlan>>,
}
#[derive(Clone, Debug)]
pub struct InitialStateRow(pub(super) Vec<F128>);
impl InitialStateGate {
  pub fn new(
    nu: usize,
    control: ControlCapacities,
    functions: usize,
    inputs: usize,
    fuel: u32,
  ) -> Result<Self> {
    ControlStepGate::new(nu, control)?;
    ensure!((1..=4).contains(&functions), "initial function capacity");
    ensure!(inputs <= control.arguments, "initial input capacity");
    Ok(Self {
      nu,
      control,
      functions,
      inputs,
      fuel,
      byte_entries: None,
      object_entries: None,
      nat_values: false,
      plan: Arc::new(OnceLock::new()),
    })
  }
  pub(crate) fn with_byte_handles(mut self, entries: usize) -> Result<Self> {
    crate::ixby::byte_value::validate_entries(entries)?;
    self.byte_entries = Some(entries);
    self.plan = Arc::new(OnceLock::new());
    Ok(self)
  }
  pub(crate) fn with_object_handles(mut self, entries: usize) -> Result<Self> {
    ensure!(
      self.byte_entries.is_some() && (1..=128).contains(&entries),
      "initial object arena capacity"
    );
    self.object_entries = Some(entries);
    self.plan = Arc::new(OnceLock::new());
    Ok(self)
  }
  pub(super) fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(|| build(self))
  }
  pub(crate) fn with_nat_handles(mut self) -> Result<Self> {
    ensure!(
      self.byte_entries.is_some(),
      "Nat initial values require a magnitude arena"
    );
    self.nat_values = true;
    self.plan = Arc::new(OnceLock::new());
    Ok(self)
  }
  pub fn r1cs(&self) -> BlockR1cs {
    self.plan().block_r1cs(self.nu)
  }
  pub fn generate_witness_into(
    &self,
    rows: &[InitialStateRow],
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
impl CountedGate for InitialStateGate {
  fn input_count(&self) -> usize {
    2 + self.functions + 2 * self.inputs
  }
  fn output_count(&self) -> usize {
    self.control.state_words() + 1
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut gate = self.clone();
    gate.nu = nu;
    gate.table()
  }
}
impl GateType for InitialStateGate {
  type Row = InitialStateRow;
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
    InitialStateRow(input.to_vec())
  }
  fn witness(&self, _: &[Self::Row], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}
#[derive(Clone, Copy, Debug)]
pub struct InitialStateSlot {
  slot: SlotId,
  zero: Wire,
  functions: usize,
  inputs: usize,
  words: usize,
}
impl InitialStateSlot {
  pub fn declare(b: &mut impl CircuitEmitter, gate: InitialStateGate) -> Self {
    let (functions, inputs, words) =
      (gate.functions, gate.inputs, gate.control.state_words());
    Self {
      slot: b.slot(gate),
      zero: b.fixed_public_input(F128::ZERO),
      functions,
      inputs,
      words,
    }
  }
  pub fn slot(&self) -> SlotId {
    self.slot
  }
  pub fn initial(
    &self,
    b: &mut impl CircuitEmitter,
    program_header: Wire,
    functions: &[Wire],
    input: &[Wire],
  ) -> Vec<Wire> {
    assert_eq!(functions.len(), self.functions);
    assert_eq!(input.len(), 1 + 2 * self.inputs);
    let mut args = vec![program_header];
    args.extend_from_slice(functions);
    args.extend_from_slice(input);
    let output = b.gate(self.slot, &args);
    b.connect(output[self.words], self.zero);
    output[..self.words].to_vec()
  }
}
fn build(gate: &InitialStateGate) -> BooleanR1csPlan {
  let reserved = 128 * (gate.input_count() + gate.output_count());
  let columns = reserved
    + if gate.nat_values { 2048 * (gate.inputs + 4) } else { 0 }
    + 4096
    + 1024 * (gate.functions + gate.inputs)
    + gate.object_entries.map_or(0, |_| 1024 * gate.inputs);
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
  let entry: Vec<_> = (0..32).collect();
  let function_count: Vec<_> = (32..64).collect();
  bounded_prefix(&mut b, one, &mut violations, &function_count, gate.functions);
  let valid_entry = subtract(&mut b, one, zero, &entry, &function_count).1;
  require(&mut b, one, &mut violations, one, valid_entry);
  let functions: Vec<_> = (0..gate.functions)
    .map(|index| {
      (equal_constant(&mut b, one, &entry, index as u64), 128 * (1 + index))
    })
    .collect();
  let function = select(&mut b, one, zero, &functions, 128);
  violations.extend_from_slice(&function[96..]);
  let valid_block =
    subtract(&mut b, one, zero, &function[32..64], &function[64..96]).1;
  require(&mut b, one, &mut violations, one, valid_block);
  let input_base = 128 * (1 + gate.functions);
  violations.extend(input_base + 32..input_base + 128);
  let count: Vec<_> = (input_base..input_base + 32).collect();
  let live = bounded_prefix(&mut b, one, &mut violations, &count, gate.inputs);
  let arity = equal(&mut b, one, &count, &function[..32]);
  require(&mut b, one, &mut violations, one, arity);
  let mut out = vec![zero; 128 * gate.control.state_words()];
  out[32..64].copy_from_slice(&constant_bits(one, zero, gate.fuel));
  out[128..160].copy_from_slice(&entry);
  out[160..192].copy_from_slice(&function[32..64]);
  out[192..224].copy_from_slice(&count);
  for (index, enabled) in live.iter().enumerate() {
    let base = input_base + 128 * (1 + 2 * index);
    let value: Vec<_> = (base..base + 256).collect();
    match (gate.byte_entries, gate.object_entries) {
      (Some(entries), objects) if gate.nat_values => {
        cell_with_nat_handles(
          &mut b,
          one,
          &mut violations,
          *enabled,
          &value,
          entries,
          objects,
        );
      },
      (None, _) => {
        scalar_cell(&mut b, one, &mut violations, *enabled, &value);
      },
      (Some(entries), None) => {
        cell_with_byte_handles(
          &mut b,
          one,
          &mut violations,
          *enabled,
          &value,
          entries,
        );
      },
      (Some(bytes), Some(objects)) => {
        cell_with_object_handles(
          &mut b,
          one,
          &mut violations,
          *enabled,
          &value,
          bytes,
          objects,
        );
      },
    }
    out[256 + 256 * index..512 + 256 * index].copy_from_slice(&value);
  }
  for (bit, source) in out.iter().enumerate() {
    b.write_xor(128 * gate.input_count() + bit, &[*source], one);
  }
  let violation = any(&mut b, one, &violations);
  b.write_xor(
    128 * (gate.input_count() + gate.control.state_words()),
    &[violation],
    one,
  );
  b.finish()
}
