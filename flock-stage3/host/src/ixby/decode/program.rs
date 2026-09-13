use super::{
  PrimitiveSet,
  bytes::{Bits, Decoder},
  evaluate, fill_words, scalar_primitive_arity,
};
use crate::{
  boolean::{BooleanR1csPlan, generate_boolean_witness_into},
  ixby::{
    bits::add,
    control::{ControlCapacities, ControlStepGate},
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
#[path = "program_tests.rs"]
mod tests;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProgramCapacities {
  pub bytes: usize,
  pub functions: usize,
  /// Maximum blocks PER function, not a guest-dependent global table size.
  pub blocks: usize,
  pub operands: usize,
}

impl ProgramCapacities {
  pub(super) fn validate(self) -> Result<()> {
    ensure!((1..=512).contains(&self.bytes), "prototype program byte capacity");
    ensure!((1..=4).contains(&self.functions), "prototype function capacity");
    ensure!(
      (1..=8).contains(&self.blocks),
      "prototype per-function block capacity"
    );
    ensure!((1..=4).contains(&self.operands), "prototype operand capacity");
    Ok(())
  }
  pub fn data_words(self) -> usize {
    self.bytes.div_ceil(16)
  }
  pub fn layout(self) -> ProgramLayout {
    ProgramLayout(self)
  }
}

/// Table words derived entirely from canonical program bytes. Header:
/// (entry, function count, 0, 0); function: (arity, entry, block count, 0).
/// Block: (locals, kind, target, alternative), (callee, primitive, argc, 0),
/// then `operands` records (physical operand kind/index header, tag, payload).
/// Block kinds 1..6 are copy, primitive, call, return, tail-call and branch;
/// self calls resolve to their containing function during decoding. These are
/// internal decoded records, never a separately admitted guest byte format.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProgramLayout(ProgramCapacities);

impl ProgramLayout {
  pub fn capacity(self) -> ProgramCapacities {
    self.0
  }
  pub fn block_words(self) -> usize {
    2 + 3 * self.0.operands
  }
  pub fn words(self) -> usize {
    1 + self.0.functions + self.0.functions * self.0.blocks * self.block_words()
  }
  pub fn function_word(self, function: usize) -> usize {
    assert!(function < self.0.functions);
    1 + function
  }
  pub fn block_word(self, function: usize, block: usize) -> usize {
    assert!(function < self.0.functions && block < self.0.blocks);
    1 + self.0.functions
      + (function * self.0.blocks + block) * self.block_words()
  }
}

#[derive(Clone, Debug)]
pub struct ProgramDecodeGate {
  nu: usize,
  capacity: ProgramCapacities,
  control: ControlCapacities,
  primitives: PrimitiveSet,
  plan: Arc<OnceLock<BooleanR1csPlan>>,
}

#[derive(Clone, Debug)]
pub struct ProgramDecodeRow(Vec<F128>);

impl ProgramDecodeGate {
  pub fn new(
    nu: usize,
    capacity: ProgramCapacities,
    control: ControlCapacities,
    primitives: PrimitiveSet,
  ) -> Result<Self> {
    capacity.validate()?;
    ControlStepGate::new(nu, control)?;
    ensure!(
      control.arguments <= capacity.operands,
      "callee arguments exceed operand bank"
    );
    Ok(Self {
      nu,
      capacity,
      control,
      primitives,
      plan: Arc::new(OnceLock::new()),
    })
  }
  pub fn capacity(&self) -> ProgramCapacities {
    self.capacity
  }
  pub fn layout(&self) -> ProgramLayout {
    self.capacity.layout()
  }
  fn plan(&self) -> &BooleanR1csPlan {
    self
      .plan
      .get_or_init(|| build(self.capacity, self.control, self.primitives))
  }
  pub fn r1cs(&self) -> BlockR1cs {
    self.plan().block_r1cs(self.nu)
  }
  pub fn generate_witness_into(
    &self,
    rows: &[ProgramDecodeRow],
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

impl CountedGate for ProgramDecodeGate {
  fn input_count(&self) -> usize {
    1 + self.capacity.data_words()
  }
  fn output_count(&self) -> usize {
    self.layout().words() + 1
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut gate = self.clone();
    gate.nu = nu;
    gate.table()
  }
}

impl GateType for ProgramDecodeGate {
  type Row = ProgramDecodeRow;
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
    ProgramDecodeRow(inputs.to_vec())
  }
  fn witness(&self, _: &[Self::Row], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}

#[derive(Clone, Copy, Debug)]
pub struct ProgramDecodeSlot {
  slot: SlotId,
  zero: Wire,
  layout: ProgramLayout,
}

impl ProgramDecodeSlot {
  pub fn declare(b: &mut impl CircuitEmitter, gate: ProgramDecodeGate) -> Self {
    let layout = gate.layout();
    Self { slot: b.slot(gate), zero: b.fixed_public_input(F128::ZERO), layout }
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
    assert_eq!(data.len(), self.layout.0.data_words());
    let mut input = vec![length];
    input.extend_from_slice(data);
    let output = b.gate(self.slot, &input);
    b.connect(output[self.layout.words()], self.zero);
    output[..self.layout.words()].to_vec()
  }
}

struct Block {
  locals: Bits,
  target: Bits,
  alternative: Bits,
  callee: Bits,
  args: Bits,
  binding: usize,
  entering: usize,
  branch: usize,
}

struct Function {
  enabled: usize,
  arity: Bits,
  entry: Bits,
  count: Bits,
  blocks: Vec<Block>,
}

fn enum_bits(d: &mut Decoder, variants: &[(usize, u32)]) -> Bits {
  (0..32)
    .map(|bit| {
      let flags: Vec<_> = variants
        .iter()
        .filter(|(_, value)| value & (1 << bit) != 0)
        .map(|(flag, _)| *flag)
        .collect();
      d.sum(&flags)
    })
    .collect()
}

fn selected(d: &mut Decoder, index: &[usize], values: &[&[usize]]) -> Bits {
  let selectors: Vec<_> =
    (0..values.len()).map(|i| d.eq_const(index, i as u64)).collect();
  let terms: Vec<_> =
    selectors.into_iter().zip(values.iter().copied()).collect();
  d.choose(&terms)
}

fn block(
  d: &mut Decoder,
  c: ProgramCapacities,
  control: ControlCapacities,
  primitives: PrimitiveSet,
  function: usize,
  enabled: usize,
  output: usize,
) -> Block {
  let locals = d.u32(enabled);
  d.bounded(&locals, control.locals, enabled);
  let instruction = d.byte(enabled);
  let matches: Vec<_> =
    [0, 1, 2, 3, 6].map(|tag| d.eq_const(&instruction, tag)).into();
  let valid = d.sum(&matches);
  d.require(enabled, valid);
  let modes: Vec<_> =
    matches.into_iter().map(|matched| d.and(enabled, matched)).collect();
  let [let_op, returning, tail_direct, tail_self, branch]: [usize; 5] =
    modes.try_into().unwrap();
  let op = d.byte(let_op);
  let matches: Vec<_> = [0, 1, 5, 6].map(|tag| d.eq_const(&op, tag)).into();
  let valid = d.sum(&matches);
  d.require(let_op, valid);
  let modes: Vec<_> =
    matches.into_iter().map(|matched| d.and(let_op, matched)).collect();
  let [copy, primitive, call_direct, call_self]: [usize; 4] =
    modes.try_into().unwrap();
  let opcode = d.byte(primitive);
  let direct = d.sum(&[call_direct, tail_direct]);
  let direct_callee = d.u32(direct);
  let self_call = d.sum(&[call_self, tail_self]);
  let self_index = d.constant(32, function as u64);
  let callee = d.choose(&[(d.one, &direct_callee), (self_call, &self_index)]);
  let call = d.sum(&[call_direct, call_self]);
  let tail = d.sum(&[tail_direct, tail_self]);
  let entering = d.sum(&[call, tail]);
  let vector = d.sum(&[primitive, entering]);
  let vector_count = d.u32(vector);
  let single = d.sum(&[copy, returning, branch]);
  let one = d.constant(32, 1);
  let args = d.choose(&[(d.one, &vector_count), (single, &one)]);
  let counts = d.bounded(&args, c.operands, enabled);
  let primitive_matches: Vec<_> = primitives
    .opcodes()
    .map(|opcode_value| {
      (
        d.eq_const(&opcode, u64::from(opcode_value)),
        scalar_primitive_arity(opcode_value).unwrap() as u32,
      )
    })
    .collect();
  let primitive_valid = d.sum(
    &primitive_matches.iter().map(|(matched, _)| *matched).collect::<Vec<_>>(),
  );
  d.require(primitive, primitive_valid);
  let arity = enum_bits(d, &primitive_matches);
  let arity_matches = d.equal(&args, &arity);
  d.require(primitive, arity_matches);
  for operand in 0..c.operands {
    let active = d.live(&counts, operand, enabled);
    let record = d.operand(active, &locals);
    for (word, value) in record.iter().enumerate() {
      d.write(output + 2 + 3 * operand + word, value);
    }
  }
  let transfer = d.sum(&[let_op, branch]);
  let target = d.u32(transfer);
  let alternative = d.u32(branch);
  let kind = enum_bits(
    d,
    &[
      (copy, 1),
      (primitive, 2),
      (call, 3),
      (returning, 4),
      (tail, 5),
      (branch, 6),
    ],
  );
  let header = d.pack(&[&locals, &kind, &target, &alternative]);
  d.write(output, &header);
  let header = d.pack(&[&callee, &opcode, &args]);
  d.write(output + 1, &header);
  let binding = d.sum(&[copy, primitive, call]);
  Block { locals, target, alternative, callee, args, binding, entering, branch }
}

fn build(
  c: ProgramCapacities,
  control: ControlCapacities,
  primitives: PrimitiveSet,
) -> BooleanR1csPlan {
  let layout = c.layout();
  let output = 1 + c.data_words();
  let reads = 5 + c.functions * (3 + c.blocks * (8 + 4 * c.operands));
  let extra = 4096
    + 4096 * c.functions * c.blocks
    + 1024 * (c.functions + c.blocks).pow(2);
  let mut d = Decoder::new(c.bytes, output, layout.words() + 1, reads, extra);
  d.header(b"IXBY");
  let entry = d.u32(d.one);
  let constructors = d.u32(d.one);
  d.require_zero(d.one, &constructors);
  let count = d.u32(d.one);
  let counts = d.bounded(&count, c.functions, d.one);
  let entry_in_range = d.less(&entry, &count);
  d.require(d.one, entry_in_range);
  let header = d.pack(&[&entry, &count]);
  d.write(output, &header);
  let mut functions = Vec::new();
  for function in 0..c.functions {
    let enabled = d.live(&counts, function, d.one);
    let arity = d.u32(enabled);
    d.bounded(&arity, control.arguments, enabled);
    let entry = d.u32(enabled);
    let count = d.u32(enabled);
    let blocks = d.bounded(&count, c.blocks, enabled);
    let entry_in_range = d.less(&entry, &count);
    d.require(enabled, entry_in_range);
    let header = d.pack(&[&arity, &entry, &count]);
    d.write(output + layout.function_word(function), &header);
    let blocks = (0..c.blocks)
      .map(|index| {
        let active = d.live(&blocks, index, enabled);
        block(
          &mut d,
          c,
          control,
          primitives,
          function,
          active,
          output + layout.block_word(function, index),
        )
      })
      .collect();
    functions.push(Function { enabled, arity, entry, count, blocks });
  }
  // Whole-image validation, including every unvisited block/function. The
  // decoded table is fixed-size; invalid indices cannot alias padding slots.
  let arities: Vec<_> =
    functions.iter().map(|function| function.arity.as_slice()).collect();
  for function in &functions {
    let block_locals: Vec<_> =
      function.blocks.iter().map(|block| block.locals.as_slice()).collect();
    let entry_locals = selected(&mut d, &function.entry, &block_locals);
    let entry_contract = d.equal(&entry_locals, &function.arity);
    d.require(function.enabled, entry_contract);
    for block in &function.blocks {
      let transfers = d.sum(&[block.binding, block.branch]);
      let valid = d.less(&block.target, &function.count);
      d.require(transfers, valid);
      let destination = selected(&mut d, &block.target, &block_locals);
      let one = d.constant(32, 1);
      let (appended, carry) = add(&mut d.b, d.one, d.zero, &block.locals, &one);
      let overflow = d.and(block.binding, carry);
      d.violate(overflow);
      let expected =
        d.choose(&[(block.binding, &appended), (block.branch, &block.locals)]);
      let same = d.equal(&destination, &expected);
      d.require(transfers, same);
      let valid = d.less(&block.alternative, &function.count);
      d.require(block.branch, valid);
      let alternative = selected(&mut d, &block.alternative, &block_locals);
      let same = d.equal(&alternative, &block.locals);
      d.require(block.branch, same);
      let valid = d.less(&block.callee, &count);
      d.require(block.entering, valid);
      let callee_arity = selected(&mut d, &block.callee, &arities);
      let same = d.equal(&callee_arity, &block.args);
      d.require(block.entering, same);
    }
  }
  d.finish(output + layout.words())
}
