use super::{
  PrimitiveSet,
  bytes::{Bits, Decoder},
  evaluate, fill_words, primitive_arity,
};
use crate::{
  boolean::{BooleanR1csPlan, generate_boolean_witness_into},
  ixby::{
    bits::add,
    byte_value::ByteDecodeLayout,
    control::{ControlCapacities, ControlStepGate},
    object_value::ObjectLayout,
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
#[path = "program_nat_tests.rs"]
mod nat_tests;
#[cfg(test)]
#[path = "program_object_tests.rs"]
mod object_tests;
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
  byte_layout: Option<ByteDecodeLayout>,
  object_layout: Option<ObjectLayout>,
  nat_capacity: Option<crate::ixby::nat_value::NatCapacity>,
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
    layout.validate(self.byte_records())?;
    self.byte_layout = Some(layout);
    self.plan = Arc::new(OnceLock::new());
    Ok(self)
  }
  fn byte_records(&self) -> usize {
    self.capacity.functions * self.capacity.blocks * self.capacity.operands
  }
  pub(crate) fn with_objects(mut self, layout: ObjectLayout) -> Result<Self> {
    ensure!(
      self.byte_layout.is_some(),
      "object programs require byte-capable literals"
    );
    self.object_layout = Some(layout);
    self.plan = Arc::new(OnceLock::new());
    Ok(self)
  }
  pub(crate) fn object_data_word(&self) -> usize {
    self.layout().words()
      + self.byte_layout.map_or(0, |layout| {
        self.byte_records() * layout.capacity.record_words()
      })
  }
  pub(crate) fn with_nat_values(
    mut self,
    capacity: crate::ixby::nat_value::NatCapacity,
  ) -> Result<Self> {
    ensure!(
      self
        .byte_layout
        .is_some_and(|bytes| bytes.capacity.bytes() >= capacity.bytes()),
      "Nat literal magnitude capacity"
    );
    self.nat_capacity = Some(capacity);
    self.plan = Arc::new(OnceLock::new());
    Ok(self)
  }
  pub fn decoded_words(&self) -> usize {
    self.layout().words()
      + self.byte_layout.map_or(0, |layout| {
        self.byte_records() * layout.capacity.record_words()
      })
      + self.object_layout.map_or(0, ObjectLayout::program_words)
  }
  pub fn capacity(&self) -> ProgramCapacities {
    self.capacity
  }
  pub fn layout(&self) -> ProgramLayout {
    self.capacity.layout()
  }
  fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(|| {
      build(
        self.capacity,
        self.control,
        self.primitives,
        self.byte_layout,
        self.object_layout,
        self.nat_capacity,
      )
    })
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
    self.decoded_words() + 1
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
  words: usize,
}

impl ProgramDecodeSlot {
  pub fn declare(b: &mut impl CircuitEmitter, gate: ProgramDecodeGate) -> Self {
    let layout = gate.layout();
    let words = gate.decoded_words();
    Self {
      slot: b.slot(gate),
      zero: b.fixed_public_input(F128::ZERO),
      layout,
      words,
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
    assert_eq!(data.len(), self.layout.0.data_words());
    let mut input = vec![length];
    input.extend_from_slice(data);
    let output = b.gate(self.slot, &input);
    b.connect(output[self.words], self.zero);
    output[..self.words].to_vec()
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
  nat_case: usize,
  cases: Vec<(usize, Bits, Bits)>,
}

struct ObjectBlock<'a> {
  layout: ObjectLayout,
  output: usize,
  count: &'a Bits,
  declarations: &'a [[Bits; 4]],
}
struct BlockExtras<'a> {
  bytes: Option<(ByteDecodeLayout, usize, usize)>,
  objects: Option<ObjectBlock<'a>>,
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
  location: (usize, usize),
  enabled: usize,
  extras: BlockExtras<'_>,
) -> Block {
  let (function, output) = location;
  let locals = d.u32(enabled);
  d.bounded(&locals, control.locals, enabled);
  let instruction = d.byte(enabled);
  let mut matches: Vec<_> =
    [0, 1, 2, 3, 6].map(|tag| d.eq_const(&instruction, tag)).into();
  if extras.objects.is_some() {
    matches.push(d.eq_const(&instruction, 5));
  }
  if d.nat_capacity.is_some() {
    matches.push(d.eq_const(&instruction, 7));
  }
  let valid = d.sum(&matches);
  d.require(enabled, valid);
  let modes: Vec<_> =
    matches.into_iter().map(|matched| d.and(enabled, matched)).collect();
  let [let_op, returning, tail_direct, tail_self, branch]: [usize; 5] =
    modes[..5].try_into().unwrap();
  let case = if extras.objects.is_some() { modes[5] } else { d.zero };
  let nat_case =
    if d.nat_capacity.is_some() { *modes.last().unwrap() } else { d.zero };
  let op = d.byte(let_op);
  let mut matches: Vec<_> = [0, 1, 5, 6].map(|tag| d.eq_const(&op, tag)).into();
  if extras.objects.is_some() {
    matches.extend([2, 3].map(|tag| d.eq_const(&op, tag)));
  }
  let valid = d.sum(&matches);
  d.require(let_op, valid);
  let modes: Vec<_> =
    matches.into_iter().map(|matched| d.and(let_op, matched)).collect();
  let [copy, primitive, call_direct, call_self]: [usize; 4] =
    modes[..4].try_into().unwrap();
  let construct = modes.get(4).copied().unwrap_or(d.zero);
  let project = modes.get(5).copied().unwrap_or(d.zero);
  let opcode = d.byte(primitive);
  let direct = d.sum(&[call_direct, tail_direct]);
  let direct_callee = d.u32(direct);
  let self_call = d.sum(&[call_self, tail_self]);
  let self_index = d.constant(32, function as u64);
  let mut callee =
    d.choose(&[(d.one, &direct_callee), (self_call, &self_index)]);
  let declaration = extras.objects.as_ref().map(|_| d.u32(construct));
  let call = d.sum(&[call_direct, call_self]);
  let tail = d.sum(&[tail_direct, tail_self]);
  let entering = d.sum(&[call, tail]);
  let vector = if extras.objects.is_some() {
    d.sum(&[primitive, entering, construct])
  } else {
    d.sum(&[primitive, entering])
  };
  let vector_count = d.u32(vector);
  let mut single = if extras.objects.is_some() {
    d.sum(&[copy, returning, branch, project, case])
  } else {
    d.sum(&[copy, returning, branch])
  };
  if d.nat_capacity.is_some() {
    single = d.sum(&[single, nat_case]);
  }
  let one = d.constant(32, 1);
  let args = d.choose(&[(d.one, &vector_count), (single, &one)]);
  let counts = d.bounded(&args, c.operands, enabled);
  let primitive_matches: Vec<_> = primitives
    .opcodes()
    .map(|opcode_value| {
      (
        d.eq_const(&opcode, u64::from(opcode_value)),
        primitive_arity(opcode_value).unwrap() as u32,
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
  if let (Some(objects), Some(declaration)) = (&extras.objects, &declaration) {
    let in_range = d.less(declaration, objects.count);
    d.require(construct, in_range);
    let fields: Vec<_> =
      objects.declarations.iter().map(|record| &record[3][..32]).collect();
    let expected = selected(d, declaration, &fields);
    let same = d.equal(&args, &expected);
    d.require(construct, same);
  }
  for operand in 0..c.operands {
    let active = d.live(&counts, operand, enabled);
    let record = match extras.bytes {
      None => d.operand(active, &locals),
      Some((layout, first_slot, byte_output)) => {
        let (record, data) =
          d.operand_with_bytes(active, &locals, layout, first_slot + operand);
        for (word, bits) in data.iter().enumerate() {
          d.write(
            byte_output + operand * layout.capacity.record_words() + word,
            bits,
          );
        }
        record
      },
    };
    for (word, value) in record.iter().enumerate() {
      d.write(output + 2 + 3 * operand + word, value);
    }
  }
  let mut cases: Vec<(usize, Bits, Bits)> = Vec::new();
  if let Some(objects) = &extras.objects {
    let field = d.u32(project);
    callee = d.choose(&[
      (d.one, &callee),
      (d.one, declaration.as_ref().unwrap()),
      (d.one, &field),
    ]);
    let count = d.u32(case);
    let alternatives =
      d.bounded(&count, objects.layout.capacity.constructors(), case);
    d.write(objects.output, &count);
    for index in 0..objects.layout.capacity.constructors() {
      let active = d.live(&alternatives, index, case);
      let ctor = d.u32(active);
      let target = d.u32(active);
      let valid = d.less(&ctor, objects.count);
      d.require(active, valid);
      for (previous, previous_ctor, _) in &cases {
        let same = d.equal(&ctor, previous_ctor);
        let both = d.and(active, *previous);
        let duplicate = d.and(both, same);
        d.violate(duplicate);
      }
      let word = d.pack(&[&ctor, &target]);
      d.write(objects.output + 1 + index, &word);
      cases.push((active, ctor, target));
    }
  }
  let branching =
    if d.nat_capacity.is_some() { d.sum(&[branch, nat_case]) } else { branch };
  let transfer = d.sum(&[let_op, branching]);
  let target = d.u32(transfer);
  let alternative = d.u32(branching);
  let mut kinds = vec![
    (copy, 1),
    (primitive, 2),
    (call, 3),
    (returning, 4),
    (tail, 5),
    (branch, 6),
  ];
  if extras.objects.is_some() {
    kinds.extend([(construct, 7), (project, 8), (case, 9)]);
  }
  if d.nat_capacity.is_some() {
    kinds.push((nat_case, 10));
  }
  let kind = enum_bits(d, &kinds);
  let header = d.pack(&[&locals, &kind, &target, &alternative]);
  d.write(output, &header);
  let header = d.pack(&[&callee, &opcode, &args]);
  d.write(output + 1, &header);
  let binding = if extras.objects.is_some() {
    d.sum(&[copy, primitive, call, construct, project])
  } else {
    d.sum(&[copy, primitive, call])
  };
  Block {
    locals,
    target,
    alternative,
    callee,
    args,
    binding,
    entering,
    branch,
    nat_case,
    cases,
  }
}

fn build(
  c: ProgramCapacities,
  control: ControlCapacities,
  primitives: PrimitiveSet,
  byte_layout: Option<ByteDecodeLayout>,
  object_layout: Option<ObjectLayout>,
  nat_capacity: Option<crate::ixby::nat_value::NatCapacity>,
) -> BooleanR1csPlan {
  // A registry alone cannot enable revision-1 guest instructions in v0.
  let primitives = if nat_capacity.is_some() {
    primitives
  } else {
    primitives.crypto_subset()
  };
  let layout = c.layout();
  let output = 1 + c.data_words();
  let records = c.functions * c.blocks * c.operands;
  let reads = 5
    + c.functions * (3 + c.blocks * (8 + 4 * c.operands))
    + byte_layout
      .map_or(0, |layout| records * (1 + layout.capacity.data_words()))
    + object_layout.map_or(0, |layout| {
      5 * layout.capacity.constructors()
        + c.functions * c.blocks * (3 + 2 * layout.capacity.constructors())
    });
  let extra = 4096
    + 4096 * c.functions * c.blocks
    + 1024 * (c.functions + c.blocks).pow(2)
    + byte_layout
      .map_or(0, |layout| 256 * records * (layout.capacity.bytes() + 1))
    + object_layout.map_or(0, |layout| {
      8192
        * layout.capacity.constructors()
        * (layout.capacity.constructors() + c.functions * c.blocks)
    });
  let words = layout.words()
    + byte_layout.map_or(0, |layout| records * layout.capacity.record_words())
    + object_layout.map_or(0, ObjectLayout::program_words);
  let object_output =
    output + words - object_layout.map_or(0, ObjectLayout::program_words);
  let mut d = Decoder::new(c.bytes, output, words + 1, reads, extra);
  d.nat_capacity = nat_capacity;
  d.header(b"IXBY");
  let entry = d.u32(d.one);
  let constructors = d.u32(d.one);
  let mut declarations: Vec<[Bits; 4]> = Vec::new();
  if let Some(objects) = object_layout {
    let live = d.bounded(&constructors, objects.capacity.constructors(), d.one);
    d.write(object_output, &constructors);
    for index in 0..objects.capacity.constructors() {
      let enabled = d.live(&live, index, d.one);
      let first = d.read(128, &[(enabled, 16)]);
      let second = d.read(128, &[(enabled, 16)]);
      let member = d.u32(enabled);
      let tag = d.u32(enabled);
      let fields = d.u32(enabled);
      d.bounded(&fields, c.operands, enabled);
      let record = [
        first,
        second,
        d.pack(&[&member, &tag]),
        d.pack(&[&fields, &[enabled]]),
      ];
      for previous in &declarations {
        let mut same = d.and(enabled, previous[3][32]);
        for word in 0..3 {
          let equal = d.equal(&record[word], &previous[word]);
          same = d.and(same, equal);
        }
        d.violate(same);
      }
      for (word, bits) in record.iter().enumerate() {
        d.write(object_output + 1 + 4 * index + word, bits);
      }
      declarations.push(record);
    }
  } else {
    d.require_zero(d.one, &constructors);
  }
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
          (function, output + layout.block_word(function, index)),
          active,
          BlockExtras {
            bytes: byte_layout.map(|bytes| {
              let first = (function * c.blocks + index) * c.operands;
              (
                bytes,
                first,
                output + layout.words() + first * bytes.capacity.record_words(),
              )
            }),
            objects: object_layout.map(|objects| ObjectBlock {
              layout: objects,
              output: object_output + objects.case_word(function, index),
              count: &constructors,
              declarations: &declarations,
            }),
          },
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
      let branching = if nat_capacity.is_some() {
        d.sum(&[block.branch, block.nat_case])
      } else {
        block.branch
      };
      let transfers = d.sum(&[block.binding, branching]);
      let valid = d.less(&block.target, &function.count);
      d.require(transfers, valid);
      let destination = selected(&mut d, &block.target, &block_locals);
      let one = d.constant(32, 1);
      let (appended, carry) = add(&mut d.b, d.one, d.zero, &block.locals, &one);
      let overflow = d.and(block.binding, carry);
      d.violate(overflow);
      let expected =
        d.choose(&[(block.binding, &appended), (branching, &block.locals)]);
      let same = d.equal(&destination, &expected);
      d.require(transfers, same);
      let valid = d.less(&block.alternative, &function.count);
      d.require(branching, valid);
      let alternative = selected(&mut d, &block.alternative, &block_locals);
      let expected = if nat_capacity.is_some() {
        let overflow = d.and(block.nat_case, carry);
        d.violate(overflow);
        d.choose(&[(block.branch, &block.locals), (block.nat_case, &appended)])
      } else {
        block.locals.clone()
      };
      let same = d.equal(&alternative, &expected);
      d.require(branching, same);
      let valid = d.less(&block.callee, &count);
      d.require(block.entering, valid);
      let callee_arity = selected(&mut d, &block.callee, &arities);
      let same = d.equal(&callee_arity, &block.args);
      d.require(block.entering, same);
      if object_layout.is_some() {
        let fields: Vec<_> =
          declarations.iter().map(|record| &record[3][..32]).collect();
        for (enabled, ctor, target) in &block.cases {
          let valid = d.less(target, &function.count);
          d.require(*enabled, valid);
          let fields = selected(&mut d, ctor, &fields);
          let (appended, carry) =
            add(&mut d.b, d.one, d.zero, &block.locals, &fields);
          let overflow = d.and(*enabled, carry);
          d.violate(overflow);
          let destination = selected(&mut d, target, &block_locals);
          let same = d.equal(&destination, &appended);
          d.require(*enabled, same);
        }
      }
    }
  }
  d.finish(output + words)
}
