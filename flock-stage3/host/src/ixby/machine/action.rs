use crate::{
  boolean::{
    BooleanR1csBuilder, BooleanR1csPlan, generate_boolean_witness_into,
  },
  ixby::{
    bits::{
      any, constant_bits, equal_constant, evaluate_words, fill_words, not,
      require, require_zero, select, subtract,
    },
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

#[derive(Clone, Debug)]
pub struct ActionAssembleGate {
  nu: usize,
  control: ControlCapacities,
  operands: usize,
  applications: bool,
  pub(super) plan: Arc<OnceLock<BooleanR1csPlan>>,
}
#[derive(Clone, Debug)]
pub struct ActionAssembleRow(pub(super) Vec<F128>);
impl ActionAssembleGate {
  pub fn new(
    nu: usize,
    control: ControlCapacities,
    operands: usize,
  ) -> Result<Self> {
    ControlStepGate::new(nu, control)?;
    ensure!((1..=4).contains(&operands), "action operand capacity");
    ensure!(control.arguments <= operands, "action argument capacity");
    Ok(Self {
      nu,
      control,
      operands,
      applications: false,
      plan: Arc::new(OnceLock::new()),
    })
  }
  pub(super) fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(|| build(self))
  }
  pub(crate) fn with_applications(mut self) -> Self {
    assert_eq!(self.control.arguments, self.operands);
    self.applications = true;
    self.plan = Arc::new(OnceLock::new());
    self
  }
  fn action_words(&self) -> usize {
    if self.applications {
      self.control.application_action_words()
    } else {
      self.control.action_words()
    }
  }
  pub fn r1cs(&self) -> BlockR1cs {
    self.plan().block_r1cs(self.nu)
  }
  pub fn generate_witness_into(
    &self,
    rows: &[ActionAssembleRow],
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
impl CountedGate for ActionAssembleGate {
  fn input_count(&self) -> usize {
    5 + 2 * self.operands
      + if self.applications { 3 + 2 * self.operands } else { 0 }
  }
  fn output_count(&self) -> usize {
    self.action_words() + 1
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut gate = self.clone();
    gate.nu = nu;
    gate.table()
  }
}
impl GateType for ActionAssembleGate {
  type Row = ActionAssembleRow;
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
    ActionAssembleRow(input.to_vec())
  }
  fn witness(&self, _: &[Self::Row], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}
#[derive(Clone, Copy, Debug)]
pub struct ActionAssembleSlot {
  slot: SlotId,
  zero: Wire,
  operand_words: usize,
  words: usize,
}
impl ActionAssembleSlot {
  pub fn declare(
    b: &mut impl CircuitEmitter,
    gate: ActionAssembleGate,
  ) -> Self {
    let (operand_words, words) = (gate.input_count() - 5, gate.action_words());
    Self {
      slot: b.slot(gate),
      zero: b.fixed_public_input(F128::ZERO),
      operand_words,
      words,
    }
  }
  pub fn slot(&self) -> SlotId {
    self.slot
  }
  pub fn assemble(
    &self,
    b: &mut impl CircuitEmitter,
    headers: &[Wire; 2],
    callee: Wire,
    primitive: &[Wire; 2],
    operands: &[Wire],
  ) -> Vec<Wire> {
    assert_eq!(operands.len(), self.operand_words);
    let mut input =
      vec![headers[0], headers[1], callee, primitive[0], primitive[1]];
    input.extend_from_slice(operands);
    let output = b.gate(self.slot, &input);
    b.connect(output[self.words], self.zero);
    output[..self.words].to_vec()
  }
}
fn build(gate: &ActionAssembleGate) -> BooleanR1csPlan {
  let reserved = 128 * (gate.input_count() + gate.output_count());
  let columns = reserved
    + 4096
    + 512 * gate.operands
    + if gate.applications { 8192 + 1024 * gate.operands } else { 0 };
  let mut b = BooleanR1csBuilder::new(
    columns.next_power_of_two().ilog2() as usize,
    reserved,
  );
  for bit in 0..128 * gate.input_count() {
    b.free_boolean_at(bit);
  }
  let one = b.alloc_constant_one();
  let zero = b.xor(&[one, one], one);
  let kind: Vec<_> = (32..64).collect();
  let mut flags: Vec<_> =
    (0..=6).map(|value| equal_constant(&mut b, one, &kind, value)).collect();
  if gate.applications {
    flags.resize(12, zero);
    flags
      .extend((12..=15).map(|value| equal_constant(&mut b, one, &kind, value)));
  }
  let valid = b.xor(&flags, one);
  let mut violations = Vec::new();
  require(&mut b, one, &mut violations, one, valid);
  require_zero(
    &mut b,
    one,
    &mut violations,
    flags[0],
    &(0..gate.input_count() * 128).collect::<Vec<_>>(),
  );
  let entering = if gate.applications {
    b.xor(&[flags[3], flags[5], flags[15]], one)
  } else {
    b.xor(&[flags[3], flags[5]], one)
  };
  let starting =
    if gate.applications { b.xor(&[flags[12], flags[13]], one) } else { zero };
  let argument_used = if gate.applications {
    b.xor(&[entering, starting], one)
  } else {
    entering
  };
  let primitive_used = if gate.applications {
    b.xor(&[flags[2], flags[14]], one)
  } else {
    flags[2]
  };
  let not_entering = not(&mut b, one, entering);
  require_zero(
    &mut b,
    one,
    &mut violations,
    not_entering,
    &(256..384).collect::<Vec<_>>(),
  );
  let not_primitive = not(&mut b, one, primitive_used);
  require_zero(
    &mut b,
    one,
    &mut violations,
    not_primitive,
    &(384..640).collect::<Vec<_>>(),
  );
  let maximum = constant_bits(one, zero, (gate.control.arguments + 1) as u32);
  let count_ok =
    subtract(&mut b, one, zero, &(192..224).collect::<Vec<_>>(), &maximum).1;
  require(&mut b, one, &mut violations, argument_used, count_ok);
  let mut out = vec![zero; 128 * gate.action_words()];
  let mut modes = vec![
    (1u32, &[1, 2][..]),
    (2, &[3][..]),
    (3, &[4][..]),
    (4, &[5][..]),
    (5, &[6][..]),
  ];
  if gate.applications {
    modes.extend([
      (6, &[12][..]),
      (7, &[13][..]),
      (8, &[14][..]),
      (9, &[15][..]),
    ]);
  }
  for (mode, indices) in modes {
    let flag = b
      .xor(&indices.iter().map(|index| flags[*index]).collect::<Vec<_>>(), one);
    for (bit, target) in
      out.iter_mut().enumerate().take(if gate.applications { 4 } else { 3 })
    {
      if mode & (1 << bit) != 0 {
        *target = b.xor(&[*target, flag], one);
      }
    }
  }
  let target = if gate.applications {
    b.xor(&[flags[1], flags[2], flags[3], flags[6], flags[12]], one)
  } else {
    b.xor(&[flags[1], flags[2], flags[3], flags[6]], one)
  };
  for bit in 0..32 {
    out[32 + bit] = b.and(target, 64 + bit);
    out[64 + bit] = b.and(flags[6], 96 + bit);
    out[96 + bit] = b.and(entering, 128 + bit);
    out[128 + bit] = b.and(entering, 288 + bit);
    out[160 + bit] = b.and(entering, 256 + bit);
    out[192 + bit] = b.and(argument_used, 192 + bit);
  }
  let operand_value = b.xor(&[flags[1], flags[4], flags[6]], one);
  let mut sources = vec![(operand_value, 640), (primitive_used, 384)];
  if gate.applications {
    sources.push((starting, 640 + 256 * gate.operands));
  }
  let value = select(&mut b, one, zero, &sources, 256);
  out[256..512].copy_from_slice(&value);
  for (bit, target) in
    out[512..128 * gate.control.action_words()].iter_mut().enumerate()
  {
    *target = b.and(argument_used, 640 + bit);
  }
  if gate.applications {
    let rest = 640 + 256 * (gate.operands + 1);
    for (bit, target) in
      out[128 * gate.control.action_words()..].iter_mut().enumerate()
    {
      *target = b.and(flags[15], rest + bit);
    }
  }
  for (bit, source) in out.iter().enumerate() {
    b.write_xor(128 * gate.input_count() + bit, &[*source], one);
  }
  let violation = any(&mut b, one, &violations);
  b.write_xor(
    128 * (gate.input_count() + gate.action_words()),
    &[violation],
    one,
  );
  b.finish()
}
