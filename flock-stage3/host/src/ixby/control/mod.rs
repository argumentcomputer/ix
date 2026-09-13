//! Fixed-capacity scalar/control CEK transitions. The action is an interface
//! to constrained instruction fetch/operand/primitive resolution, NOT trusted
//! advice and NOT another guest instruction set. `machine`/`exec` wire this
//! component to canonical decoding and constrained instruction resolution.
//!
//! State words: (kind, remaining fuel, depth, 0), current frame, return value,
//! then a live-prefix stack of saved frames. A frame is (function, block,
//! local count, 0) followed by `locals` two-word cells in logical index order.
//! Every metadata lane is u32, every unused cell/frame is zero. Return/halting
//! states have a zero current frame; eval states have a zero return value.
//!
//! Actions: two four-u32 headers, value cell, fixed argument bank. Header 0 is
//! (kind, target, alternative, callee); header 1 is (entry, arity, arg count, 0).
//! Kinds 1..5 are bind/call/return/tail-call/branch. Non-eval states require an
//! all-zero action. The only halting transition is ret with an empty stack.

#[cfg(test)]
mod proof_tests;
mod synthesis;
#[cfg(test)]
mod tests;

use super::value::{BOOL_TAG, ValueWords};
use crate::{
  boolean::{BooleanR1csPlan, generate_boolean_witness_into, write_f128},
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ControlCapacities {
  pub locals: usize,
  pub continuations: usize,
  pub arguments: usize,
}

impl ControlCapacities {
  fn validate(self) -> Result<()> {
    ensure!((1..=16).contains(&self.locals), "control local capacity");
    ensure!(self.continuations <= 8, "control continuation capacity");
    ensure!(self.arguments <= self.locals, "control argument capacity");
    Ok(())
  }
  pub fn frame_words(self) -> usize {
    1 + 2 * self.locals
  }
  pub fn state_words(self) -> usize {
    3 + (self.continuations + 1) * self.frame_words()
  }
  pub fn action_words(self) -> usize {
    4 + 2 * self.arguments
  }
  fn value_word(self) -> usize {
    1 + self.frame_words()
  }
  fn stack_word(self, index: usize) -> usize {
    3 + (index + 1) * self.frame_words()
  }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ControlFrame {
  pub function: u32,
  pub block: u32,
  pub locals: Vec<ValueWords>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Control {
  Eval(ControlFrame),
  Ret(ValueWords),
  /// Physical absorbing padding after the genuine terminal transition.
  Halted(ValueWords),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ControlState {
  pub control: Control,
  pub continuation: Vec<ControlFrame>,
  pub remaining: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CallTarget {
  pub function: u32,
  pub entry: u32,
  pub arity: u32,
}

/// Untrusted witness-builder input. Call metadata must come from authenticated
/// program tables and values/arguments from constrained operand evaluation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResolvedAction {
  Idle,
  Bind { target: u32, value: ValueWords },
  Call { target: u32, callee: CallTarget, args: Vec<ValueWords> },
  Return { value: ValueWords },
  TailCall { callee: CallTarget, args: Vec<ValueWords> },
  Branch { condition: ValueWords, yes: u32, no: u32 },
}

fn meta(a: u32, b: u32, c: u32, d: u32) -> F128 {
  F128::new(
    u64::from(a) | (u64::from(b) << 32),
    u64::from(c) | (u64::from(d) << 32),
  )
}

fn lanes(word: F128) -> [u32; 4] {
  [
    word.lo as u32,
    (word.lo >> 32) as u32,
    word.hi as u32,
    (word.hi >> 32) as u32,
  ]
}

fn fill_frame(
  capacity: ControlCapacities,
  frame: &ControlFrame,
  words: &mut [F128],
) -> Result<()> {
  ensure!(frame.locals.len() <= capacity.locals, "witness frame width");
  assert_eq!(words.len(), capacity.frame_words());
  words[0] = meta(frame.function, frame.block, frame.locals.len() as u32, 0);
  for (index, value) in frame.locals.iter().enumerate() {
    words[1 + 2 * index..3 + 2 * index].copy_from_slice(value);
  }
  Ok(())
}

impl ControlState {
  /// Convenience for honest witnesses only. Hostile-advice tests bypass it;
  /// all these layout/padding checks are independently present in the gate.
  pub fn words(&self, capacity: ControlCapacities) -> Result<Vec<F128>> {
    capacity.validate()?;
    ensure!(
      self.continuation.len() <= capacity.continuations,
      "witness stack width"
    );
    let mut words = vec![F128::ZERO; capacity.state_words()];
    let kind = match &self.control {
      Control::Eval(frame) => {
        fill_frame(capacity, frame, &mut words[1..1 + capacity.frame_words()])?;
        0
      },
      Control::Ret(value) | Control::Halted(value) => {
        words[capacity.value_word()..capacity.value_word() + 2]
          .copy_from_slice(value);
        if matches!(self.control, Control::Ret(_)) { 1 } else { 2 }
      },
    };
    words[0] = meta(kind, self.remaining, self.continuation.len() as u32, 0);
    for (index, frame) in self.continuation.iter().enumerate() {
      let start = capacity.stack_word(index);
      fill_frame(
        capacity,
        frame,
        &mut words[start..start + capacity.frame_words()],
      )?;
    }
    Ok(words)
  }
}

impl ResolvedAction {
  pub fn words(&self, capacity: ControlCapacities) -> Result<Vec<F128>> {
    capacity.validate()?;
    let mut words = vec![F128::ZERO; capacity.action_words()];
    match self {
      Self::Idle => {},
      Self::Bind { target, value } => {
        words[0] = meta(1, *target, 0, 0);
        words[2..4].copy_from_slice(value);
      },
      Self::Call { target, callee, args } => {
        words[0] = meta(2, *target, 0, callee.function);
        fill_args(capacity, &mut words, callee, args)?;
      },
      Self::Return { value } => {
        words[0] = meta(3, 0, 0, 0);
        words[2..4].copy_from_slice(value);
      },
      Self::TailCall { callee, args } => {
        words[0] = meta(4, 0, 0, callee.function);
        fill_args(capacity, &mut words, callee, args)?;
      },
      Self::Branch { condition, yes, no } => {
        words[0] = meta(5, *yes, *no, 0);
        words[2..4].copy_from_slice(condition);
      },
    }
    Ok(words)
  }
}

fn fill_args(
  capacity: ControlCapacities,
  words: &mut [F128],
  callee: &CallTarget,
  args: &[ValueWords],
) -> Result<()> {
  ensure!(args.len() <= capacity.arguments, "witness argument width");
  words[1] = meta(callee.entry, callee.arity, args.len() as u32, 0);
  for (index, value) in args.iter().enumerate() {
    words[4 + 2 * index..6 + 2 * index].copy_from_slice(value);
  }
  Ok(())
}

#[derive(Clone, Debug)]
pub struct ControlStepGate {
  nu: usize,
  capacity: ControlCapacities,
  plan: Arc<OnceLock<BooleanR1csPlan>>,
}

#[derive(Clone, Debug)]
pub struct ControlStepRow(Vec<F128>);

impl ControlStepGate {
  pub fn new(nu: usize, capacity: ControlCapacities) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "control row-domain admission");
    capacity.validate()?;
    Ok(Self { nu, capacity, plan: Arc::new(OnceLock::new()) })
  }
  pub fn capacity(&self) -> ControlCapacities {
    self.capacity
  }
  fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(|| synthesis::build(self.capacity))
  }
  pub fn r1cs(&self) -> BlockR1cs {
    self.plan().block_r1cs(self.nu)
  }
  pub fn inputs(
    &self,
    state: &ControlState,
    action: &ResolvedAction,
  ) -> Result<Vec<F128>> {
    let mut input = state.words(self.capacity)?;
    input.extend(action.words(self.capacity)?);
    Ok(input)
  }
  pub fn generate_witness_into(
    &self,
    rows: &[ControlStepRow],
    mut dst: SlotWitnessDest<'_>,
  ) -> Vec<u8> {
    dst.elide_padding_writes = false;
    generate_boolean_witness_into(self.plan(), rows, self.nu, dst, fill_free)
  }
}

fn fill_free(row: &ControlStepRow, bits: &mut [bool]) {
  for (word, value) in row.0.iter().enumerate() {
    write_f128(bits, word * 128, *value);
  }
}

impl CountedGate for ControlStepGate {
  fn input_count(&self) -> usize {
    self.capacity.state_words() + self.capacity.action_words()
  }
  fn output_count(&self) -> usize {
    self.capacity.state_words() + 1
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut gate = self.clone();
    gate.nu = nu;
    gate.table()
  }
}

impl GateType for ControlStepGate {
  type Row = ControlStepRow;
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
    outputs.extend(evaluate(self.capacity, inputs));
    ControlStepRow(inputs.to_vec())
  }
  fn witness(&self, _: &[Self::Row], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}

#[derive(Clone, Copy, Debug)]
pub struct ControlStepSlot {
  slot: SlotId,
  zero: Wire,
  capacity: ControlCapacities,
}

impl ControlStepSlot {
  pub fn declare(b: &mut impl CircuitEmitter, gate: ControlStepGate) -> Self {
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
  pub fn step(
    &self,
    b: &mut impl CircuitEmitter,
    state: &[Wire],
    action: &[Wire],
  ) -> Vec<Wire> {
    assert_eq!(state.len(), self.capacity.state_words());
    assert_eq!(action.len(), self.capacity.action_words());
    let mut input = state.to_vec();
    input.extend_from_slice(action);
    let output = b.gate(self.slot, &input);
    b.connect(output[self.capacity.state_words()], self.zero);
    output[..self.capacity.state_words()].to_vec()
  }
}

fn nonzero(words: &[F128]) -> bool {
  words.iter().any(|word| *word != F128::ZERO)
}
fn xor(first: F128, second: F128) -> F128 {
  F128::new(first.lo ^ second.lo, first.hi ^ second.hi)
}

/// Total row evaluation, including malformed advice. On admitted rows this
/// implements ordinary append. XOR at the append slot also agrees with the
/// Boolean synthesis when hostile advice violates that slot's required zero.
fn evaluate(c: ControlCapacities, input: &[F128]) -> Vec<F128> {
  let state = &input[..c.state_words()];
  let action = &input[c.state_words()..];
  let [kind, fuel, depth, reserved] = lanes(state[0]);
  let [mode, target, alternative, callee] = lanes(action[0]);
  let [entry, arity, args, action_reserved] = lanes(action[1]);
  let eval = kind == 0;
  let returning = kind == 1;
  let halted = kind == 2;
  let bind = eval && mode == 1;
  let call = eval && mode == 2;
  let ret = eval && mode == 3;
  let tail = eval && mode == 4;
  let branch = eval && mode == 5;
  let entering = call || tail;
  let resume = returning && depth != 0;
  let terminal = returning && depth == 0;
  let current = &state[1..1 + c.frame_words()];
  let top = if resume && depth as usize <= c.continuations {
    let start = c.stack_word(depth as usize - 1);
    state[start..start + c.frame_words()].to_vec()
  } else {
    vec![F128::ZERO; c.frame_words()]
  };
  let [function, _, locals, _] = lanes(current[0]);
  let [saved_function, saved_block, saved_locals, _] = lanes(top[0]);
  let mut violation = kind > 2
    || reserved != 0
    || depth as usize > c.continuations
    || ((eval || returning) && fuel == 0)
    || (halted && depth != 0)
    || (eval && !(1..=5).contains(&mode))
    || (!eval && nonzero(action))
    || action_reserved != 0
    || args as usize > c.arguments
    || (entering && args != arity)
    || (!entering && (callee != 0 || entry != 0 || arity != 0 || args != 0))
    || (!(bind || call || branch) && target != 0)
    || (!branch && alternative != 0)
    || (!(bind || ret || branch) && nonzero(&action[2..4]))
    || (branch
      && (action[2] != F128::new(BOOL_TAG, 0)
        || action[3].hi != 0
        || action[3].lo > 1))
    || (call && depth as usize >= c.continuations)
    || (bind && locals as usize >= c.locals)
    || (resume && saved_locals as usize >= c.locals)
    || (eval && nonzero(&state[c.value_word()..c.value_word() + 2]));
  for index in 0..=c.continuations {
    let start = if index == 0 { 1 } else { c.stack_word(index - 1) };
    let frame = &state[start..start + c.frame_words()];
    let [_, _, length, reserved] = lanes(frame[0]);
    let live = if index == 0 { eval } else { index as u32 <= depth };
    violation |= reserved != 0
      || length as usize > c.locals
      || (!live && frame[0] != F128::ZERO);
    for local in 0..c.locals {
      violation |=
        local as u32 >= length && nonzero(&frame[1 + 2 * local..3 + 2 * local]);
    }
  }
  for index in 0..c.arguments {
    violation |=
      index as u32 >= args && nonzero(&action[4 + 2 * index..6 + 2 * index]);
  }

  let mut next = vec![F128::ZERO; c.state_words() + 1];
  let next_kind = if ret {
    1
  } else if terminal || halted {
    2
  } else {
    0
  };
  let next_fuel = if eval || returning { fuel.wrapping_sub(1) } else { fuel };
  let next_depth = if call {
    depth.wrapping_add(1)
  } else if resume {
    depth.wrapping_sub(1)
  } else {
    depth
  };
  next[0] = meta(next_kind, next_fuel, next_depth, 0);
  if bind || branch {
    next[1..1 + c.frame_words()].copy_from_slice(current);
    let next_block =
      if bind || action[3].lo & 1 != 0 { target } else { alternative };
    next[1] = meta(
      function,
      next_block,
      if bind { locals.wrapping_add(1) } else { locals },
      0,
    );
    if bind && (locals as usize) < c.locals {
      for word in 0..2 {
        let pos = 2 + 2 * locals as usize + word;
        next[pos] = xor(next[pos], action[2 + word]);
      }
    }
  } else if entering {
    next[1] = meta(callee, entry, args, 0);
    next[2..2 + 2 * c.arguments].copy_from_slice(&action[4..]);
  } else if resume {
    next[1..1 + c.frame_words()].copy_from_slice(&top);
    next[1] =
      meta(saved_function, saved_block, saved_locals.wrapping_add(1), 0);
    if (saved_locals as usize) < c.locals {
      for word in 0..2 {
        let pos = 2 + 2 * saved_locals as usize + word;
        next[pos] = xor(next[pos], state[c.value_word() + word]);
      }
    }
  }
  if ret {
    next[c.value_word()..c.value_word() + 2].copy_from_slice(&action[2..4]);
  } else if terminal || halted {
    next[c.value_word()..c.value_word() + 2]
      .copy_from_slice(&state[c.value_word()..c.value_word() + 2]);
  }
  for index in 0..c.continuations {
    let start = c.stack_word(index);
    if call && index as u32 == depth {
      next[start..start + c.frame_words()].copy_from_slice(current);
      next[start] = meta(function, target, locals, lanes(current[0])[3]);
    } else if !(resume && index as u32 + 1 == depth) {
      next[start..start + c.frame_words()]
        .copy_from_slice(&state[start..start + c.frame_words()]);
    }
  }
  next[c.state_words()] = F128::new(u64::from(violation), 0);
  next
}
