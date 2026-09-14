//! Fixed-size control relation for the original program and value grammars.
//!
//! A row consumes a *typed, constrained decoder event*, not an acceptance bit.
//! Adjacent state words, decoder cursors/bounds/fields and setup-owned event
//! tags must be wired exactly. Initial state and final Done must be pinned.
//! This component does not authenticate byte windows or registry facts, check
//! UTF-8 / the guest Nat bit limit, or supply an execution/access argument.

use super::{
  RecordKind,
  synthesis::{Bits, Builder},
};
use crate::{
  boolean::{BooleanR1csPlan, generate_boolean_witness_into},
  ixby::bits::{add, evaluate_words, fill_words, subtract},
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

/// See `GrammarState` and the grammar document for the exact word ABI.
pub const GRAMMAR_STATE_WORDS: usize = 28;
pub const GRAMMAR_EVENT_FIELDS: usize = 13;
pub const GRAMMAR_INPUTS: usize =
  GRAMMAR_STATE_WORDS + 1 + 3 + GRAMMAR_EVENT_FIELDS + 1;
const OUTPUTS: usize = GRAMMAR_STATE_WORDS + 1;
const TAG: usize = GRAMMAR_STATE_WORDS;
const BOUNDS: usize = TAG + 1;
const FIELDS: usize = BOUNDS + 3;
const NEXT: usize = FIELDS + GRAMMAR_EVENT_FIELDS;

pub(super) const CTORS: usize = 2;
pub(super) const FUNCTIONS: usize = 3;
pub(super) const FUNCTIONS_LEFT: usize = 4;
pub(super) const BLOCKS: usize = 5;
pub(super) const BLOCKS_LEFT: usize = 6;
pub(super) const CTORS_LEFT: usize = 7;
pub(super) const FUNCTION_INDEX: usize = 8;
pub(super) const LOCALS: usize = 9;
pub(super) const ITEMS: usize = 10;
pub(super) const PAYLOAD: usize = 11;
pub(super) const PENDING: usize = 12;
pub(super) const SEEN: usize = 13;
pub(super) const LIMITS: usize = 14;
pub(super) const ENTRY: usize = 24;
pub(super) const ENTRY_ARITY: usize = 25;
pub(super) const ARITY: usize = 26;
pub(super) const FUEL: usize = 27;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum GrammarKind {
  Program,
  Input,
  Output,
}

/// Values 0..12 name the existing setup-owned RecordKind variants. Extra
/// event domains are deliberately distinct from those record tags.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GrammarEvent {
  Record(RecordKind),
  Header,
  Natural,
  StringPayload,
  BytesPayload,
  Done,
}

impl GrammarEvent {
  pub fn tag(self) -> u8 {
    match self {
      Self::Record(kind) => kind as u8,
      Self::Header => 13,
      Self::Natural => 14,
      Self::StringPayload => 15,
      Self::BytesPayload => 16,
      Self::Done => 17,
    }
  }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub(super) enum Phase {
  Start,
  Constructor,
  FunctionCount,
  Function,
  Block,
  Operation,
  Operand,
  OperandCount,
  Target,
  Projection,
  FunctionIndex,
  AlternativeCount,
  Alternative,
  Scalar,
  Natural,
  StringCount,
  StringPayload,
  BytesCount,
  BytesPayload,
  Value,
  Done,
  // Internal continuations are resolved within the same row. They may never
  // appear as the input phase of a successful row.
  FinishBlock,
  FinishValue,
  NextArgument,
}
const PHASES: [Phase; 21] = [
  Phase::Start,
  Phase::Constructor,
  Phase::FunctionCount,
  Phase::Function,
  Phase::Block,
  Phase::Operation,
  Phase::Operand,
  Phase::OperandCount,
  Phase::Target,
  Phase::Projection,
  Phase::FunctionIndex,
  Phase::AlternativeCount,
  Phase::Alternative,
  Phase::Scalar,
  Phase::Natural,
  Phase::StringCount,
  Phase::StringPayload,
  Phase::BytesCount,
  Phase::BytesPayload,
  Phase::Value,
  Phase::Done,
];

/// Word 0 is `(offset, file length)` in u64 lanes. Word 1 packs five bytes:
/// phase, after-operand, after-vector, after-scalar, and targets-left. The
/// other state words are exact u128 metadata/counters, never field sums.
/// All words must be chained, including apparently inactive continuations.
#[derive(Clone, Copy, Debug)]
pub struct GrammarState(pub [Wire; GRAMMAR_STATE_WORDS]);

#[derive(Clone, Debug)]
pub struct GrammarStepGate {
  pub(super) nu: usize,
  kind: GrammarKind,
  pub(super) plan: Arc<OnceLock<BooleanR1csPlan>>,
}

#[derive(Clone, Debug)]
pub struct GrammarStepRow(pub(super) [F128; GRAMMAR_INPUTS]);

impl GrammarStepGate {
  pub fn new(nu: usize, kind: GrammarKind) -> Result<Self> {
    ensure!((3..=20).contains(&nu), "functional grammar row domain");
    Ok(Self { nu, kind, plan: Arc::new(OnceLock::new()) })
  }
  pub fn kind(&self) -> GrammarKind {
    self.kind
  }
  pub(super) fn plan(&self) -> &BooleanR1csPlan {
    self.plan.get_or_init(|| build_plan(self.kind))
  }
  pub fn r1cs(&self) -> BlockR1cs {
    self.plan().block_r1cs(self.nu)
  }
  pub fn generate_witness_into(
    &self,
    rows: &[GrammarStepRow],
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

impl CountedGate for GrammarStepGate {
  fn input_count(&self) -> usize {
    GRAMMAR_INPUTS
  }
  fn output_count(&self) -> usize {
    OUTPUTS
  }
  fn table_at(&self, nu: usize) -> TableType {
    let mut gate = self.clone();
    gate.nu = nu;
    gate.table()
  }
}
impl GateType for GrammarStepGate {
  type Row = GrammarStepRow;
  type Hint = ();
  fn table(&self) -> TableType {
    crate::boolean::table_from_block_r1cs(self.r1cs()).with_io_schema(
      (0..GRAMMAR_INPUTS)
        .map(IoWord::input)
        .chain((GRAMMAR_INPUTS..GRAMMAR_INPUTS + OUTPUTS).map(IoWord::output))
        .collect(),
    )
  }
  fn eval(&self, input: &[F128], _: &(), output: &mut Vec<F128>) -> Self::Row {
    let input: &[F128; GRAMMAR_INPUTS] =
      input.try_into().expect("fixed grammar input width");
    // This is untrusted witness preparation, never a verifier predicate.
    output.extend(evaluate_words(self.plan(), input, OUTPUTS));
    GrammarStepRow(*input)
  }
  fn witness(&self, _: &[Self::Row], _: usize) -> SlotWitness {
    SlotWitness::DeferredToRows
  }
}

#[derive(Clone, Copy, Debug)]
pub struct GrammarStepSlot {
  slot: SlotId,
  zero: Wire,
}

impl GrammarStepSlot {
  pub fn declare(b: &mut impl CircuitEmitter, gate: GrammarStepGate) -> Self {
    Self { slot: b.slot(gate), zero: b.fixed_public_input(F128::ZERO) }
  }
  pub fn slot(&self) -> SlotId {
    self.slot
  }
  /// `event_tag` must be the decoder's setup-owned constant, not free advice.
  /// Bounds and fields must be the actual decoder's inputs and outputs. All
  /// record fields after the first six are zero. Header uses thirteen fields,
  /// bounds `[file_length, 0, 0]` and its narrow offset output (high lane zero).
  /// Natural uses field 0 = the exact length checked by NaturalDecodeGate;
  /// payload events have all-zero fields and advance by the saved count.
  pub fn step(
    &self,
    b: &mut impl CircuitEmitter,
    state: GrammarState,
    event_tag: Wire,
    bounds: [Wire; 3],
    fields: [Wire; GRAMMAR_EVENT_FIELDS],
    next: Wire,
  ) -> GrammarState {
    let mut input = state.0.to_vec();
    input.push(event_tag);
    input.extend(bounds);
    input.extend(fields);
    input.push(next);
    let output = b.gate(self.slot, &input);
    b.connect(output[GRAMMAR_STATE_WORDS], self.zero);
    GrammarState(output[..GRAMMAR_STATE_WORDS].try_into().unwrap())
  }
}

fn word(index: usize) -> Bits {
  (128 * index..128 * (index + 1)).collect()
}

struct Engine {
  b: Builder,
  state: [Bits; GRAMMAR_STATE_WORDS],
  out: [Bits; GRAMMAR_STATE_WORDS],
  fields: [Bits; GRAMMAR_EVENT_FIELDS],
  phases: Vec<usize>,
}

impl Engine {
  fn new() -> Self {
    let mut b = Builder::new(GRAMMAR_INPUTS, OUTPUTS, 1 << 17);
    let state = std::array::from_fn(word);
    let phases = PHASES
      .iter()
      .map(|phase| b.eq_const(&state[1][..8], *phase as u64))
      .collect::<Vec<_>>();
    let valid = b.sum(&phases);
    b.require(b.one, valid);
    b.require_zero(b.one, &state[1][40..]);
    for byte in 1..4 {
      let choices = (0..=Phase::NextArgument as u64)
        .map(|value| b.eq_const(&state[1][8 * byte..8 * byte + 8], value))
        .collect::<Vec<_>>();
      let valid = b.sum(&choices);
      b.require(b.one, valid);
    }
    let targets = (0..=2)
      .map(|value| b.eq_const(&state[1][32..40], value))
      .collect::<Vec<_>>();
    let valid = b.sum(&targets);
    b.require(b.one, valid);
    Self {
      b,
      out: state.clone(),
      state,
      fields: std::array::from_fn(|i| word(FIELDS + i)),
      phases,
    }
  }
  fn p(&self, phase: Phase) -> usize {
    self.phases[phase as usize]
  }
  fn c(&self, value: u64) -> Bits {
    self.b.constant(128, value)
  }
  fn eq(&mut self, a: &[usize], z: &[usize]) -> usize {
    self.b.equal(a, z)
  }
  fn eqc(&mut self, a: &[usize], value: u64) -> usize {
    self.eq(a, &self.b.constant(a.len(), value))
  }
  fn nonzero(&mut self, a: &[usize]) -> usize {
    self.b.any(a)
  }
  fn and(&mut self, a: usize, z: usize) -> usize {
    self.b.b.and(a, z)
  }
  fn select(&mut self, flag: usize, yes: &[usize], no: &[usize]) -> Bits {
    assert_eq!(yes.len(), no.len());
    yes
      .iter()
      .zip(no)
      .map(|(a, z)| {
        let delta = self.b.b.product_of_parities(&[flag], &[*a, *z]);
        self.b.sum(&[*z, delta])
      })
      .collect()
  }
  fn set(&mut self, flag: usize, index: usize, value: &[usize]) {
    self.out[index] = self.select(flag, value, &self.out[index].clone());
  }
  fn control(&mut self, flag: usize, byte: usize, value: &[usize]) {
    assert_eq!(value.len(), 8);
    let previous: [usize; 8] =
      self.out[1][8 * byte..8 * byte + 8].try_into().unwrap();
    let selected = self.select(flag, value, &previous);
    self.out[1][8 * byte..8 * byte + 8].copy_from_slice(&selected);
  }
  fn control_const(&mut self, flag: usize, byte: usize, value: u64) {
    self.control(flag, byte, &self.b.constant(8, value));
  }
  fn go(&mut self, flag: usize, phase: Phase) {
    self.control_const(flag, 0, phase as u64);
  }
  fn go_if(&mut self, enabled: usize, flag: usize, yes: Phase, no: Phase) {
    let value = self.select(
      flag,
      &self.b.constant(8, yes as u64),
      &self.b.constant(8, no as u64),
    );
    self.control(enabled, 0, &value);
  }
  fn le(&mut self, flag: usize, a: &[usize], z: &[usize]) {
    let (_, borrow) = subtract(&mut self.b.b, self.b.one, self.b.zero, z, a);
    self.b.require_zero(flag, &[borrow]);
  }
  fn minus(&mut self, flag: usize, a: &[usize], z: &[usize]) -> Bits {
    let (result, borrow) =
      subtract(&mut self.b.b, self.b.one, self.b.zero, a, z);
    self.b.require_zero(flag, &[borrow]);
    result
  }
  fn plus(&mut self, flag: usize, a: &[usize], z: &[usize]) -> Bits {
    let (result, carry) = add(&mut self.b.b, self.b.one, self.b.zero, a, z);
    self.b.require_zero(flag, &[carry]);
    result
  }
  fn decrement(&mut self, flag: usize, index: usize) -> Bits {
    let value = self.minus(flag, &self.state[index].clone(), &self.c(1));
    self.set(flag, index, &value);
    value
  }
  fn expect(
    &mut self,
    flag: usize,
    event: GrammarEvent,
    bounds: [Bits; 3],
    used_fields: usize,
  ) {
    let same = self.eqc(&word(TAG), event.tag().into());
    self.b.require(flag, same);
    for (index, bound) in bounds.iter().enumerate() {
      let same = self.eq(&word(BOUNDS + index), bound);
      self.b.require(flag, same);
    }
    for index in used_fields..GRAMMAR_EVENT_FIELDS {
      self.b.require_zero(flag, &self.fields[index].clone());
    }
  }
  fn record(&mut self, phase: Phase, kind: RecordKind, bounds: [Bits; 3]) {
    self.expect(self.p(phase), GrammarEvent::Record(kind), bounds, 6);
  }
  fn zeros(&self) -> [Bits; 3] {
    std::array::from_fn(|_| self.c(0))
  }
  fn tags(&mut self, enabled: usize, field: usize, count: usize) -> Vec<usize> {
    let flags: Vec<_> = (0..count)
      .map(|i| {
        let same = self.eqc(&self.fields[field].clone(), i as u64);
        self.and(enabled, same)
      })
      .collect();
    let good = self.b.sum(&flags);
    self.b.require(enabled, good);
    flags
  }
  fn args(&mut self, enabled: usize, count: &[usize]) {
    self.set(enabled, ITEMS, count);
    self.control_const(enabled, 1, Phase::NextArgument as u64);
    let more = self.nonzero(count);
    let after: [usize; 8] = self.state[1][16..24].try_into().unwrap();
    let phase =
      self.select(more, &self.b.constant(8, Phase::Operand as u64), &after);
    self.control(enabled, 0, &phase);
  }
  fn finish(mut self, kind: GrammarKind) -> BooleanR1csPlan {
    let current: [usize; 8] = self.out[1][..8].try_into().unwrap();
    let finish_block = self.eqc(&current, Phase::FinishBlock as u64);
    let blocks = self.nonzero(&self.out[BLOCKS_LEFT].clone());
    let functions = self.nonzero(&self.out[FUNCTIONS_LEFT].clone());
    let phase = self.select(
      functions,
      &self.b.constant(8, Phase::Function as u64),
      &self.b.constant(8, Phase::Done as u64),
    );
    let phase =
      self.select(blocks, &self.b.constant(8, Phase::Block as u64), &phase);
    self.control(finish_block, 0, &phase);
    let current: [usize; 8] = self.out[1][..8].try_into().unwrap();
    let finish_value = self.eqc(&current, Phase::FinishValue as u64);
    let pending = self.nonzero(&self.out[PENDING].clone());
    self.go_if(finish_value, pending, Phase::Value, Phase::Done);
    let current: [usize; 8] = self.out[1][..8].try_into().unwrap();
    let phases = PHASES
      .iter()
      .map(|phase| self.eqc(&current, *phase as u64))
      .collect::<Vec<_>>();
    let valid = self.b.sum(&phases);
    self.b.require(self.b.one, valid);
    let done = self.eqc(&current, Phase::Done as u64);
    let cursor: [usize; 128] = self.out[0].as_slice().try_into().unwrap();
    let same = self.eq(&cursor[..64], &cursor[64..]);
    self.b.require(done, same);
    for index in
      [FUNCTIONS_LEFT, BLOCKS_LEFT, CTORS_LEFT, ITEMS, PAYLOAD, PENDING]
    {
      self.b.require_zero(done, &self.out[index].clone());
    }
    if kind != GrammarKind::Program {
      for phase in &PHASES[1..13] {
        self.b.require_zero(self.b.one, &[self.p(*phase)]);
      }
      self.b.require_zero(self.b.one, &[self.p(Phase::Operand)]);
    } else {
      self.b.require_zero(self.b.one, &[self.p(Phase::Value)]);
    }
    for index in 0..GRAMMAR_STATE_WORDS {
      self.b.write(GRAMMAR_INPUTS + index, &self.out[index]);
    }
    self.b.finish(GRAMMAR_INPUTS + GRAMMAR_STATE_WORDS)
  }
}

fn build_plan(kind: GrammarKind) -> BooleanR1csPlan {
  let mut e = Engine::new();
  let start = e.p(Phase::Start);
  let done = e.p(Phase::Done);
  let active = e.b.not(done);
  let state = e.state.clone();
  let f = e.fields.clone();
  let zero = e.c(0);
  let one = e.c(1);
  let cursor = &state[0];
  let next = word(NEXT);
  e.le(e.b.one, &cursor[..64], &cursor[64..]);
  let header_start =
    if kind == GrammarKind::Program { start } else { e.b.zero };
  let ordinary = e.b.not(header_start);
  let same = e.eq(&next[64..], &cursor[64..]);
  e.b.require(ordinary, same);
  e.b.require_zero(header_start, &next[64..]);
  e.le(e.b.one, &next[..64], &cursor[64..]);
  let (_, forward) =
    subtract(&mut e.b.b, e.b.one, e.b.zero, &cursor[..64], &next[..64]);
  e.b.require(active, forward);
  let same = e.eq(&next, cursor);
  e.b.require(done, same);
  e.out[0] = [next[..64].to_vec(), cursor[64..].to_vec()].concat();
  e.expect(done, GrammarEvent::Done, e.zeros(), 0);
  e.b.require_zero(start, &cursor[..64]);
  for (index, value) in state.iter().enumerate().skip(1) {
    let context = kind != GrammarKind::Program
      && (index == CTORS
        || index == FUNCTIONS
        || (LIMITS..=ENTRY_ARITY).contains(&index)
        || index == FUEL);
    if !context {
      e.b.require_zero(start, value);
    }
  }

  if kind == GrammarKind::Program {
    let mut length = cursor[64..].to_vec();
    length.resize(128, e.b.zero);
    e.expect(
      start,
      GrammarEvent::Header,
      [length, zero.clone(), zero.clone()],
      13,
    );
    for (index, field) in f.iter().take(10).enumerate() {
      e.set(start, LIMITS + index, field);
    }
    e.set(start, FUEL, &f[10]);
    e.set(start, ENTRY, &f[11]);
    e.set(start, CTORS, &f[12]);
    e.set(start, CTORS_LEFT, &f[12]);
    let more = e.nonzero(&f[12]);
    e.go_if(start, more, Phase::Constructor, Phase::FunctionCount);
  } else {
    let (record, bounds) = if kind == GrammarKind::Input {
      (
        RecordKind::Input,
        [
          state[LIMITS + 4].clone(),
          state[ENTRY_ARITY].clone(),
          state[LIMITS + 6].clone(),
        ],
      )
    } else {
      (
        RecordKind::Output,
        [state[LIMITS + 6].clone(), zero.clone(), zero.clone()],
      )
    };
    e.expect(start, GrammarEvent::Record(record), bounds, 6);
    e.set(start, PENDING, &f[0]);
    e.le(start, &f[0], &state[LIMITS + 6]);
    e.go(start, Phase::FinishValue);
  }

  e.record(
    Phase::Constructor,
    RecordKind::Constructor,
    [state[LIMITS + 4].clone(), zero.clone(), zero.clone()],
  );
  let left = e.decrement(e.p(Phase::Constructor), CTORS_LEFT);
  let more = e.nonzero(&left);
  e.go_if(
    e.p(Phase::Constructor),
    more,
    Phase::Constructor,
    Phase::FunctionCount,
  );
  e.record(
    Phase::FunctionCount,
    RecordKind::Count,
    [state[LIMITS].clone(), zero.clone(), zero.clone()],
  );
  let enabled = e.p(Phase::FunctionCount);
  e.set(enabled, FUNCTIONS, &f[0]);
  e.set(enabled, FUNCTIONS_LEFT, &f[0]);
  let (_, in_bounds) =
    subtract(&mut e.b.b, e.b.one, e.b.zero, &state[ENTRY], &f[0]);
  e.b.require(enabled, in_bounds);
  e.go(enabled, Phase::Function);

  e.record(
    Phase::Function,
    RecordKind::Function,
    [
      state[LIMITS + 4].clone(),
      state[LIMITS + 3].clone(),
      state[LIMITS + 2].clone(),
    ],
  );
  let enabled = e.p(Phase::Function);
  e.decrement(enabled, FUNCTIONS_LEFT);
  let index = e.plus(enabled, &state[FUNCTION_INDEX], &one);
  e.set(enabled, FUNCTION_INDEX, &index);
  let entry = e.eq(&state[FUNCTION_INDEX], &state[ENTRY]);
  let entry = e.and(enabled, entry);
  e.set(entry, ENTRY_ARITY, &f[0]);
  e.set(enabled, ARITY, &f[0]);
  e.set(enabled, BLOCKS, &f[2]);
  e.set(enabled, BLOCKS_LEFT, &f[2]);
  let nonempty = e.nonzero(&f[2]);
  e.b.require(enabled, nonempty);
  e.go(enabled, Phase::Block);

  e.record(
    Phase::Block,
    RecordKind::Block,
    [state[LIMITS + 3].clone(), zero.clone(), zero.clone()],
  );
  let enabled = e.p(Phase::Block);
  e.decrement(enabled, BLOCKS_LEFT);
  e.set(enabled, LOCALS, &f[0]);
  let tags = e.tags(enabled, 1, 8);
  for (tag, phase) in [
    Phase::Operation,
    Phase::Operand,
    Phase::FunctionIndex,
    Phase::OperandCount,
    Phase::Operand,
    Phase::Operand,
    Phase::Operand,
    Phase::Operand,
  ]
  .into_iter()
  .enumerate()
  {
    e.go(tags[tag], phase);
  }
  e.control_const(enabled, 1, Phase::FinishBlock as u64);
  e.control_const(enabled, 2, Phase::FinishBlock as u64);
  e.control_const(enabled, 3, 0);
  e.control_const(enabled, 4, 0);
  e.control_const(tags[0], 2, Phase::Target as u64);
  e.control_const(tags[0], 4, 1);
  e.control_const(tags[4], 1, Phase::OperandCount as u64);
  e.control_const(tags[5], 1, Phase::AlternativeCount as u64);
  for tag in [6, 7] {
    e.control_const(tags[tag], 1, Phase::Target as u64);
    e.control_const(tags[tag], 4, 2);
  }

  e.record(
    Phase::Operation,
    RecordKind::Operation,
    [state[LIMITS + 4].clone(), state[CTORS].clone(), state[FUNCTIONS].clone()],
  );
  let enabled = e.p(Phase::Operation);
  let tags = e.tags(enabled, 0, 8);
  for (tag, continuation) in
    [(0, Phase::Target), (3, Phase::Projection), (7, Phase::OperandCount)]
  {
    e.go(tags[tag], Phase::Operand);
    e.control_const(tags[tag], 1, continuation as u64);
  }
  let counted = e.b.sum(&[tags[1], tags[2], tags[4], tags[5], tags[6]]);
  e.args(counted, &f[3]);
  e.record(
    Phase::FunctionIndex,
    RecordKind::Index,
    [state[FUNCTIONS].clone(), zero.clone(), zero.clone()],
  );
  e.go(e.p(Phase::FunctionIndex), Phase::OperandCount);
  e.record(
    Phase::OperandCount,
    RecordKind::Count,
    [state[LIMITS + 4].clone(), zero.clone(), zero.clone()],
  );
  e.args(e.p(Phase::OperandCount), &f[0]);

  e.record(
    Phase::Operand,
    RecordKind::Operand,
    [state[LOCALS].clone(), zero.clone(), zero.clone()],
  );
  let enabled = e.p(Phase::Operand);
  let tags = e.tags(enabled, 0, 3);
  let vector = e.eqc(&state[1][8..16], Phase::NextArgument as u64);
  let vector_enabled = e.and(enabled, vector);
  let left = e.decrement(vector_enabled, ITEMS);
  let more = e.nonzero(&left);
  let after =
    e.select(more, &e.b.constant(8, Phase::Operand as u64), &state[1][16..24]);
  let after = e.select(vector, &after, &state[1][8..16]);
  let direct = e.b.sum(&[tags[0], tags[2]]);
  e.control(direct, 0, &after);
  e.go(tags[1], Phase::Scalar);
  e.control(tags[1], 3, &after);

  e.record(Phase::Projection, RecordKind::Metadata, e.zeros());
  e.go(e.p(Phase::Projection), Phase::Target);
  e.record(
    Phase::Target,
    RecordKind::Index,
    [state[BLOCKS].clone(), zero.clone(), zero.clone()],
  );
  let enabled = e.p(Phase::Target);
  let target_count = state[1][32..40].to_vec();
  let allowed = e.eqc(&target_count, 1);
  let two = e.eqc(&target_count, 2);
  let allowed = e.b.sum(&[allowed, two]);
  e.b.require(enabled, allowed);
  let left = e.minus(enabled, &target_count, &e.b.constant(8, 1));
  e.control(enabled, 4, &left);
  e.go_if(enabled, two, Phase::Target, Phase::FinishBlock);
  e.record(
    Phase::AlternativeCount,
    RecordKind::Count,
    [state[LIMITS + 1].clone(), zero.clone(), zero.clone()],
  );
  let enabled = e.p(Phase::AlternativeCount);
  e.set(enabled, ITEMS, &f[0]);
  let more = e.nonzero(&f[0]);
  e.go_if(enabled, more, Phase::Alternative, Phase::FinishBlock);
  e.record(
    Phase::Alternative,
    RecordKind::Alternative,
    [state[CTORS].clone(), state[BLOCKS].clone(), zero.clone()],
  );
  let enabled = e.p(Phase::Alternative);
  let left = e.decrement(enabled, ITEMS);
  let more = e.nonzero(&left);
  e.go_if(enabled, more, Phase::Alternative, Phase::FinishBlock);

  e.record(Phase::Scalar, RecordKind::Scalar, e.zeros());
  let tags = e.tags(e.p(Phase::Scalar), 0, 7);
  e.go(tags[0], Phase::Natural);
  e.go(tags[1], Phase::StringCount);
  e.go(tags[6], Phase::BytesCount);
  let fixed = e.b.sum(&tags[2..6]);
  e.control(fixed, 0, &state[1][24..32]);
  e.expect(e.p(Phase::Natural), GrammarEvent::Natural, e.zeros(), 1);
  let enabled = e.p(Phase::Natural);
  e.le(enabled, &one, &f[0]);
  e.le(enabled, &f[0], &e.c(4096usize.div_ceil(7) as u64));
  let mut delta = e.minus(active, &next[..64], &cursor[..64]);
  delta.resize(128, e.b.zero);
  let same = e.eq(&delta, &f[0]);
  e.b.require(enabled, same);
  e.control(enabled, 0, &state[1][24..32]);

  for (count_phase, payload_phase, limit, event) in [
    (Phase::StringCount, Phase::StringPayload, 8, GrammarEvent::StringPayload),
    (Phase::BytesCount, Phase::BytesPayload, 9, GrammarEvent::BytesPayload),
  ] {
    e.record(
      count_phase,
      RecordKind::Count,
      [state[LIMITS + limit].clone(), zero.clone(), zero.clone()],
    );
    let enabled = e.p(count_phase);
    e.set(enabled, PAYLOAD, &f[0]);
    let more = e.nonzero(&f[0]);
    let phase =
      e.select(more, &e.b.constant(8, payload_phase as u64), &state[1][24..32]);
    e.control(enabled, 0, &phase);
    let enabled = e.p(payload_phase);
    e.expect(enabled, event, e.zeros(), 0);
    let same = e.eq(&delta, &state[PAYLOAD]);
    e.b.require(enabled, same);
    e.set(enabled, PAYLOAD, &zero);
    e.control(enabled, 0, &state[1][24..32]);
  }

  let enabled = e.p(Phase::Value);
  let seen = e.plus(enabled, &state[SEEN], &one);
  let remaining = e.minus(enabled, &state[LIMITS + 6], &seen);
  e.record(
    Phase::Value,
    RecordKind::Value,
    [state[LIMITS + 4].clone(), state[FUNCTIONS].clone(), remaining],
  );
  let tags = e.tags(enabled, 0, 4);
  let pending = e.minus(enabled, &state[PENDING], &one);
  let pending = e.plus(enabled, &pending, &f[5]);
  let committed = e.plus(enabled, &pending, &seen);
  e.le(enabled, &committed, &state[LIMITS + 6]);
  e.set(enabled, PENDING, &pending);
  e.set(enabled, SEEN, &seen);
  e.go(enabled, Phase::FinishValue);
  e.go(tags[0], Phase::Scalar);
  e.control_const(tags[0], 3, Phase::FinishValue as u64);
  e.finish(kind)
}
