use super::{
  super::{
    dispatch::*, references::CheckedProgramReferences, source::SourceReadWires,
    *,
  },
  *,
};
use crate::sizing::CircuitEmitter;
use flock_prover::{
  circuit::builder::{SlotId, Wire},
  field::F128,
};

#[derive(Clone, Debug)]
pub struct ValueArenaState {
  dispatch: DispatchState,
  program: CheckedProgramReferences,
  accumulator: [Wire; ACC_WORDS],
  count: Wire,
  bank: Vec<Wire>,
}
/// Only `finish` can construct this source-connected, typed preorder arena.
#[derive(Clone, Debug)]
pub struct FinishedValueArena {
  config: ValueConfig,
  program: CheckedProgramReferences,
  grammar: GrammarState,
  summary: [Wire; 3],
  bank: Vec<Wire>,
}
impl FinishedValueArena {
  pub(super) fn program(&self) -> &CheckedProgramReferences {
    &self.program
  }
  pub(super) fn binding(&self) -> &[Wire] {
    &self.bank
  }
  pub fn grammar(&self) -> GrammarState {
    self.grammar
  }
  /// Node count, root count, maximum depth (zero for an empty input).
  pub fn summary(&self) -> [Wire; 3] {
    self.summary
  }
  pub fn config(&self) -> ValueConfig {
    self.config
  }
}
#[derive(Clone, Debug)]
pub struct ValueReadWires {
  pub index: Wire,
  /// Presence, kind, scalar subtype, resolved reference, child count,
  /// own span, payload range, fixed scalar, Nat limbs, then tree metadata.
  pub record: Vec<Wire>,
}
#[derive(Clone, Debug)]
pub struct ValueArenaSlots {
  config: ValueConfig,
  dispatch: DispatchSlots,
  slots: [SlotId; 7],
  zero: Wire,
  residual: Wire,
}
impl ValueArenaSlots {
  pub fn declare(
    b: &mut impl CircuitEmitter,
    nu: usize,
    config: ValueConfig,
  ) -> Result<Self> {
    config.validate()?;
    let dispatch = DispatchSlots::declare(
      b,
      nu,
      DispatchConfig { kind: config.kind, natural: config.arena.natural },
    )?;
    let slots = ValueOp::ALL
      .into_iter()
      .map(|op| Ok(b.slot(ValueGate::new(nu, config, op)?)))
      .collect::<Result<Vec<_>>>()?
      .try_into()
      .unwrap();
    Ok(Self {
      config,
      dispatch,
      slots,
      zero: b.fixed_public_input(F128::ZERO),
      residual: b.fixed_public_input(F128::ZERO),
    })
  }
  pub fn dispatch(&self) -> &DispatchSlots {
    &self.dispatch
  }
  pub fn slot(&self, op: ValueOp) -> SlotId {
    self.slots[op as usize]
  }
  fn gate(
    &self,
    b: &mut impl CircuitEmitter,
    op: ValueOp,
    input: &[Wire],
  ) -> Vec<Wire> {
    let mut out = b.gate(self.slot(op), input);
    b.connect(out.pop().unwrap(), self.residual);
    out
  }
  pub fn initialize(
    &self,
    b: &mut impl CircuitEmitter,
    length: Wire,
    program: &CheckedProgramReferences,
  ) -> ValueArenaState {
    let (capacity, _) = program.registry().binding();
    assert_eq!(capacity, self.config.registry);
    ValueArenaState {
      dispatch: self.dispatch.initialize(
        b,
        length,
        program.registry().context(),
      ),
      program: program.clone(),
      accumulator: [self.zero; ACC_WORDS],
      count: self.zero,
      bank: vec![self.zero; self.config.arena.bank_words()],
    }
  }
  /// The caller authenticates these exact requests to one expected transport.
  /// Registry reads, completed node ordinals and insertion wires are internal.
  pub fn step<B: CircuitEmitter>(
    &self,
    b: &mut B,
    state: ValueArenaState,
    read: impl FnOnce(&mut B, Wire, Wire) -> SourceReadWires,
  ) -> ValueArenaState {
    let grammar = state.dispatch.0[..28].to_vec();
    let event = self.dispatch.step(b, state.dispatch, read);
    let mut link = vec![event.committed, event.tag];
    link.extend(event.fields);
    link.extend(state.program.registry().binding().1);
    let resolved = self.gate(b, ValueOp::Link, &link)[0];
    let mut node = grammar;
    node.extend([event.committed, event.tag]);
    node.extend(event.fields);
    node.extend([
      event.next,
      event.natural_range,
      event.payload_range,
      resolved,
    ]);
    node.extend(event.natural_magnitude);
    node.extend(state.accumulator);
    let node = self.gate(b, ValueOp::Node, &node);
    let accumulator = node[..ACC_WORDS].try_into().unwrap();
    let mut capture = vec![state.count, node[PACKET_INDEX]];
    capture.extend(&node[PACKET_RECORD..]);
    capture.extend(state.bank);
    let capture = self.gate(b, ValueOp::Capture, &capture);
    ValueArenaState {
      dispatch: event.state,
      program: state.program,
      accumulator,
      count: capture[0],
      bank: capture[1..].to_vec(),
    }
  }
  pub fn finish(
    &self,
    b: &mut impl CircuitEmitter,
    state: ValueArenaState,
  ) -> FinishedValueArena {
    let grammar = self.dispatch.finish(b, state.dispatch);
    let mut input = grammar.0.to_vec();
    input.extend(state.accumulator);
    input.push(state.count);
    input.extend(state.bank);
    let output = self.gate(b, ValueOp::Finish, &input);
    FinishedValueArena {
      config: self.config,
      program: state.program,
      grammar,
      summary: output[..3].try_into().unwrap(),
      bank: output[3..].to_vec(),
    }
  }
  fn read(
    &self,
    b: &mut impl CircuitEmitter,
    arena: &FinishedValueArena,
    op: ValueOp,
    enabled: Wire,
    index: Wire,
    owner: Wire,
  ) -> ValueReadWires {
    assert_eq!(arena.config, self.config);
    let mut input = vec![enabled, index, owner];
    input.extend(&arena.bank);
    let out = self.gate(b, op, &input);
    ValueReadWires { index: out[0], record: out[1..].to_vec() }
  }
  pub fn node(
    &self,
    b: &mut impl CircuitEmitter,
    arena: &FinishedValueArena,
    enabled: Wire,
    index: Wire,
  ) -> ValueReadWires {
    self.read(b, arena, ValueOp::ReadNode, enabled, index, self.zero)
  }
  pub fn child(
    &self,
    b: &mut impl CircuitEmitter,
    arena: &FinishedValueArena,
    enabled: Wire,
    parent: Wire,
    ordinal: Wire,
  ) -> ValueReadWires {
    self.read(b, arena, ValueOp::ReadChild, enabled, ordinal, parent)
  }
  pub fn root(
    &self,
    b: &mut impl CircuitEmitter,
    arena: &FinishedValueArena,
    enabled: Wire,
    ordinal: Wire,
  ) -> ValueReadWires {
    self.read(b, arena, ValueOp::ReadRoot, enabled, ordinal, self.zero)
  }
}
