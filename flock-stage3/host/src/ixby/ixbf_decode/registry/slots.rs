use super::{
  super::{dispatch::*, source::SourceReadWires, *},
  *,
};
use crate::sizing::CircuitEmitter;
use flock_prover::{
  circuit::builder::{SlotId, Wire},
  field::F128,
};

/// State construction is private so the wrapper owns genuine initialization,
/// every dispatcher event, and the complete registry carry.
#[derive(Clone, Debug)]
pub struct ProgramRegistryState {
  dispatch: DispatchState,
  bank: Vec<Wire>,
  capacity: RegistryCapacity,
}
impl ProgramRegistryState {
  pub(in crate::ixby::ixbf_decode) fn grammar(&self) -> GrammarState {
    GrammarState(self.dispatch.0[..28].try_into().unwrap())
  }
}

/// This means completed declaration/header registration, NOT whole-program
/// semantic admission. The actual final grammar context is available for
/// downstream components; typed references/instruction/value checks remain.
#[derive(Clone, Debug)]
pub struct FinishedProgramRegistry {
  state: GrammarState,
  bank: Vec<Wire>,
  capacity: RegistryCapacity,
}
impl FinishedProgramRegistry {
  pub fn grammar(&self) -> GrammarState {
    self.state
  }
  pub fn context(&self) -> [Wire; DISPATCH_CONTEXT_WORDS] {
    DISPATCH_CONTEXT_INDICES.map(|index| self.state.0[index])
  }
}

#[derive(Clone, Copy, Debug)]
pub struct RegistryReadWires {
  /// Constructor: block[2], member, tag, fields. Function: arity, entry,
  /// blocks. Block: locals, instruction. All remaining words are zero.
  pub fields: [Wire; 5],
  /// Exact original-source header range `(start, end)` in u64 lanes. This is
  /// not a full function/block-body span or an executable code commitment.
  pub header_range: Wire,
}

#[derive(Clone, Debug)]
pub struct ProgramRegistrySlots {
  dispatch: DispatchSlots,
  capacity: RegistryCapacity,
  slots: [SlotId; 5],
  zero: Wire,
  residual: Wire,
}
impl ProgramRegistrySlots {
  pub fn declare(
    b: &mut impl CircuitEmitter,
    nu: usize,
    natural: NaturalCapacity,
    capacity: RegistryCapacity,
  ) -> Result<Self> {
    let dispatch = DispatchSlots::declare(
      b,
      nu,
      DispatchConfig { kind: GrammarKind::Program, natural },
    )?;
    let slots = RegistryOp::ALL
      .into_iter()
      .map(|op| Ok(b.slot(RegistryGate::new(nu, capacity, op)?)))
      .collect::<Result<Vec<_>>>()?
      .try_into()
      .unwrap();
    Ok(Self {
      dispatch,
      capacity,
      slots,
      zero: b.fixed_public_input(F128::ZERO),
      // Residual outputs are never reused as input constants: upstream's
      // dataflow graph includes every producer of a connected wire class.
      residual: b.fixed_public_input(F128::ZERO),
    })
  }
  pub fn dispatch(&self) -> &DispatchSlots {
    &self.dispatch
  }
  pub fn capacity(&self) -> RegistryCapacity {
    self.capacity
  }
  pub fn slot(&self, op: RegistryOp) -> SlotId {
    self.slots[op as usize]
  }
  fn gate(
    &self,
    b: &mut impl CircuitEmitter,
    op: RegistryOp,
    input: &[Wire],
  ) -> Vec<Wire> {
    let mut out = b.gate(self.slot(op), input);
    b.connect(out.pop().unwrap(), self.residual);
    out
  }
  pub fn initialize(
    &self,
    b: &mut impl CircuitEmitter,
    file_length: Wire,
  ) -> ProgramRegistryState {
    ProgramRegistryState {
      dispatch: self.dispatch.initialize(
        b,
        file_length,
        [self.zero; DISPATCH_CONTEXT_WORDS],
      ),
      bank: vec![self.zero; self.capacity.words()],
      capacity: self.capacity,
    }
  }
  /// The reader must authenticate these exact requests to ONE expected file,
  /// as required by DispatchSlots. The returned event can feed later semantic
  /// consumers; it never chooses the registry insertion address.
  pub fn step<B: CircuitEmitter>(
    &self,
    b: &mut B,
    state: ProgramRegistryState,
    read: impl FnOnce(&mut B, Wire, Wire) -> SourceReadWires,
  ) -> (ProgramRegistryState, DispatchStepWires) {
    assert_eq!(state.capacity, self.capacity);
    let event = self.dispatch.step(b, state.dispatch, read);
    let mut input = state.dispatch.0[..28].to_vec();
    input.extend([event.committed, event.tag]);
    input.extend(event.fields);
    input.push(event.next);
    input.extend(state.bank);
    let bank = self.gate(b, RegistryOp::Capture, &input);
    (
      ProgramRegistryState {
        dispatch: event.state,
        bank,
        capacity: self.capacity,
      },
      event,
    )
  }
  pub fn finish(
    &self,
    b: &mut impl CircuitEmitter,
    state: ProgramRegistryState,
  ) -> FinishedProgramRegistry {
    assert_eq!(state.capacity, self.capacity);
    let grammar = self.dispatch.finish(b, state.dispatch);
    let mut input = grammar.0.to_vec();
    input.extend_from_slice(&state.bank);
    self.gate(b, RegistryOp::Finish, &input);
    FinishedProgramRegistry {
      state: grammar,
      bank: state.bank,
      capacity: self.capacity,
    }
  }
  fn read(
    &self,
    b: &mut impl CircuitEmitter,
    registry: &FinishedProgramRegistry,
    op: RegistryOp,
    request: [Wire; 3],
  ) -> RegistryReadWires {
    assert_eq!(registry.capacity, self.capacity);
    let mut input = request.to_vec();
    input.extend_from_slice(&registry.bank);
    let out = self.gate(b, op, &input);
    RegistryReadWires {
      fields: out[..5].try_into().unwrap(),
      header_range: out[5],
    }
  }
  pub fn constructor(
    &self,
    b: &mut impl CircuitEmitter,
    registry: &FinishedProgramRegistry,
    enabled: Wire,
    index: Wire,
  ) -> RegistryReadWires {
    self.read(b, registry, RegistryOp::Constructor, [enabled, index, self.zero])
  }
  pub fn function(
    &self,
    b: &mut impl CircuitEmitter,
    registry: &FinishedProgramRegistry,
    enabled: Wire,
    index: Wire,
  ) -> RegistryReadWires {
    self.read(b, registry, RegistryOp::Function, [enabled, index, self.zero])
  }
  pub fn block(
    &self,
    b: &mut impl CircuitEmitter,
    registry: &FinishedProgramRegistry,
    enabled: Wire,
    owner: Wire,
    index: Wire,
  ) -> RegistryReadWires {
    self.read(b, registry, RegistryOp::Block, [enabled, index, owner])
  }
}
