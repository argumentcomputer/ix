use super::{
  super::{dispatch::*, registry::*, source::SourceReadWires, *},
  *,
};
use crate::sizing::CircuitEmitter;
use anyhow::Result;
use flock_prover::{
  circuit::builder::{SlotId, Wire},
  field::F128,
};

/// Private construction retains every actual event, including inactive rows.
/// The event list is circuit wiring, never a host-selected witness schedule.
#[derive(Clone, Debug)]
pub struct ProgramReferenceState {
  registry: ProgramRegistryState,
  events: Vec<(GrammarState, DispatchStepWires)>,
}
impl ProgramReferenceState {
  /// Actual retained wires, including inactive steps, for typed body assembly.
  pub(in crate::ixby::ixbf_decode) fn events(
    &self,
  ) -> &[(GrammarState, DispatchStepWires)] {
    &self.events
  }
}

/// Completed bounded instruction/reference checks. This does not certify a
/// typed executable body/value representation or native constraint refinement.
#[derive(Clone, Debug)]
pub struct CheckedProgramReferences {
  registry: FinishedProgramRegistry,
}
impl CheckedProgramReferences {
  pub fn registry(&self) -> &FinishedProgramRegistry {
    &self.registry
  }
}

#[derive(Clone, Debug)]
pub struct ProgramReferenceSlots {
  registry: ProgramRegistrySlots,
  slots: [SlotId; 2],
  zero: Wire,
  residual: Wire,
}
impl ProgramReferenceSlots {
  pub fn declare(
    b: &mut impl CircuitEmitter,
    nu: usize,
    natural: NaturalCapacity,
    capacity: RegistryCapacity,
  ) -> Result<Self> {
    let registry = ProgramRegistrySlots::declare(b, nu, natural, capacity)?;
    let slots = ReferenceOp::ALL
      .into_iter()
      .map(|op| Ok(b.slot(ReferenceGate::new(nu, capacity, op)?)))
      .collect::<Result<Vec<_>>>()?
      .try_into()
      .unwrap();
    Ok(Self {
      registry,
      slots,
      zero: b.fixed_public_input(F128::ZERO),
      residual: b.fixed_public_input(F128::ZERO),
    })
  }
  pub fn registry_slots(&self) -> &ProgramRegistrySlots {
    &self.registry
  }
  pub fn slot(&self, op: ReferenceOp) -> SlotId {
    self.slots[op as usize]
  }
  pub fn initialize(
    &self,
    b: &mut impl CircuitEmitter,
    length: Wire,
  ) -> ProgramReferenceState {
    ProgramReferenceState {
      registry: self.registry.initialize(b, length),
      events: Vec::new(),
    }
  }
  /// Authenticate the exact requested bytes to one expected original file.
  /// Event retention and later semantic read addresses are owned by this wrapper.
  pub fn step<B: CircuitEmitter>(
    &self,
    b: &mut B,
    state: ProgramReferenceState,
    read: impl FnOnce(&mut B, Wire, Wire) -> SourceReadWires,
  ) -> ProgramReferenceState {
    let grammar = state.registry.grammar();
    let (registry, event) = self.registry.step(b, state.registry, read);
    let mut events = state.events;
    events.push((grammar, event));
    ProgramReferenceState { registry, events }
  }
  pub fn finish(
    &self,
    b: &mut impl CircuitEmitter,
    state: ProgramReferenceState,
  ) -> CheckedProgramReferences {
    let registry = self.registry.finish(b, state.registry);
    let mut carried = [self.zero; STATE_WORDS];
    for (grammar, event) in state.events {
      let mut input = grammar.0.to_vec();
      input.extend([event.committed, event.tag]);
      input.extend(event.fields);
      input.extend(carried);
      let request = b.gate(self.slot(ReferenceOp::Request), &input);
      b.connect(*request.last().unwrap(), self.residual);
      carried = request[..STATE_WORDS].try_into().unwrap();
      let facts = &request[STATE_WORDS..STATE_WORDS + FACTS];
      let constructor = self.registry.constructor(
        b,
        &registry,
        facts[CTOR_ENABLE],
        facts[CTOR_INDEX],
      );
      let function = self.registry.function(
        b,
        &registry,
        facts[FUNCTION_ENABLE],
        facts[FUNCTION_INDEX],
      );
      let block = self.registry.block(
        b,
        &registry,
        facts[BLOCK_ENABLE],
        facts[BLOCK_OWNER],
        facts[BLOCK_INDEX],
      );
      let mut input = facts.to_vec();
      input.extend(constructor.fields);
      input.extend(function.fields);
      input.extend(block.fields);
      let out = b.gate(self.slot(ReferenceOp::Check), &input);
      b.connect(out[0], self.residual);
    }
    CheckedProgramReferences { registry }
  }
}
