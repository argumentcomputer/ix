use super::{
  super::{references::*, source::SourceReadWires},
  *,
};
use crate::sizing::CircuitEmitter;
use flock_prover::{
  circuit::builder::{SlotId, Wire},
  field::F128,
};
#[derive(Clone, Debug)]
pub struct ProgramBodyState {
  program: ProgramReferenceState,
}
#[derive(Clone, Debug)]
pub struct FinishedProgramBodies {
  capacity: BodyCapacity,
  program: CheckedProgramReferences,
  bank: Vec<Wire>,
}
impl FinishedProgramBodies {
  pub fn references(&self) -> &CheckedProgramReferences {
    &self.program
  }
  pub fn capacity(&self) -> BodyCapacity {
    self.capacity
  }
}
#[derive(Clone, Debug)]
pub struct BodyReadWires {
  pub fields: Vec<Wire>,
}
#[derive(Clone, Debug)]
pub struct ProgramBodySlots {
  capacity: BodyCapacity,
  program: ProgramReferenceSlots,
  slots: [SlotId; 7],
  zero: Wire,
  residual: Wire,
}
impl ProgramBodySlots {
  pub fn declare(
    b: &mut impl CircuitEmitter,
    nu: usize,
    capacity: BodyCapacity,
  ) -> Result<Self> {
    let program = ProgramReferenceSlots::declare(
      b,
      nu,
      capacity.natural,
      capacity.registry,
    )?;
    let slots = BodyOp::ALL
      .into_iter()
      .map(|op| Ok(b.slot(BodyGate::new(nu, capacity, op)?)))
      .collect::<Result<Vec<_>>>()?
      .try_into()
      .unwrap();
    Ok(Self {
      capacity,
      program,
      slots,
      zero: b.fixed_public_input(F128::ZERO),
      residual: b.fixed_public_input(F128::ZERO),
    })
  }
  pub fn reference_slots(&self) -> &ProgramReferenceSlots {
    &self.program
  }
  pub fn slot(&self, op: BodyOp) -> SlotId {
    self.slots[op as usize]
  }
  fn gate(
    &self,
    b: &mut impl CircuitEmitter,
    op: BodyOp,
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
  ) -> ProgramBodyState {
    ProgramBodyState { program: self.program.initialize(b, length) }
  }
  /// Authenticate every exact request to one expected original program.
  pub fn step<B: CircuitEmitter>(
    &self,
    b: &mut B,
    state: ProgramBodyState,
    read: impl FnOnce(&mut B, Wire, Wire) -> SourceReadWires,
  ) -> ProgramBodyState {
    ProgramBodyState { program: self.program.step(b, state.program, read) }
  }
  pub fn finish(
    &self,
    b: &mut impl CircuitEmitter,
    state: ProgramBodyState,
  ) -> FinishedProgramBodies {
    let events = state.program.events().to_vec();
    let program = self.program.finish(b, state.program);
    let mut current = vec![self.zero; self.capacity.state_words()];
    let mut bank = vec![self.zero; self.capacity.bank_words()];
    for (grammar, event) in events {
      let mut input = grammar.0.to_vec();
      input.extend([event.committed, event.tag]);
      input.extend(event.fields);
      input.extend([
        event.next,
        event.state.0[1],
        event.natural_range,
        event.payload_range,
      ]);
      input.extend(event.natural_magnitude);
      input.extend(current);
      let step = self.gate(b, BodyOp::Step, &input);
      current = step[..self.capacity.state_words()].to_vec();
      let mut capture = step[self.capacity.state_words()..].to_vec();
      capture.extend(bank);
      bank = self.gate(b, BodyOp::Capture, &capture);
    }
    let mut input = program.registry().grammar().0.to_vec();
    input.extend(current);
    input.extend(program.registry().binding().1);
    input.extend(bank);
    let bank = self.gate(b, BodyOp::Finish, &input);
    FinishedProgramBodies { capacity: self.capacity, program, bank }
  }
  fn read(
    &self,
    b: &mut impl CircuitEmitter,
    program: &FinishedProgramBodies,
    op: BodyOp,
    request: [Wire; 4],
  ) -> BodyReadWires {
    assert_eq!(self.capacity, program.capacity);
    let mut input = request.to_vec();
    input.extend(&program.bank);
    BodyReadWires { fields: self.gate(b, op, &input) }
  }
  pub fn function(
    &self,
    b: &mut impl CircuitEmitter,
    program: &FinishedProgramBodies,
    enabled: Wire,
    index: Wire,
  ) -> BodyReadWires {
    self.read(
      b,
      program,
      BodyOp::ReadFunction,
      [enabled, index, self.zero, self.zero],
    )
  }
  pub fn block(
    &self,
    b: &mut impl CircuitEmitter,
    program: &FinishedProgramBodies,
    enabled: Wire,
    owner: Wire,
    index: Wire,
  ) -> BodyReadWires {
    self.read(b, program, BodyOp::ReadBlock, [enabled, owner, index, self.zero])
  }
  pub fn operand(
    &self,
    b: &mut impl CircuitEmitter,
    program: &FinishedProgramBodies,
    request: [Wire; 4],
  ) -> BodyReadWires {
    self.read(b, program, BodyOp::ReadOperand, request)
  }
  pub fn alternative(
    &self,
    b: &mut impl CircuitEmitter,
    program: &FinishedProgramBodies,
    request: [Wire; 4],
  ) -> BodyReadWires {
    self.read(b, program, BodyOp::ReadAlternative, request)
  }
}
