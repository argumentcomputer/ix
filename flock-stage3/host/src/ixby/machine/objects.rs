use crate::{
  ixby::{
    control::ControlCapacities,
    object_value::{ObjectDispatchGate, ObjectLayout},
  },
  sizing::CircuitEmitter,
};
use flock_prover::{
  circuit::builder::{SlotId, Wire},
  field::F128,
};

pub(crate) struct ObjectMachineSlots {
  pub layout: ObjectLayout,
  pub gate: ObjectDispatchGate,
  pub slot: SlotId,
  frame_words: usize,
  zero: Wire,
  residual_zero: Wire,
}

pub(super) struct ObjectStep<'a> {
  pub state: &'a mut [Wire],
  pub headers: [Wire; 2],
  pub callee: Wire,
  pub primitive: [Wire; 2],
  pub args: &'a [Wire],
  pub program: &'a [Wire],
  pub arena: &'a mut [Wire],
  pub allocation: usize,
}

impl ObjectMachineSlots {
  pub(super) fn declare(
    b: &mut impl CircuitEmitter,
    nu: usize,
    layout: ObjectLayout,
    control: ControlCapacities,
  ) -> Self {
    let gate = ObjectDispatchGate::new(nu, layout, control);
    Self {
      layout,
      slot: b.slot(gate.clone()),
      gate,
      frame_words: control.frame_words(),
      zero: b.fixed_public_input(F128::ZERO),
      residual_zero: b.fixed_public_input(F128::ZERO),
    }
  }
  pub(super) fn bank(&self, input: &[Wire]) -> Vec<Wire> {
    assert_eq!(
      input.len(),
      self.layout.input_slots() * self.layout.record_words()
    );
    let mut arena = input.to_vec();
    arena.resize(self.layout.entries() * self.layout.record_words(), self.zero);
    arena
  }
  /// New instructions resolve to ordinary bind/branch actions. Case fields
  /// are constrained into the frame before the existing control step, which
  /// still consumes exactly one unit of fuel and preserves the continuation.
  pub(super) fn step(
    &self,
    b: &mut impl CircuitEmitter,
    step: ObjectStep<'_>,
  ) -> ([Wire; 2], Wire, [Wire; 2], Vec<Wire>) {
    let mut input =
      vec![b.fixed_public_input(F128::new(step.allocation as u64, 0))];
    input.extend_from_slice(&step.state[1..1 + self.frame_words]);
    input.extend(step.headers);
    input.push(step.callee);
    input.extend(step.primitive);
    input.extend_from_slice(step.args);
    input.extend_from_slice(step.program);
    input.extend_from_slice(step.arena);
    let output = b.gate(self.slot, &input);
    b.connect(*output.last().unwrap(), self.residual_zero);
    step.state[1..1 + self.frame_words]
      .copy_from_slice(&output[..self.frame_words]);
    let header = self.frame_words;
    let normal = self.gate.normalized_words();
    let width = self.layout.record_words();
    step.arena[step.allocation * width..(step.allocation + 1) * width]
      .copy_from_slice(&output[normal..normal + width]);
    (
      output[header..header + 2].try_into().unwrap(),
      output[header + 2],
      output[header + 3..header + 5].try_into().unwrap(),
      output[header + 5..normal].to_vec(),
    )
  }
}
