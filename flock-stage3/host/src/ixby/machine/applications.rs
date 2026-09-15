use crate::{
  ixby::{
    application::PapDispatchGate, control::ControlCapacities,
    object_value::ObjectLayout,
  },
  sizing::CircuitEmitter,
};
use flock_prover::{
  circuit::builder::{SlotId, Wire},
  field::F128,
};

pub(crate) struct ApplicationMachineSlots {
  pub gate: PapDispatchGate,
  pub slot: SlotId,
  zero: Wire,
}
pub(super) struct ApplicationStep<'a> {
  pub state: &'a [Wire],
  pub headers: [Wire; 2],
  pub callee: Wire,
  pub primitive: [Wire; 2],
  pub args: &'a [Wire],
  pub functions: &'a [Wire],
  pub arena: &'a mut [Wire],
  pub allocation: usize,
}
impl ApplicationMachineSlots {
  pub(super) fn declare(
    b: &mut impl CircuitEmitter,
    nu: usize,
    layout: ObjectLayout,
    control: ControlCapacities,
  ) -> Self {
    let gate = PapDispatchGate::new(nu, layout, control);
    Self {
      slot: b.slot(gate.clone()),
      gate,
      zero: b.fixed_public_input(F128::ZERO),
    }
  }
  pub(super) fn step(
    &self,
    b: &mut impl CircuitEmitter,
    step: ApplicationStep<'_>,
  ) -> ([Wire; 2], Wire, [Wire; 2], Vec<Wire>) {
    let mut input =
      vec![b.fixed_public_input(F128::new(step.allocation as u64, 0))];
    input.extend_from_slice(step.state);
    input.extend(step.headers);
    input.push(step.callee);
    input.extend(step.primitive);
    input.extend_from_slice(step.args);
    input.extend_from_slice(step.functions);
    input.extend_from_slice(step.arena);
    let output = b.gate(self.slot, &input);
    b.connect(*output.last().unwrap(), self.zero);
    let normal = self.gate.normalized_words();
    let width = self.gate.layout.record_words();
    step.arena[step.allocation * width..(step.allocation + 1) * width]
      .copy_from_slice(&output[normal..normal + width]);
    (
      output[..2].try_into().unwrap(),
      output[2],
      output[3..5].try_into().unwrap(),
      output[5..normal].to_vec(),
    )
  }
}
