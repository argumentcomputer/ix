//! Capacity-only connections between decoded artifacts, primitive evaluation
//! and the ordered-frame control machine. No host-resolved action is a free
//! input at this boundary.

mod action;
mod initial;
mod output;
#[cfg(test)]
pub(crate) mod tests;

pub use action::{ActionAssembleGate, ActionAssembleRow, ActionAssembleSlot};
pub use initial::{InitialStateGate, InitialStateRow, InitialStateSlot};
pub use output::{OutputEncodeGate, OutputEncodeRow, OutputEncodeSlot};

use crate::{
  ixby::{
    control::{ControlCapacities, ControlStepGate, ControlStepSlot},
    decode::{
      InputCapacities, InputDecodeGate, InputDecodeSlot, OperandResolveGate,
      OperandResolveSlot, PrimitiveSet, ProgramCapacities, ProgramDecodeGate,
      ProgramDecodeSlot, ProgramFetchGate, ProgramFetchSlot,
    },
    primitive::{PrimitivePrepareGate, ScalarPrimitiveSlots},
  },
  sizing::CircuitEmitter,
};
use anyhow::{Result, ensure};
use flock_prover::circuit::builder::Wire;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MachineCapacities {
  pub program: ProgramCapacities,
  pub control: ControlCapacities,
  pub input: InputCapacities,
  pub output_bytes: usize,
  pub steps: usize,
}

/// All typed gate handles are retained for the untrusted prover's row driver.
/// Declaring and running this network does not supply a cryptographic proof.
pub struct ScalarMachineSlots {
  pub program_gate: ProgramDecodeGate,
  pub program_slot: ProgramDecodeSlot,
  pub input_gate: InputDecodeGate,
  pub input_slot: InputDecodeSlot,
  pub fetch_gate: ProgramFetchGate,
  pub fetch_slot: ProgramFetchSlot,
  pub operand_gate: OperandResolveGate,
  pub operand_slot: OperandResolveSlot,
  pub primitive_gate: PrimitivePrepareGate,
  pub primitive_slots: ScalarPrimitiveSlots,
  pub action_gate: ActionAssembleGate,
  pub action_slot: ActionAssembleSlot,
  pub control_gate: ControlStepGate,
  pub control_slot: ControlStepSlot,
  pub initial_gate: InitialStateGate,
  pub initial_slot: InitialStateSlot,
  pub output_gate: OutputEncodeGate,
  pub output_slot: OutputEncodeSlot,
  capacity: MachineCapacities,
}

impl ScalarMachineSlots {
  pub fn declare(
    b: &mut impl CircuitEmitter,
    nu: usize,
    c: MachineCapacities,
    registry: PrimitiveSet,
  ) -> Result<Self> {
    ensure!((1..=64).contains(&c.steps), "prototype execution step capacity");
    let program_gate =
      ProgramDecodeGate::new(nu, c.program, c.control, registry)?;
    let input_gate = InputDecodeGate::new(nu, c.input)?;
    let fetch_gate = ProgramFetchGate::new(nu, c.program.layout())?;
    let operand_gate =
      OperandResolveGate::new(nu, c.control.locals, c.program.operands)?;
    let primitive_gate =
      PrimitivePrepareGate::new(nu, c.program.operands, registry)?;
    let action_gate =
      ActionAssembleGate::new(nu, c.control, c.program.operands)?;
    let control_gate = ControlStepGate::new(nu, c.control)?;
    let initial_gate = InitialStateGate::new(
      nu,
      c.control,
      c.program.functions,
      c.input.values,
      c.steps as u32,
    )?;
    let output_gate = OutputEncodeGate::new(nu, c.control, c.output_bytes)?;
    Ok(Self {
      program_slot: ProgramDecodeSlot::declare(b, program_gate.clone()),
      program_gate,
      input_slot: InputDecodeSlot::declare(b, input_gate.clone()),
      input_gate,
      fetch_slot: ProgramFetchSlot::declare(b, fetch_gate.clone()),
      fetch_gate,
      operand_slot: OperandResolveSlot::declare(b, operand_gate.clone()),
      operand_gate,
      primitive_slots: ScalarPrimitiveSlots::declare(b, primitive_gate.clone()),
      primitive_gate,
      action_slot: ActionAssembleSlot::declare(b, action_gate.clone()),
      action_gate,
      control_slot: ControlStepSlot::declare(b, control_gate.clone()),
      control_gate,
      initial_slot: InitialStateSlot::declare(b, initial_gate.clone()),
      initial_gate,
      output_slot: OutputEncodeSlot::declare(b, output_gate.clone()),
      output_gate,
      capacity: c,
    })
  }

  /// Each artifact is one length word followed by its fixed padded byte bank.
  /// Output has the same form. There are no free trace or action inputs.
  pub fn execute(
    &self,
    b: &mut impl CircuitEmitter,
    code: &[Wire],
    input: &[Wire],
  ) -> Vec<Wire> {
    let c = self.capacity;
    assert_eq!(code.len(), 1 + c.program.data_words());
    assert_eq!(input.len(), 1 + c.input.data_words());
    let program = self.program_slot.decode(b, code[0], &code[1..]);
    let values = self.input_slot.decode(b, input[0], &input[1..]);
    let mut state = self.initial_slot.initial(
      b,
      program[0],
      &program[1..1 + c.program.functions],
      &values,
    );
    for _ in 0..c.steps {
      let fetched = self.fetch_slot.fetch(b, state[0], state[1], &program);
      let block_words = c.program.layout().block_words();
      let args = self.operand_slot.resolve(
        b,
        &state[1..1 + c.control.frame_words()],
        &fetched[..block_words],
      );
      let headers = [fetched[0], fetched[1]];
      let primitive = self.primitive_slots.evaluate(b, &headers, &args);
      let action = self.action_slot.assemble(
        b,
        &headers,
        fetched[block_words],
        &primitive,
        &args,
      );
      state = self.control_slot.step(b, &state, &action);
    }
    self.primitive_slots.finish_canonical(b);
    self.output_slot.encode(b, &state)
  }
}
