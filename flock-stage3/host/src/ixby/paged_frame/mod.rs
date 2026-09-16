//! Frame and continuation transitions backed by the authenticated memory log.
//!
//! Locals occupy disjoint 128-cell banks indexed by continuation depth. A
//! call saves only its header; the caller's local cells remain at that depth.
//! Entering a function copies an already resolved operand vector one cell at
//! a time, so tail calls cannot overwrite operands still being resolved.
//!
//! This is a new physical component, separate from the existing Exec setup.
//! The caller must derive actions from authenticated code/value consumers,
//! authenticate all five state words plus fuel and memory at batch boundaries,
//! and pass every returned access to the same ordered MemoryLogSlots check.
//! This component alone does not admit an IXBF execution proof.

#[cfg(test)]
mod batch_tests;
mod gate;
mod model;
#[cfg(test)]
mod proof_tests;
mod synthesis;
#[cfg(test)]
mod tests;
mod witness;

pub use gate::{FrameGate, FrameRow};
pub use model::{
  Action, ActionKind, CONTINUATIONS, FrameState, HEAP, LOCALS, Phase, SCRATCH,
  STATE_WORDS, Vector,
};

use crate::{
  ixby::{
    memory_log::AccessWires,
    wide_fuel::{Fuel64StepGate, Fuel64StepSlot},
  },
  sizing::CircuitEmitter,
};
use anyhow::Result;
use flock_prover::{
  circuit::builder::{SlotId, Wire},
  field::F128,
};

pub struct FrameSlots {
  frame: (SlotId, FrameGate),
  fuel: (Fuel64StepSlot, Fuel64StepGate),
  zero: Wire,
}

pub struct FrameStepWires {
  pub state: [Wire; STATE_WORDS],
  pub fuel: Wire,
  pub accesses: [AccessWires; 3],
}

impl FrameSlots {
  pub fn declare(b: &mut impl CircuitEmitter, nu: usize) -> Result<Self> {
    let gate = FrameGate::new(nu)?;
    let frame = (b.slot(gate.clone()), gate);
    let gate = Fuel64StepGate::new(nu)?;
    let fuel = (Fuel64StepSlot::declare(b, gate.clone()), gate);
    Ok(Self { frame, fuel, zero: b.fixed_public_input(F128::ZERO) })
  }
  pub fn frame_gate(&self) -> (SlotId, &FrameGate) {
    (self.frame.0, &self.frame.1)
  }
  pub fn fuel_gate(&self) -> (SlotId, &Fuel64StepGate) {
    (self.fuel.0.slot(), &self.fuel.1)
  }
  /// The action and memory reply must be the actual upstream wires. Accesses
  /// include a canonical read of cell zero when unused; no step can write it.
  #[allow(clippy::too_many_arguments)]
  pub fn step(
    &self,
    b: &mut impl CircuitEmitter,
    state: [Wire; STATE_WORDS],
    action: [Wire; 5],
    reply: [Wire; 2],
    limits: Wire,
    fuel: Wire,
    budget: Wire,
  ) -> FrameStepWires {
    let input = state
      .into_iter()
      .chain(action)
      .chain(reply)
      .chain([limits])
      .collect::<Vec<_>>();
    let output = b.gate(self.frame.0, &input);
    b.connect(output[18], self.zero);
    let fuel = self.fuel.0.step(b, fuel, output[17], budget);
    FrameStepWires {
      state: output[..STATE_WORDS].try_into().unwrap(),
      fuel,
      accesses: std::array::from_fn(|i| {
        let at = STATE_WORDS + 4 * i;
        AccessWires {
          address: output[at],
          write: output[at + 1],
          value: [output[at + 2], output[at + 3]],
        }
      }),
    }
  }
}
