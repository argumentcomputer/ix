use super::*;
use crate::{
  ixby::{
    ixbf_decode::dispatch::{DispatchState, DispatchStepWires},
    memory_log::AccessWires,
  },
  sizing::CircuitEmitter,
};
use anyhow::{Result, ensure};
use flock_prover::{
  circuit::builder::{SlotId, Wire},
  field::F128,
};
pub struct InputCaptureSlots {
  capture: (SlotId, InputCaptureGate),
  zero: Wire,
}
pub struct InputCaptureWires {
  pub state: [Wire; STATE_WORDS],
  pub accesses: [AccessWires; 6],
}
impl InputCaptureSlots {
  pub fn declare(b: &mut impl CircuitEmitter, nu: usize) -> Result<Self> {
    let g = InputCaptureGate::new(nu)?;
    Ok(Self {
      capture: (b.slot(g.clone()), g),
      zero: b.fixed_public_input(F128::ZERO),
    })
  }
  pub fn capture_gate(&self) -> (SlotId, &InputCaptureGate) {
    (self.capture.0, &self.capture.1)
  }
  #[allow(clippy::too_many_arguments)]
  pub fn step(
    &self,
    b: &mut impl CircuitEmitter,
    old: DispatchState,
    event: &DispatchStepWires,
    state: [Wire; STATE_WORDS],
    resolved: Wire,
    replies: [[Wire; 2]; 4],
  ) -> Result<InputCaptureWires> {
    ensure!(
      event.natural_magnitude.len() == 1,
      "input capture requires Nat128 decoder"
    );
    let mut input = GRAMMAR_INDICES.map(|i| old.0[i]).to_vec();
    input.extend([event.next, event.tag, event.committed]);
    input.extend(event.fields);
    input.extend([event.natural_magnitude[0], event.payload_range]);
    input.extend(state);
    input.push(resolved);
    input.extend(replies.into_iter().flatten());
    let out = b.gate(self.capture.0, &input);
    b.connect(out[29], self.zero);
    Ok(InputCaptureWires {
      state: out[..STATE_WORDS].try_into().unwrap(),
      accesses: std::array::from_fn(|i| {
        let at = STATE_WORDS + 4 * i;
        AccessWires {
          address: out[at],
          write: out[at + 1],
          value: [out[at + 2], out[at + 3]],
        }
      }),
    })
  }
}
