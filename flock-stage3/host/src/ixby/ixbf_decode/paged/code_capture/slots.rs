use super::*;
use crate::{
  ixby::{
    ixbf_decode::dispatch::{DispatchState, DispatchStepWires},
    memory_log::AccessWires,
    paged_code::{CodeGate, CodeGateKind},
  },
  sizing::CircuitEmitter,
};
use anyhow::{Result, ensure};
use flock_prover::{
  circuit::builder::{SlotId, Wire},
  field::F128,
};

pub struct CodeCaptureSlots {
  capture: (SlotId, CodeCaptureGate),
  header: (SlotId, CodeGate),
  zero: Wire,
}
pub struct CodeCaptureWires {
  pub state: [Wire; STATE_WORDS],
  pub accesses: [AccessWires; 3],
}
impl CodeCaptureSlots {
  pub fn declare(b: &mut impl CircuitEmitter, nu: usize) -> Result<Self> {
    let g = CodeCaptureGate::new(nu)?;
    let capture = (b.slot(g.clone()), g);
    let g = CodeGate::new(nu, CodeGateKind::Block)?;
    let header = (b.slot(g.clone()), g);
    Ok(Self { capture, header, zero: b.fixed_public_input(F128::ZERO) })
  }
  pub fn capture_gate(&self) -> (SlotId, &CodeCaptureGate) {
    (self.capture.0, &self.capture.1)
  }
  pub fn header_gate(&self) -> (SlotId, &CodeGate) {
    (self.header.0, &self.header.1)
  }
  /// The same Program parser event supplies all typed fields and payload
  /// values. The fixed physical profile requires exactly one Nat128 limb.
  pub fn step(
    &self,
    b: &mut impl CircuitEmitter,
    old: DispatchState,
    event: &DispatchStepWires,
    state: [Wire; STATE_WORDS],
  ) -> Result<CodeCaptureWires> {
    ensure!(
      event.natural_magnitude.len() == 1,
      "code capture requires exact Nat128 decoder"
    );
    let mut input = GRAMMAR_INDICES.map(|i| old.0[i]).to_vec();
    input.extend([event.next, event.state.0[1], event.tag, event.committed]);
    input.extend(event.fields);
    input.extend([event.natural_magnitude[0], event.payload_range]);
    input.extend(state);
    let out = b.gate(self.capture.0, &input);
    b.connect(out[22], self.zero);
    let checked =
      b.gate(self.header.0, &[out[19], out[20], out[21], self.zero]);
    b.connect(checked[4], self.zero);
    Ok(CodeCaptureWires {
      state: out[..7].try_into().unwrap(),
      accesses: std::array::from_fn(|i| {
        let at = 7 + 4 * i;
        AccessWires {
          address: out[at],
          write: out[at + 1],
          value: [out[at + 2], out[at + 3]],
        }
      }),
    })
  }
}
