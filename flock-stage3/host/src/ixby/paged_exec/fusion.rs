//! Fixed compositions of existing checked microsteps. Intermediate state and
//! operand values travel on actual circuit wires. Scratch writes remain in
//! the memory log so every boundary has the original state and memory root.
use super::*;
use crate::{ixby::memory_log::AccessWires, sizing::CircuitEmitter};
use flock_prover::circuit::builder::Wire;

impl ExecutionSlots {
  fn zero_access(&self, b: &mut impl CircuitEmitter, access: AccessWires) {
    for wire in [access.address, access.write, access.value[0], access.value[1]]
    {
      self.constrain_zero(b, wire);
    }
  }
  fn forwarded_read(
    &self,
    b: &mut impl CircuitEmitter,
    read: AccessWires,
    write: AccessWires,
  ) {
    self.constrain_zero(b, read.write);
    let residuals = b.gate(
      self.forwarding.as_ref().expect("fused forwarding gate").0,
      &[
        read.address,
        read.value[0],
        read.value[1],
        write.address,
        write.value[0],
        write.value[1],
      ],
    );
    for residual in residuals {
      self.constrain_zero(b, residual);
    }
  }
  #[allow(clippy::too_many_arguments)]
  pub(super) fn fused_step(
    &self,
    b: &mut impl CircuitEmitter,
    chip: Chip,
    enabled: Wire,
    state: [Wire; STATE_WORDS],
    advice: &[Wire],
    parameters: [Wire; 3],
  ) -> StepWires {
    if chip == Chip::CopyPair {
      let mut state = state;
      let mut accesses = Vec::new();
      for reply in advice.as_chunks::<2>().0 {
        let step =
          self.step(b, Chip::Resume, enabled, state, reply, parameters);
        // The continuation event is a read of zero for copying. Binding all
        // four words also rules out silently dropping any other operation.
        self.zero_access(b, step.accesses[1]);
        accesses.extend([step.accesses[0], step.accesses[2]]);
        state = step.state;
      }
      return StepWires { state, accesses };
    }
    let call_arity = chip.call_arity();
    assert!(
      matches!(chip, Chip::FusedControl | Chip::FusedNumeric)
        || call_arity.is_some()
    );
    let step =
      self.step(b, Chip::Fetch, enabled, state, &advice[..2], parameters);
    let mut state = step.state;
    let mut accesses = step.accesses;
    let operands_end = advice.len() - if call_arity.is_some() { 2 } else { 0 };
    let mut writes = Vec::new();
    for reply in advice[2..operands_end].as_chunks::<4>().0 {
      let step = self.step(b, Chip::Resolve, enabled, state, reply, parameters);
      // ResolveFinish produces the value and its scratch write together.
      // Forward those exact wires into the consumer instead of reading it
      // back as independent advice through the memory routing network.
      writes.push(step.accesses[2]);
      accesses.extend(step.accesses);
      state = step.state;
    }
    if let Some(arity) = call_arity {
      assert_eq!(writes.len(), arity);
      let step = self.step(
        b,
        Chip::Call,
        enabled,
        state,
        &advice[operands_end..],
        parameters,
      );
      // Call reads no value and does not bind a local. The continuation
      // write remains authenticated, including the tail-call zero case.
      self.zero_access(b, step.accesses[1]);
      self.zero_access(b, step.accesses[3]);
      accesses.extend([step.accesses[0], step.accesses[2]]);
      state = step.state;
      // Resolve every argument before writing any callee local. This is
      // necessary for self/tail calls that reuse the caller's local bank.
      for write in writes {
        let step =
          self.step(b, Chip::Resume, enabled, state, &write.value, parameters);
        self.forwarded_read(b, step.accesses[0], write);
        self.zero_access(b, step.accesses[1]);
        accesses.push(step.accesses[2]);
        state = step.state;
      }
      return StepWires { state, accesses };
    }
    let mut operands = [self.zero; 6];
    for (i, write) in writes.iter().enumerate() {
      operands[2 * i..2 * i + 2].copy_from_slice(&write.value);
    }
    let numeric = chip == Chip::FusedNumeric;
    let count = if numeric { 3 } else { 1 };
    let prefix = [enabled].into_iter().chain(state).collect::<Vec<_>>();
    let reads = self.gate(
      b,
      MicroKind::Scratch(count),
      &prefix
        .iter()
        .copied()
        .chain(operands[..2 * count].iter().copied())
        .collect::<Vec<_>>(),
    );
    for (i, record) in reads.as_chunks::<4>().0.iter().enumerate() {
      let read = AccessWires {
        address: record[0],
        write: record[1],
        value: [record[2], record[3]],
      };
      if let Some(write) = writes.get(i) {
        self.forwarded_read(b, read, *write);
      } else {
        self.zero_access(b, read);
      }
    }
    let (value, kind) = if numeric {
      let result = self.numeric.evaluate(b, enabled, state[HEADER], operands);
      self.constrain_zero(b, result.byte_code);
      (result.value, MicroKind::NumericAction)
    } else {
      ([operands[0], operands[1]], MicroKind::ControlAction)
    };
    let action =
      self.gate(b, kind, &prefix.into_iter().chain(value).collect::<Vec<_>>());
    self.complete(
      b,
      enabled,
      state,
      action.try_into().unwrap(),
      [self.zero; 2],
      parameters,
      accesses,
    )
  }
}
