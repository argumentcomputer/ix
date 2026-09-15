//! Nat results share authenticated magnitude records with byte values, but
//! retain distinct tags. Each step chooses exactly one producer for its new
//! record. No proof may replace a decoder/operation output with host advice.
use super::{MachineCapacities, bytes::ByteMachineSlots};
use crate::{
  ixby::{
    decode::PrimitiveSet,
    nat_value::{NatCapacity, NatDispatchGate},
  },
  sizing::CircuitEmitter,
};
use anyhow::Result;
use flock_prover::{
  circuit::builder::{SlotId, Wire},
  field::F128,
};

pub(crate) struct NatMachineSlots {
  pub gate: NatDispatchGate,
  pub slot: SlotId,
  zero: Wire,
  residual_zero: Wire,
}

pub(super) struct NatStep {
  pub headers: [Wire; 2],
  pub evaluation_headers: [Wire; 2],
  pub args: Vec<Wire>,
  primitive: Wire,
  handled: Wire,
  result: [Wire; 2],
  record: Vec<Wire>,
}

pub(super) struct NatStepInput<'a> {
  pub state: &'a mut [Wire],
  pub headers: [Wire; 2],
  pub args: &'a [Wire],
  pub bank: &'a [Wire],
  pub allocation: usize,
}

impl NatMachineSlots {
  pub(super) fn declare(
    b: &mut impl CircuitEmitter,
    nu: usize,
    c: MachineCapacities,
    bytes: &ByteMachineSlots,
    capacity: NatCapacity,
    registry: PrimitiveSet,
  ) -> Result<Self> {
    let gate = NatDispatchGate::new(
      nu,
      (capacity, bytes.capacity),
      c.control,
      c.program.operands,
      bytes.entries,
      registry,
    )?;
    Ok(Self {
      slot: b.slot(gate.clone()),
      gate,
      zero: b.fixed_public_input(F128::ZERO),
      residual_zero: b.fixed_public_input(F128::ZERO),
    })
  }
  pub(super) fn resolve(
    &self,
    b: &mut impl CircuitEmitter,
    bytes: &ByteMachineSlots,
    step: NatStepInput<'_>,
  ) -> NatStep {
    let NatStepInput { state, headers, args, bank, allocation } = step;
    let f = self.gate.control.frame_words();
    let first = bytes.read_slot.read(b, &args[..2], bank);
    let second =
      bytes.read_slot.read(b, args.get(2..4).unwrap_or(&[self.zero; 2]), bank);
    let mut input = state[1..1 + f].to_vec();
    input.extend(headers);
    input.push(b.fixed_public_input(F128::new(allocation as u64, 0)));
    input.extend_from_slice(args);
    input.extend(first);
    input.extend(second);
    let output = b.gate(self.slot, &input);
    b.connect(*output.last().unwrap(), self.residual_zero);
    state[1..1 + f].copy_from_slice(&output[..f]);
    let result = self.gate.result_word();
    NatStep {
      headers: output[f..f + 2].try_into().unwrap(),
      evaluation_headers: output[f + 2..f + 4].try_into().unwrap(),
      args: output[f + 4..result - 2].to_vec(),
      primitive: output[result - 2],
      handled: output[result - 1],
      result: output[result..result + 2].try_into().unwrap(),
      record: output[result + 2..output.len() - 1].to_vec(),
    }
  }
  pub(super) fn finish(
    &self,
    b: &mut impl CircuitEmitter,
    bytes: &ByteMachineSlots,
    step: &NatStep,
    primitive: [Wire; 2],
    bank: &mut [Wire],
    allocation: usize,
  ) -> [Wire; 2] {
    let width = bytes.capacity.record_words();
    let target = &mut bank[allocation * width..(allocation + 1) * width];
    // Reuse the existing two-word selector and its single witness driver.
    for (nat, ordinary) in step.record.chunks(2).zip(target.chunks_mut(2)) {
      let mut yes = [self.zero; 2];
      yes[..nat.len()].copy_from_slice(nat);
      let mut no = [self.zero; 2];
      no[..ordinary.len()].copy_from_slice(ordinary);
      let selected = bytes.select_slot.select(b, step.handled, &yes, &no);
      ordinary.copy_from_slice(&selected[..ordinary.len()]);
    }
    bytes
      .select_slot
      .select(b, step.primitive, &step.result, &primitive)
      .try_into()
      .unwrap()
  }
}
