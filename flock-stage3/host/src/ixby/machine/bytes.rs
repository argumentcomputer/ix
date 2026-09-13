//! Setup-fixed immutable allocations and byte dispatch. This bank contains
//! only decoder/operation outputs or the public zero word, never host advice.

use super::MachineCapacities;
use crate::{
  ixby::{
    bounded_hash::BoundedBlake3,
    byte_value::{ByteCapacity, BytePrimitiveGate, ByteReadGate, ByteReadSlot},
    decode::PrimitiveSet,
    object_value::ObjectLayout,
    primitive::ScalarPrimitiveSlots,
    select::{SelectWordsGate, SelectWordsSlot},
  },
  sizing::CircuitEmitter,
};
use anyhow::Result;
use flock_prover::{
  circuit::builder::{SlotId, Wire},
  field::F128,
};

pub(crate) struct ByteMachineSlots {
  pub read_gate: ByteReadGate,
  pub read_slot: ByteReadSlot,
  pub primitive_gate: BytePrimitiveGate,
  pub primitive_slot: SlotId,
  pub select_gate: SelectWordsGate,
  pub select_slot: SelectWordsSlot,
  pub hash: BoundedBlake3,
  pub capacity: ByteCapacity,
  pub entries: usize,
  zero: Wire,
  residual_zero: Wire,
}

impl ByteMachineSlots {
  pub(super) fn allocations(c: MachineCapacities) -> Result<(usize, usize)> {
    let program = c
      .program
      .functions
      .checked_mul(c.program.blocks)
      .and_then(|n| n.checked_mul(c.program.operands))
      .ok_or_else(|| anyhow::anyhow!("byte literal allocation overflow"))?;
    let entries = program
      .checked_add(c.input.values)
      .and_then(|n| n.checked_add(c.steps))
      .ok_or_else(|| anyhow::anyhow!("immutable-byte allocation overflow"))?;
    crate::ixby::byte_value::validate_entries(entries)?;
    Ok((program, entries))
  }

  pub(super) fn declare(
    b: &mut impl CircuitEmitter,
    nu: usize,
    c: MachineCapacities,
    capacity: ByteCapacity,
    registry: PrimitiveSet,
    common_hash: &BoundedBlake3,
    values: (Option<ObjectLayout>, Option<crate::ixby::nat_value::NatCapacity>),
  ) -> Result<Self> {
    let (objects, nats) = values;
    let entries = match objects {
      None => Self::allocations(c)?.1,
      Some(layout) => layout.byte_entries(),
    };
    let mut read_gate = ByteReadGate::new(nu, capacity, entries)?;
    if let Some(layout) = objects {
      read_gate = read_gate.with_object_handles(layout.entries());
    }
    if let Some(capacity) = nats {
      read_gate = read_gate.with_nat_capacity(capacity)?;
    }
    let primitive_gate = BytePrimitiveGate::new(
      nu,
      capacity,
      entries,
      c.program.operands,
      registry.crypto_subset(),
    )?;
    let select_gate = SelectWordsGate::new(nu, 2)?;
    Ok(Self {
      read_slot: ByteReadSlot::declare(b, read_gate.clone()),
      read_gate,
      primitive_slot: b.slot(primitive_gate.clone()),
      primitive_gate,
      select_slot: SelectWordsSlot::declare(b, select_gate.clone()),
      select_gate,
      hash: common_hash.sharing_primitives(b, capacity.bytes())?,
      capacity,
      entries,
      zero: b.fixed_public_input(F128::ZERO),
      residual_zero: b.fixed_public_input(F128::ZERO),
    })
  }

  pub(super) fn bank(&self, program: &[Wire], input: &[Wire]) -> Vec<Wire> {
    let mut bank = program.to_vec();
    bank.extend_from_slice(input);
    assert!(bank.len() <= self.entries * self.capacity.record_words());
    bank.resize(self.entries * self.capacity.record_words(), self.zero);
    bank
  }

  pub(super) fn evaluate(
    &self,
    b: &mut impl CircuitEmitter,
    scalar: &ScalarPrimitiveSlots,
    headers: &[Wire; 2],
    args: &[Wire],
    bank: &mut [Wire],
    allocation: usize,
  ) -> [Wire; 2] {
    assert!(allocation < self.entries);
    let first = self.read_slot.read(b, &args[..2], bank);
    let second =
      self.read_slot.read(b, args.get(2..4).unwrap_or(&[self.zero; 2]), bank);
    let mut message = first[1..].to_vec();
    message.resize(self.hash.padded_words(), self.zero);
    // Every step runs the same hash network. Dispatch only controls whether
    // its constrained digest becomes the operation's allocated record.
    let digest = self.hash.hash(b, first[0], &message);
    let id = b.fixed_public_input(F128::new(allocation as u64, 0));
    let mut inputs = headers.to_vec();
    inputs.push(id);
    inputs.extend_from_slice(args);
    inputs.extend_from_slice(&first);
    inputs.extend_from_slice(&second);
    inputs.extend_from_slice(&digest);
    let output = b.gate(self.primitive_slot, &inputs);
    let record_words = self.capacity.record_words();
    // The residual class must not be reused as an input: the upstream
    // witness scheduler treats connected gate outputs as class producers.
    b.connect(output[5 + record_words], self.residual_zero);
    let scalar_result = scalar.evaluate(b, &[output[1], output[2]], args);
    let result =
      self.select_slot.select(b, output[0], &output[3..5], &scalar_result);
    bank[allocation * record_words..(allocation + 1) * record_words]
      .copy_from_slice(&output[5..5 + record_words]);
    result.try_into().unwrap()
  }
}
