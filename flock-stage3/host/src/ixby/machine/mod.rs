//! Capacity-only connections between decoded artifacts, primitive evaluation
//! and the ordered-frame control machine. No host-resolved action is a free
//! input at this boundary.

mod action;
mod bytes;
mod initial;
mod nats;
mod objects;
mod output;
#[cfg(test)]
pub(crate) mod tests;

pub use action::{ActionAssembleGate, ActionAssembleRow, ActionAssembleSlot};
pub use initial::{InitialStateGate, InitialStateRow, InitialStateSlot};
pub use output::{OutputEncodeGate, OutputEncodeRow, OutputEncodeSlot};

use crate::{
  ixby::{
    bounded_hash::BoundedBlake3,
    byte_value::{ByteCapacity, ByteDecodeLayout, ByteReadGate},
    control::{ControlCapacities, ControlStepGate, ControlStepSlot},
    decode::{
      InputCapacities, InputDecodeGate, InputDecodeSlot, OperandResolveGate,
      OperandResolveSlot, PrimitiveSet, ProgramCapacities, ProgramDecodeGate,
      ProgramDecodeSlot, ProgramFetchGate, ProgramFetchSlot,
    },
    nat_value::NatCapacity,
    object_value::{ObjectCapacity, ObjectLayout},
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
  pub(crate) bytes: Option<bytes::ByteMachineSlots>,
  pub(crate) objects: Option<objects::ObjectMachineSlots>,
  pub(crate) nats: Option<nats::NatMachineSlots>,
  capacity: MachineCapacities,
}

impl ScalarMachineSlots {
  pub fn declare(
    b: &mut impl CircuitEmitter,
    nu: usize,
    c: MachineCapacities,
    registry: PrimitiveSet,
  ) -> Result<Self> {
    Self::declare_inner(b, nu, c, registry, None, None, None)
  }

  /// Explicit byte-capable implementation. Sharing the commitment hash's
  /// primitives keeps one driver per physical table in the compiled executor.
  pub fn declare_with_bytes(
    b: &mut impl CircuitEmitter,
    nu: usize,
    c: MachineCapacities,
    registry: PrimitiveSet,
    capacity: ByteCapacity,
    common_hash: &BoundedBlake3,
  ) -> Result<Self> {
    Self::declare_inner(
      b,
      nu,
      c,
      registry,
      Some((capacity, common_hash)),
      None,
      None,
    )
  }

  pub fn declare_with_objects(
    b: &mut impl CircuitEmitter,
    nu: usize,
    c: MachineCapacities,
    registry: PrimitiveSet,
    values: (ByteCapacity, ObjectCapacity),
    common_hash: &BoundedBlake3,
  ) -> Result<Self> {
    let objects = ObjectLayout::new(c, values.1)?;
    Self::declare_inner(
      b,
      nu,
      c,
      registry,
      Some((values.0, common_hash)),
      Some(objects),
      None,
    )
  }

  pub fn byte_capacity(&self) -> Option<ByteCapacity> {
    self.bytes.as_ref().map(|bytes| bytes.capacity)
  }
  pub fn nat_capacity(&self) -> Option<NatCapacity> {
    self.nats.as_ref().map(|nats| nats.gate.capacity)
  }
  pub fn declare_with_nats(
    b: &mut impl CircuitEmitter,
    nu: usize,
    c: MachineCapacities,
    registry: PrimitiveSet,
    values: (ByteCapacity, Option<ObjectCapacity>, NatCapacity),
    common_hash: &BoundedBlake3,
  ) -> Result<Self> {
    let objects = values
      .1
      .map(|capacity| {
        let mut layout = ObjectLayout::new(c, capacity)?;
        layout.nat_capacity = Some(values.2);
        Ok::<_, anyhow::Error>(layout)
      })
      .transpose()?;
    Self::declare_inner(
      b,
      nu,
      c,
      registry,
      Some((values.0, common_hash)),
      objects,
      Some(values.2),
    )
  }
  pub fn object_capacity(&self) -> Option<ObjectCapacity> {
    self.objects.as_ref().map(|objects| objects.layout.capacity)
  }

  fn declare_inner(
    b: &mut impl CircuitEmitter,
    nu: usize,
    c: MachineCapacities,
    registry: PrimitiveSet,
    byte_values: Option<(ByteCapacity, &BoundedBlake3)>,
    object_values: Option<ObjectLayout>,
    nat_values: Option<NatCapacity>,
  ) -> Result<Self> {
    ensure!((1..=64).contains(&c.steps), "prototype execution step capacity");
    ensure!(
      nat_values.is_some() || registry == registry.crypto_subset(),
      "Nat registry requires revision-1 execution"
    );
    let mut program_gate =
      ProgramDecodeGate::new(nu, c.program, c.control, registry)?;
    let mut input_gate = InputDecodeGate::new(nu, c.input)?;
    let mut fetch_gate = ProgramFetchGate::new(nu, c.program.layout())?;
    let mut operand_gate =
      OperandResolveGate::new(nu, c.control.locals, c.program.operands)?;
    let primitive_gate = PrimitivePrepareGate::new(
      nu,
      c.program.operands,
      if byte_values.is_some() {
        registry.crypto_scalar_subset()
      } else {
        registry
      },
    )?;
    let action_gate =
      ActionAssembleGate::new(nu, c.control, c.program.operands)?;
    let control_gate = ControlStepGate::new(nu, c.control)?;
    let mut initial_gate = InitialStateGate::new(
      nu,
      c.control,
      c.program.functions,
      c.input.values,
      c.steps as u32,
    )?;
    let mut output_gate = OutputEncodeGate::new(nu, c.control, c.output_bytes)?;
    if let Some((capacity, _)) = byte_values {
      let (program_records, mut entries) =
        bytes::ByteMachineSlots::allocations(c)?;
      if let Some(objects) = object_values {
        entries = objects.byte_entries();
      }
      // Admit the entire bank before any decoder table is materialized.
      ByteReadGate::new(nu, capacity, entries)?;
      program_gate = program_gate
        .with_byte_values(ByteDecodeLayout { capacity, base: 0 })?;
      input_gate = input_gate.with_byte_values(ByteDecodeLayout {
        capacity,
        base: program_records,
      })?;
      operand_gate = operand_gate.with_byte_handles(entries)?;
      initial_gate = initial_gate.with_byte_handles(entries)?;
      output_gate = output_gate.with_byte_values(capacity, entries)?;
      if let Some(objects) = object_values {
        program_gate = program_gate.with_objects(objects)?;
        input_gate = input_gate.with_objects(objects)?;
        fetch_gate = fetch_gate.with_objects();
        operand_gate = operand_gate.with_object_handles(objects.entries())?;
        initial_gate = initial_gate.with_object_handles(objects.entries())?;
        output_gate = output_gate.with_objects(objects, capacity);
      }
      if let Some(nats) = nat_values {
        program_gate = program_gate.with_nat_values(nats)?;
        input_gate = input_gate.with_nat_values(nats)?;
        fetch_gate = fetch_gate.with_nats();
        operand_gate = operand_gate.with_nat_handles()?;
        initial_gate = initial_gate.with_nat_handles()?;
        output_gate = output_gate.with_nat_values(nats)?;
      }
    }
    let mut machine = Self {
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
      bytes: byte_values
        .map(|(capacity, common)| {
          bytes::ByteMachineSlots::declare(
            b,
            nu,
            c,
            capacity,
            registry,
            common,
            (object_values, nat_values),
          )
        })
        .transpose()?,
      objects: object_values.map(|layout| {
        objects::ObjectMachineSlots::declare(b, nu, layout, c.control)
      }),
      nats: None,
      capacity: c,
    };
    if let Some(capacity) = nat_values {
      machine.nats = Some(nats::NatMachineSlots::declare(
        b,
        nu,
        c,
        machine.bytes.as_ref().unwrap(),
        capacity,
        registry,
      )?);
    }
    Ok(machine)
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
    let program_words = c.program.layout().words();
    let object_data = self.program_gate.object_data_word();
    let values = match &self.objects {
      None => self.input_slot.decode(b, input[0], &input[1..]),
      Some(objects) => self.input_slot.decode_with_objects(
        b,
        input[0],
        &input[1..],
        &program[object_data..object_data + objects.layout.declaration_words()],
      ),
    };
    let value_words = c.input.value_words();
    let value_bytes_end = value_words
      + self.bytes.as_ref().map_or(0, |bytes| {
        self.input_gate.byte_records() * bytes.capacity.record_words()
      });
    let mut bank = self.bytes.as_ref().map(|bytes| {
      bytes.bank(
        &program[program_words..object_data],
        &values[value_words..value_bytes_end],
      )
    });
    let mut arena = self
      .objects
      .as_ref()
      .map(|objects| objects.bank(&values[value_bytes_end..]));
    let object_program = &program[object_data..];
    let program = &program[..program_words];
    let mut state = self.initial_slot.initial(
      b,
      program[0],
      &program[1..1 + c.program.functions],
      &values[..value_words],
    );
    for step in 0..c.steps {
      let fetched = self.fetch_slot.fetch(b, state[0], state[1], program);
      let block_words = c.program.layout().block_words();
      let args = self.operand_slot.resolve(
        b,
        &state[1..1 + c.control.frame_words()],
        &fetched[..block_words],
      );
      let headers = [fetched[0], fetched[1]];
      let nat = self.nats.as_ref().map(|nats| {
        let bytes = self.bytes.as_ref().unwrap();
        nats.resolve(
          b,
          bytes,
          nats::NatStepInput {
            state: &mut state,
            headers,
            args: &args,
            bank: bank.as_ref().unwrap(),
            allocation: bytes.entries - c.steps + step,
          },
        )
      });
      let headers = nat.as_ref().map_or(headers, |nat| nat.headers);
      let evaluation_headers =
        nat.as_ref().map_or(headers, |nat| nat.evaluation_headers);
      let args = nat.as_ref().map_or(args.clone(), |nat| nat.args.clone());
      let mut primitive = if let Some(bytes) = &self.bytes {
        bytes.evaluate(
          b,
          &self.primitive_slots,
          &evaluation_headers,
          &args,
          bank.as_mut().unwrap(),
          bytes.entries - c.steps + step,
        )
      } else {
        self.primitive_slots.evaluate(b, &evaluation_headers, &args)
      };
      if let Some(nat) = &nat {
        let bytes = self.bytes.as_ref().unwrap();
        primitive = self.nats.as_ref().unwrap().finish(
          b,
          bytes,
          nat,
          primitive,
          bank.as_mut().unwrap(),
          bytes.entries - c.steps + step,
        );
      }
      let (headers, callee, primitive, args) = match &self.objects {
        None => (headers, fetched[block_words], primitive, args),
        Some(objects) => objects.step(
          b,
          objects::ObjectStep {
            state: &mut state,
            headers,
            callee: fetched[block_words],
            primitive,
            args: &args,
            program: object_program,
            arena: arena.as_mut().unwrap(),
            allocation: objects.layout.input_slots() + step,
          },
        ),
      };
      let action =
        self.action_slot.assemble(b, &headers, callee, &primitive, &args);
      state = self.control_slot.step(b, &state, &action);
    }
    self.primitive_slots.finish_canonical(b);
    if let Some(objects) = &self.objects {
      let mut records =
        object_program[..objects.layout.declaration_words()].to_vec();
      records.extend_from_slice(arena.as_ref().unwrap());
      records.extend_from_slice(bank.as_ref().unwrap());
      self.output_slot.encode_with_bytes(b, &state, &records)
    } else if let Some(bytes) = &self.bytes {
      let value_base = 1 + c.control.frame_words();
      let buffer = bytes.read_slot.read(
        b,
        &state[value_base..value_base + 2],
        bank.as_ref().unwrap(),
      );
      self.output_slot.encode_with_bytes(b, &state, &buffer)
    } else {
      self.output_slot.encode(b, &state)
    }
  }
}
