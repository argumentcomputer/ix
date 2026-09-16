use super::*;
use crate::{
  ixby::{
    auth_memory::{MemoryDepth, MemoryOpeningWires, SparseMemory},
    io::{InputLayout, LayoutEmitter, PublicLayout},
    memory_log::{BoundaryWires, MemoryBatch, MemoryLogSlots},
    wide_fuel::Fuel64,
  },
  sizing::{CircuitEmitter, CountingEmitter},
};
use flock_prover::circuit::builder::{CircuitShape, GateType, ShapeBuilder};

pub(super) const NU: usize = 10;
pub(super) const STEPS: usize = 6;
pub(super) const CELLS: usize = 8;
pub(super) const OUTPUTS: usize = 48;
pub(super) const BUDGET: u64 = 16_000_000_000;
pub(super) struct Emission {
  pub frame: FrameSlots,
  pub memory: MemoryLogSlots,
  pub inputs: InputLayout,
  pub public: PublicLayout,
}
pub(super) fn emit(b: &mut impl CircuitEmitter) -> Emission {
  let mut b = LayoutEmitter::new(b);
  let frame = FrameSlots::declare(&mut b, NU).unwrap();
  let memory =
    MemoryLogSlots::declare(&mut b, NU, MemoryDepth::new(40).unwrap()).unwrap();
  let mut state = std::array::from_fn(|_| b.input());
  let mut fuel = b.input();
  let root = std::array::from_fn(|_| b.input());
  let limits = b.input();
  let budget = b.input();
  for wire in
    state.into_iter().chain([fuel]).chain(root).chain([limits, budget])
  {
    b.publish(wire);
  }
  let mut accesses = Vec::new();
  for _ in 0..STEPS {
    let action = std::array::from_fn(|_| b.input());
    for word in action {
      b.publish(word);
    }
    let reply = std::array::from_fn(|_| b.input());
    let output = frame.step(&mut b, state, action, reply, limits, fuel, budget);
    state = output.state;
    fuel = output.fuel;
    accesses.extend(output.accesses);
  }
  for word in state.into_iter().chain([fuel]) {
    b.publish(word);
  }
  let cells = (0..CELLS)
    .map(|_| BoundaryWires {
      address: b.input(),
      opening: MemoryOpeningWires {
        value: std::array::from_fn(|_| b.input()),
        siblings: (0..40).map(|_| std::array::from_fn(|_| b.input())).collect(),
      },
      final_value: std::array::from_fn(|_| b.input()),
    })
    .collect::<Vec<_>>();
  let switches =
    (0..MemoryLogSlots::plan(3 * STEPS, CELLS).unwrap().switches())
      .map(|_| b.input())
      .collect::<Vec<_>>();
  for word in memory.check(&mut b, root, &accesses, &cells, &switches) {
    b.publish(word);
  }
  let (inputs, public) = b.finish();
  assert_eq!(public.outputs(), OUTPUTS);
  Emission { frame, memory, inputs, public }
}
pub(super) fn setup() -> (Emission, CircuitShape) {
  let mut b = ShapeBuilder::new(NU);
  let emission = emit(&mut b);
  (emission, b.finish().unwrap())
}
pub(super) fn fixture(salt: u64) -> (Vec<F128>, Vec<F128>) {
  let value = |n| [F128::new(8, 0), F128::new(n, salt)];
  let mut memory = SparseMemory::new(MemoryDepth::new(40).unwrap());
  memory.replace(SCRATCH, value(1)).unwrap();
  memory.replace(SCRATCH + 1, value(2)).unwrap();
  let root = memory.root();
  let mut state = FrameState::eval(680, 184, 72, 647).words();
  let mut fuel = Fuel64::initial(BUDGET);
  let limits = F128::new(128, 1024);
  let mut private = state
    .into_iter()
    .chain([fuel.word()])
    .chain(root)
    .chain([limits, F128::new(BUDGET, 0)])
    .collect::<Vec<_>>();
  let mut expected = private.clone();
  let mut bind = Action::new(ActionKind::Bind);
  bind.target = 41;
  bind.value = value(3);
  let mut call = Action::new(ActionKind::Call);
  call.target = 42;
  call.callee = 671;
  call.entry = 180;
  call.arity = 2;
  call.arguments = Vector { pointer: SCRATCH, count: 2 };
  let mut ret = Action::new(ActionKind::Return);
  ret.value = value(4);
  let commands = [Some(bind), Some(call), None, None, Some(ret), None];
  let mut batch = MemoryBatch::new(&mut memory);
  let gate = FrameGate::new(NU).unwrap();
  for action in commands {
    let action = action.map_or([F128::ZERO; 5], Action::words);
    private.extend(action);
    expected.extend(action);
    let phase = state[0].lo as u8;
    let read_address = match phase {
      1 => CONTINUATIONS + (state[0].lo >> 48) - 1,
      4 => state[1].lo + (state[0].hi & 255),
      _ => 0,
    };
    let reply = batch.value(read_address).unwrap();
    private.extend(reply);
    let input = state
      .into_iter()
      .chain(action)
      .chain(reply)
      .chain([limits])
      .collect::<Vec<_>>();
    let mut output = Vec::new();
    gate.eval(&input, &(), &mut output);
    assert_eq!(output[18], F128::ZERO);
    for event in output[5..17].as_chunks::<4>().0 {
      let address = event[0].lo;
      let value = [event[2], event[3]];
      if event[1] == F128::ONE {
        batch.write(address, value).unwrap();
      } else {
        assert_eq!(event[1], F128::ZERO);
        assert_eq!(batch.read(address).unwrap(), value);
      }
    }
    state = output[..5].try_into().unwrap();
    if output[17] != F128::new(2, 0) {
      fuel.remaining -= 1;
      fuel.consumed += 1;
    }
  }
  assert_eq!(state, FrameState::eval(680, 42, 74, 647).words());
  assert_eq!(fuel.consumed, 4);
  expected.extend(state);
  expected.push(fuel.word());
  let advice = batch.finish().unwrap();
  assert_eq!(advice.boundaries.len(), CELLS);
  assert_eq!(advice.initial_root, root);
  private.extend(advice.private_boundary_words());
  expected.extend(advice.final_root);
  (private, expected)
}

#[test]
fn frame_batches_bind_fuel_memory_and_every_state_boundary_word() {
  let (emission, shape) = setup();
  let mut counted = CountingEmitter::new();
  let counted_emission = emit(&mut counted);
  counted.ensure_matches(&shape).unwrap();
  assert_eq!(counted_emission.inputs, emission.inputs);
  assert_eq!(counted_emission.public, emission.public);
  for salt in [0, 1, u64::MAX] {
    let (private, expected) = fixture(salt);
    let witness = shape.run(&emission.inputs.assign(&private).unwrap(), &[]);
    assert_eq!(witness.public, emission.public.instantiate(&expected).unwrap());
  }
  // The high-bit differential and locally recomputed attacks are exercised
  // by the frame row tests and the separate real proof test.
}
