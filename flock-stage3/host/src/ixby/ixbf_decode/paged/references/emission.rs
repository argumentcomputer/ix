use super::*;
use crate::{
  ixby::{
    auth_memory::{
      MemoryDepth,
      multi::{MultiMemorySlots, MultiProofWires},
    },
    io::{InputLayout, LayoutEmitter, PublicLayout},
    memory_log::{AccessWires, MemoryLogSlots},
  },
  sizing::CircuitEmitter,
};
use flock_prover::circuit::builder::SlotId;
pub(super) struct Emission {
  pub reference: (SlotId, ReferenceGate),
  pub log: MemoryLogSlots,
  pub tree: MultiMemorySlots,
  pub inputs: InputLayout,
  pub public: PublicLayout,
}
pub(super) fn emit(b: &mut impl CircuitEmitter) -> Emission {
  let mut b = LayoutEmitter::new(b);
  let depth = MemoryDepth::new(40).unwrap();
  let log = MemoryLogSlots::declare(&mut b, NU, depth).unwrap();
  let tree = MultiMemorySlots::sharing_compression(
    &mut b,
    NU,
    depth,
    log.memory().compression(),
  )
  .unwrap();
  let g = ReferenceGate::new(NU).unwrap();
  let reference = (b.slot(g.clone()), g);
  let zero = b.fixed_public_input(F128::ZERO);
  let context: [_; 3] = std::array::from_fn(|_| b.input());
  let root: [_; 2] = std::array::from_fn(|_| b.input());
  let mut state: [_; 3] = std::array::from_fn(|_| b.input());
  for w in context.into_iter().chain(root).chain(state) {
    b.publish(w);
  }
  let mut accesses = Vec::new();
  for _ in 0..STEPS {
    let mut input = context.into_iter().chain(state).collect::<Vec<_>>();
    input.extend((0..9).map(|_| b.input()));
    let out = b.gate(reference.0, &input);
    b.connect(out[19], zero);
    state.copy_from_slice(&out[..3]);
    for r in out[3..19].as_chunks::<4>().0 {
      accesses.push(AccessWires {
        address: r[0],
        write: r[1],
        value: [r[2], r[3]],
      });
    }
  }
  for w in state {
    b.publish(w);
  }
  let memory = MultiProofWires::inputs(&mut b, capacity());
  let switches =
    (0..MemoryLogSlots::plan(4 * STEPS, CELLS).unwrap().switches())
      .map(|_| b.input())
      .collect::<Vec<_>>();
  log.check_shared(&mut b, &tree, [root, root], &accesses, &memory, &switches);
  let (inputs, public) = b.finish();
  Emission { reference, log, tree, inputs, public }
}
