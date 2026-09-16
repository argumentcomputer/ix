use super::*;
use crate::{
  ixby::{
    auth_memory::{
      MemoryDepth,
      multi::{
        FrontierWires, LeafWires, MultiMemorySlots, MultiProofWires,
        ParentWires,
      },
    },
    io::{InputLayout, LayoutEmitter, PublicLayout},
    ixbf_decode::source::{
      SourceCapacity, SourceChunkProofWires, SourceReadSlots,
    },
  },
  sizing::CircuitEmitter,
};
use flock_prover::circuit::builder::SlotId;

pub(super) struct Emission {
  pub gates: [(SlotId, SourceBytesGate); 2],
  pub source: SourceReadSlots,
  pub memory: MultiMemorySlots,
  pub inputs: InputLayout,
  pub public: PublicLayout,
}
pub(super) fn emit(b: &mut impl CircuitEmitter, bank: SourceBank) -> Emission {
  let mut b = LayoutEmitter::new(b);
  let memory = MultiMemorySlots::declare(
    &mut b,
    NU,
    MemoryDepth::new(MEMORY_DEPTH).unwrap(),
  )
  .unwrap();
  let source = SourceReadSlots::sharing_compression(
    &mut b,
    NU,
    SourceCapacity::new(SOURCE_DEPTH, 0).unwrap(),
    memory.compression(),
  )
  .unwrap();
  let gates = [SourceBytesOp::Control, SourceBytesOp::Copy].map(|op| {
    let g = SourceBytesGate::new(bank, NU, op).unwrap();
    (b.slot(g.clone()), g)
  });
  let zero = b.fixed_public_input(F128::ZERO);
  let residual = b.fixed_public_input(F128::ZERO);
  let first_words: [_; 6] = std::array::from_fn(|_| {
    let w = b.input();
    b.publish(w);
    w
  });
  let [length, root0, root1, first, old0, old1] = first_words;
  let control = b.gate(gates[0].0, &[length, first]);
  b.connect(control[4], residual);
  b.publish(control[3]);
  let final_root = std::array::from_fn(|_| {
    let w = b.input();
    b.publish(w);
    w
  });
  let proofs: [SourceChunkProofWires; 3] =
    std::array::from_fn(|_| SourceChunkProofWires {
      bytes: std::array::from_fn(|_| b.input()),
      siblings: (0..SOURCE_DEPTH)
        .map(|_| std::array::from_fn(|_| b.input()))
        .collect(),
    });
  for (index, proof) in [first, control[0], control[1]].into_iter().zip(&proofs)
  {
    source.authenticate_chunk(&mut b, length, index, [root0, root1], proof);
  }
  let copy_input = [first, control[2]]
    .into_iter()
    .chain(proofs[0].bytes)
    .chain(proofs[1].bytes)
    .collect::<Vec<_>>();
  let copy = b.gate(gates[1].0, &copy_input);
  b.connect(copy[3 * CELLS], residual);
  let leaves = (0..CELLS)
    .map(|i| LeafWires {
      address: copy[3 * i],
      old: [zero; 2],
      new: [copy[3 * i + 1], copy[3 * i + 2]],
    })
    .collect();
  let frontier = (0..capacity().frontier())
    .map(|_| FrontierWires {
      enabled: b.input(),
      position: b.input(),
      hash: std::array::from_fn(|_| b.input()),
    })
    .collect();
  let parents = (0..PARENTS)
    .map(|_| ParentWires {
      enabled: b.input(),
      position: b.input(),
      old_children: std::array::from_fn(|_| std::array::from_fn(|_| b.input())),
      new_children: std::array::from_fn(|_| std::array::from_fn(|_| b.input())),
    })
    .collect();
  let switches = (0..capacity().plan().switches()).map(|_| b.input()).collect();
  memory.check(
    &mut b,
    [[old0, old1], final_root],
    &MultiProofWires { leaves, frontier, parents, switches },
  );
  let (inputs, public) = b.finish();
  Emission { gates, source, memory, inputs, public }
}
