use super::*;
use crate::{
  equality::F128EqualityGate,
  ixby::{
    auth_memory::{
      MemoryDepth,
      multi::{MultiMemorySlots, MultiProofWires},
    },
    io::{InputLayout, LayoutEmitter, PublicLayout},
    ixbf_decode::{
      source::{SourceCapacity, SourceChunkProofWires, SourceReadSlots},
      stream::{StreamGate, StreamOp},
    },
    memory_log::{AccessWires, MemoryLogSlots},
  },
  sizing::CircuitEmitter,
};
use flock_prover::circuit::builder::{SlotId, Wire};
pub(super) fn source_capacity() -> SourceCapacity {
  SourceCapacity::new(SOURCE_DEPTH, 32).unwrap()
}
pub(super) struct Emission {
  pub gates: [(SlotId, OutputBytesGate); 2],
  pub controls: [(SlotId, StreamGate); 2],
  pub equal: SlotId,
  pub source: SourceReadSlots,
  pub log: MemoryLogSlots,
  pub tree: MultiMemorySlots,
  pub inputs: InputLayout,
  pub public: PublicLayout,
}
fn equal(
  b: &mut impl CircuitEmitter,
  slot: SlotId,
  zero: Wire,
  x: Wire,
  y: Wire,
) {
  let out = b.gate(slot, &[x, y]);
  b.connect(out[0], zero);
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
  let source = SourceReadSlots::sharing_compression(
    &mut b,
    NU,
    source_capacity(),
    log.memory().compression(),
  )
  .unwrap();
  let gates = [OutputBytesOp::Header, OutputBytesOp::Step].map(|op| {
    let g = OutputBytesGate::new(NU, op).unwrap();
    (b.slot(g.clone()), g)
  });
  let controls = [StreamOp::Cache, StreamOp::Read].map(|op| {
    let g = StreamGate::new(NU, source_capacity(), op).unwrap();
    (b.slot(g.clone()), g)
  });
  let equality = b.slot(F128EqualityGate { nu: NU });
  let zero = b.fixed_public_input(F128::ZERO);
  let one = b.fixed_public_input(F128::ONE);
  let shared: [_; 7] = std::array::from_fn(|_| {
    let w = b.input();
    b.publish(w);
    w
  });
  let [length, hash0, hash1, root0, root1, tag, range] = shared;
  let mut index = b.input();
  b.publish(index);
  let first = b.input();
  let proofs: [SourceChunkProofWires; 4] =
    std::array::from_fn(|_| SourceChunkProofWires {
      bytes: std::array::from_fn(|_| b.input()),
      siblings: (0..SOURCE_DEPTH)
        .map(|_| std::array::from_fn(|_| b.input()))
        .collect(),
    });
  let cache = b.gate(controls[0].0, &[length, first]);
  b.connect(cache[2], zero);
  for (chunk, proof) in
    [zero, first, cache[0], cache[1]].into_iter().zip(&proofs)
  {
    source.authenticate_chunk(&mut b, length, chunk, [hash0, hash1], proof);
  }
  let header = b.gate(
    gates[0].0,
    &[length, tag, range, proofs[0].bytes[0], proofs[0].bytes[1], index],
  );
  b.connect(header[2], zero);
  let mut accesses = Vec::new();
  for step in 0..STEPS {
    let enabled = if step == 0 { one } else { b.input() };
    let replies: [Wire; 4] = std::array::from_fn(|_| b.input());
    let out = b.gate(
      gates[1].0,
      &[tag, range, header[0], length, index, enabled]
        .into_iter()
        .chain(replies)
        .collect::<Vec<_>>(),
    );
    b.connect(out[7], zero);
    index = out[0];
    let prepared = b.gate(controls[1].0, &[out[1], out[2], length, first]);
    b.connect(prepared[2], zero);
    let window = b.gate(
      source.window_gate().0,
      &[prepared[0], prepared[1]]
        .into_iter()
        .chain(proofs[1].bytes)
        .chain(proofs[2].bytes)
        .collect::<Vec<_>>(),
    );
    b.connect(window[6], zero);
    for (x, y) in [
      (window[0], length),
      (window[1], first),
      (window[2], cache[0]),
      (window[4], out[5]),
      (window[5], out[6]),
    ] {
      equal(&mut b, equality, zero, x, y);
    }
    for i in 0..2 {
      accesses.push(AccessWires {
        address: out[3 + i],
        write: zero,
        value: [replies[2 * i], replies[2 * i + 1]],
      });
    }
  }
  b.publish(index);
  let memory = MultiProofWires::inputs(&mut b, capacity());
  let switches =
    (0..MemoryLogSlots::plan(2 * STEPS, CELLS).unwrap().switches())
      .map(|_| b.input())
      .collect::<Vec<_>>();
  log.check_shared(
    &mut b,
    &tree,
    [[root0, root1]; 2],
    &accesses,
    &memory,
    &switches,
  );
  let (inputs, public) = b.finish();
  Emission {
    gates,
    controls,
    equal: equality,
    source,
    log,
    tree,
    inputs,
    public,
  }
}
