use super::*;
use crate::{
  ixby::{
    auth_memory::{
      MemoryDepth,
      multi::{MultiMemorySlots, MultiProofWires},
    },
    io::{InputLayout, LayoutEmitter, PublicLayout},
    ixbf_decode::{
      dispatch::DispatchState, paged::input_capture::InputCaptureSlots,
      source::SourceChunkProofWires, stream::StreamSlots,
    },
    memory_log::MemoryLogSlots,
  },
  sizing::CircuitEmitter,
};
pub(super) struct Emission {
  pub stream: StreamSlots,
  pub capture: InputCaptureSlots,
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
  let stream = StreamSlots::sharing_compression(
    &mut b,
    NU,
    config(),
    DEPTH,
    log.memory().compression(),
  )
  .unwrap();
  let capture = InputCaptureSlots::declare(&mut b, NU).unwrap();
  let length = b.input();
  let root = std::array::from_fn(|_| b.input());
  let initial = DispatchState(std::array::from_fn(|_| b.input()));
  let initial_capture: [_; 5] = std::array::from_fn(|_| b.input());
  let initial_root: [_; 2] = std::array::from_fn(|_| b.input());
  for w in [length]
    .into_iter()
    .chain(root)
    .chain(initial.0)
    .chain(initial_capture)
    .chain(initial_root)
  {
    b.publish(w);
  }
  let first = b.input();
  let mut remaining = b.input();
  let proofs = std::array::from_fn(|_| SourceChunkProofWires {
    bytes: std::array::from_fn(|_| b.input()),
    siblings: (0..DEPTH).map(|_| std::array::from_fn(|_| b.input())).collect(),
  });
  let cached = stream.authenticate(&mut b, length, root, first, &proofs);
  let mut state = initial;
  let mut captured = initial_capture;
  let mut accesses = Vec::new();
  for _ in 0..STEPS {
    let step = stream.step(&mut b, &cached, state, remaining);
    let resolved = b.input();
    let replies = std::array::from_fn(|_| std::array::from_fn(|_| b.input()));
    let out = capture
      .step(&mut b, state, &step.event, captured, resolved, replies)
      .unwrap();
    remaining = step.remaining;
    state = step.event.state;
    captured = out.state;
    accesses.extend(out.accesses);
  }
  stream.finish_batch(&mut b, remaining);
  for w in state.0.into_iter().chain(captured) {
    b.publish(w);
  }
  let final_root = std::array::from_fn(|_| {
    let w = b.input();
    b.publish(w);
    w
  });
  let memory = MultiProofWires::inputs(&mut b, capacity());
  let switches =
    (0..MemoryLogSlots::plan(6 * STEPS, CELLS).unwrap().switches())
      .map(|_| b.input())
      .collect::<Vec<_>>();
  log.check_shared(
    &mut b,
    &tree,
    [initial_root, final_root],
    &accesses,
    &memory,
    &switches,
  );
  let (inputs, public) = b.finish();
  Emission { stream, capture, log, tree, inputs, public }
}
