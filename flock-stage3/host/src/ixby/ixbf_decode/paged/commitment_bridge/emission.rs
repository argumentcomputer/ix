use super::*;
use crate::{
  ixby::{
    io::{InputLayout, LayoutEmitter, PublicLayout},
    ixbf_decode::source::{
      SourceCapacity, SourceChunkProofWires, SourceReadSlots,
    },
  },
  sizing::CircuitEmitter,
};
use flock_prover::circuit::builder::SlotId;
pub(super) struct Emission {
  pub gates: [(SlotId, CommitmentBridgeGate); 2],
  pub source: SourceReadSlots,
  pub prefixed: SourceReadSlots,
  pub inputs: InputLayout,
  pub public: PublicLayout,
}
pub(super) fn emit(
  b: &mut impl CircuitEmitter,
  domain: ArtifactDomain,
) -> Emission {
  let mut b = LayoutEmitter::new(b);
  let source = SourceReadSlots::declare(
    &mut b,
    NU,
    SourceCapacity::new(RAW_DEPTH, 0).unwrap(),
  )
  .unwrap();
  let prefixed = SourceReadSlots::sharing_compression(
    &mut b,
    NU,
    SourceCapacity::new(PREFIXED_DEPTH, 0).unwrap(),
    source.compression(),
  )
  .unwrap();
  let gates =
    [CommitmentBridgeOp::Control, CommitmentBridgeOp::Copy].map(|op| {
      let g = CommitmentBridgeGate::new(NU, domain, op).unwrap();
      (b.slot(g.clone()), g)
    });
  let zero = b.fixed_public_input(F128::ZERO);
  let public: [_; 8] = std::array::from_fn(|_| {
    let w = b.input();
    b.publish(w);
    w
  });
  let [length, raw0, raw1, parent0, parent1, hash0, hash1, index] = public;
  let control = b.gate(gates[0].0, &[length, index]);
  b.connect(control[7], zero);
  b.publish(control[4]);
  let raw: [SourceChunkProofWires; 3] =
    std::array::from_fn(|_| SourceChunkProofWires {
      bytes: std::array::from_fn(|_| b.input()),
      siblings: (0..RAW_DEPTH)
        .map(|_| std::array::from_fn(|_| b.input()))
        .collect(),
    });
  for (at, proof) in control[..3].iter().zip(&raw) {
    source.authenticate_chunk(&mut b, length, *at, [raw0, raw1], proof);
  }
  let copy = b.gate(
    gates[1].0,
    &[index, parent0, parent1, control[5]]
      .into_iter()
      .chain(raw[0].bytes)
      .chain(raw[1].bytes)
      .collect::<Vec<_>>(),
  );
  b.connect(copy[64], zero);
  let transformed = SourceChunkProofWires {
    bytes: copy[..64].try_into().unwrap(),
    siblings: (0..PREFIXED_DEPTH)
      .map(|_| std::array::from_fn(|_| b.input()))
      .collect(),
  };
  prefixed.authenticate_chunk(
    &mut b,
    control[3],
    index,
    [hash0, hash1],
    &transformed,
  );
  // The independently authenticated final transformed chunk binds this
  // component's exact prefixed length even before a chain is completed.
  let final_index = control[6];
  let last = SourceChunkProofWires {
    bytes: std::array::from_fn(|_| b.input()),
    siblings: (0..PREFIXED_DEPTH)
      .map(|_| std::array::from_fn(|_| b.input()))
      .collect(),
  };
  prefixed.authenticate_chunk(
    &mut b,
    control[3],
    final_index,
    [hash0, hash1],
    &last,
  );
  let (inputs, public) = b.finish();
  Emission { gates, source, prefixed, inputs, public }
}
