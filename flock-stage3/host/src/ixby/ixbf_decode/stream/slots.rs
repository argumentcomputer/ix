use super::*;
use crate::{
  blake3_backend::Blake3CompressionSlots,
  equality::F128EqualityGate,
  ixby::{
    ixbf_decode::{dispatch::*, source::*},
    select::{SelectWordsGate, SelectWordsSlot},
  },
  sizing::CircuitEmitter,
};
use anyhow::Result;
use flock_prover::{
  circuit::builder::{SlotId, Wire},
  field::F128,
};

/// Only a checked authentication can create a cache. No host byte buffer or
/// arbitrary root can be substituted for its retained circuit wires.
#[derive(Clone, Debug)]
pub struct CachedSource {
  capacity: SourceCapacity,
  length: Wire,
  first: Wire,
  next: Wire,
  chunks: [[Wire; 64]; 2],
}

pub struct StreamStepWires {
  pub remaining: Wire,
  pub event: DispatchStepWires,
}

pub struct StreamSlots {
  dispatch: DispatchSlots,
  source: SourceReadSlots,
  controls: [SlotId; 3],
  select: SelectWordsSlot,
  equal: SlotId,
  zero: Wire,
}
impl StreamSlots {
  pub fn declare(
    b: &mut impl CircuitEmitter,
    nu: usize,
    config: DispatchConfig,
    depth: usize,
  ) -> Result<Self> {
    Self::declare_inner(b, nu, config, depth, None)
  }
  pub fn sharing_compression(
    b: &mut impl CircuitEmitter,
    nu: usize,
    config: DispatchConfig,
    depth: usize,
    compression: &Blake3CompressionSlots,
  ) -> Result<Self> {
    Self::declare_inner(b, nu, config, depth, Some(compression))
  }
  fn declare_inner(
    b: &mut impl CircuitEmitter,
    nu: usize,
    config: DispatchConfig,
    depth: usize,
    compression: Option<&Blake3CompressionSlots>,
  ) -> Result<Self> {
    let capacity = SourceCapacity::new(depth, config.window_bytes())?;
    let dispatch = DispatchSlots::declare(b, nu, config)?;
    let source = match compression {
      Some(compression) => {
        SourceReadSlots::sharing_compression(b, nu, capacity, compression)?
      },
      None => SourceReadSlots::declare(b, nu, capacity)?,
    };
    let controls = StreamOp::ALL
      .into_iter()
      .map(|op| Ok(b.slot(StreamGate::new(nu, capacity, op)?)))
      .collect::<Result<Vec<_>>>()?
      .try_into()
      .unwrap();
    Ok(Self {
      dispatch,
      source,
      controls,
      select: SelectWordsSlot::declare(b, SelectWordsGate::new(nu, 31)?),
      equal: b.slot(F128EqualityGate { nu }),
      zero: b.fixed_public_input(F128::ZERO),
    })
  }
  pub fn dispatch(&self) -> &DispatchSlots {
    &self.dispatch
  }
  pub fn source(&self) -> &SourceReadSlots {
    &self.source
  }
  pub fn control_slot(&self, op: StreamOp) -> SlotId {
    self.controls[op as usize]
  }
  pub fn select_slot(&self) -> SlotId {
    self.select.slot()
  }
  pub fn equality_slot(&self) -> SlotId {
    self.equal
  }
  fn equal(&self, b: &mut impl CircuitEmitter, first: Wire, second: Wire) {
    let out = b.gate(self.equal, &[first, second]);
    b.connect(out[0], self.zero);
  }
  fn control(
    &self,
    b: &mut impl CircuitEmitter,
    op: StreamOp,
    input: &[Wire],
  ) -> Vec<Wire> {
    let mut out = b.gate(self.control_slot(op), input);
    b.connect(out.pop().unwrap(), self.zero);
    out
  }

  /// Bind `root` to the externally expected artifact. A final-chunk proof
  /// binds its exact length even when opaque siblings hide the file suffix.
  /// Advice is first, next and final; aliases still use the same fixed shape.
  pub fn authenticate(
    &self,
    b: &mut impl CircuitEmitter,
    length: Wire,
    root: [Wire; 2],
    first: Wire,
    proofs: &[SourceChunkProofWires; 3],
  ) -> CachedSource {
    let indices = self.control(b, StreamOp::Cache, &[length, first]);
    for (index, proof) in
      [first, indices[0], indices[1]].into_iter().zip(proofs)
    {
      assert_eq!(proof.siblings.len(), self.source.capacity().depth());
      self.source.authenticate_chunk(b, length, index, root, proof);
    }
    CachedSource {
      capacity: self.source.capacity(),
      length,
      first,
      next: indices[0],
      chunks: [proofs[0].bytes, proofs[1].bytes],
    }
  }

  fn read(
    &self,
    b: &mut impl CircuitEmitter,
    cache: &CachedSource,
    cursor: Wire,
    take: Wire,
  ) -> SourceReadWires {
    assert_eq!(cache.capacity, self.source.capacity());
    let mut input = self.control(
      b,
      StreamOp::Read,
      &[cursor, take, cache.length, cache.first],
    );
    input.extend(cache.chunks[0]);
    input.extend(cache.chunks[1]);
    let mut out = b.gate(self.source.window_gate().0, &input);
    b.connect(out.pop().unwrap(), self.zero);
    // These independently computed outputs depend on the cache controls.
    // Directed equality avoids merging them into their own producer inputs.
    self.equal(b, out[0], cache.length);
    self.equal(b, out[1], cache.first);
    self.equal(b, out[2], cache.next);
    SourceReadWires { file_length: out[0], words: out[4..].to_vec() }
  }

  /// Consume one actual decoder step while `remaining > 0`; otherwise carry
  /// all state words unchanged and expose no committed event. Remaining is
  /// exact u64, decremented in-circuit. Pin it to zero after the physical batch.
  /// A positive byte request must begin in the authenticated first chunk;
  /// lookahead can cross into the next chunk. Zero-take payload advances and
  /// padding return constrained zero bytes without a spurious page reload.
  pub fn step(
    &self,
    b: &mut impl CircuitEmitter,
    cache: &CachedSource,
    state: DispatchState,
    remaining: Wire,
  ) -> StreamStepWires {
    let mut input = vec![remaining];
    input.extend(state.0);
    let prepared = self.control(b, StreamOp::Prepare, &input);
    let view = DispatchState(prepared[2..].try_into().unwrap());
    let mut event = self
      .dispatch
      .step(b, view, |b, cursor, take| self.read(b, cache, cursor, take));
    let mut yes = event.state.0.to_vec();
    yes.push(event.committed);
    let mut no = state.0.to_vec();
    no.push(self.zero);
    let selected = self.select.select(b, prepared[1], &yes, &no);
    event.state = DispatchState(selected[..30].try_into().unwrap());
    event.committed = selected[30];
    StreamStepWires { remaining: prepared[0], event }
  }
  pub fn finish_batch(&self, b: &mut impl CircuitEmitter, remaining: Wire) {
    b.connect(remaining, self.zero);
  }
}
