use super::{
  SOURCE_CHUNK_WORDS, SourceBlockGate, SourceCapacity, SourcePathGate,
  SourceWindowGate,
};
use crate::{
  blake3_backend::{Blake3Backend, Blake3CompressionSlots},
  hash::{IV, pack8},
  ixby::select::{SelectWordsGate, SelectWordsSlot},
  sizing::CircuitEmitter,
};
use anyhow::Result;
use flock_prover::{
  circuit::builder::{SlotId, Wire},
  field::F128,
};

/// Untrusted chunk bytes and one sibling CV per setup-owned tree level.
/// An absent sibling must be zero. The bytes include canonical chunk padding.
#[derive(Clone, Debug)]
pub struct SourceChunkProofWires {
  pub bytes: [Wire; SOURCE_CHUNK_WORDS],
  pub siblings: Vec<[Wire; 2]>,
}

#[derive(Clone, Debug)]
pub struct SourceReadWires {
  pub file_length: Wire,
  pub words: Vec<Wire>,
}

/// Fixed-shape authenticated source read, not a complete parser or an Exec
/// profile. Every read authenticates first, next and final chunks. A future
/// streaming parser should share chunk authentication across many records,
/// and authenticate the final chunk only once per file; it must not bypass
/// the length binding. Declaration/counting never examines witness values.
#[derive(Clone)]
pub struct SourceReadSlots {
  capacity: SourceCapacity,
  window: (SlotId, SourceWindowGate),
  block: (SlotId, SourceBlockGate),
  path: (SlotId, SourcePathGate),
  select_gate: SelectWordsGate,
  select: SelectWordsSlot,
  compression: Blake3CompressionSlots,
  zero: Wire,
  iv: [Wire; 2],
  block_indices: [Wire; 16],
  levels: Vec<Wire>,
}

impl SourceReadSlots {
  pub fn declare(
    b: &mut impl CircuitEmitter,
    nu: usize,
    capacity: SourceCapacity,
  ) -> Result<Self> {
    let window_gate = SourceWindowGate::new(nu, capacity)?;
    let block_gate = SourceBlockGate::new(nu, capacity.depth())?;
    let path_gate = SourcePathGate::new(nu, capacity.depth())?;
    let window = (b.slot(window_gate.clone()), window_gate);
    let block = (b.slot(block_gate.clone()), block_gate);
    let path = (b.slot(path_gate.clone()), path_gate);
    let select_gate = SelectWordsGate::new(nu, 2)?;
    let select = SelectWordsSlot::declare(b, select_gate.clone());
    let compression =
      Blake3CompressionSlots::declare(b, nu, Blake3Backend::LegacyOptionF)?;
    let zero = b.fixed_public_input(F128::ZERO);
    let iv = pack8(&IV).map(|v| b.fixed_public_input(v));
    let block_indices =
      std::array::from_fn(|i| b.fixed_public_input(F128::new(i as u64, 0)));
    let levels = (0..capacity.depth())
      .map(|i| b.fixed_public_input(F128::new(i as u64, 0)))
      .collect();
    Ok(Self {
      capacity,
      window,
      block,
      path,
      select_gate,
      select,
      compression,
      zero,
      iv,
      block_indices,
      levels,
    })
  }
  pub fn capacity(&self) -> SourceCapacity {
    self.capacity
  }
  pub fn window_gate(&self) -> &(SlotId, SourceWindowGate) {
    &self.window
  }
  pub fn block_gate(&self) -> &(SlotId, SourceBlockGate) {
    &self.block
  }
  pub fn path_gate(&self) -> &(SlotId, SourcePathGate) {
    &self.path
  }
  pub fn select_gate(&self) -> (SlotId, &SelectWordsGate) {
    (self.select.slot(), &self.select_gate)
  }
  pub fn compression(&self) -> &Blake3CompressionSlots {
    &self.compression
  }

  /// `cursor = (offset, file_length)` and narrow `take` are constrained here;
  /// callers must bind them to actual decoder/grammar cursors. `root` must be
  /// the externally expected raw BLAKE3 digest, not arbitrary private advice.
  /// Proofs are in first, next, final chunk order.
  pub fn read(
    &self,
    b: &mut impl CircuitEmitter,
    cursor: Wire,
    take: Wire,
    root: [Wire; 2],
    proofs: &[SourceChunkProofWires; 3],
  ) -> SourceReadWires {
    let [first, next, last] = proofs;
    for proof in [first, next, last] {
      assert_eq!(proof.siblings.len(), self.capacity.depth());
    }
    let mut input = vec![cursor, take];
    input.extend(first.bytes);
    input.extend(next.bytes);
    let out = b.gate(self.window.0, &input);
    b.connect(*out.last().unwrap(), self.zero);
    self.authenticate_chunk(b, out[0], out[1], root, first);
    self.authenticate_chunk(b, out[0], out[2], root, next);
    self.authenticate_chunk(b, out[0], out[3], root, last);
    SourceReadWires {
      file_length: out[0],
      words: out[4..out.len() - 1].to_vec(),
    }
  }

  fn authenticate_chunk(
    &self,
    b: &mut impl CircuitEmitter,
    length: Wire,
    index: Wire,
    root: [Wire; 2],
    proof: &SourceChunkProofWires,
  ) {
    let mut cv = self.iv;
    for block in 0..16 {
      let message: [Wire; 4] =
        proof.bytes[4 * block..4 * block + 4].try_into().unwrap();
      let mut input = vec![length, index, self.block_indices[block]];
      input.extend(message);
      let control = b.gate(self.block.0, &input);
      b.connect(control[2], self.zero);
      let candidate = self.compression.compress(
        b,
        [
          cv[0], cv[1], message[0], message[1], message[2], message[3],
          control[0],
        ],
      );
      cv = self
        .select
        .select(b, control[1], &candidate[..2], &cv)
        .try_into()
        .unwrap();
    }
    for level in 0..self.capacity.depth() {
      let control = b.gate(
        self.path.0,
        &[
          length,
          index,
          self.levels[level],
          cv[0],
          cv[1],
          proof.siblings[level][0],
          proof.siblings[level][1],
        ],
      );
      b.connect(control[6], self.zero);
      let candidate = self.compression.compress(
        b,
        [
          self.iv[0], self.iv[1], control[0], control[1], control[2],
          control[3], control[4],
        ],
      );
      cv = self
        .select
        .select(b, control[5], &candidate[..2], &cv)
        .try_into()
        .unwrap();
    }
    for word in 0..2 {
      b.connect(cv[word], root[word]);
    }
  }
}
