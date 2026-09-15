use super::super::super::{code::SealedCode, source::*};
use super::super::{FinishedValueArena, ValueConfig};
use super::{layout::*, *};
use crate::{
  blake3_backend::Blake3CompressionSlots,
  hash::pack_bytes,
  ixby::{bounded_hash::BoundedBlake3, hash_control::MAX_HASH_CAPACITY},
  sizing::CircuitEmitter,
};
use anyhow::{Result, ensure};
use flock_prover::{
  circuit::builder::{SlotId, Wire},
  field::F128,
};

/// Only a source-connected completed arena can construct a production seal.
#[derive(Clone, Debug)]
pub struct SealedValues {
  layout: ValueLayout,
  root: [Wire; 2],
  length: Wire,
}
impl SealedValues {
  #[cfg(test)]
  pub(super) fn expected(
    layout: ValueLayout,
    root: [Wire; 2],
    length: Wire,
  ) -> Self {
    Self { layout, root, length }
  }
  pub fn layout(&self) -> ValueLayout {
    self.layout
  }
  pub fn digest(&self) -> [Wire; 2] {
    self.root
  }
}
pub struct ValueCommitSlots {
  layout: ValueLayout,
  hash: BoundedBlake3,
  prefix: [Wire; PREFIX_WORDS],
  length: Wire,
  zero: Wire,
}
impl ValueCommitSlots {
  pub fn declare(
    b: &mut impl CircuitEmitter,
    config: ValueConfig,
    shared: &BoundedBlake3,
  ) -> Result<Self> {
    config.validate()?;
    let layout = ValueLayout::from_arena(config);
    ensure!(
      layout.bytes() <= MAX_HASH_CAPACITY as u64,
      "bounded value sealing size"
    );
    let hash = shared.sharing_primitives(b, layout.bytes() as usize)?;
    let prefix = [
      pack_bytes(&PREFIX),
      F128::new(layout.kind() as u64, 0),
      F128::new(layout.nodes(), 0),
      F128::new(layout.max_depth(), 0),
      F128::new(layout.natural().bits() as u64, 0),
    ]
    .map(|v| b.fixed_public_input(v));
    Ok(Self {
      layout,
      hash,
      prefix,
      length: b.fixed_public_input(F128::new(layout.bytes(), 0)),
      zero: b.fixed_public_input(F128::ZERO),
    })
  }
  pub fn hash(&self) -> &BoundedBlake3 {
    &self.hash
  }
  /// `original_digest` must be the actual root used to authenticate this
  /// arena's transport reads. This binds String/ByteArray ranges to their
  /// original payloads. The code's complete actual registry is connected to
  /// the registry that initialized and resolved references in this arena.
  pub fn seal(
    &self,
    b: &mut impl CircuitEmitter,
    arena: &FinishedValueArena,
    code: &SealedCode,
    original_digest: [Wire; 2],
  ) -> SealedValues {
    assert_eq!(ValueLayout::from_arena(arena.config()), self.layout);
    let arena_program = arena.program().registry();
    let code_program = code.program().registry();
    let (capacity, bank) = arena_program.binding();
    let (code_capacity, code_bank) = code_program.binding();
    assert_eq!(capacity, code_capacity);
    assert_eq!(bank.len(), code_bank.len());
    for (a, c) in
      arena_program.grammar().0.into_iter().zip(code_program.grammar().0)
    {
      b.connect(a, c);
    }
    for (&a, &c) in bank.iter().zip(code_bank) {
      b.connect(a, c);
    }
    let mut words = self.prefix.to_vec();
    words.extend(code.digest());
    words.extend(original_digest);
    words.extend(arena.grammar().0);
    words.extend(arena.summary());
    words.extend(arena.binding());
    assert_eq!(words.len() as u64, self.layout.words());
    words.resize(self.hash.padded_words(), self.zero);
    let root = self.hash.hash(b, self.length, &words);
    SealedValues { layout: self.layout, root, length: self.length }
  }
}
#[derive(Clone, Debug)]
pub struct ValueRequestWires {
  layout: ValueLayout,
  kind: ValueKind,
  query: [Wire; 4],
  cursor: Wire,
  take: Wire,
  chunks: [Wire; 2],
}
impl ValueRequestWires {
  pub fn chunk_indices(&self) -> [Wire; 2] {
    self.chunks
  }
}
#[derive(Clone, Debug)]
pub struct AuthenticatedValueChunk {
  layout: ValueLayout,
  root: [Wire; 2],
  index: Wire,
  bytes: [Wire; 64],
}
#[derive(Clone, Debug)]
pub struct ValueAccessReadWires {
  pub kind: ValueKind,
  /// Physical node index; zero for a Manifest or a disabled read.
  pub index: Wire,
  /// Manifest fields, or the complete source-derived node and tree metadata.
  pub record: Vec<Wire>,
}
pub struct ValueAccessSlots {
  layout: ValueLayout,
  source: SourceReadSlots,
  requests: [SlotId; 4],
  records: [SlotId; 4],
  zero: Wire,
}
impl ValueAccessSlots {
  pub fn declare(
    b: &mut impl CircuitEmitter,
    nu: usize,
    layout: ValueLayout,
    compression: &Blake3CompressionSlots,
  ) -> Result<Self> {
    let source = SourceReadSlots::sharing_compression(
      b,
      nu,
      SourceCapacity::new(layout.depth(), 16 * layout.window_words())?,
      compression,
    )?;
    let mut declare = |op| -> Result<[SlotId; 4]> {
      ValueKind::ALL
        .into_iter()
        .map(|kind| Ok(b.slot(ValueAccessGate::new(nu, layout, kind, op)?)))
        .collect::<Result<Vec<_>>>()
        .map(|v| v.try_into().unwrap())
    };
    let requests = declare(ValueAccessOp::Request)?;
    let records = declare(ValueAccessOp::Record)?;
    Ok(Self {
      layout,
      source,
      requests,
      records,
      zero: b.fixed_public_input(F128::ZERO),
    })
  }
  pub fn source_slots(&self) -> &SourceReadSlots {
    &self.source
  }
  pub fn slot(&self, kind: ValueKind, op: ValueAccessOp) -> SlotId {
    match op {
      ValueAccessOp::Request => self.requests[kind as usize],
      ValueAccessOp::Record => self.records[kind as usize],
    }
  }
  /// Query = (enabled, node/parent, ordinal, locator).
  /// Node uses only node/parent. Child uses all fields. Root uses ordinal and
  /// locator. Manifest uses none. Unused/disabled words must be zero.
  /// A locator is untrusted physical-node advice, authenticated and checked
  /// against the requested parent/root and ordinal by `read`.
  pub fn request(
    &self,
    b: &mut impl CircuitEmitter,
    kind: ValueKind,
    query: [Wire; 4],
  ) -> ValueRequestWires {
    let out = b.gate(self.slot(kind, ValueAccessOp::Request), &query);
    b.connect(out[4], self.zero);
    ValueRequestWires {
      layout: self.layout,
      kind,
      query,
      cursor: out[0],
      take: out[1],
      chunks: [out[2], out[3]],
    }
  }
  pub fn authenticate(
    &self,
    b: &mut impl CircuitEmitter,
    values: &SealedValues,
    index: Wire,
    proof: &SourceChunkProofWires,
  ) -> AuthenticatedValueChunk {
    assert_eq!(values.layout, self.layout);
    assert_eq!(proof.siblings.len(), self.layout.depth());
    self.source.authenticate_chunk(b, values.length, index, values.root, proof);
    AuthenticatedValueChunk {
      layout: self.layout,
      root: values.root,
      index,
      bytes: proof.bytes,
    }
  }
  pub fn read(
    &self,
    b: &mut impl CircuitEmitter,
    values: &SealedValues,
    request: &ValueRequestWires,
    chunks: [&AuthenticatedValueChunk; 2],
  ) -> ValueAccessReadWires {
    assert_eq!(values.layout, self.layout);
    assert_eq!(request.layout, self.layout);
    for (i, chunk) in chunks.iter().enumerate() {
      assert_eq!(chunk.layout, self.layout);
      for word in 0..2 {
        b.connect(chunk.root[word], values.root[word]);
      }
      b.connect(chunk.index, request.chunks[i]);
    }
    let mut input = vec![request.cursor, request.take];
    input.extend(chunks[0].bytes);
    input.extend(chunks[1].bytes);
    let out = b.gate(self.source.window_gate().0, &input);
    b.connect(*out.last().unwrap(), self.zero);
    b.connect(out[0], values.length);
    b.connect(out[1], request.chunks[0]);
    b.connect(out[2], request.chunks[1]);
    let mut input = request.query.to_vec();
    input.extend(&out[4..out.len() - 1]);
    let mut fields =
      b.gate(self.slot(request.kind, ValueAccessOp::Record), &input);
    b.connect(fields.pop().unwrap(), self.zero);
    ValueAccessReadWires {
      kind: request.kind,
      index: fields[0],
      record: fields[1..].to_vec(),
    }
  }
}
