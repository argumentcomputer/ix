use super::super::{
  bodies::{BodyCapacity, FinishedProgramBodies},
  references::CheckedProgramReferences,
  source::*,
};
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

/// Construction is private: these roots hash actual completed code wires.
#[derive(Clone, Debug)]
pub struct SealedCode {
  layout: CodeLayout,
  root: [Wire; 2],
  length: Wire,
  program: Option<CheckedProgramReferences>,
}
impl SealedCode {
  #[cfg(test)]
  pub(super) fn expected(
    layout: CodeLayout,
    root: [Wire; 2],
    length: Wire,
  ) -> Self {
    Self { layout, root, length, program: None }
  }
  pub(in crate::ixby::ixbf_decode) fn program(
    &self,
  ) -> &CheckedProgramReferences {
    self.program.as_ref().expect("actual code seal required for composition")
  }
  pub fn layout(&self) -> CodeLayout {
    self.layout
  }
  pub fn digest(&self) -> [Wire; 2] {
    self.root
  }
}
pub struct CodeCommitSlots {
  layout: CodeLayout,
  hash: BoundedBlake3,
  prefix: [Wire; 6],
  length: Wire,
  zero: Wire,
}
impl CodeCommitSlots {
  pub fn declare(
    b: &mut impl CircuitEmitter,
    c: BodyCapacity,
    shared: &BoundedBlake3,
  ) -> Result<Self> {
    let layout = CodeLayout::from_bodies(c);
    ensure!(
      layout.bytes() <= MAX_HASH_CAPACITY as u64,
      "bounded code sealing size"
    );
    let hash = shared.sharing_primitives(b, layout.bytes() as usize)?;
    let prefix = [
      pack_bytes(&PREFIX),
      F128::new(layout.constructors, 0),
      F128::new(layout.functions, 0),
      F128::new(layout.blocks, 0),
      F128::new(layout.operands, 0),
      F128::new(layout.natural.bits() as u64, 0),
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
  /// The caller must supply the actual raw digest used to authenticate the
  /// original Program reads. It binds String/ByteArray source ranges to their
  /// payload bytes; it must not be independent private advice.
  pub fn seal(
    &self,
    b: &mut impl CircuitEmitter,
    program: &FinishedProgramBodies,
    original_digest: [Wire; 2],
  ) -> SealedCode {
    assert_eq!(CodeLayout::from_bodies(program.capacity()), self.layout);
    let mut words = self.prefix.to_vec();
    words.extend(original_digest);
    words.extend(program.references().registry().grammar().0);
    words.extend(
      &program.references().registry().binding().1
        [..self.layout.constructors as usize * 7],
    );
    words.extend(program.binding());
    assert_eq!(words.len() as u64, self.layout.words());
    words.resize(self.hash.padded_words(), self.zero);
    let root = self.hash.hash(b, self.length, &words);
    SealedCode {
      layout: self.layout,
      root,
      length: self.length,
      program: Some(program.references().clone()),
    }
  }
}
#[derive(Clone, Debug)]
pub struct CodeRequestWires {
  layout: CodeLayout,
  kind: CodeKind,
  enabled: Wire,
  cursor: Wire,
  take: Wire,
  chunks: [Wire; 2],
}
impl CodeRequestWires {
  pub fn chunk_indices(&self) -> [Wire; 2] {
    self.chunks
  }
}
#[derive(Clone, Debug)]
pub struct AuthenticatedCodeChunk {
  layout: CodeLayout,
  root: [Wire; 2],
  index: Wire,
  bytes: [Wire; 64],
}
#[derive(Clone, Debug)]
pub struct CodeReadWires {
  pub kind: CodeKind,
  pub fields: Vec<Wire>,
}
pub struct CodeAccessSlots {
  layout: CodeLayout,
  source: SourceReadSlots,
  requests: [SlotId; 6],
  records: [SlotId; 6],
  zero: Wire,
}
impl CodeAccessSlots {
  pub fn declare(
    b: &mut impl CircuitEmitter,
    nu: usize,
    layout: CodeLayout,
    compression: &Blake3CompressionSlots,
  ) -> Result<Self> {
    let source = SourceReadSlots::sharing_compression(
      b,
      nu,
      SourceCapacity::new(layout.depth(), 16 * layout.window_words())?,
      compression,
    )?;
    let mut declare = |op| -> Result<[SlotId; 6]> {
      CodeKind::ALL
        .into_iter()
        .map(|kind| Ok(b.slot(CodeGate::new(nu, layout, kind, op)?)))
        .collect::<Result<Vec<_>>>()
        .map(|v| v.try_into().unwrap())
    };
    let requests = declare(CodeOp::Request)?;
    let records = declare(CodeOp::Record)?;
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
  pub fn slot(&self, kind: CodeKind, op: CodeOp) -> SlotId {
    match op {
      CodeOp::Request => self.requests[kind as usize],
      CodeOp::Record => self.records[kind as usize],
    }
  }
  pub fn request(
    &self,
    b: &mut impl CircuitEmitter,
    kind: CodeKind,
    query: [Wire; 4],
  ) -> CodeRequestWires {
    let out = b.gate(self.slot(kind, CodeOp::Request), &query);
    b.connect(out[4], self.zero);
    CodeRequestWires {
      layout: self.layout,
      kind,
      enabled: query[0],
      cursor: out[0],
      take: out[1],
      chunks: [out[2], out[3]],
    }
  }
  /// Authenticate once, then reuse this handle in any read whose constrained
  /// chunk index matches. Each handle retains the actual file-root wires.
  pub fn authenticate(
    &self,
    b: &mut impl CircuitEmitter,
    code: &SealedCode,
    index: Wire,
    proof: &SourceChunkProofWires,
  ) -> AuthenticatedCodeChunk {
    assert_eq!(code.layout, self.layout);
    assert_eq!(proof.siblings.len(), self.layout.depth());
    self.source.authenticate_chunk(b, code.length, index, code.root, proof);
    AuthenticatedCodeChunk {
      layout: self.layout,
      root: code.root,
      index,
      bytes: proof.bytes,
    }
  }
  pub fn read(
    &self,
    b: &mut impl CircuitEmitter,
    code: &SealedCode,
    request: &CodeRequestWires,
    chunks: [&AuthenticatedCodeChunk; 2],
  ) -> CodeReadWires {
    assert_eq!(code.layout, self.layout);
    assert_eq!(request.layout, self.layout);
    for (i, chunk) in chunks.iter().enumerate() {
      assert_eq!(chunk.layout, self.layout);
      for word in 0..2 {
        b.connect(chunk.root[word], code.root[word]);
      }
      b.connect(chunk.index, request.chunks[i]);
    }
    let mut input = vec![request.cursor, request.take];
    input.extend(chunks[0].bytes);
    input.extend(chunks[1].bytes);
    let out = b.gate(self.source.window_gate().0, &input);
    b.connect(*out.last().unwrap(), self.zero);
    b.connect(out[0], code.length);
    b.connect(out[1], request.chunks[0]);
    b.connect(out[2], request.chunks[1]);
    let mut input = vec![request.enabled];
    input.extend(&out[4..out.len() - 1]);
    let mut fields = b.gate(self.slot(request.kind, CodeOp::Record), &input);
    b.connect(fields.pop().unwrap(), self.zero);
    CodeReadWires { kind: request.kind, fields }
  }
}
