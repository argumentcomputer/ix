//! Fixed-depth authenticated mutable memory for execution segments.
//!
//! A cell is two field words (32 bytes). The approved setup selects depth;
//! every access constrains the complete address and all sibling directions.
//! Replacement authenticates the old cell and derives the new root using
//! the same path. Execution must wire its actual address, value and carried
//! root; this component alone does not establish instruction semantics.

mod arena;
mod gate;
pub mod multi;
#[cfg(test)]
mod proof_tests;
#[cfg(test)]
mod tests;
mod witness;

pub use arena::{ArenaStateWires, ImmutableArenaSlots};
pub use gate::{MemoryGate, MemoryGateKind, MemoryRow};
pub use witness::{
  FrontierNode, LeafUpdate, MemoryOpening, MultiUpdate, ParentUpdate,
  SparseMemory,
};

use crate::{
  blake3_backend::{Blake3Backend, Blake3CompressionSlots},
  hash::{
    CHUNK_END, CHUNK_START, IV, PARENT, ROOT, pack_bytes, pack_params, pack8,
  },
  sizing::CircuitEmitter,
};
use anyhow::{Result, ensure};
use flock_prover::{
  circuit::builder::{SlotId, Wire},
  field::F128,
};

const CELL_DOMAIN: [u8; 32] = *b"IxBy/memory/cell/v0\0\0\0\0\0\0\0\0\0\0\0\0\0";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MemoryDepth(usize);
impl MemoryDepth {
  pub fn new(depth: usize) -> Result<Self> {
    ensure!(depth <= 64, "memory address depth exceeds u64");
    Ok(Self(depth))
  }
  pub fn bits(self) -> usize {
    self.0
  }
  pub fn admits(self, address: u64) -> bool {
    self.0 == 64 || address < (1u64 << self.0)
  }
}

/// Prover-supplied opening. The requested address and expected root are
/// separate caller wires, so an opening cannot select its own memory access.
#[derive(Clone)]
pub struct MemoryOpeningWires {
  pub value: [Wire; 2],
  pub siblings: Vec<[Wire; 2]>,
}

#[derive(Clone)]
pub struct MemoryAccessSlots {
  depth: MemoryDepth,
  address: (SlotId, MemoryGate),
  path: (SlotId, MemoryGate),
  compression: Blake3CompressionSlots,
  zero: Wire,
  iv: [Wire; 2],
  domain: [Wire; 2],
  leaf_params: Wire,
  parent_params: Wire,
  levels: Vec<Wire>,
}
impl MemoryAccessSlots {
  pub fn declare(
    b: &mut impl CircuitEmitter,
    nu: usize,
    depth: MemoryDepth,
  ) -> Result<Self> {
    Self::declare_inner(b, nu, depth, None)
  }
  /// Sharing is valid only within the same emitter and row domain.
  pub fn sharing_compression(
    b: &mut impl CircuitEmitter,
    nu: usize,
    depth: MemoryDepth,
    compression: &Blake3CompressionSlots,
  ) -> Result<Self> {
    Self::declare_inner(b, nu, depth, Some(compression.clone()))
  }
  fn declare_inner(
    b: &mut impl CircuitEmitter,
    nu: usize,
    depth: MemoryDepth,
    shared: Option<Blake3CompressionSlots>,
  ) -> Result<Self> {
    let address_gate = MemoryGate::new(nu, depth, MemoryGateKind::Address)?;
    let path_gate = MemoryGate::new(nu, depth, MemoryGateKind::Path)?;
    let address = (b.slot(address_gate.clone()), address_gate);
    let path = (b.slot(path_gate.clone()), path_gate);
    let compression = match shared {
      Some(compression) => compression,
      None => {
        Blake3CompressionSlots::declare(b, nu, Blake3Backend::LegacyOptionF)?
      },
    };
    Ok(Self {
      depth,
      address,
      path,
      compression,
      zero: b.fixed_public_input(F128::ZERO),
      iv: pack8(&IV).map(|v| b.fixed_public_input(v)),
      domain: [pack_bytes(&CELL_DOMAIN[..16]), pack_bytes(&CELL_DOMAIN[16..])]
        .map(|v| b.fixed_public_input(v)),
      leaf_params: b.fixed_public_input(pack_params(
        0,
        64,
        CHUNK_START | CHUNK_END | ROOT,
      )),
      parent_params: b.fixed_public_input(pack_params(0, 64, PARENT | ROOT)),
      levels: (0..depth.bits())
        .map(|i| b.fixed_public_input(F128::new(i as u64, 0)))
        .collect(),
    })
  }
  pub fn depth(&self) -> MemoryDepth {
    self.depth
  }
  pub fn gates(&self) -> [(SlotId, &MemoryGate); 2] {
    [(self.address.0, &self.address.1), (self.path.0, &self.path.1)]
  }
  pub fn compression(&self) -> &Blake3CompressionSlots {
    &self.compression
  }
  fn root(
    &self,
    b: &mut impl CircuitEmitter,
    address: Wire,
    value: [Wire; 2],
    siblings: &[[Wire; 2]],
  ) -> [Wire; 2] {
    assert_eq!(siblings.len(), self.depth.bits(), "memory path shape");
    let residual = b.gate(self.address.0, &[address]);
    b.connect(residual[0], self.zero);
    let leaf = self.compression.compress(
      b,
      [
        self.iv[0],
        self.iv[1],
        self.domain[0],
        self.domain[1],
        value[0],
        value[1],
        self.leaf_params,
      ],
    );
    let mut current = [leaf[0], leaf[1]];
    for (&level, sibling) in self.levels.iter().zip(siblings) {
      let ordered = b.gate(
        self.path.0,
        &[address, level, current[0], current[1], sibling[0], sibling[1]],
      );
      b.connect(ordered[4], self.zero);
      let next = self.compression.compress(
        b,
        [
          self.iv[0],
          self.iv[1],
          ordered[0],
          ordered[1],
          ordered[2],
          ordered[3],
          self.parent_params,
        ],
      );
      current = [next[0], next[1]];
    }
    current
  }
  pub fn read(
    &self,
    b: &mut impl CircuitEmitter,
    expected_root: [Wire; 2],
    address: Wire,
    opening: &MemoryOpeningWires,
  ) -> [Wire; 2] {
    let actual = self.root(b, address, opening.value, &opening.siblings);
    for (actual, expected) in actual.into_iter().zip(expected_root) {
      b.connect(actual, expected);
    }
    opening.value
  }
  /// Authenticate the old value against the carried root before deriving
  /// the replacement root. Both paths share the actual address and siblings.
  pub fn replace(
    &self,
    b: &mut impl CircuitEmitter,
    expected_root: [Wire; 2],
    address: Wire,
    opening: &MemoryOpeningWires,
    value: [Wire; 2],
  ) -> [Wire; 2] {
    self.read(b, expected_root, address, opening);
    self.root(b, address, value, &opening.siblings)
  }
}
