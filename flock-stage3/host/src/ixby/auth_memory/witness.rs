//! Untrusted sparse-tree advice generation; never used by a verifier.
use super::{CELL_DOMAIN, MemoryDepth};
use crate::hash::pack_bytes;
use anyhow::{Result, ensure};
use blake3::hazmat::{Mode, merge_subtrees_root};
use flock_prover::field::F128;
use std::collections::{HashMap, HashSet};

fn bytes(value: [F128; 2]) -> [u8; 32] {
  let mut out = [0; 32];
  for (i, word) in value.iter().enumerate() {
    out[16 * i..16 * i + 8].copy_from_slice(&word.lo.to_le_bytes());
    out[16 * i + 8..16 * i + 16].copy_from_slice(&word.hi.to_le_bytes());
  }
  out
}
fn words(value: [u8; 32]) -> [F128; 2] {
  [pack_bytes(&value[..16]), pack_bytes(&value[16..])]
}
fn leaf(value: [F128; 2]) -> [u8; 32] {
  let mut message = [0; 64];
  message[..32].copy_from_slice(&CELL_DOMAIN);
  message[32..].copy_from_slice(&bytes(value));
  *blake3::hash(&message).as_bytes()
}
fn parent(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
  *merge_subtrees_root(left, right, Mode::Hash).as_bytes()
}

#[derive(Clone, Debug)]
pub struct MemoryOpening {
  pub address: u64,
  pub value: [F128; 2],
  pub siblings: Vec<[F128; 2]>,
}
impl MemoryOpening {
  pub fn words(&self) -> Vec<F128> {
    let mut result = vec![F128::new(self.address, 0)];
    result.extend(self.value);
    result.extend(self.siblings.iter().flatten());
    result
  }
}
pub struct SparseMemory {
  depth: MemoryDepth,
  empty: Vec<[u8; 32]>,
  cells: HashMap<u64, [F128; 2]>,
  nodes: HashMap<(usize, u64), [u8; 32]>,
}
impl SparseMemory {
  pub fn new(depth: MemoryDepth) -> Self {
    let mut empty = vec![leaf([F128::ZERO; 2])];
    for level in 0..depth.bits() {
      empty.push(parent(&empty[level], &empty[level]));
    }
    Self { depth, empty, cells: HashMap::new(), nodes: HashMap::new() }
  }
  /// Construct untrusted initial-tree advice in linear work per populated
  /// level. The resulting root and openings are identical to repeated writes.
  /// Duplicate addresses, including explicit zero cells, are rejected.
  pub fn from_cells(
    depth: MemoryDepth,
    cells: impl IntoIterator<Item = (u64, [F128; 2])>,
  ) -> Result<Self> {
    let mut memory = Self::new(depth);
    let mut seen = HashSet::new();
    let mut frontier = Vec::new();
    for (address, value) in cells {
      ensure!(depth.admits(address), "memory address out of range");
      ensure!(seen.insert(address), "duplicate initial memory address");
      if value != [F128::ZERO; 2] {
        memory.cells.insert(address, value);
        let digest = leaf(value);
        if digest != memory.empty[0] {
          memory.nodes.insert((0, address), digest);
          frontier.push(address);
        }
      }
    }
    for level in 1..=depth.bits() {
      let parents = frontier.iter().map(|i| i >> 1).collect::<HashSet<_>>();
      frontier.clear();
      for index in parents {
        let digest = parent(
          &memory.node(level - 1, index * 2),
          &memory.node(level - 1, index * 2 + 1),
        );
        if digest != memory.empty[level] {
          memory.nodes.insert((level, index), digest);
          frontier.push(index);
        }
      }
    }
    Ok(memory)
  }
  pub fn root(&self) -> [F128; 2] {
    words(self.node(self.depth.bits(), 0))
  }
  pub fn empty_root(&self) -> [F128; 2] {
    words(self.empty[self.depth.bits()])
  }
  /// Untrusted native advice without constructing an authentication path.
  pub fn value(&self, address: u64) -> Result<[F128; 2]> {
    ensure!(self.depth.admits(address), "memory address out of range");
    Ok(self.cells.get(&address).copied().unwrap_or([F128::ZERO; 2]))
  }
  fn node(&self, level: usize, index: u64) -> [u8; 32] {
    self.nodes.get(&(level, index)).copied().unwrap_or(self.empty[level])
  }
  pub fn open(&self, address: u64) -> Result<MemoryOpening> {
    ensure!(self.depth.admits(address), "memory address out of range");
    Ok(MemoryOpening {
      address,
      value: self.cells.get(&address).copied().unwrap_or([F128::ZERO; 2]),
      siblings: (0..self.depth.bits())
        .map(|level| words(self.node(level, (address >> level) ^ 1)))
        .collect(),
    })
  }
  pub fn replace(
    &mut self,
    address: u64,
    value: [F128; 2],
  ) -> Result<MemoryOpening> {
    let old = self.open(address)?;
    if value == [F128::ZERO; 2] {
      self.cells.remove(&address);
    } else {
      self.cells.insert(address, value);
    }
    let mut current = leaf(value);
    let mut index = address;
    for level in 0..=self.depth.bits() {
      if current == self.empty[level] {
        self.nodes.remove(&(level, index));
      } else {
        self.nodes.insert((level, index), current);
      }
      if level < self.depth.bits() {
        let sibling = self.node(level, index ^ 1);
        current = if index & 1 == 0 {
          parent(&current, &sibling)
        } else {
          parent(&sibling, &current)
        };
        index >>= 1;
      }
    }
    Ok(old)
  }
}
