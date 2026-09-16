//! Untrusted sparse-tree advice generation; never used by a verifier.
use super::{CELL_DOMAIN, MemoryDepth};
use crate::hash::pack_bytes;
use anyhow::{Result, ensure};
use blake3::hazmat::{Mode, merge_subtrees_root};
use flock_prover::field::F128;
use std::collections::{BTreeSet, HashMap, HashSet};

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
#[derive(Clone, Debug)]
pub struct LeafUpdate {
  pub address: u64,
  pub old: [F128; 2],
  pub new: [F128; 2],
  pub old_hash: [F128; 2],
  pub new_hash: [F128; 2],
}
#[derive(Clone, Debug)]
pub struct ParentUpdate {
  pub level: usize,
  pub index: u64,
  pub old_children: [[F128; 2]; 2],
  pub new_children: [[F128; 2]; 2],
  pub old_hash: [F128; 2],
  pub new_hash: [F128; 2],
}
#[derive(Clone, Debug)]
pub struct FrontierNode {
  pub level: usize,
  pub index: u64,
  pub hash: [F128; 2],
}
/// Untrusted advice for one shared tree of simultaneous cell replacements.
#[derive(Clone, Debug)]
pub struct MultiUpdate {
  pub depth: MemoryDepth,
  pub initial_root: [F128; 2],
  pub final_root: [F128; 2],
  pub leaves: Vec<LeafUpdate>,
  pub parents: Vec<ParentUpdate>,
  pub frontier: Vec<FrontierNode>,
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
  pub fn depth(&self) -> MemoryDepth {
    self.depth
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
  /// Untrusted simultaneous-update advice. Every distinct internal node is
  /// recomputed once, and unchanged sibling subtrees form a shared frontier.
  /// Validate all addresses before making any change to the native memory.
  pub fn replace_many(
    &mut self,
    updates: impl IntoIterator<Item = (u64, [F128; 2])>,
  ) -> Result<MultiUpdate> {
    let updates = updates.into_iter().collect::<Vec<_>>();
    let mut addresses = HashSet::new();
    let mut internal = BTreeSet::new();
    for &(address, _) in &updates {
      ensure!(self.depth.admits(address), "memory address out of range");
      ensure!(addresses.insert(address), "duplicate memory update address");
      for level in 1..=self.depth.bits() {
        internal
          .insert((level, address.checked_shr(level as u32).unwrap_or(0)));
      }
    }
    let initial_root = self.root();
    let mut frontier = Vec::new();
    let mut parents = Vec::with_capacity(internal.len());
    for &(level, index) in &internal {
      let children = [index * 2, index * 2 + 1];
      let old_children =
        children.map(|child| words(self.node(level - 1, child)));
      for (&child, &hash) in children.iter().zip(&old_children) {
        let covered = if level == 1 {
          addresses.contains(&child)
        } else {
          internal.contains(&(level - 1, child))
        };
        if !covered {
          frontier.push(FrontierNode { level: level - 1, index: child, hash });
        }
      }
      parents.push(ParentUpdate {
        level,
        index,
        old_children,
        new_children: [[F128::ZERO; 2]; 2],
        old_hash: words(self.node(level, index)),
        new_hash: [F128::ZERO; 2],
      });
    }
    if updates.is_empty() {
      frontier.push(FrontierNode {
        level: self.depth.bits(),
        index: 0,
        hash: initial_root,
      });
    }
    let mut leaves = Vec::with_capacity(updates.len());
    for (address, new) in updates {
      let old = self.cells.get(&address).copied().unwrap_or([F128::ZERO; 2]);
      let old_hash = words(self.node(0, address));
      if new == [F128::ZERO; 2] {
        self.cells.remove(&address);
      } else {
        self.cells.insert(address, new);
      }
      let hash = leaf(new);
      if hash == self.empty[0] {
        self.nodes.remove(&(0, address));
      } else {
        self.nodes.insert((0, address), hash);
      }
      leaves.push(LeafUpdate {
        address,
        old,
        new,
        old_hash,
        new_hash: words(hash),
      });
    }
    for node in &mut parents {
      let left = self.node(node.level - 1, node.index * 2);
      let right = self.node(node.level - 1, node.index * 2 + 1);
      node.new_children = [words(left), words(right)];
      let hash = parent(&left, &right);
      if hash == self.empty[node.level] {
        self.nodes.remove(&(node.level, node.index));
      } else {
        self.nodes.insert((node.level, node.index), hash);
      }
      node.new_hash = words(hash);
    }
    Ok(MultiUpdate {
      depth: self.depth,
      initial_root,
      final_root: self.root(),
      leaves,
      parents,
      frontier,
    })
  }
}
