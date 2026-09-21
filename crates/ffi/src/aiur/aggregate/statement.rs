//! Aggregation statement.

use ix_common::address::Address;
use ixon::{
  Claim,
  assumption_tree::AssumptionTree,
  merkle::{
    MerklePath, leaf_hash, merkle_root_canonical_sorted, node_hash,
    zero_address,
  },
};
use rustc_hash::FxHashMap;
use std::{
  cmp::Ordering,
  sync::{Arc, OnceLock},
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct ShardSet(pub(super) Vec<u64>);

impl ShardSet {
  pub(super) fn singleton(index: usize, shard_count: usize) -> Self {
    let mut words = vec![0; shard_count.div_ceil(64)];
    words[index / 64] |= 1u64 << (index % 64);
    Self(words)
  }

  pub(super) fn union(&self, other: &Self) -> Self {
    debug_assert_eq!(self.0.len(), other.0.len());
    Self(self.0.iter().zip(&other.0).map(|(a, b)| a | b).collect())
  }

  pub(super) fn contains(&self, index: usize) -> bool {
    self
      .0
      .get(index / 64)
      .is_some_and(|word| word & (1u64 << (index % 64)) != 0)
  }
}

/// Canonical sorted tree whose expensive derivative representations are built
/// once, on demand. The root is computed once at construction.
#[derive(Debug)]
pub(super) struct CanonicalTree {
  pub(super) leaves: Arc<[Address]>,
  pub(super) root: Address,
  pub(super) serialized: OnceLock<Vec<u8>>,
  pub(super) levels: OnceLock<Vec<Vec<Address>>>,
}

impl CanonicalTree {
  pub(super) fn from_sorted(
    leaves: Vec<Address>,
  ) -> Result<Option<Arc<Self>>, String> {
    if leaves.is_empty() {
      return Ok(None);
    }
    if !leaves.windows(2).all(|w| w[0] < w[1]) {
      return Err("canonical tree leaves are not strictly sorted".into());
    }
    let root = merkle_root_canonical_sorted(&leaves)
      .ok_or("nonempty canonical tree did not produce a root")?;
    Ok(Some(Arc::new(Self {
      leaves: leaves.into(),
      root,
      serialized: OnceLock::new(),
      levels: OnceLock::new(),
    })))
  }

  pub(super) fn serialized(&self) -> &[u8] {
    self.serialized.get_or_init(|| {
      let tree = AssumptionTree::canonical(&self.leaves)
        .expect("a nonempty canonical leaf list has a tree");
      debug_assert_eq!(tree.root(), self.root);
      tree.ser()
    })
  }

  pub(super) fn levels(&self) -> &[Vec<Address>] {
    self.levels.get_or_init(|| {
      let mut levels: Vec<Vec<Address>> =
        vec![self.leaves.iter().map(leaf_hash).collect()];
      let zero = zero_address();
      while levels.last().is_some_and(|level| level.len() > 1) {
        let previous = levels.last().expect("one level exists");
        let mut next = Vec::with_capacity(previous.len().div_ceil(2));
        for pair in previous.chunks(2) {
          next.push(node_hash(&pair[0], pair.get(1).unwrap_or(&zero)));
        }
        levels.push(next);
      }
      levels
    })
  }

  pub(super) fn merkle_proof(&self, target: &Address) -> Option<MerklePath> {
    let mut position = self.leaves.binary_search(target).ok()?;
    let levels = self.levels();
    let zero = zero_address();
    let mut path = Vec::with_capacity(levels.len().saturating_sub(1));
    for level in levels.iter().take(levels.len().saturating_sub(1)) {
      let sibling =
        level.get(position ^ 1).cloned().unwrap_or_else(|| zero.clone());
      path.push((sibling, position & 1 == 1));
      position /= 2;
    }
    Some(path)
  }
}

#[derive(Debug)]
pub(super) enum SubjectRepr {
  Canonical(Arc<CanonicalTree>),
  Structural { left: Arc<SubjectTree>, right: Arc<SubjectTree> },
}

#[derive(Debug)]
pub(super) struct SubjectTree {
  pub(super) root: Address,
  pub(super) count: usize,
  pub(super) shards: ShardSet,
  pub(super) repr: SubjectRepr,
}

impl SubjectTree {
  pub(super) fn canonical(
    leaves: Vec<Address>,
    shards: ShardSet,
  ) -> Result<Arc<Self>, String> {
    let count = leaves.len();
    let canonical = CanonicalTree::from_sorted(leaves)?
      .ok_or("a shard cannot have an empty subject tree")?;
    Ok(Arc::new(Self {
      root: canonical.root.clone(),
      count,
      shards,
      repr: SubjectRepr::Canonical(canonical),
    }))
  }

  pub(super) fn flat(
    left: &Arc<Self>,
    right: &Arc<Self>,
  ) -> Result<Arc<Self>, String> {
    let SubjectRepr::Canonical(left_tree) = &left.repr else {
      return Err("flat aggregate has a structural left child".into());
    };
    let SubjectRepr::Canonical(right_tree) = &right.repr else {
      return Err("flat aggregate has a structural right child".into());
    };
    let leaves = merge_sorted(&left_tree.leaves, &right_tree.leaves);
    if leaves.len() != left.count.saturating_add(right.count) {
      return Err("aggregate subject sets overlap".into());
    }
    Self::canonical(leaves, left.shards.union(&right.shards))
  }

  pub(super) fn structural(left: Arc<Self>, right: Arc<Self>) -> Arc<Self> {
    Arc::new(Self {
      root: node_hash(&left.root, &right.root),
      count: left.count.saturating_add(right.count),
      shards: left.shards.union(&right.shards),
      repr: SubjectRepr::Structural { left, right },
    })
  }

  pub(super) fn canonical_tree(&self) -> Option<&CanonicalTree> {
    match &self.repr {
      SubjectRepr::Canonical(tree) => Some(tree),
      SubjectRepr::Structural { .. } => None,
    }
  }

  pub(super) fn merkle_proof(
    &self,
    target: &Address,
    owner: usize,
  ) -> Option<MerklePath> {
    if !self.shards.contains(owner) {
      return None;
    }
    match &self.repr {
      SubjectRepr::Canonical(tree) => tree.merkle_proof(target),
      SubjectRepr::Structural { left, right } => {
        if left.shards.contains(owner) {
          let mut path = left.merkle_proof(target, owner)?;
          path.push((right.root.clone(), false));
          Some(path)
        } else {
          let mut path = right.merkle_proof(target, owner)?;
          path.push((left.root.clone(), true));
          Some(path)
        }
      },
    }
  }

  pub(super) fn collect_leaves(&self, out: &mut Vec<Address>) {
    match &self.repr {
      SubjectRepr::Canonical(tree) => out.extend_from_slice(&tree.leaves),
      SubjectRepr::Structural { left, right } => {
        left.collect_leaves(out);
        right.collect_leaves(out);
      },
    }
  }
}

#[derive(Debug)]
pub(super) struct Statement {
  pub(super) subjects: Arc<SubjectTree>,
  pub(super) assumptions: Option<Arc<CanonicalTree>>,
  pub(super) claim: Claim,
  pub(super) claim_bytes: Vec<u8>,
}

impl Statement {
  pub(super) fn new(
    subjects: Arc<SubjectTree>,
    assumptions: Option<Arc<CanonicalTree>>,
  ) -> Arc<Self> {
    let claim = Claim::CheckEnv {
      root: subjects.root.clone(),
      assumptions: assumptions.as_ref().map(|tree| tree.root.clone()),
    };
    let mut claim_bytes = Vec::new();
    claim.put(&mut claim_bytes);
    Arc::new(Self { subjects, assumptions, claim, claim_bytes })
  }

  pub(super) fn join(
    left: &Arc<Self>,
    right: &Arc<Self>,
    structural: bool,
    owner_by_address: &FxHashMap<Address, usize>,
  ) -> Result<Arc<Self>, String> {
    let subjects = if structural {
      SubjectTree::structural(left.subjects.clone(), right.subjects.clone())
    } else {
      SubjectTree::flat(&left.subjects, &right.subjects)?
    };
    let candidates = merge_optional_sets(
      left.assumptions.as_deref(),
      right.assumptions.as_deref(),
    );
    let mut remaining = Vec::with_capacity(candidates.len());
    for candidate in candidates {
      let owner = owner_by_address.get(&candidate).ok_or_else(|| {
        format!("aggregate assumption {} has no owning shard", candidate.hex())
      })?;
      if !subjects.shards.contains(*owner) {
        remaining.push(candidate);
      }
    }
    let assumptions = CanonicalTree::from_sorted(remaining)?;
    Ok(Self::new(subjects, assumptions))
  }
}

pub(super) fn merge_sorted(
  left: &[Address],
  right: &[Address],
) -> Vec<Address> {
  let mut out = Vec::with_capacity(left.len().saturating_add(right.len()));
  let (mut i, mut j) = (0, 0);
  while i < left.len() && j < right.len() {
    match left[i].cmp(&right[j]) {
      Ordering::Less => {
        out.push(left[i].clone());
        i += 1;
      },
      Ordering::Greater => {
        out.push(right[j].clone());
        j += 1;
      },
      Ordering::Equal => {
        out.push(left[i].clone());
        i += 1;
        j += 1;
      },
    }
  }
  out.extend_from_slice(&left[i..]);
  out.extend_from_slice(&right[j..]);
  out
}

pub(super) fn merge_optional_sets(
  left: Option<&CanonicalTree>,
  right: Option<&CanonicalTree>,
) -> Vec<Address> {
  match (left, right) {
    (None, None) => Vec::new(),
    (Some(tree), None) | (None, Some(tree)) => tree.leaves.to_vec(),
    (Some(left), Some(right)) => merge_sorted(&left.leaves, &right.leaves),
  }
}
