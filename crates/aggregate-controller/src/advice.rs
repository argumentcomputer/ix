//! The backend-neutral parts of a join's advice: the trees the circuit
//! re-hashes and the Merkle paths of discharged assumptions.

use crate::statement::{CanonicalTree, Statement, merge_optional_sets};
use ix_common::address::Address;
use ixon::merkle::MerklePath;
use rustc_hash::FxHashMap;

pub struct OwnedTreeAdvice {
  pub root: [u8; 32],
  pub bytes: Vec<u8>,
}

pub fn push_canonical_tree(
  out: &mut Vec<OwnedTreeAdvice>,
  tree: &CanonicalTree,
) {
  out.push(OwnedTreeAdvice {
    root: *tree.root.as_bytes(),
    bytes: tree.serialized().to_vec(),
  });
}
pub fn path_payload(path: Option<&MerklePath>) -> Result<Vec<u8>, String> {
  let Some(path) = path else {
    return Ok(vec![0]);
  };
  let length = u8::try_from(path.len()).map_err(|_overflow| {
    format!("aggregate Merkle path has {} steps", path.len())
  })?;
  if length > 64 {
    return Err(format!(
      "aggregate Merkle path has {length} steps (maximum 64)"
    ));
  }
  let mut out = Vec::with_capacity(2 + path.len() * 33);
  out.extend([1, length]);
  for (sibling, is_left) in path {
    out.push(if *is_left { 0 } else { 1 });
    out.extend_from_slice(sibling.as_bytes());
  }
  Ok(out)
}

/// The trees a join's circuit re-hashes, in the order it reads them: for a
/// flat join every subject and assumption tree (left, right, output), for
/// a structural join only the assumption trees.
pub fn advice_trees<'a>(
  left: &'a Statement,
  right: &'a Statement,
  output: &'a Statement,
  structural: bool,
) -> Result<Vec<&'a CanonicalTree>, String> {
  let mut trees = Vec::new();
  for (statement, side) in
    [(left, "left"), (right, "right"), (output, "output")]
  {
    if !structural {
      trees.push(
        statement
          .subjects
          .canonical_tree()
          .ok_or_else(|| format!("flat join has structural {side} subjects"))?,
      );
    }
    if let Some(tree) = &statement.assumptions {
      trees.push(tree);
    }
  }
  Ok(trees)
}

pub fn tree_advice(
  left: &Statement,
  right: &Statement,
  output: &Statement,
  structural: bool,
) -> Result<Vec<OwnedTreeAdvice>, String> {
  let mut trees = Vec::new();
  for tree in advice_trees(left, right, output, structural)? {
    push_canonical_tree(&mut trees, tree);
  }
  Ok(trees)
}

pub fn structural_path_advice(
  left: &Statement,
  right: &Statement,
  output: &Statement,
  owner_by_address: &FxHashMap<Address, usize>,
) -> Result<Vec<(Address, Vec<u8>)>, String> {
  let candidates = merge_optional_sets(
    left.assumptions.as_deref(),
    right.assumptions.as_deref(),
  );
  let mut paths = Vec::with_capacity(candidates.len());
  for candidate in candidates {
    let owner = owner_by_address.get(&candidate).ok_or_else(|| {
      format!("aggregate assumption {} has no owning shard", candidate.hex())
    })?;
    let path = output.subjects.merkle_proof(&candidate, *owner);
    paths.push((candidate, path_payload(path.as_ref())?));
  }
  Ok(paths)
}

pub fn assumption_count(statement: &Statement) -> usize {
  statement.assumptions.as_ref().map_or(0, |tree| tree.leaves.len())
}
