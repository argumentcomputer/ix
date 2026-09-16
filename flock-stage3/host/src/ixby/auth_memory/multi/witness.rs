//! Native routing advice. None of the node lists or hashes is a verifier fact.
use super::{super::MultiUpdate, CLAIM_WORDS, MultiCapacity};
use anyhow::{Context, Result, ensure};
use flock_prover::field::F128;
use std::collections::{BTreeMap, VecDeque};

pub struct MultiAdvice {
  pub private: Vec<F128>,
  pub expected: Vec<F128>,
}
fn claim(
  level: usize,
  index: u64,
  old: [F128; 2],
  new: [F128; 2],
) -> [F128; CLAIM_WORDS] {
  [F128::ONE, F128::new(level as u64, index), old[0], old[1], new[0], new[1]]
}
fn key(record: &[F128; CLAIM_WORDS]) -> [u64; 2 * CLAIM_WORDS] {
  std::array::from_fn(|i| {
    if i & 1 == 0 { record[i / 2].lo } else { record[i / 2].hi }
  })
}
impl MultiAdvice {
  pub fn new(capacity: MultiCapacity, update: &MultiUpdate) -> Result<Self> {
    ensure!(
      update.leaves.len() == capacity.leaves
        && update.parents.len() <= capacity.parents
        && update.frontier.len() <= capacity.frontier(),
      "native memory multiproof quota"
    );
    let plan = capacity.plan();
    let pad = [F128::ZERO; CLAIM_WORDS];
    let mut supplied = Vec::new();
    let mut requested = Vec::new();
    let mut private = update
      .initial_root
      .into_iter()
      .chain(update.final_root)
      .collect::<Vec<_>>();
    for leaf in &update.leaves {
      private.push(F128::new(leaf.address, 0));
      private.extend(leaf.old);
      private.extend(leaf.new);
      supplied.push(claim(0, leaf.address, leaf.old_hash, leaf.new_hash));
    }
    let expected = private.clone();
    for i in 0..capacity.frontier() {
      if let Some(node) = update.frontier.get(i) {
        private.extend([F128::ONE, F128::new(node.level as u64, node.index)]);
        private.extend(node.hash);
        supplied.push(claim(node.level, node.index, node.hash, node.hash));
      } else {
        private.extend([F128::ZERO; 4]);
        supplied.push(pad);
      }
    }
    for i in 0..capacity.parents {
      if let Some(node) = update.parents.get(i) {
        ensure!(
          node.level > 0 && node.level <= update.depth.bits(),
          "native parent level"
        );
        private.extend([F128::ONE, F128::new(node.level as u64, node.index)]);
        private.extend(node.old_children.into_iter().flatten());
        private.extend(node.new_children.into_iter().flatten());
        supplied.push(claim(
          node.level,
          node.index,
          node.old_hash,
          node.new_hash,
        ));
        for child in 0..2 {
          requested.push(claim(
            node.level - 1,
            node.index * 2 + child as u64,
            node.old_children[child],
            node.new_children[child],
          ));
        }
      } else {
        private.extend([F128::ZERO; 10]);
        supplied.push(pad);
        requested.extend([pad; 2]);
      }
    }
    requested.push(claim(
      update.depth.bits(),
      0,
      update.initial_root,
      update.final_root,
    ));
    supplied.resize(plan.lanes(), pad);
    requested.resize(plan.lanes(), pad);
    let mut positions = BTreeMap::<_, VecDeque<_>>::new();
    for (i, record) in requested.iter().enumerate() {
      positions.entry(key(record)).or_default().push_back(i);
    }
    let mut destination = Vec::with_capacity(plan.lanes());
    for record in &supplied {
      destination.push(
        positions
          .get_mut(&key(record))
          .and_then(VecDeque::pop_front)
          .context("unmatched native memory-tree claim")?,
      );
    }
    private.extend(plan.route(&destination)?);
    Ok(Self { private, expected })
  }
}
