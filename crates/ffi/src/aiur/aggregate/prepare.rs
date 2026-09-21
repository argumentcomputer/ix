//! Aggregation prepare.

use super::statement::{CanonicalTree, ShardSet, Statement, SubjectTree};
use ix_common::address::Address;
use ix_kernel::shard::{AggNode, ShardManifest};
use ixon::{
  Constant, ConstantInfo, merkle::merkle_root_canonical_sorted,
  shard_claim::walk_edges,
};
use rayon::prelude::*;
use rustc_hash::{FxHashMap, FxHashSet};
use std::sync::Arc;

#[derive(Debug)]
pub(super) struct PreparedShard {
  pub(super) original_id: u32,
  pub(super) statement: Arc<Statement>,
}

pub(super) struct PreparedRun {
  pub(super) shards: Vec<PreparedShard>,
  pub(super) owner_by_address: FxHashMap<Address, usize>,
  pub(super) tree: AggNode,
  pub(super) env_root: Address,
  pub(super) env_count: usize,
  pub(super) expected_shards: ShardSet,
}

pub(super) fn projection_block(addr: &Address, constant: &Constant) -> Address {
  match &constant.info {
    ConstantInfo::IPrj(p) => p.block.clone(),
    ConstantInfo::CPrj(p) => p.block.clone(),
    ConstantInfo::RPrj(p) => p.block.clone(),
    ConstantInfo::DPrj(p) => p.block.clone(),
    _ => addr.clone(),
  }
}

pub(super) fn prepare_run(
  env: &ixon::Env,
  manifest: &ShardManifest,
) -> Result<PreparedRun, String> {
  if manifest.shards.is_empty() {
    return Err("manifest contains no shards".into());
  }

  let mut block_to_shard = FxHashMap::default();
  let mut id_to_index = FxHashMap::default();
  for (index, shard) in manifest.shards.iter().enumerate() {
    if id_to_index.insert(shard.id, index).is_some() {
      return Err(format!("manifest repeats shard id {}", shard.id));
    }
    for block in &shard.blocks {
      if let Some(previous) = block_to_shard.insert(block.clone(), index) {
        return Err(format!(
          "manifest block {} is owned by shards {} and {}",
          block.hex(),
          manifest.shards[previous].id,
          shard.id
        ));
      }
    }
  }

  // DashMap iteration is deliberately unordered. Sort first so indexed Rayon
  // collection and the later sequential fold retain deterministic errors and
  // output independent of worker scheduling.
  let mut all_addresses: Vec<Address> =
    env.consts.iter().map(|entry| entry.key().clone()).collect();
  all_addresses.par_sort_unstable();

  // Materializing an .ixe constant parses its serialized representation, and
  // lazy constants intentionally do not cache that representation. Classify
  // ownership and extract the kernel walk edges in the same parallel pass so
  // frontier construction does not parse all constants a second time.
  let classified_results: Vec<Result<(usize, Vec<Address>), String>> =
    all_addresses
      .par_iter()
      .map(|addr| {
        let constant = env
          .try_get_const(addr)
          .ok_or_else(|| {
            format!("environment constant {} disappeared", addr.hex())
          })?
          .map_err(|error| {
            format!("cannot parse environment constant {}: {error}", addr.hex())
          })?;
        let block = projection_block(addr, &constant);
        let owner = block_to_shard.get(&block).copied().ok_or_else(|| {
          format!(
            "environment constant {} (block {}) has no owning manifest shard",
            addr.hex(),
            block.hex()
          )
        })?;
        let mut edges = Vec::new();
        walk_edges(&constant, &mut edges);
        Ok((owner, edges))
      })
      .collect();
  // Resolve failures in canonical-address order rather than whichever Rayon
  // worker happens to finish first.
  let classified: Vec<(usize, Vec<Address>)> =
    classified_results.into_iter().collect::<Result<_, _>>()?;

  let mut owned = vec![Vec::new(); manifest.shards.len()];
  let mut walk_edges_by_shard = vec![Vec::new(); manifest.shards.len()];
  let mut owners_old = Vec::with_capacity(all_addresses.len());
  for (addr, (owner, edges)) in all_addresses.iter().zip(classified) {
    owned[owner].push(addr.clone());
    walk_edges_by_shard[owner].extend(edges);
    owners_old.push(owner);
  }
  if owners_old.len() != env.consts.len() {
    return Err(
      "manifest ownership did not cover every environment constant".into(),
    );
  }

  let retained_old: Vec<usize> = owned
    .iter()
    .enumerate()
    .filter_map(|(index, addresses)| (!addresses.is_empty()).then_some(index))
    .collect();
  if retained_old.is_empty() {
    return Err("manifest has no shard owning an environment constant".into());
  }
  let retained_ids: FxHashSet<u32> =
    retained_old.iter().map(|index| manifest.shards[*index].id).collect();
  let source_tree = manifest.tree.clone().unwrap_or_else(|| {
    let ids: Vec<u32> = manifest.shards.iter().map(|shard| shard.id).collect();
    AggNode::balanced(&ids).expect("a nonempty id list has a balanced tree")
  });
  let tree = source_tree
    .prune(&|id| retained_ids.contains(&id))
    .ok_or("pruning removed every aggregate-tree leaf")?;

  let mut old_to_retained = FxHashMap::default();
  for (retained, old) in retained_old.iter().copied().enumerate() {
    old_to_retained.insert(old, retained);
  }
  let owner_by_address: FxHashMap<Address, usize> = all_addresses
    .iter()
    .cloned()
    .zip(owners_old)
    .map(|(address, old)| (address, old_to_retained[&old]))
    .collect();

  let shard_inputs: Vec<(usize, u32, Vec<Address>, Vec<Address>)> =
    retained_old
      .iter()
      .copied()
      .enumerate()
      .map(|(retained, old)| {
        (
          retained,
          manifest.shards[old].id,
          std::mem::take(&mut owned[old]),
          std::mem::take(&mut walk_edges_by_shard[old]),
        )
      })
      .collect();
  let shard_results: Vec<Result<PreparedShard, String>> = shard_inputs
    .into_par_iter()
    .map(|(retained, original_id, subjects, candidates)| {
      // Every environment constant has exactly one retained owner. Thus this
      // is the thin-frontier predicate without rebuilding a subject hash set:
      // retain present walk edges owned by another shard, exclude local and
      // absent (including blob-sentinel) edges.
      let mut frontier_set = FxHashSet::default();
      for candidate in candidates {
        if owner_by_address
          .get(&candidate)
          .is_some_and(|owner| *owner != retained)
        {
          frontier_set.insert(candidate);
        }
      }
      let mut frontier: Vec<Address> = frontier_set.into_iter().collect();
      frontier.sort_unstable();
      let subject_tree = SubjectTree::canonical(
        subjects,
        ShardSet::singleton(retained, retained_old.len()),
      )?;
      let assumptions = CanonicalTree::from_sorted(frontier)?;
      let statement = Statement::new(subject_tree, assumptions);
      Ok(PreparedShard { original_id, statement })
    })
    .collect();
  // Retained-shard order is stable because Vec's parallel iterator is indexed;
  // resolve any errors in that same order for deterministic diagnostics.
  let shards = shard_results.into_iter().collect::<Result<Vec<_>, _>>()?;

  let env_root = merkle_root_canonical_sorted(&all_addresses)
    .ok_or("cannot aggregate an empty environment")?;
  let expected_shards = ShardSet(
    (0..retained_old.len().div_ceil(64))
      .map(|word| {
        let remaining = retained_old.len().saturating_sub(word * 64);
        if remaining >= 64 { u64::MAX } else { (1u64 << remaining) - 1 }
      })
      .collect(),
  );

  Ok(PreparedRun {
    shards,
    owner_by_address,
    tree,
    env_root,
    env_count: all_addresses.len(),
    expected_shards,
  })
}

/// Check the semantic certificate attached to the root statement independently
/// of any proof: every environment constant occurs exactly once, every retained
/// shard contributes, the canonicalized subject root is the environment root,
/// and no assumption survives.
pub(super) fn validate_root_statement(
  prepared: &PreparedRun,
  root: &Statement,
) -> Result<(), String> {
  if root.subjects.count != prepared.env_count {
    return Err(format!(
      "aggregate root has {} subjects, environment has {}",
      root.subjects.count, prepared.env_count
    ));
  }
  if root.subjects.shards != prepared.expected_shards {
    return Err("aggregate root does not contain every retained shard".into());
  }
  let mut root_leaves = Vec::with_capacity(prepared.env_count);
  root.subjects.collect_leaves(&mut root_leaves);
  if root_leaves.len() != prepared.env_count {
    return Err(format!(
      "aggregate root tree contains {} subject occurrences, environment has {} constants",
      root_leaves.len(),
      prepared.env_count
    ));
  }
  root_leaves.sort_unstable();
  if root_leaves.windows(2).any(|pair| pair[0] == pair[1]) {
    return Err("aggregate root contains a duplicate subject".into());
  }
  if let Some(foreign) = root_leaves
    .iter()
    .find(|addr| !prepared.owner_by_address.contains_key(*addr))
  {
    return Err(format!(
      "aggregate root contains foreign subject {}",
      foreign.hex()
    ));
  }
  let canonical_root = merkle_root_canonical_sorted(&root_leaves)
    .ok_or("aggregate root has no subject leaves")?;
  if canonical_root != prepared.env_root {
    return Err(format!(
      "aggregate root subjects canonicalize to {}, not environment root {}",
      canonical_root.hex(),
      prepared.env_root.hex()
    ));
  }
  if root.assumptions.is_some() {
    return Err("aggregate root retains undischarged assumptions".into());
  }
  Ok(())
}
