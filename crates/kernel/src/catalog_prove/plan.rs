use super::*;
use crate::profile::{OpCounts, ProfileBuilder};
use crate::shard::{AggNode, Hypergraph, ShardManifest};
use ixon::constant::ConstantInfo;
use ixon::shard_claim::{shard_check_env_claim, walk_edges};
use rustc_hash::{FxHashMap, FxHashSet};

pub(super) struct Inventory {
  pub addresses: Vec<Address>,
  pub axioms: Vec<Address>,
  pub blocks: FxHashMap<Address, Address>,
  sizes: FxHashMap<Address, u64>,
  edges: Vec<(Address, Address)>,
}

impl Inventory {
  pub(super) fn read(env: &Env) -> Result<Self, String> {
    if !env.assumptions.is_empty() {
      return Err("catalog proving requires a closed corpus".into());
    }
    let mut addresses: Vec<_> =
      env.consts.iter().map(|entry| entry.key().clone()).collect();
    addresses.sort_unstable();
    if addresses.is_empty() {
      return Err("cannot prove an empty catalog".into());
    }
    let mut axioms = Vec::new();
    let mut blocks = FxHashMap::default();
    let mut sizes: FxHashMap<Address, u64> = FxHashMap::default();
    let mut edges = Vec::new();
    for address in &addresses {
      let lazy = env.consts.get(address).ok_or("missing constant")?;
      let constant = lazy.value().get_at(address)?;
      let block = match &constant.info {
        ConstantInfo::IPrj(p) => p.block.clone(),
        ConstantInfo::CPrj(p) => p.block.clone(),
        ConstantInfo::RPrj(p) => p.block.clone(),
        ConstantInfo::DPrj(p) => p.block.clone(),
        ConstantInfo::Axio(_) => {
          axioms.push(address.clone());
          address.clone()
        },
        _ => address.clone(),
      };
      if !env.consts.contains_key(&block) {
        return Err(format!(
          "projection {} has missing block {}",
          address.hex(),
          block.hex()
        ));
      }
      *sizes.entry(block.clone()).or_default() +=
        lazy.value().raw_bytes().len() as u64;
      blocks.insert(address.clone(), block);
      let mut refs = Vec::new();
      walk_edges(&constant, &mut refs);
      for dependency in refs {
        if !env.consts.contains_key(&dependency) {
          return Err(format!(
            "constant {} has missing dependency {}",
            address.hex(),
            dependency.hex()
          ));
        }
        edges.push((address.clone(), dependency));
      }
    }
    Ok(Self { addresses, axioms, blocks, sizes, edges })
  }

  pub(super) fn check_axioms(&self, allowed: &[Address]) -> Result<(), String> {
    let forbidden: Vec<_> = self
      .axioms
      .iter()
      .filter(|address| allowed.binary_search(address).is_err())
      .map(Address::hex)
      .collect();
    if !forbidden.is_empty() {
      return Err(format!(
        "unapproved axiom addresses: {}. Pass an explicitly reviewed --allow-axioms file for the baseline",
        forbidden.join(", ")
      ));
    }
    Ok(())
  }
}

#[derive(Clone, Debug)]
pub(super) struct Leaf {
  pub id: u32,
  pub claim: Address,
  pub subjects: Vec<Address>,
  pub frontier: Vec<Address>,
}

impl Leaf {
  pub(super) fn json(&self) -> Value {
    json!({"id": self.id, "claim": self.claim.hex(),
      "subjects": addresses_json(&self.subjects), "frontier": addresses_json(&self.frontier)})
  }
}

/// Reconstruct claims from the actual corpus, including projections that may
/// have appeared after an older block was assigned to its shard.
pub(super) fn leaves(
  env: &Env,
  inventory: &Inventory,
  manifest: &ShardManifest,
) -> Result<Vec<Leaf>, String> {
  if manifest.shards.is_empty()
    || manifest.num_shards as usize != manifest.shards.len()
  {
    return Err("invalid shard count".into());
  }
  let mut owner = FxHashMap::default();
  for (index, shard) in manifest.shards.iter().enumerate() {
    if shard.id as usize != index || shard.blocks.is_empty() {
      return Err(
        "catalog proving requires dense IDs and nonempty shards".into(),
      );
    }
    for block in &shard.blocks {
      if !inventory.sizes.contains_key(block) {
        return Err(format!(
          "shard {} owns an absent block {}",
          shard.id,
          block.hex()
        ));
      }
      if owner.insert(block.clone(), index).is_some() {
        return Err(format!("duplicate block owner for {}", block.hex()));
      }
    }
  }
  let ids: Vec<_> = manifest.shards.iter().map(|shard| shard.id).collect();
  let tree = manifest
    .tree
    .clone()
    .or_else(|| AggNode::balanced(&ids))
    .ok_or("missing tree")?;
  let mut tree_ids = Vec::new();
  tree.collect_leaves(&mut tree_ids);
  tree_ids.sort_unstable();
  if tree_ids != ids {
    return Err(
      "aggregation tree does not cover each shard exactly once".into(),
    );
  }
  let mut subjects = vec![Vec::new(); manifest.shards.len()];
  for address in &inventory.addresses {
    let block = &inventory.blocks[address];
    let index = owner
      .get(block)
      .ok_or_else(|| format!("unowned block {}", block.hex()))?;
    subjects[*index].push(address.clone());
  }
  subjects
    .into_iter()
    .enumerate()
    .map(|(index, owned)| {
      let (claim, frontier) =
        shard_check_env_claim(env, &owned).ok_or("empty shard")?;
      let mut bytes = Vec::new();
      claim.put(&mut bytes);
      Ok(Leaf {
        id: manifest.shards[index].id,
        claim: Address::hash(&bytes),
        subjects: owned,
        frontier,
      })
    })
    .collect()
}

pub(super) struct Plan {
  pub manifest: ShardManifest,
  pub leaves: Vec<Leaf>,
  pub new_subjects: usize,
  pub retained_claims: usize,
  pub changed_base_claims: usize,
}

/// Preserve old block ownership and tree shape; partition only unowned blocks.
/// A new projection can change an old leaf's claim, so reuse is determined by
/// reconstructed claims rather than shard IDs or block-list equality.
pub(super) fn extend(
  env: &Env,
  inventory: &Inventory,
  base: Option<(&Env, &Inventory, &ShardManifest)>,
  requested_shards: usize,
) -> Result<Plan, String> {
  let mut previous = Vec::new();
  let mut manifest = if let Some((base_env, base_inventory, old)) = base {
    previous = leaves(base_env, base_inventory, old)?;
    if base_inventory
      .addresses
      .iter()
      .any(|a| inventory.addresses.binary_search(a).is_err())
    {
      return Err("corpus update dropped a previously owned subject".into());
    }
    old.clone()
  } else {
    ShardManifest {
      num_shards: 0,
      shards: Vec::new(),
      total_cross_ingress: 0,
      tree: None,
    }
  };
  if manifest.tree.is_none() && !manifest.shards.is_empty() {
    manifest.tree = AggNode::balanced(
      &manifest.shards.iter().map(|s| s.id).collect::<Vec<_>>(),
    );
  }
  let old_blocks: FxHashSet<_> =
    manifest.shards.iter().flat_map(|s| s.blocks.iter().cloned()).collect();
  let mut new_blocks: Vec<_> = inventory
    .sizes
    .keys()
    .filter(|a| !old_blocks.contains(*a))
    .cloned()
    .collect();
  new_blocks.sort_unstable();
  if !new_blocks.is_empty() {
    let new_set: FxHashSet<_> = new_blocks.iter().cloned().collect();
    let mut builder = ProfileBuilder::new();
    let mut bytes = 0u64;
    for block in &new_blocks {
      let size = inventory.sizes[block];
      bytes = bytes.saturating_add(size);
      let size32 = u32::try_from(size)
        .map_err(|_| "atomic block exceeds profile size limit")?;
      builder.block(block.clone(), size.max(1), size32, 1, OpCounts::default());
    }
    for (consumer, producer) in &inventory.edges {
      let c = &inventory.blocks[consumer];
      let p = &inventory.blocks[producer];
      if new_set.contains(c) && new_set.contains(p) {
        builder.delta_edge(c.clone(), p.clone());
      }
    }
    let profile = builder.finish();
    let count = if requested_shards == 0 {
      usize::try_from(bytes.div_ceil(16 * 1024 * 1024))
        .map_err(|_| "too many shards")?
        .max(1)
    } else {
      requested_shards
    }
    .min(new_blocks.len());
    let (assignment, tree) =
      Hypergraph::from_profile(&profile).partition_with_tree(count, 0.05);
    let mut added = ShardManifest::build(&profile, &assignment, count);
    let offset = u32::try_from(manifest.shards.len())
      .map_err(|_| "too many old shards")?;
    fn shifted(tree: AggNode, offset: u32) -> Result<AggNode, String> {
      Ok(match tree {
        AggNode::Leaf(id) => {
          AggNode::Leaf(id.checked_add(offset).ok_or("shard ID overflow")?)
        },
        AggNode::Internal(l, r) => AggNode::Internal(
          Box::new(shifted(*l, offset)?),
          Box::new(shifted(*r, offset)?),
        ),
      })
    }
    let tree = shifted(tree, offset)?;
    for shard in &mut added.shards {
      shard.id = shard.id.checked_add(offset).ok_or("shard ID overflow")?;
    }
    manifest.shards.extend(added.shards);
    manifest.tree = Some(match manifest.tree.take() {
      Some(old) => AggNode::Internal(Box::new(old), Box::new(tree)),
      None => tree,
    });
    manifest.num_shards =
      u32::try_from(manifest.shards.len()).map_err(|_| "too many shards")?;
  }
  let current = leaves(env, inventory, &manifest)?;
  for (shard, leaf) in manifest.shards.iter_mut().zip(&current) {
    shard.assumption_root =
      ixon::merkle::merkle_root_canonical_sorted(&leaf.frontier);
    let foreign: FxHashSet<_> =
      leaf.frontier.iter().map(|a| inventory.blocks[a].clone()).collect();
    shard.foreign_blocks = foreign.into_iter().collect();
    shard.foreign_blocks.sort_unstable();
    shard.cross_ingress =
      shard.foreign_blocks.iter().map(|a| inventory.sizes[a]).sum();
    shard.own_size = shard.blocks.iter().map(|a| inventory.sizes[a]).sum();
    if let Some(old) = previous.get(shard.id as usize) {
      if old.claim != leaf.claim {
        shard.measured_peak_bytes = 0;
      }
    }
  }
  manifest.total_cross_ingress =
    manifest.shards.iter().map(|s| u128::from(s.cross_ingress)).sum();
  let retained_claims =
    previous.iter().zip(&current).filter(|(a, b)| a.claim == b.claim).count();
  Ok(Plan {
    new_subjects: inventory.addresses.len()
      - base.map_or(0, |(_, i, _)| i.addresses.len()),
    changed_base_claims: previous.len() - retained_claims,
    retained_claims,
    manifest,
    leaves: current,
  })
}
