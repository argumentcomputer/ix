//! Native Stage 2 orchestration for `ix aggregate`.
//!
//! Lean still constructs the two Aiur bytecode systems, because their source
//! programs are Lean-authored. Everything data-dependent after that point is
//! kept here: manifest/environment binding, shard-claim reconstruction,
//! statement folding, cache validation, dependency scheduling, recursive
//! advice construction, proving, and persistence.
//!
//! The host statements deliberately cache roots and sorted leaves. Structural
//! subject trees carry only their two children and a small shard-membership
//! bitset, so deciding whether an assumption is discharged is O(1), and a
//! Merkle path is O(log n). This avoids the eager recursive `root`/`leaves`/
//! `contains` traversals that made the former Lean startup super-linear.

#![allow(clippy::too_many_arguments)]

use std::{
  cmp::Ordering,
  fs,
  path::{Path, PathBuf},
  sync::{Arc, OnceLock, mpsc},
  thread,
  time::Instant,
};

use aiur::{
  G, function_channel,
  synthesis::{AiurProof, AiurSystem, GatedProve},
};
use ix_common::address::Address;
use ix_kernel::shard::{AggNode, ShardManifest};
use ixon::{
  Claim, Constant, ConstantInfo, Proof as IxonProof,
  assumption_tree::AssumptionTree,
  merkle::{
    MerklePath, leaf_hash, merkle_root_canonical_sorted, node_hash,
    zero_address,
  },
  shard_claim::thin_frontier,
};
use ixvm_codegen::{
  aiur_ix_aggr_runner::{
    AggrAdvice, AggrPath, AggrPreimage, AggrTree, aggr_io_buffer,
    execute_ix_aggr,
  },
  env_handle::EnvHandle,
};
use lean_ffi::object::{
  LeanBorrowed, LeanByteArray, LeanExcept, LeanExternal, LeanNat, LeanOwned,
  LeanString,
};
use multi_stark::p3_field::{PrimeCharacteristicRing, PrimeField64};
use rustc_hash::{FxHashMap, FxHashSet};

use super::lean_unbox_nat_as_usize;

const CACHE_VERSION: u64 = 2;
const MIB: usize = 1024 * 1024;
const GIB: usize = 1024 * 1024 * 1024;
const WRAP_RAM_BYTES: usize = 195 * GIB;
const STRUCTURAL_RAM_BYTES: usize = 195 * GIB;
const RAW_SHARD_RAM_BYTES: usize = 4 * GIB;
const DIRECT_RAM_BYTES: usize = 390 * GIB;
const MIXED_RAM_BYTES: usize = 340 * GIB;
const FLAT_RAM_PER_SUBJECT: usize = 1024 * 1024;

fn format_gib(bytes: usize) -> String {
  let tenths = bytes.saturating_mul(10) / GIB;
  format!("{}.{:01}", tenths / 10, tenths % 10)
}

fn format_mib(bytes: usize) -> String {
  let tenths = bytes.saturating_mul(10) / MIB;
  format!("{}.{:01}", tenths / 10, tenths % 10)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ChildKind {
  Ixvm,
  Aggr,
}

impl ChildKind {
  const fn code(self) -> u8 {
    match self {
      Self::Ixvm => 0,
      Self::Aggr => 1,
    }
  }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ShardSet(Vec<u64>);

impl ShardSet {
  fn singleton(index: usize, shard_count: usize) -> Self {
    let mut words = vec![0; shard_count.div_ceil(64)];
    words[index / 64] |= 1u64 << (index % 64);
    Self(words)
  }

  fn union(&self, other: &Self) -> Self {
    debug_assert_eq!(self.0.len(), other.0.len());
    Self(self.0.iter().zip(&other.0).map(|(a, b)| a | b).collect())
  }

  fn contains(&self, index: usize) -> bool {
    self
      .0
      .get(index / 64)
      .is_some_and(|word| word & (1u64 << (index % 64)) != 0)
  }
}

/// Canonical sorted tree whose expensive derivative representations are built
/// once, on demand. The root is computed once at construction.
#[derive(Debug)]
struct CanonicalTree {
  leaves: Arc<[Address]>,
  root: Address,
  serialized: OnceLock<Vec<u8>>,
  levels: OnceLock<Vec<Vec<Address>>>,
}

impl CanonicalTree {
  fn from_sorted(leaves: Vec<Address>) -> Result<Option<Arc<Self>>, String> {
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

  fn serialized(&self) -> &[u8] {
    self.serialized.get_or_init(|| {
      let tree = AssumptionTree::canonical(&self.leaves)
        .expect("a nonempty canonical leaf list has a tree");
      debug_assert_eq!(tree.root(), self.root);
      tree.ser()
    })
  }

  fn levels(&self) -> &[Vec<Address>] {
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

  fn merkle_proof(&self, target: &Address) -> Option<MerklePath> {
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
enum SubjectRepr {
  Canonical(Arc<CanonicalTree>),
  Structural { left: Arc<SubjectTree>, right: Arc<SubjectTree> },
}

#[derive(Debug)]
struct SubjectTree {
  root: Address,
  count: usize,
  shards: ShardSet,
  repr: SubjectRepr,
}

impl SubjectTree {
  fn canonical(
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

  fn flat(left: &Arc<Self>, right: &Arc<Self>) -> Result<Arc<Self>, String> {
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

  fn structural(left: Arc<Self>, right: Arc<Self>) -> Arc<Self> {
    Arc::new(Self {
      root: node_hash(&left.root, &right.root),
      count: left.count.saturating_add(right.count),
      shards: left.shards.union(&right.shards),
      repr: SubjectRepr::Structural { left, right },
    })
  }

  fn canonical_tree(&self) -> Option<&CanonicalTree> {
    match &self.repr {
      SubjectRepr::Canonical(tree) => Some(tree),
      SubjectRepr::Structural { .. } => None,
    }
  }

  fn merkle_proof(&self, target: &Address, owner: usize) -> Option<MerklePath> {
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

  fn collect_leaves(&self, out: &mut Vec<Address>) {
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
struct Statement {
  subjects: Arc<SubjectTree>,
  assumptions: Option<Arc<CanonicalTree>>,
  claim: Claim,
  claim_bytes: Vec<u8>,
}

impl Statement {
  fn new(
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

  fn join(
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

#[derive(Debug)]
struct PreparedShard {
  original_id: u32,
  statement: Arc<Statement>,
}

struct PreparedRun {
  shards: Vec<PreparedShard>,
  owner_by_address: FxHashMap<Address, usize>,
  tree: AggNode,
  env_root: Address,
  env_count: usize,
  expected_shards: ShardSet,
}

#[derive(Clone, Copy, Debug)]
enum PlanOp {
  Leaf(usize),
  Join(usize, usize),
}

#[derive(Debug)]
struct SlotSpec {
  op: PlanOp,
  statement: Arc<Statement>,
  subject_count: usize,
  structural: bool,
  kind: ChildKind,
  shape: Option<u8>,
  outer_claim: Vec<G>,
  cache_key: Address,
  ram_bytes: usize,
}

struct Slot {
  kind: ChildKind,
  statement: Arc<Statement>,
  outer_claim: Vec<G>,
  proof: AiurProof,
  proof_address: Option<Address>,
  claims_bytes: Vec<u8>,
}

#[derive(Clone, Copy)]
struct ProveContext<'a> {
  specs: &'a [SlotSpec],
  prepared: &'a [PreparedShard],
  proofs: Option<&'a [Arc<IxonProof>]>,
  owner_by_address: &'a FxHashMap<Address, usize>,
  ixvm_system: &'a AiurSystem,
  aggr_system: &'a AiurSystem,
  ixvm_vk: &'a [u8],
  aggr_vk: &'a [u8],
  allowed: &'a [u8],
  verify_idx: usize,
  aggr_idx: usize,
  store_dir: &'a Path,
  cache_dir: Option<&'a Path>,
  reprove_slot: Option<usize>,
  write_outputs: bool,
}

#[derive(Clone, Copy)]
struct RunConfig<'a> {
  ixvm_system: &'a AiurSystem,
  aggr_system: &'a AiurSystem,
  env_handle: &'a EnvHandle,
  manifest_path: &'a Path,
  proof_hexes: &'a str,
  verify_idx: usize,
  aggr_idx: usize,
  jobs: usize,
  ram_budget_bytes: usize,
  structural_above: usize,
  reprove_slot: Option<usize>,
  direct_joins: bool,
  plan_only: bool,
  cache_fri_bytes: &'a [u8],
  use_cache: bool,
  write_outputs: bool,
}

fn projection_block(addr: &Address, constant: &Constant) -> Address {
  match &constant.info {
    ConstantInfo::IPrj(p) => p.block.clone(),
    ConstantInfo::CPrj(p) => p.block.clone(),
    ConstantInfo::RPrj(p) => p.block.clone(),
    ConstantInfo::DPrj(p) => p.block.clone(),
    _ => addr.clone(),
  }
}

fn prepare_run(
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

  let mut owned = vec![Vec::new(); manifest.shards.len()];
  let mut owner_old = FxHashMap::default();
  for entry in env.consts.iter() {
    let addr = entry.key().clone();
    let constant = entry.value().get().map_err(|error| {
      format!("cannot parse environment constant {}: {error}", addr.hex())
    })?;
    let block = projection_block(&addr, &constant);
    let owner = block_to_shard.get(&block).copied().ok_or_else(|| {
      format!(
        "environment constant {} (block {}) has no owning manifest shard",
        addr.hex(),
        block.hex()
      )
    })?;
    owned[owner].push(addr.clone());
    owner_old.insert(addr, owner);
  }
  if owner_old.len() != env.consts.len() {
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
  let owner_by_address: FxHashMap<Address, usize> = owner_old
    .into_iter()
    .map(|(address, old)| {
      let retained = old_to_retained[&old];
      (address, retained)
    })
    .collect();

  let mut shards = Vec::with_capacity(retained_old.len());
  for (retained, old) in retained_old.iter().copied().enumerate() {
    let mut subjects = std::mem::take(&mut owned[old]);
    subjects.sort_unstable();
    subjects.dedup();
    let frontier = thin_frontier(env, &subjects);
    let subject_tree = SubjectTree::canonical(
      subjects,
      ShardSet::singleton(retained, retained_old.len()),
    )?;
    let assumptions = CanonicalTree::from_sorted(frontier)?;
    let statement = Statement::new(subject_tree, assumptions);
    shards
      .push(PreparedShard { original_id: manifest.shards[old].id, statement });
  }

  let mut all_addresses: Vec<Address> =
    owner_by_address.keys().cloned().collect();
  all_addresses.sort_unstable();
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

fn merge_sorted(left: &[Address], right: &[Address]) -> Vec<Address> {
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

fn merge_optional_sets(
  left: Option<&CanonicalTree>,
  right: Option<&CanonicalTree>,
) -> Vec<Address> {
  match (left, right) {
    (None, None) => Vec::new(),
    (Some(tree), None) | (None, Some(tree)) => tree.leaves.to_vec(),
    (Some(left), Some(right)) => merge_sorted(&left.leaves, &right.leaves),
  }
}

fn build_plan(
  tree: &AggNode,
  shard_by_id: &FxHashMap<u32, usize>,
  out: &mut Vec<PlanOp>,
) -> Result<usize, String> {
  match tree {
    AggNode::Leaf(id) => {
      let shard = shard_by_id.get(id).copied().ok_or_else(|| {
        format!("aggregate tree references missing shard {id}")
      })?;
      let index = out.len();
      out.push(PlanOp::Leaf(shard));
      Ok(index)
    },
    AggNode::Internal(left, right) => {
      let left_index = build_plan(left, shard_by_id, out)?;
      let right_index = build_plan(right, shard_by_id, out)?;
      let index = out.len();
      out.push(PlanOp::Join(left_index, right_index));
      Ok(index)
    },
  }
}

fn packed_digest(bytes: &[u8]) -> Vec<G> {
  let digest = blake3::hash(bytes);
  digest
    .as_bytes()
    .as_chunks::<4>()
    .0
    .iter()
    .map(|word| G::from_u32(u32::from_le_bytes(*word)))
    .collect()
}

fn build_claim(fun_idx: usize, input: &[G], output: &[G]) -> Vec<G> {
  let mut claim = Vec::with_capacity(2 + input.len() + output.len());
  claim.push(function_channel());
  claim.push(G::from_usize(fun_idx));
  claim.extend_from_slice(input);
  claim.extend_from_slice(output);
  claim
}

fn serialize_claims(claims: &[&[G]]) -> Vec<u8> {
  let mut out = Vec::new();
  out.extend_from_slice(&(claims.len() as u64).to_le_bytes());
  for claim in claims {
    out.extend_from_slice(&(claim.len() as u64).to_le_bytes());
    for value in *claim {
      out.extend_from_slice(&value.as_canonical_u64().to_le_bytes());
    }
  }
  out
}

fn inner_claim(verify_idx: usize, claim_bytes: &[u8]) -> Vec<G> {
  build_claim(verify_idx, &packed_digest(claim_bytes), &[])
}

fn aggregate_outer_claim(
  aggr_idx: usize,
  allowed: &[u8],
  claim_bytes: &[u8],
) -> Vec<G> {
  let mut input = packed_digest(allowed);
  input.extend(packed_digest(claim_bytes));
  build_claim(aggr_idx, &input, &[])
}

fn allowed_blob(
  ixvm_vk: &[u8],
  verify_idx: usize,
  aggr_vk: &[u8],
  aggr_idx: usize,
) -> Vec<u8> {
  let mut out = Vec::with_capacity(80);
  out.extend_from_slice(blake3::hash(ixvm_vk).as_bytes());
  out.extend_from_slice(&(verify_idx as u64).to_le_bytes());
  out.extend_from_slice(blake3::hash(aggr_vk).as_bytes());
  out.extend_from_slice(&(aggr_idx as u64).to_le_bytes());
  out
}

fn cache_key(
  aggr_vk: &[u8],
  cache_fri_bytes: &[u8],
  outer_claim: &[G],
) -> Address {
  let mut bytes = Vec::with_capacity(8 + 32 + cache_fri_bytes.len() + 256);
  bytes.extend_from_slice(&CACHE_VERSION.to_le_bytes());
  bytes.extend_from_slice(blake3::hash(aggr_vk).as_bytes());
  bytes.extend_from_slice(cache_fri_bytes);
  bytes.extend(serialize_claims(&[outer_claim]));
  Address::hash(&bytes)
}

fn shape_code(left: ChildKind, right: Option<ChildKind>) -> u8 {
  match right {
    None => left.code(),
    Some(right) => 2 + 2 * left.code() + right.code(),
  }
}

fn structural_shape_code(left: ChildKind, right: ChildKind) -> u8 {
  6 + 2 * left.code() + right.code()
}

fn shape_ram_bytes(shape: u8, subject_count: usize) -> usize {
  match shape {
    0 | 1 => WRAP_RAM_BYTES,
    3 | 4 | 7 | 8 => MIXED_RAM_BYTES,
    5 => STRUCTURAL_RAM_BYTES
      .saturating_add(subject_count.saturating_mul(FLAT_RAM_PER_SUBJECT)),
    9 => STRUCTURAL_RAM_BYTES,
    // Shapes 2/6 are direct pairs; unknown shapes retain the conservative
    // direct-pair fallback used by the Lean reference scheduler.
    _ => DIRECT_RAM_BYTES,
  }
}

fn build_specs(
  prepared: &PreparedRun,
  verify_idx: usize,
  aggr_idx: usize,
  structural_above: usize,
  direct_joins: bool,
  aggr_vk: &[u8],
  allowed: &[u8],
  cache_fri_bytes: &[u8],
) -> Result<Vec<SlotSpec>, String> {
  let shard_by_id: FxHashMap<u32, usize> = prepared
    .shards
    .iter()
    .enumerate()
    .map(|(index, shard)| (shard.original_id, index))
    .collect();
  let mut ops = Vec::new();
  build_plan(&prepared.tree, &shard_by_id, &mut ops)?;
  let raw_leaves = direct_joins && ops.len() > 1;
  let mut specs: Vec<SlotSpec> = Vec::with_capacity(ops.len());
  for op in ops {
    match op {
      PlanOp::Leaf(shard) => {
        let prepared_shard = &prepared.shards[shard];
        let kind = if raw_leaves { ChildKind::Ixvm } else { ChildKind::Aggr };
        let shape = (!raw_leaves).then_some(shape_code(ChildKind::Ixvm, None));
        let outer_claim = if raw_leaves {
          inner_claim(verify_idx, &prepared_shard.statement.claim_bytes)
        } else {
          aggregate_outer_claim(
            aggr_idx,
            allowed,
            &prepared_shard.statement.claim_bytes,
          )
        };
        let key = cache_key(aggr_vk, cache_fri_bytes, &outer_claim);
        specs.push(SlotSpec {
          op,
          statement: prepared_shard.statement.clone(),
          subject_count: prepared_shard.statement.subjects.count,
          structural: false,
          kind,
          shape,
          outer_claim,
          cache_key: key,
          ram_bytes: shape.map_or(RAW_SHARD_RAM_BYTES, |value| {
            shape_ram_bytes(value, prepared_shard.statement.subjects.count)
          }),
        });
      },
      PlanOp::Join(left_index, right_index) => {
        let left = specs
          .get(left_index)
          .ok_or("aggregate plan has a missing left child")?;
        let right = specs
          .get(right_index)
          .ok_or("aggregate plan has a missing right child")?;
        let subject_count =
          left.subject_count.saturating_add(right.subject_count);
        let structural = subject_count > structural_above;
        let shape = if structural {
          structural_shape_code(left.kind, right.kind)
        } else {
          shape_code(left.kind, Some(right.kind))
        };
        let statement = Statement::join(
          &left.statement,
          &right.statement,
          structural,
          &prepared.owner_by_address,
        )?;
        if statement.subjects.count != subject_count {
          return Err("aggregate plan has inconsistent subject counts".into());
        }
        let outer_claim =
          aggregate_outer_claim(aggr_idx, allowed, &statement.claim_bytes);
        let key = cache_key(aggr_vk, cache_fri_bytes, &outer_claim);
        specs.push(SlotSpec {
          op,
          statement,
          subject_count,
          structural,
          kind: ChildKind::Aggr,
          shape: Some(shape),
          outer_claim,
          cache_key: key,
          ram_bytes: shape_ram_bytes(shape, subject_count),
        });
      },
    }
  }
  Ok(specs)
}

fn store_path(root: &Path, address: &Address) -> PathBuf {
  let hex = address.hex();
  root.join(&hex[0..2]).join(&hex[2..4]).join(&hex[4..6]).join(&hex[6..])
}

fn read_store(root: &Path, address: &Address) -> Result<Vec<u8>, String> {
  let path = store_path(root, address);
  fs::read(&path).map_err(|error| format!("read {}: {error}", path.display()))
}

fn write_store(root: &Path, bytes: &[u8]) -> Result<Address, String> {
  let address = Address::hash(bytes);
  let path = store_path(root, &address);
  let parent = path.parent().ok_or("store path has no parent")?;
  fs::create_dir_all(parent)
    .map_err(|error| format!("create {}: {error}", parent.display()))?;
  fs::write(&path, bytes)
    .map_err(|error| format!("write {}: {error}", path.display()))?;
  Ok(address)
}

fn decode_wrapper(bytes: &[u8]) -> Result<IxonProof, String> {
  let mut cursor = bytes;
  let proof = IxonProof::get(&mut cursor)?;
  if !cursor.is_empty() {
    return Err(format!("{} trailing bytes after proof wrapper", cursor.len()));
  }
  Ok(proof)
}

fn load_input_proofs(
  proof_hexes: &str,
  store_dir: &Path,
  prepared: &[PreparedShard],
) -> Result<Vec<Arc<IxonProof>>, String> {
  let values: Vec<&str> =
    proof_hexes.lines().filter(|line| !line.is_empty()).collect();
  if values.len() != prepared.len() {
    return Err(format!(
      "aggregate requires exactly {} shard proofs; got {}",
      prepared.len(),
      values.len()
    ));
  }
  let by_digest: FxHashMap<Address, usize> = prepared
    .iter()
    .enumerate()
    .map(|(index, shard)| (Address::hash(&shard.statement.claim_bytes), index))
    .collect();
  if by_digest.len() != prepared.len() {
    return Err("two reconstructed shard claims have the same digest".into());
  }
  let mut proofs: Vec<Option<Arc<IxonProof>>> = vec![None; prepared.len()];
  for value in values {
    let address = Address::from_hex(value).ok_or_else(|| {
      format!("shard proof is not a 64-character address: {value}")
    })?;
    let bytes = read_store(store_dir, &address)?;
    if Address::hash(&bytes) != address {
      return Err(format!(
        "shard proof store object {} has the wrong digest",
        address.hex()
      ));
    }
    let wrapper = decode_wrapper(&bytes).map_err(|error| {
      format!("decode shard proof {}: {error}", address.hex())
    })?;
    let mut claim_bytes = Vec::new();
    wrapper.claim.put(&mut claim_bytes);
    let digest = Address::hash(&claim_bytes);
    let shard = by_digest.get(&digest).copied().ok_or_else(|| {
      format!("proof {} matches no manifest shard", address.hex())
    })?;
    if wrapper.claim != prepared[shard].statement.claim {
      return Err(format!(
        "proof {} hit a claim-digest collision for shard {}",
        address.hex(),
        prepared[shard].original_id
      ));
    }
    if proofs[shard].is_some() {
      return Err(format!(
        "more than one proof supplied for shard {}",
        prepared[shard].original_id
      ));
    }
    proofs[shard] = Some(Arc::new(wrapper));
  }
  proofs
    .into_iter()
    .enumerate()
    .map(|(index, proof)| {
      proof.ok_or_else(|| {
        format!("no proof supplied for shard {}", prepared[index].original_id)
      })
    })
    .collect()
}

fn cache_address(cache_dir: &Path, key: &Address) -> Option<Address> {
  let path = cache_dir.join(key.hex());
  let raw = fs::read_to_string(path).ok()?;
  Address::from_hex(raw.trim())
}

fn load_cached(
  ctx: ProveContext<'_>,
  slot_index: usize,
  spec: &SlotSpec,
) -> Option<(AiurProof, Address)> {
  let cache_dir = ctx.cache_dir?;
  let address = cache_address(cache_dir, &spec.cache_key)?;
  let reject = |reason: &str| {
    eprintln!(
      "[aggregate] slot {slot_index}: cache miss (wrapper {} rejected: {reason})",
      address.hex()
    );
  };
  let bytes = match read_store(ctx.store_dir, &address) {
    Ok(bytes) => bytes,
    Err(error) => {
      reject(&error);
      return None;
    },
  };
  if Address::hash(&bytes) != address {
    reject("store object has a different content digest");
    return None;
  }
  let wrapper = match decode_wrapper(&bytes) {
    Ok(wrapper) => wrapper,
    Err(error) => {
      reject(&error);
      return None;
    },
  };
  if wrapper.claim != spec.statement.claim {
    reject("bundled claim does not match the expected statement");
    return None;
  }
  let proof = match AiurProof::from_bytes(&wrapper.proof) {
    Ok(proof) => proof,
    Err(error) => {
      reject(&format!("proof deserialization failed: {error}"));
      return None;
    },
  };
  if let Err(error) = ctx.aggr_system.verify(&spec.outer_claim, &proof) {
    reject(&format!("native verification failed: {error:?}"));
    return None;
  }
  eprintln!("[aggregate] slot {slot_index}: cache hit {}", address.hex());
  Some((proof, address))
}

fn wrapper_bytes(
  statement: &Statement,
  proof: &AiurProof,
) -> Result<Vec<u8>, String> {
  let proof_bytes = proof.to_bytes().map_err(|error| {
    format!("aggregate proof serialization failed: {error}")
  })?;
  let wrapper = IxonProof::new(statement.claim.clone(), proof_bytes);
  let mut bytes = Vec::new();
  wrapper.put(&mut bytes);
  Ok(bytes)
}

fn wrapper_address(
  statement: &Statement,
  proof: &AiurProof,
) -> Result<Address, String> {
  Ok(Address::hash(&wrapper_bytes(statement, proof)?))
}

fn persist_wrapper(
  store_dir: &Path,
  statement: &Statement,
  proof: &AiurProof,
) -> Result<Address, String> {
  write_store(store_dir, &statement.claim_bytes)?;
  write_store(store_dir, &wrapper_bytes(statement, proof)?)
}

fn persist_cached(
  ctx: ProveContext<'_>,
  slot_index: usize,
  spec: &SlotSpec,
  proof: &AiurProof,
) -> Option<Address> {
  if !ctx.write_outputs {
    return None;
  }
  let cache_dir = ctx.cache_dir?;
  match (|| -> Result<Address, String> {
    let address = persist_wrapper(ctx.store_dir, &spec.statement, proof)?;
    fs::create_dir_all(cache_dir).map_err(|error| {
      format!("create aggregate cache {}: {error}", cache_dir.display())
    })?;
    let destination = cache_dir.join(spec.cache_key.hex());
    let temporary = cache_dir.join(format!(
      "{}.tmp.{}.{}",
      spec.cache_key.hex(),
      std::process::id(),
      slot_index
    ));
    fs::write(&temporary, format!("{}\n", address.hex())).map_err(|error| {
      format!("write cache index {}: {error}", temporary.display())
    })?;
    fs::rename(&temporary, &destination).map_err(|error| {
      format!(
        "publish cache index {} -> {}: {error}",
        temporary.display(),
        destination.display()
      )
    })?;
    Ok(address)
  })() {
    Ok(address) => {
      eprintln!(
        "[aggregate] slot {slot_index}: cached proof {}",
        address.hex()
      );
      Some(address)
    },
    Err(error) => {
      eprintln!(
        "[aggregate] slot {slot_index}: warning: could not persist cache entry: {error}"
      );
      None
    },
  }
}

struct OwnedTreeAdvice {
  root: [u8; 32],
  bytes: Vec<u8>,
}

fn push_canonical_tree(out: &mut Vec<OwnedTreeAdvice>, tree: &CanonicalTree) {
  out.push(OwnedTreeAdvice {
    root: *tree.root.as_bytes(),
    bytes: tree.serialized().to_vec(),
  });
}

fn path_payload(path: Option<&MerklePath>) -> Result<Vec<u8>, String> {
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

fn tree_advice(
  left: &Statement,
  right: &Statement,
  output: &Statement,
  structural: bool,
) -> Result<Vec<OwnedTreeAdvice>, String> {
  let mut trees = Vec::new();
  if !structural {
    let left_subjects = left
      .subjects
      .canonical_tree()
      .ok_or("flat join has structural left subjects")?;
    push_canonical_tree(&mut trees, left_subjects);
  }
  if let Some(tree) = &left.assumptions {
    push_canonical_tree(&mut trees, tree);
  }
  if !structural {
    let right_subjects = right
      .subjects
      .canonical_tree()
      .ok_or("flat join has structural right subjects")?;
    push_canonical_tree(&mut trees, right_subjects);
  }
  if let Some(tree) = &right.assumptions {
    push_canonical_tree(&mut trees, tree);
  }
  if !structural {
    let output_subjects = output
      .subjects
      .canonical_tree()
      .ok_or("flat join produced structural subjects")?;
    push_canonical_tree(&mut trees, output_subjects);
  }
  if let Some(tree) = &output.assumptions {
    push_canonical_tree(&mut trees, tree);
  }
  Ok(trees)
}

fn structural_path_advice(
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

fn assumption_count(statement: &Statement) -> usize {
  statement.assumptions.as_ref().map_or(0, |tree| tree.leaves.len())
}

fn prove_aggregate(
  ctx: ProveContext<'_>,
  spec: &SlotSpec,
  left: &Slot,
  right: Option<&Slot>,
  slot_index: usize,
) -> Result<(AiurProof, Option<Address>), String> {
  let replaying = ctx.reprove_slot == Some(slot_index);
  if !replaying {
    if let Some((proof, address)) = load_cached(ctx, slot_index, spec) {
      return Ok((proof, Some(address)));
    }
  } else {
    eprintln!(
      "[aggregate] replay slot {slot_index}: bypassing its cache entry"
    );
  }
  let started = Instant::now();

  let left_system = match left.kind {
    ChildKind::Ixvm => ctx.ixvm_system,
    ChildKind::Aggr => ctx.aggr_system,
  };
  let left_advice = left_system
    .proof_to_advice_bytes(&left.outer_claim, &left.proof)
    .map_err(|error| format!("left child proof advice failed: {error:?}"))?;
  let right_advice = if let Some(right) = right {
    let system = match right.kind {
      ChildKind::Ixvm => ctx.ixvm_system,
      ChildKind::Aggr => ctx.aggr_system,
    };
    system
      .proof_to_advice_bytes(&right.outer_claim, &right.proof)
      .map_err(|error| format!("right child proof advice failed: {error:?}"))?
  } else {
    Vec::new()
  };

  let mut preimage_storage = Vec::new();
  if let Some(right) = right {
    preimage_storage.push((
      *blake3::hash(&left.statement.claim_bytes).as_bytes(),
      left.statement.claim_bytes.as_slice(),
    ));
    preimage_storage.push((
      *blake3::hash(&right.statement.claim_bytes).as_bytes(),
      right.statement.claim_bytes.as_slice(),
    ));
  }
  let preimages: Vec<AggrPreimage<'_>> = preimage_storage
    .iter()
    .map(|(digest, bytes)| AggrPreimage { digest: *digest, bytes })
    .collect();

  let (tree_storage, path_storage) = if let Some(right) = right {
    (
      tree_advice(
        &left.statement,
        &right.statement,
        &spec.statement,
        spec.structural,
      )?,
      if spec.structural {
        structural_path_advice(
          &left.statement,
          &right.statement,
          &spec.statement,
          ctx.owner_by_address,
        )?
      } else {
        Vec::new()
      },
    )
  } else {
    (Vec::new(), Vec::new())
  };
  let trees: Vec<AggrTree<'_>> = tree_storage
    .iter()
    .map(|tree| AggrTree { root: tree.root, bytes: &tree.bytes })
    .collect();
  let paths: Vec<AggrPath<'_>> = path_storage
    .iter()
    .map(|(candidate, bytes)| AggrPath {
      candidate: *candidate.as_bytes(),
      bytes,
    })
    .collect();
  let empty = Vec::new();
  let right_claims =
    right.map_or(empty.as_slice(), |slot| slot.claims_bytes.as_slice());
  let shape = spec.shape.ok_or("aggregate proof slot has no shape")?;
  let mut io = aggr_io_buffer(&AggrAdvice {
    shape,
    proof_advice: [&left_advice, &right_advice],
    ixvm_vk: ctx.ixvm_vk,
    self_vk: ctx.aggr_vk,
    child_claims: [&left.claims_bytes, right_claims],
    output_claim: &spec.statement.claim_bytes,
    allowed: ctx.allowed,
    preimages: &preimages,
    trees: &trees,
    paths: &paths,
  });
  let mut public_input = packed_digest(ctx.allowed);
  public_input.extend(packed_digest(&spec.statement.claim_bytes));
  let proving_started = Instant::now();
  let (outer_claim, proof, peak) = match ctx
    .aggr_system
    .prove_ixvm_within_budget(
      ctx.aggr_idx,
      &public_input,
      &mut io,
      execute_ix_aggr,
      None,
      false,
    ) {
    GatedProve::Proved { claim, proof, peak } => (claim, proof, peak),
    GatedProve::Split { .. } | GatedProve::Measured { .. } => {
      return Err("unbudgeted aggregate prove did not produce a proof".into());
    },
  };
  let proved_at = Instant::now();
  if outer_claim != spec.outer_claim {
    return Err("aggregate prover returned an unexpected outer claim".into());
  }
  let address = persist_cached(ctx, slot_index, spec, &proof);
  if replaying {
    let tree_bytes: usize =
      tree_storage.iter().map(|tree| tree.bytes.len()).sum();
    let path_bytes: usize =
      path_storage.iter().map(|(_, path)| path.len()).sum();
    let preimage_bytes: usize =
      preimage_storage.iter().map(|(_, bytes)| bytes.len()).sum();
    let right_assumptions =
      right.map_or(0, |slot| assumption_count(&slot.statement));
    eprintln!(
      "[aggregate] replay slot {slot_index}: shape {shape}, {} subjects, assumptions {}/{}/{}, proof advice {}+{} MiB, {} trees/{} MiB, {} paths/{} MiB, preimages {} MiB, query-record peak {} GiB ({} bytes)",
      spec.subject_count,
      assumption_count(&left.statement),
      right_assumptions,
      assumption_count(&spec.statement),
      format_mib(left_advice.len()),
      format_mib(right_advice.len()),
      tree_storage.len(),
      format_mib(tree_bytes),
      path_storage.len(),
      format_mib(path_bytes),
      format_mib(preimage_bytes),
      format_gib(peak),
      peak,
    );
    eprintln!(
      "[aggregate] replay slot {slot_index}: advice {:.3}s, execute+prove {:.3}s, persistence {:.3}s, total {:.3}s",
      (proving_started - started).as_secs_f64(),
      (proved_at - proving_started).as_secs_f64(),
      proved_at.elapsed().as_secs_f64(),
      started.elapsed().as_secs_f64(),
    );
  }
  Ok((proof, address))
}

fn prove_slot(
  ctx: ProveContext<'_>,
  slot_index: usize,
  children: &[Arc<Slot>],
) -> Result<Arc<Slot>, String> {
  let spec = ctx.specs.get(slot_index).ok_or("missing aggregate slot spec")?;
  match spec.op {
    PlanOp::Leaf(shard) => {
      let prepared = &ctx.prepared[shard];
      let wrapper =
        ctx.proofs.and_then(|proofs| proofs.get(shard)).ok_or_else(|| {
          format!(
            "shard {} proof was not loaded for replay",
            prepared.original_id
          )
        })?;
      let proof = AiurProof::from_bytes(&wrapper.proof).map_err(|error| {
        format!("shard {} proof does not decode: {error}", prepared.original_id)
      })?;
      let inner = inner_claim(ctx.verify_idx, &prepared.statement.claim_bytes);
      ctx.ixvm_system.verify(&inner, &proof).map_err(|error| {
        format!(
          "shard {} proof fails native verification: {error:?}",
          prepared.original_id
        )
      })?;
      let inner_claims = serialize_claims(&[&inner]);
      if spec.kind == ChildKind::Ixvm {
        if spec.outer_claim != inner {
          return Err("direct shard slot has an unexpected outer claim".into());
        }
        return Ok(Arc::new(Slot {
          kind: ChildKind::Ixvm,
          statement: spec.statement.clone(),
          outer_claim: inner,
          proof,
          proof_address: None,
          claims_bytes: inner_claims,
        }));
      }
      eprintln!(
        "[aggregate] wrapping shard {} into slot {slot_index}",
        prepared.original_id
      );
      let raw = Slot {
        kind: ChildKind::Ixvm,
        statement: spec.statement.clone(),
        outer_claim: inner,
        proof,
        proof_address: None,
        claims_bytes: inner_claims,
      };
      let (proof, proof_address) =
        prove_aggregate(ctx, spec, &raw, None, slot_index)?;
      Ok(Arc::new(Slot {
        kind: ChildKind::Aggr,
        statement: spec.statement.clone(),
        outer_claim: spec.outer_claim.clone(),
        proof,
        proof_address,
        claims_bytes: serialize_claims(&[&spec.outer_claim]),
      }))
    },
    PlanOp::Join(left_index, right_index) => {
      if children.len() != 2 {
        return Err("aggregate join did not receive two children".into());
      }
      let left = &children[0];
      let right = &children[1];
      let mode = if spec.structural { "structural" } else { "flat" };
      eprintln!(
        "[aggregate] {mode}-joining slots {left_index}, {right_index} into {slot_index}"
      );
      let (proof, proof_address) =
        prove_aggregate(ctx, spec, left, Some(right), slot_index)?;
      Ok(Arc::new(Slot {
        kind: ChildKind::Aggr,
        statement: spec.statement.clone(),
        outer_claim: spec.outer_claim.clone(),
        proof,
        proof_address,
        claims_bytes: serialize_claims(&[&spec.outer_claim]),
      }))
    },
  }
}

#[derive(Debug, PartialEq, Eq)]
struct ReplayPlan {
  children: Vec<usize>,
  needs_input_proofs: bool,
}

fn plan_replay(
  specs: &[SlotSpec],
  target: usize,
) -> Result<ReplayPlan, String> {
  let spec = specs.get(target).ok_or_else(|| {
    format!(
      "--reprove-slot {target} is out of range; the plan has slots 0..{}",
      specs.len().saturating_sub(1)
    )
  })?;
  if spec.kind == ChildKind::Ixvm {
    return Err(format!(
      "--reprove-slot {target} selects a raw IxVM leaf, not a Stage 2 proof"
    ));
  }
  let children = match spec.op {
    PlanOp::Leaf(_) => Vec::new(),
    PlanOp::Join(left, right) => vec![left, right],
  };
  let needs_input_proofs = children.is_empty()
    || children.iter().any(|index| specs[*index].kind == ChildKind::Ixvm);
  Ok(ReplayPlan { children, needs_input_proofs })
}

fn load_replay_child(
  ctx: ProveContext<'_>,
  target: usize,
  child_index: usize,
) -> Result<Arc<Slot>, String> {
  let spec = ctx
    .specs
    .get(child_index)
    .ok_or("replay target has a missing child slot")?;
  if spec.kind == ChildKind::Ixvm {
    return prove_slot(ctx, child_index, &[]);
  }
  let (proof, proof_address) = load_cached(ctx, child_index, spec).ok_or_else(|| {
    format!(
      "replay slot {target} requires cached child slot {child_index}; run Stage 2 through that child first"
    )
  })?;
  Ok(Arc::new(Slot {
    kind: ChildKind::Aggr,
    statement: spec.statement.clone(),
    outer_claim: spec.outer_claim.clone(),
    proof,
    proof_address: Some(proof_address),
    claims_bytes: serialize_claims(&[&spec.outer_claim]),
  }))
}

fn run_replay(
  ctx: ProveContext<'_>,
  target: usize,
  plan: &ReplayPlan,
) -> Result<String, String> {
  let started = Instant::now();
  eprintln!(
    "[aggregate] replay slot {target}: loading {} immediate child proof(s)",
    plan.children.len()
  );
  let children: Vec<Arc<Slot>> = plan
    .children
    .iter()
    .map(|child| load_replay_child(ctx, target, *child))
    .collect::<Result<_, _>>()?;
  let children_loaded_at = Instant::now();
  let slot = prove_slot(ctx, target, &children)?;
  ctx.aggr_system.verify(&slot.outer_claim, &slot.proof).map_err(|error| {
    format!("replayed slot {target} proof failed verification: {error:?}")
  })?;
  let verified_at = Instant::now();
  let persisted = slot.proof_address.is_some();
  let address = match slot.proof_address.as_ref() {
    Some(address) => address.clone(),
    None => wrapper_address(&slot.statement, &slot.proof)?,
  };
  let disposition = if persisted { "persisted" } else { "not persisted" };
  eprintln!(
    "[aggregate] replay slot {target}: proof {} ({disposition})",
    address.hex()
  );
  eprintln!(
    "[aggregate] replay slot {target}: children {:.3}s, target+verify {:.3}s, address {:.3}s, end-to-end {:.3}s",
    (children_loaded_at - started).as_secs_f64(),
    (verified_at - children_loaded_at).as_secs_f64(),
    verified_at.elapsed().as_secs_f64(),
    started.elapsed().as_secs_f64(),
  );
  Ok(address.hex())
}

fn dependencies_complete(spec: &SlotSpec, completed: &[bool]) -> bool {
  match spec.op {
    PlanOp::Leaf(_) => true,
    PlanOp::Join(left, right) => completed[left] && completed[right],
  }
}

fn run_scheduler(
  ctx: ProveContext<'_>,
  jobs: usize,
  budget: usize,
) -> Result<Vec<Arc<Slot>>, String> {
  if budget == 0 {
    return Err("aggregate scheduler RAM budget must be positive".into());
  }
  let max_jobs = if jobs == 0 { ctx.specs.len().max(1) } else { jobs.max(1) };
  let (sender, receiver) = mpsc::channel();
  thread::scope(|scope| -> Result<Vec<Arc<Slot>>, String> {
    let mut slots: Vec<Option<Arc<Slot>>> = vec![None; ctx.specs.len()];
    let mut completed = vec![false; ctx.specs.len()];
    let mut in_flight = vec![false; ctx.specs.len()];
    let mut completed_count = 0usize;
    let mut active = 0usize;
    let mut reserved = 0usize;
    let mut failures: Vec<(usize, String)> = Vec::new();

    while completed_count < ctx.specs.len() {
      if failures.is_empty() && active < max_jobs {
        let mut ready: Vec<usize> = ctx
          .specs
          .iter()
          .enumerate()
          .filter_map(|(index, spec)| {
            (!completed[index]
              && !in_flight[index]
              && dependencies_complete(spec, &completed))
            .then_some(index)
          })
          .collect();
        ready.sort_unstable_by(|left, right| {
          ctx.specs[*right]
            .ram_bytes
            .cmp(&ctx.specs[*left].ram_bytes)
            .then_with(|| left.cmp(right))
        });
        for index in ready {
          if active >= max_jobs {
            break;
          }
          let weight = ctx.specs[index].ram_bytes;
          let fits = reserved.saturating_add(weight) <= budget;
          if !fits && active != 0 {
            continue;
          }
          let children = match ctx.specs[index].op {
            PlanOp::Leaf(_) => Vec::new(),
            PlanOp::Join(left, right) => vec![
              slots[left].as_ref().expect("completed left slot").clone(),
              slots[right].as_ref().expect("completed right slot").clone(),
            ],
          };
          in_flight[index] = true;
          active += 1;
          reserved = reserved.saturating_add(weight);
          let over =
            if weight > budget { "; over-budget slot runs alone" } else { "" };
          eprintln!(
            "[aggregate] slot {index}: admitted {} GiB; reserved {}/{} GiB; active {active}/{max_jobs}{over}",
            format_gib(weight),
            format_gib(reserved),
            format_gib(budget),
          );
          let sender = sender.clone();
          scope.spawn(move || {
            let result =
              std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                prove_slot(ctx, index, &children)
              }))
              .unwrap_or_else(|payload| {
                Err(format!(
                  "Rust proof worker panicked: {}",
                  panic_text(&payload)
                ))
              });
            let _ = sender.send((index, weight, result));
          });
        }
      }

      if active == 0 {
        if failures.is_empty() {
          failures
            .push((ctx.specs.len(), "aggregate scheduler deadlocked".into()));
        }
        break;
      }

      let (index, weight, result) = receiver.recv().map_err(|error| {
        format!("aggregate scheduler channel closed: {error}")
      })?;
      if !in_flight.get(index).copied().unwrap_or(false) {
        failures.push((index, "duplicate or unknown scheduler result".into()));
        continue;
      }
      in_flight[index] = false;
      active -= 1;
      reserved = reserved.saturating_sub(weight);
      match result {
        Ok(slot) => {
          slots[index] = Some(slot);
          completed[index] = true;
          completed_count += 1;
        },
        Err(error) => failures.push((index, error)),
      }
    }

    while active > 0 {
      let (index, weight, result) = receiver.recv().map_err(|error| {
        format!("aggregate scheduler drain failed: {error}")
      })?;
      if in_flight.get(index).copied().unwrap_or(false) {
        in_flight[index] = false;
        active -= 1;
        reserved = reserved.saturating_sub(weight);
      }
      match result {
        Ok(slot) => {
          slots[index] = Some(slot);
          completed[index] = true;
        },
        Err(error) => failures.push((index, error)),
      }
    }
    if !failures.is_empty() {
      failures.sort_unstable_by_key(|(index, _)| *index);
      let (index, error) = failures.remove(0);
      return Err(if index < ctx.specs.len() {
        format!("slot {index}: {error}")
      } else {
        error
      });
    }
    slots
      .into_iter()
      .enumerate()
      .map(|(index, slot)| {
        slot.ok_or_else(|| format!("scheduler completed without slot {index}"))
      })
      .collect()
  })
}

fn print_plan(
  specs: &[SlotSpec],
  prepared: &[PreparedShard],
  threshold: usize,
) {
  let leaves =
    specs.iter().filter(|spec| matches!(spec.op, PlanOp::Leaf(_))).count();
  let wraps = specs
    .iter()
    .filter(|spec| {
      matches!(spec.op, PlanOp::Leaf(_)) && spec.kind == ChildKind::Aggr
    })
    .count();
  let structural = specs.iter().filter(|spec| spec.structural).count();
  let policy = if wraps == leaves {
    format!("{wraps} wraps")
  } else {
    format!("{} direct IxVM leaves", leaves - wraps)
  };
  eprintln!(
    "[aggregate] plan: {policy} + {} binary joins ({structural} structural; threshold > {threshold} subject leaves)",
    specs.len() - leaves
  );
  for (index, spec) in specs.iter().enumerate() {
    match spec.op {
      PlanOp::Leaf(shard) => {
        let mode =
          if spec.kind == ChildKind::Ixvm { "raw shard" } else { "wrap shard" };
        eprintln!(
          "  slot {index}: {mode} {} ({} subjects)",
          prepared[shard].original_id, spec.subject_count
        );
      },
      PlanOp::Join(left, right) => {
        let mode = if spec.structural { "structural" } else { "flat" };
        eprintln!(
          "  slot {index}: {mode} shape {} slots {left}, {right} ({} subjects)",
          spec.shape.unwrap_or(u8::MAX),
          spec.subject_count
        );
      },
    }
  }
}

fn run(config: RunConfig<'_>) -> Result<String, String> {
  if config.cache_fri_bytes.len() != 40 {
    return Err(format!(
      "aggregate cache FRI serialization is {} bytes, expected 40",
      config.cache_fri_bytes.len()
    ));
  }
  if config.plan_only && config.reprove_slot.is_some() {
    return Err("--plan-only cannot be combined with --reprove-slot".into());
  }
  if config.reprove_slot.is_some() && !config.use_cache {
    return Err("--reprove-slot requires aggregate cache reads".into());
  }
  let started = Instant::now();
  let manifest_bytes = fs::read(config.manifest_path).map_err(|error| {
    format!("read manifest {}: {error}", config.manifest_path.display())
  })?;
  let manifest = ShardManifest::from_bytes(&manifest_bytes)
    .map_err(|error| format!("manifest parse failed: {error}"))?;
  let parsed_at = Instant::now();
  let prepared = prepare_run(&config.env_handle.env, &manifest)?;
  let prepared_at = Instant::now();

  let ixvm_vk = aiur::vk_codec::aiur_system_to_bytes(config.ixvm_system)
    .map_err(|error| format!("IxVM VK serialization failed: {error}"))?;
  let aggr_vk = aiur::vk_codec::aiur_system_to_bytes(config.aggr_system)
    .map_err(|error| format!("ixAggr VK serialization failed: {error}"))?;
  let allowed =
    allowed_blob(&ixvm_vk, config.verify_idx, &aggr_vk, config.aggr_idx);
  let specs = build_specs(
    &prepared,
    config.verify_idx,
    config.aggr_idx,
    config.structural_above,
    config.direct_joins,
    &aggr_vk,
    &allowed,
    config.cache_fri_bytes,
  )?;
  let replay_plan = config
    .reprove_slot
    .map(|target| plan_replay(&specs, target))
    .transpose()?;
  let specs_at = Instant::now();
  print_plan(&specs, &prepared.shards, config.structural_above);
  if config.plan_only {
    eprintln!(
      "[aggregate] Rust plan startup: manifest {:.3}s, env/claims {:.3}s, plan/statements {:.3}s; total {:.3}s",
      (parsed_at - started).as_secs_f64(),
      (prepared_at - parsed_at).as_secs_f64(),
      (specs_at - prepared_at).as_secs_f64(),
      (specs_at - started).as_secs_f64(),
    );
    return Ok(String::new());
  }

  let home = std::env::var_os("HOME").ok_or("no HOME environment variable")?;
  let ix_root = PathBuf::from(home).join(".ix");
  let store_dir = ix_root.join("store");
  let cache_path = ix_root.join("cache").join("aggregate");
  let cache_dir = config.use_cache.then_some(cache_path.as_path());
  if let Some(dir) = cache_dir {
    if config.write_outputs {
      fs::create_dir_all(dir).map_err(|error| {
        format!("create aggregate cache {}: {error}", dir.display())
      })?;
    } else if config.reprove_slot.is_some() && !dir.is_dir() {
      return Err(format!(
        "aggregate replay cache {} does not exist",
        dir.display()
      ));
    }
  } else {
    eprintln!("[aggregate] cache disabled (--no-cache)");
  }
  if !config.write_outputs {
    eprintln!("[aggregate] output writes disabled (--no-write)");
  }
  let needs_input_proofs =
    replay_plan.as_ref().is_none_or(|plan| plan.needs_input_proofs);
  let proofs = if needs_input_proofs {
    Some(load_input_proofs(config.proof_hexes, &store_dir, &prepared.shards)?)
  } else {
    let supplied =
      config.proof_hexes.lines().filter(|line| !line.is_empty()).count();
    eprintln!(
      "[aggregate] replay uses cached aggregate children; skipping {supplied} supplied shard proof wrapper(s)"
    );
    None
  };
  let proofs_at = Instant::now();
  eprintln!(
    "[aggregate] Rust startup: manifest {:.3}s, env/claims {:.3}s, plan/statements {:.3}s, proofs {:.3}s; total {:.3}s",
    (parsed_at - started).as_secs_f64(),
    (prepared_at - parsed_at).as_secs_f64(),
    (specs_at - prepared_at).as_secs_f64(),
    (proofs_at - specs_at).as_secs_f64(),
    (proofs_at - started).as_secs_f64(),
  );
  let context = ProveContext {
    specs: &specs,
    prepared: &prepared.shards,
    proofs: proofs.as_deref(),
    owner_by_address: &prepared.owner_by_address,
    ixvm_system: config.ixvm_system,
    aggr_system: config.aggr_system,
    ixvm_vk: &ixvm_vk,
    aggr_vk: &aggr_vk,
    allowed: &allowed,
    verify_idx: config.verify_idx,
    aggr_idx: config.aggr_idx,
    store_dir: &store_dir,
    cache_dir,
    reprove_slot: config.reprove_slot,
    write_outputs: config.write_outputs,
  };
  if let (Some(target), Some(plan)) =
    (config.reprove_slot, replay_plan.as_ref())
  {
    return run_replay(context, target, plan);
  }

  let jobs_label = if config.jobs == 0 {
    "all ready slots".to_string()
  } else {
    config.jobs.to_string()
  };
  eprintln!(
    "[aggregate] scheduler: jobs={jobs_label}, RAM budget {} GiB; wrap/self 195.0 GiB, direct 390.0 GiB, mixed 340.0 GiB, flat +1 MiB/subject",
    format_gib(config.ram_budget_bytes)
  );
  let slots = run_scheduler(context, config.jobs, config.ram_budget_bytes)?;
  let root = slots.last().ok_or("aggregate plan produced no root slot")?;
  if root.kind != ChildKind::Aggr {
    return Err("aggregate plan produced a raw IxVM root".into());
  }
  if root.statement.subjects.count != prepared.env_count {
    return Err(format!(
      "aggregate root has {} subjects, environment has {}",
      root.statement.subjects.count, prepared.env_count
    ));
  }
  if root.statement.subjects.shards != prepared.expected_shards {
    return Err("aggregate root does not contain every retained shard".into());
  }
  let mut root_leaves = Vec::with_capacity(prepared.env_count);
  root.statement.subjects.collect_leaves(&mut root_leaves);
  root_leaves.sort_unstable();
  root_leaves.dedup();
  let canonical_root = merkle_root_canonical_sorted(&root_leaves)
    .ok_or("aggregate root has no subject leaves")?;
  if canonical_root != prepared.env_root {
    return Err(format!(
      "aggregate root subjects canonicalize to {}, not environment root {}",
      canonical_root.hex(),
      prepared.env_root.hex()
    ));
  }
  if root.statement.assumptions.is_some() {
    return Err("aggregate root retains undischarged assumptions".into());
  }
  config.aggr_system.verify(&root.outer_claim, &root.proof).map_err(
    |error| format!("aggregate root proof failed verification: {error:?}"),
  )?;
  let (address, persisted) = match &root.proof_address {
    Some(address) => (address.clone(), true),
    None if config.write_outputs => {
      (persist_wrapper(&store_dir, &root.statement, &root.proof)?, true)
    },
    None => (wrapper_address(&root.statement, &root.proof)?, false),
  };
  let disposition = if persisted { "" } else { " (not persisted)" };
  eprintln!("[aggregate] root proof: {}{disposition}", address.hex());
  Ok(address.hex())
}

fn panic_text(payload: &Box<dyn std::any::Any + Send>) -> &str {
  payload
    .downcast_ref::<&str>()
    .copied()
    .or_else(|| payload.downcast_ref::<String>().map(String::as_str))
    .unwrap_or("unknown Rust panic")
}

/// Production FFI called once after Lean has compiled the IxVM and ixAggr
/// systems. Proof addresses are newline-separated to keep the ABI flat.
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_stage2_aggregate(
  ixvm_system: LeanExternal<AiurSystem, LeanBorrowed<'_>>,
  aggr_system: LeanExternal<AiurSystem, LeanBorrowed<'_>>,
  env_handle: LeanExternal<EnvHandle, LeanBorrowed<'_>>,
  manifest_path: LeanString<LeanBorrowed<'_>>,
  proof_hexes: LeanString<LeanBorrowed<'_>>,
  verify_idx: LeanNat<LeanBorrowed<'_>>,
  aggr_idx: LeanNat<LeanBorrowed<'_>>,
  jobs: LeanNat<LeanBorrowed<'_>>,
  ram_budget_bytes: LeanNat<LeanBorrowed<'_>>,
  structural_above: LeanNat<LeanBorrowed<'_>>,
  reprove_slot_code: LeanNat<LeanBorrowed<'_>>,
  direct_joins: bool,
  plan_only: bool,
  cache_fri_bytes: LeanByteArray<LeanBorrowed<'_>>,
  use_cache: bool,
  write_outputs: bool,
) -> LeanExcept<LeanOwned> {
  let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
    let reprove_slot =
      lean_unbox_nat_as_usize(reprove_slot_code.inner()).checked_sub(1);
    run(RunConfig {
      ixvm_system: ixvm_system.get(),
      aggr_system: aggr_system.get(),
      env_handle: env_handle.get(),
      manifest_path: Path::new(manifest_path.as_str()),
      proof_hexes: proof_hexes.as_str(),
      verify_idx: lean_unbox_nat_as_usize(verify_idx.inner()),
      aggr_idx: lean_unbox_nat_as_usize(aggr_idx.inner()),
      jobs: lean_unbox_nat_as_usize(jobs.inner()),
      ram_budget_bytes: lean_unbox_nat_as_usize(ram_budget_bytes.inner()),
      structural_above: lean_unbox_nat_as_usize(structural_above.inner()),
      reprove_slot,
      direct_joins,
      plan_only,
      cache_fri_bytes: cache_fri_bytes.as_bytes(),
      use_cache,
      write_outputs,
    })
  }));
  match result {
    Ok(Ok(address)) => LeanExcept::ok(LeanString::new(&address)),
    Ok(Err(error)) => LeanExcept::error_string(&error),
    Err(payload) => LeanExcept::error_string(&format!(
      "native Stage 2 orchestration panicked: {}",
      panic_text(&payload)
    )),
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use ix_kernel::shard::ShardInfo;
  use ixon::{Axiom, Expr};

  fn addr(label: &str) -> Address {
    Address::hash(label.as_bytes())
  }

  #[test]
  fn sorted_merge_is_a_set_union() {
    let a = addr("a");
    let b = addr("b");
    let c = addr("c");
    let mut left = vec![a.clone(), c.clone()];
    let mut right = vec![b.clone(), c.clone()];
    left.sort_unstable();
    right.sort_unstable();
    let merged = merge_sorted(&left, &right);
    assert_eq!(merged.len(), 3);
    assert!(merged.windows(2).all(|window| window[0] < window[1]));
  }

  #[test]
  fn cached_canonical_path_matches_root() {
    let mut leaves: Vec<Address> =
      (0..17).map(|index| addr(&format!("leaf-{index}"))).collect();
    leaves.sort_unstable();
    let tree = CanonicalTree::from_sorted(leaves.clone()).unwrap().unwrap();
    for leaf in leaves {
      let path = tree.merkle_proof(&leaf).expect("member path");
      assert!(ixon::merkle::verify_merkle_proof(&tree.root, &leaf, &path));
    }
  }

  #[test]
  fn structural_path_uses_cached_child_roots() {
    let mut left_leaves = vec![addr("a"), addr("b")];
    let mut right_leaves = vec![addr("c"), addr("d")];
    left_leaves.sort_unstable();
    right_leaves.sort_unstable();
    let left =
      SubjectTree::canonical(left_leaves.clone(), ShardSet::singleton(0, 2))
        .unwrap();
    let right =
      SubjectTree::canonical(right_leaves.clone(), ShardSet::singleton(1, 2))
        .unwrap();
    let joined = SubjectTree::structural(left, right);
    for leaf in left_leaves.iter().chain(&right_leaves) {
      let owner = usize::from(right_leaves.contains(leaf));
      let path = joined.merkle_proof(leaf, owner).expect("member path");
      assert!(ixon::merkle::verify_merkle_proof(&joined.root, leaf, &path));
    }
  }

  #[test]
  fn cache_key_has_a_stable_test_vector() {
    let claim = vec![G::from_u64(1), G::from_u64(2), G::from_u64(3)];
    let key = cache_key(b"vk", &[7; 40], &claim);
    assert_eq!(
      key.hex(),
      "86ed059157e2915fe0a83f1afd58f31f7553659ad778669f6b795e1473e7afe0"
    );
  }

  fn store_axiom(
    env: &ixon::Env,
    typ: Arc<Expr>,
    refs: Vec<Address>,
  ) -> Address {
    let constant = Constant {
      info: ConstantInfo::Axio(Axiom { is_unsafe: false, lvls: 0, typ }),
      sharing: Vec::new(),
      refs,
      univs: Vec::new(),
    };
    let mut bytes = Vec::new();
    constant.put(&mut bytes);
    let address = Address::hash(&bytes);
    env.store_const(address.clone(), constant);
    address
  }

  fn shard(id: u32, block: Address) -> ShardInfo {
    ShardInfo {
      id,
      blocks: vec![block],
      heartbeats: 0,
      own_size: 0,
      foreign_blocks: Vec::new(),
      cross_ingress: 0,
      assumption_root: None,
      measured_peak_bytes: 0,
    }
  }

  #[test]
  fn native_preparation_and_structural_fold_discharge_a_frontier() {
    let env = ixon::Env::new();
    let dependency = store_axiom(&env, Expr::sort(0), Vec::new());
    let consumer = store_axiom(
      &env,
      Expr::reference(0, Vec::new()),
      vec![dependency.clone()],
    );
    let manifest = ShardManifest {
      num_shards: 2,
      shards: vec![shard(0, consumer), shard(1, dependency.clone())],
      total_cross_ingress: 0,
      tree: Some(AggNode::Internal(
        Box::new(AggNode::Leaf(0)),
        Box::new(AggNode::Leaf(1)),
      )),
    };
    let prepared = prepare_run(&env, &manifest).expect("native preparation");
    let specs = build_specs(
      &prepared,
      3,
      5,
      0,
      false,
      b"aggregate-vk",
      b"allowed",
      &[0; 40],
    )
    .expect("native specs");
    assert_eq!(specs.len(), 3);
    assert!(specs[2].structural);
    assert_eq!(specs[2].subject_count, 2);
    assert!(specs[2].statement.assumptions.is_none());
    assert_eq!(
      plan_replay(&specs, 0).unwrap(),
      ReplayPlan { children: Vec::new(), needs_input_proofs: true }
    );
    assert_eq!(
      plan_replay(&specs, 2).unwrap(),
      ReplayPlan { children: vec![0, 1], needs_input_proofs: false }
    );
    assert!(plan_replay(&specs, 3).unwrap_err().contains("out of range"));

    let direct_specs = build_specs(
      &prepared,
      3,
      5,
      0,
      true,
      b"aggregate-vk",
      b"allowed",
      &[0; 40],
    )
    .expect("direct native specs");
    assert!(
      plan_replay(&direct_specs, 0).unwrap_err().contains("raw IxVM leaf")
    );
    assert!(plan_replay(&direct_specs, 2).unwrap().needs_input_proofs);
    let paths = structural_path_advice(
      &specs[0].statement,
      &specs[1].statement,
      &specs[2].statement,
      &prepared.owner_by_address,
    )
    .expect("structural paths");
    assert_eq!(paths.len(), 1);
    assert_eq!(paths[0].0, dependency);
    assert_eq!(paths[0].1.first(), Some(&1));
  }
}
