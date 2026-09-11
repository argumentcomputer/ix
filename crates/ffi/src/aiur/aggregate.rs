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
  G,
  execute::IOBuffer,
  function_channel,
  range::{
    preamble_bytes, proofs_slice_bytes, range_residual, range_statement,
  },
  synthesis::{AiurProof, AiurSystem, GatedProve, PreparedProve},
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
  shard_claim::walk_edges,
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
use multi_stark::{
  p3_field::{PrimeCharacteristicRing, PrimeField64},
  types::ExtVal,
};
use rayon::prelude::*;
use rustc_hash::{FxHashMap, FxHashSet};

use super::lean_unbox_nat_as_usize;
use crate::lean::LeanAiurAggregateExpected;

const CACHE_VERSION: u64 = 2;

/// The range-sum recursion shapes of `ix_aggr` (`Aggr.rangeLeafShape` and
/// friends in `Ix/Aggr.lean`).
const RANGE_LEAF_SHAPE: u8 = 10;
const RANGE_JOIN_SHAPE: u8 = 11;
const RANGE_ROOT_SHAPE: u8 = 12;
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
struct StatementSpec {
  op: PlanOp,
  statement: Arc<Statement>,
  subject_count: usize,
  structural: bool,
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
  /// The prover budget of one slot when its execution is proven as trace
  /// shards; `None` proves every slot unsharded and unbudgeted.
  wrap_budget: Option<usize>,
  /// Wrap a shard proof of more than this many trace shards as a range-sum
  /// tree whose leaves verify at most this many shards each; 0 always wraps
  /// the whole batch in one proof.
  range_width: usize,
  /// How many range-tree nodes prove at once, each under `wrap_budget`.
  range_jobs: usize,
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
  trace_shards: bool,
  range_width: usize,
  /// Wrap the root proof (shape 1) until the final proof is a single
  /// trace shard.
  wrap_root: bool,
  /// Slots preparing (executing) ahead of the provers; `0` fuses
  /// preparation and proving on one worker per slot.
  exec_ahead: usize,
  /// `ix verify --ixes <proofs>`: stop after the proof import — every
  /// shard claim reconstructed natively, every supplied proof bound to its
  /// shard by claim digest and verified in parallel, exactly one per shard
  /// — and report that composed verdict instead of proving.
  verify_only: bool,
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

/// Build the claim-bearing statement at every aggregate slot. This is the
/// shared source of truth for proving and manifest-bound verification: the
/// verifier must not reconstruct the same DAG independently in Lean.
fn build_statement_specs(
  prepared: &PreparedRun,
  structural_above: usize,
) -> Result<Vec<StatementSpec>, String> {
  let shard_by_id: FxHashMap<u32, usize> = prepared
    .shards
    .iter()
    .enumerate()
    .map(|(index, shard)| (shard.original_id, index))
    .collect();
  let mut ops = Vec::new();
  build_plan(&prepared.tree, &shard_by_id, &mut ops)?;
  let mut specs: Vec<StatementSpec> = Vec::with_capacity(ops.len());
  for op in ops {
    match op {
      PlanOp::Leaf(shard) => {
        let prepared_shard = &prepared.shards[shard];
        specs.push(StatementSpec {
          op,
          statement: prepared_shard.statement.clone(),
          subject_count: prepared_shard.statement.subjects.count,
          structural: false,
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
        let statement = Statement::join(
          &left.statement,
          &right.statement,
          structural,
          &prepared.owner_by_address,
        )?;
        if statement.subjects.count != subject_count {
          return Err("aggregate plan has inconsistent subject counts".into());
        }
        specs.push(StatementSpec { op, statement, subject_count, structural });
      },
    }
  }
  Ok(specs)
}

/// Check the semantic certificate attached to the root statement independently
/// of any proof: every environment constant occurs exactly once, every retained
/// shard contributes, the canonicalized subject root is the environment root,
/// and no assumption survives.
fn validate_root_statement(
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

fn expected_from_manifest(
  env: &ixon::Env,
  manifest: &ShardManifest,
  structural_above: usize,
) -> Result<(Arc<Statement>, usize), String> {
  let prepared = prepare_run(env, manifest)?;
  let specs = build_statement_specs(&prepared, structural_above)?;
  let root = specs
    .last()
    .ok_or("aggregate manifest produced no root statement")?
    .statement
    .clone();
  validate_root_statement(&prepared, &root)?;
  Ok((root, prepared.env_count))
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
  let statement_specs = build_statement_specs(prepared, structural_above)?;
  let raw_leaves = direct_joins && statement_specs.len() > 1;
  let mut specs: Vec<SlotSpec> = Vec::with_capacity(statement_specs.len());
  for statement_spec in statement_specs {
    let StatementSpec { op, statement, subject_count, structural } =
      statement_spec;
    match op {
      PlanOp::Leaf(_) => {
        let kind = if raw_leaves { ChildKind::Ixvm } else { ChildKind::Aggr };
        let shape = (!raw_leaves).then_some(shape_code(ChildKind::Ixvm, None));
        let outer_claim = if raw_leaves {
          inner_claim(verify_idx, &statement.claim_bytes)
        } else {
          aggregate_outer_claim(aggr_idx, allowed, &statement.claim_bytes)
        };
        let key = cache_key(aggr_vk, cache_fri_bytes, &outer_claim);
        specs.push(SlotSpec {
          op,
          statement,
          subject_count,
          structural,
          kind,
          shape,
          outer_claim,
          cache_key: key,
          ram_bytes: shape.map_or(RAW_SHARD_RAM_BYTES, |value| {
            shape_ram_bytes(value, subject_count)
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
        let shape = if structural {
          structural_shape_code(left.kind, right.kind)
        } else {
          shape_code(left.kind, Some(right.kind))
        };
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

pub(crate) fn write_store(
  root: &Path,
  bytes: &[u8],
) -> Result<Address, String> {
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

/// A slot executed and planned, waiting for the prover.
struct PreparedAggregate {
  slot_index: usize,
  prepared: PreparedProve,
  started: Instant,
  proving_started: Instant,
  /// The replayed slot's advice diagnostics, printed once it is proven.
  replay: Option<String>,
}

/// What preparing a slot yields: its proof straight from the cache, or its
/// execution waiting for the prover.
enum Staged {
  Cached(Box<AiurProof>, Address),
  Prepared(Box<PreparedAggregate>),
}

/// The execution half of [`prove_aggregate`]: the cache probe, both
/// children's advice, the trees and paths, then the `ix_aggr` execution
/// planned within the slot budget. CPU work only, so one slot can prepare
/// while another proves.
fn prepare_aggregate(
  ctx: ProveContext<'_>,
  spec: &SlotSpec,
  left: &Slot,
  right: Option<&Slot>,
  slot_index: usize,
) -> Result<Staged, String> {
  let replaying = ctx.reprove_slot == Some(slot_index);
  if !replaying {
    if let Some((proof, address)) = load_cached(ctx, slot_index, spec) {
      return Ok(Staged::Cached(Box::new(proof), address));
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
  let prepared = prepare_aggr_io(
    ctx,
    &mut io,
    &public_input,
    &format!("slot {slot_index}"),
  )?;
  let replay = replaying.then(|| {
    let tree_bytes: usize =
      tree_storage.iter().map(|tree| tree.bytes.len()).sum();
    let path_bytes: usize =
      path_storage.iter().map(|(_, path)| path.len()).sum();
    let preimage_bytes: usize =
      preimage_storage.iter().map(|(_, bytes)| bytes.len()).sum();
    let right_assumptions =
      right.map_or(0, |slot| assumption_count(&slot.statement));
    format!(
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
      format_gib(prepared.peak),
      prepared.peak,
    )
  });
  Ok(Staged::Prepared(Box::new(PreparedAggregate {
    slot_index,
    prepared,
    started,
    proving_started,
    replay,
  })))
}

/// The proving half of [`prove_aggregate`]: the STARK, the outer-claim
/// check and persistence.
fn finish_aggregate(
  ctx: ProveContext<'_>,
  staged: Staged,
) -> Result<(AiurProof, Option<Address>), String> {
  let PreparedAggregate {
    slot_index,
    prepared,
    started,
    proving_started,
    replay,
  } = match staged {
    Staged::Cached(proof, address) => return Ok((*proof, Some(address))),
    Staged::Prepared(prepared) => *prepared,
  };
  let spec = ctx.specs.get(slot_index).ok_or("missing aggregate slot spec")?;
  let (outer_claim, proof, _) = finish_aggr_io(ctx, prepared);
  let proved_at = Instant::now();
  if outer_claim != spec.outer_claim {
    return Err("aggregate prover returned an unexpected outer claim".into());
  }
  let address = persist_cached(ctx, slot_index, spec, &proof);
  if let Some(line) = replay {
    eprintln!("{line}");
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

/// Execute and prove one `ix_aggr` invocation over its advice buffer, as
/// trace shards within the slot budget when the run has one.
fn prove_aggr_io(
  ctx: ProveContext<'_>,
  io: &mut IOBuffer,
  public_input: &[G],
  label: &str,
) -> Result<(Vec<G>, AiurProof, usize), String> {
  let prepared = prepare_aggr_io(ctx, io, public_input, label)?;
  Ok(finish_aggr_io(ctx, prepared))
}

/// The execution half of [`prove_aggr_io`]: executes the invocation, gates
/// and plans it within the slot budget, and returns what
/// [`finish_aggr_io`] proves from, so one node can execute while another
/// proves.
fn prepare_aggr_io(
  ctx: ProveContext<'_>,
  io: &mut IOBuffer,
  public_input: &[G],
  label: &str,
) -> Result<PreparedProve, String> {
  match ctx.aggr_system.prepare_ixvm_within_budget(
    ctx.aggr_idx,
    public_input,
    io,
    execute_ix_aggr,
    ctx.wrap_budget,
    ctx.wrap_budget.is_some(),
    None,
  ) {
    Ok(prepared) => Ok(prepared),
    Err(GatedProve::Split { peak, .. }) => Err(format!(
      "{OVER_SLOT_BUDGET}{label}: no trace-shard count fits the {} B budget \
       (whole-execution peak {peak} B) — raise --max-ram",
      ctx.wrap_budget.unwrap_or(0)
    )),
    Err(_) => Err(format!("{label}: aggregate prove did not produce a proof")),
  }
}

/// Prefix of the error [`prepare_aggr_io`] returns when a node's execution
/// does not fit the slot budget, so callers can tell that outcome apart.
const OVER_SLOT_BUDGET: &str = "over the slot budget: ";

/// The proving half of [`prove_aggr_io`].
fn finish_aggr_io(
  ctx: ProveContext<'_>,
  prepared: PreparedProve,
) -> (Vec<G>, AiurProof, usize) {
  ctx.aggr_system.prove_prepared(prepared)
}

/// One proven node of a range-sum tree: shards `[lo, hi)` of the batch and
/// their residual sum, stated by `statement` (`aiur::range::range_statement`).
struct RangeNode {
  lo: usize,
  hi: usize,
  residual: ExtVal,
  statement: Vec<u8>,
  outer_claim: Vec<G>,
  proof: AiurProof,
}

/// A range-tree node executed and planned, waiting for the prover.
struct PreparedNode {
  lo: usize,
  hi: usize,
  residual: ExtVal,
  statement: Vec<u8>,
  kind: &'static str,
  started: Instant,
  prepared: PreparedProve,
}

/// Prove every item of one tree level. With one job the level is a
/// pipeline: a producer thread executes and plans item `k + 1` while this
/// thread proves item `k`, at most one node ahead (a rendezvous channel), so
/// the prover never waits for an execution it could have overlapped. With
/// more jobs, that many items execute and prove at once.
fn prove_range_level<T, P, F>(
  items: Vec<T>,
  jobs: usize,
  prepare: &P,
  finish: &F,
) -> Result<Vec<RangeNode>, String>
where
  T: Send,
  P: Fn(T) -> Result<PreparedNode, String> + Sync,
  F: Fn(PreparedNode) -> Result<RangeNode, String> + Sync,
{
  if jobs <= 1 {
    let span = tracing::Span::current();
    return thread::scope(|scope| {
      let (sender, receiver) =
        mpsc::sync_channel::<Result<PreparedNode, String>>(0);
      let producer = scope.spawn(move || {
        let _g = span.entered();
        for item in items {
          let prepared = prepare(item);
          let failed = prepared.is_err();
          if sender.send(prepared).is_err() || failed {
            break;
          }
        }
      });
      let mut nodes = Vec::new();
      let mut outcome = Ok(());
      for prepared in receiver {
        match prepared.and_then(finish) {
          Ok(node) => nodes.push(node),
          Err(error) => {
            outcome = Err(error);
            break;
          },
        }
      }
      // Dropping the receiver stops the producer at its next send.
      producer.join().map_err(|payload| {
        format!("range node preparation panicked: {}", panic_text(&payload))
      })?;
      outcome.map(|()| nodes)
    });
  }
  let mut nodes = Vec::with_capacity(items.len());
  let mut pending = items.into_iter().peekable();
  while pending.peek().is_some() {
    let batch: Vec<T> = pending.by_ref().take(jobs).collect();
    let proven: Vec<Result<RangeNode, String>> = thread::scope(|scope| {
      let handles: Vec<_> = batch
        .into_iter()
        .map(|item| scope.spawn(move || prepare(item).and_then(finish)))
        .collect();
      handles
        .into_iter()
        .map(|handle| {
          handle.join().unwrap_or_else(|payload| {
            Err(format!("range node panicked: {}", panic_text(&payload)))
          })
        })
        .collect()
    });
    for node in proven {
      nodes.push(node?);
    }
  }
  Ok(nodes)
}

/// Wrap a shard proof of many trace shards as a range-sum tree: leaves of at
/// most `range_width` shards, joins of adjacent ranges, and a root whose
/// statement is exactly the wrap's, so the slot's cache entry and every
/// consumer are unchanged.
fn prove_range_tree(
  ctx: ProveContext<'_>,
  spec: &SlotSpec,
  batch: &AiurProof,
  slot_index: usize,
) -> Result<(AiurProof, Option<Address>), String> {
  if ctx.reprove_slot != Some(slot_index)
    && let Some((proof, address)) = load_cached(ctx, slot_index, spec)
  {
    return Ok((proof, Some(address)));
  }
  let started = Instant::now();
  let shards = batch.preamble.headers.len();
  // No requested width: two leaves per node slot, so a slot's pipeline
  // always has a next leaf to execute while it proves one, and each leaf
  // is as large as that allows; a leaf over the slot budget fails its
  // gate, and a derived width is halved until the leaves fit.
  let mut width = if ctx.range_width > 0 {
    ctx.range_width
  } else {
    shards.div_ceil(2 * ctx.range_jobs.max(1)).max(1)
  };
  let preamble = preamble_bytes(batch)?;
  let digest = *blake3::hash(&preamble).as_bytes();
  let leaves_of = |width: usize| -> Vec<(usize, usize)> {
    (0..shards)
      .step_by(width)
      .map(|lo| (lo, (lo + width).min(shards)))
      .collect()
  };
  eprintln!(
    "[aggregate] slot {slot_index}: range tree over {shards} shards: {} leaves of at most {width} shards, {} at a time",
    leaves_of(width).len(),
    ctx.range_jobs
  );
  let self_claims = |node: &RangeNode| serialize_claims(&[&node.outer_claim]);
  let child_advice = |node: &RangeNode| -> Result<Vec<u8>, String> {
    ctx
      .aggr_system
      .proof_to_advice_bytes(&node.outer_claim, &node.proof)
      .map_err(|error| {
        format!(
          "slot {slot_index}: range node {}..{} proof advice failed: {error}",
          node.lo, node.hi
        )
      })
  };
  let prepare_node = |shape: u8,
                      lo: usize,
                      hi: usize,
                      residual: ExtVal,
                      proof_advice: [&[u8]; 2],
                      child_claims: [&[u8]; 2],
                      preimages: &[AggrPreimage<'_>]|
   -> Result<PreparedNode, String> {
    let node_started = Instant::now();
    let statement = range_statement(&digest, lo, hi, residual);
    let mut io = aggr_io_buffer(&AggrAdvice {
      shape,
      proof_advice,
      ixvm_vk: ctx.ixvm_vk,
      self_vk: ctx.aggr_vk,
      child_claims,
      output_claim: &statement,
      allowed: ctx.allowed,
      preimages,
      trees: &[],
      paths: &[],
    });
    let mut public_input = packed_digest(ctx.allowed);
    public_input.extend(packed_digest(&statement));
    let kind = if shape == RANGE_LEAF_SHAPE { "leaf" } else { "join" };
    let prepared = prepare_aggr_io(
      ctx,
      &mut io,
      &public_input,
      &format!("slot {slot_index} range {kind} {lo}..{hi}"),
    )?;
    eprintln!(
      "[aggregate] slot {slot_index}: range {kind} {lo}..{hi} executed in {:.1}s",
      node_started.elapsed().as_secs_f64()
    );
    Ok(PreparedNode {
      lo,
      hi,
      residual,
      statement,
      kind,
      started: node_started,
      prepared,
    })
  };
  let finish_node = |node: PreparedNode| -> Result<RangeNode, String> {
    let PreparedNode { lo, hi, residual, statement, kind, started, prepared } =
      node;
    let (outer_claim, proof, peak) = finish_aggr_io(ctx, prepared);
    eprintln!(
      "[aggregate] slot {slot_index}: range {kind} {lo}..{hi} proven in {:.1}s (query-record peak {} GiB)",
      started.elapsed().as_secs_f64(),
      format_gib(peak)
    );
    Ok(RangeNode { lo, hi, residual, statement, outer_claim, proof })
  };

  let prove_leaves = |width: usize| {
    prove_range_level(
      leaves_of(width),
      ctx.range_jobs,
      &|(lo, hi)| {
        let proofs = proofs_slice_bytes(batch, lo, hi)?;
        prepare_node(
          RANGE_LEAF_SHAPE,
          lo,
          hi,
          range_residual(batch, lo, hi),
          [&preamble, &proofs],
          [&[], &[]],
          &[],
        )
      },
      &finish_node,
    )
  };
  let mut nodes = loop {
    match prove_leaves(width) {
      Ok(nodes) => break nodes,
      Err(error)
        if ctx.range_width == 0
          && width > 1
          && error.starts_with(OVER_SLOT_BUDGET) =>
      {
        width /= 2;
        eprintln!(
          "[aggregate] slot {slot_index}: a leaf did not fit the slot budget; retrying with leaves of at most {width} shards"
        );
      },
      Err(error) => return Err(error),
    }
  };
  while nodes.len() > 1 {
    let mut pairs = Vec::with_capacity(nodes.len().div_ceil(2));
    let mut carried = None;
    let mut pending = nodes.into_iter();
    while let Some(left) = pending.next() {
      match pending.next() {
        Some(right) => pairs.push((left, right)),
        None => carried = Some(left),
      }
    }
    nodes = prove_range_level(
      pairs,
      ctx.range_jobs,
      &|(left, right)| {
        let advice = [child_advice(&left)?, child_advice(&right)?];
        let claims = [self_claims(&left), self_claims(&right)];
        let preimages = [
          AggrPreimage {
            digest: *blake3::hash(&left.statement).as_bytes(),
            bytes: &left.statement,
          },
          AggrPreimage {
            digest: *blake3::hash(&right.statement).as_bytes(),
            bytes: &right.statement,
          },
        ];
        prepare_node(
          RANGE_JOIN_SHAPE,
          left.lo,
          right.hi,
          left.residual + right.residual,
          [&advice[0], &advice[1]],
          [&claims[0], &claims[1]],
          &preimages,
        )
      },
      &finish_node,
    )?;
    // An unpaired last node joins at the next level, keeping ranges in
    // shard order.
    nodes.extend(carried);
  }
  let node = nodes.pop().ok_or("range tree has no root")?;

  let root_started = Instant::now();
  let advice = child_advice(&node)?;
  let claims = self_claims(&node);
  let preimages = [AggrPreimage {
    digest: *blake3::hash(&node.statement).as_bytes(),
    bytes: &node.statement,
  }];
  let mut io = aggr_io_buffer(&AggrAdvice {
    shape: RANGE_ROOT_SHAPE,
    proof_advice: [&advice, &preamble],
    ixvm_vk: ctx.ixvm_vk,
    self_vk: ctx.aggr_vk,
    child_claims: [&claims, &[]],
    output_claim: &spec.statement.claim_bytes,
    allowed: ctx.allowed,
    preimages: &preimages,
    trees: &[],
    paths: &[],
  });
  let mut public_input = packed_digest(ctx.allowed);
  public_input.extend(packed_digest(&spec.statement.claim_bytes));
  let (outer_claim, proof, peak) = prove_aggr_io(
    ctx,
    &mut io,
    &public_input,
    &format!("slot {slot_index} range root"),
  )?;
  if outer_claim != spec.outer_claim {
    return Err("range root returned an unexpected outer claim".into());
  }
  eprintln!(
    "[aggregate] slot {slot_index}: range root proven in {:.1}s (query-record peak {} GiB); range tree total {:.1}s",
    root_started.elapsed().as_secs_f64(),
    format_gib(peak),
    started.elapsed().as_secs_f64()
  );
  let address = persist_cached(ctx, slot_index, spec, &proof);
  Ok((proof, address))
}

/// Wraps `proof`, a proof of `root`'s claim, once more: shape 1 verifies
/// one `ix_aggr` proof and passes its statement through, so a root that is
/// a batch of trace shards (a direct join) ends as a smaller proof of the
/// same claim.
fn wrap_root(
  ctx: ProveContext<'_>,
  root: &Slot,
  proof: &AiurProof,
) -> Result<AiurProof, String> {
  let started = Instant::now();
  let advice_shards = proof.preamble.headers.len();
  let advice = ctx
    .aggr_system
    .proof_to_advice_bytes(&root.outer_claim, proof)
    .map_err(|error| format!("root proof advice failed: {error}"))?;
  let mut io = aggr_io_buffer(&AggrAdvice {
    shape: shape_code(ChildKind::Aggr, None),
    proof_advice: [&advice, &[]],
    ixvm_vk: ctx.ixvm_vk,
    self_vk: ctx.aggr_vk,
    child_claims: [&root.claims_bytes, &[]],
    output_claim: &root.statement.claim_bytes,
    allowed: ctx.allowed,
    preimages: &[],
    trees: &[],
    paths: &[],
  });
  let mut public_input = packed_digest(ctx.allowed);
  public_input.extend(packed_digest(&root.statement.claim_bytes));
  let (outer_claim, proof, peak) =
    prove_aggr_io(ctx, &mut io, &public_input, "root wrap")?;
  if outer_claim != root.outer_claim {
    return Err("root wrap returned an unexpected outer claim".into());
  }
  eprintln!(
    "[aggregate] root wrap proven in {:.1}s (query-record peak {} GiB): {} shard(s) verified into {}",
    started.elapsed().as_secs_f64(),
    format_gib(peak),
    advice_shards,
    proof.preamble.headers.len()
  );
  Ok(proof)
}

/// Verifies raw shard `shard` of slot `slot_index` natively and returns it
/// as a raw IxVM slot (the child a direct join takes, or what a wrap-first
/// leaf wraps).
fn verify_leaf(
  ctx: ProveContext<'_>,
  slot_index: usize,
  shard: usize,
) -> Result<Slot, String> {
  let spec = ctx.specs.get(slot_index).ok_or("missing aggregate slot spec")?;
  let prepared = &ctx.prepared[shard];
  let wrapper =
    ctx.proofs.and_then(|proofs| proofs.get(shard)).ok_or_else(|| {
      format!("shard {} proof was not loaded for replay", prepared.original_id)
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
  if spec.kind == ChildKind::Ixvm && spec.outer_claim != inner {
    return Err("direct shard slot has an unexpected outer claim".into());
  }
  Ok(Slot {
    kind: ChildKind::Ixvm,
    statement: spec.statement.clone(),
    outer_claim: inner,
    proof,
    proof_address: None,
    claims_bytes: inner_claims,
  })
}

/// A slot prepared for the prover: complete already (a raw leaf verified,
/// a cached proof), a wrap-first leaf whose batch becomes a range tree
/// (executed and proven together), or an execution waiting for its STARK
/// (a wrap or a join).
enum StagedSlot {
  Done(Arc<Slot>),
  Range(Box<Slot>),
  Staged(Staged),
}

/// The execution half of [`prove_slot`]: verification and, for a wrap or
/// a join, the `ix_aggr` execution planned within the slot budget. No
/// proving happens here, so it can run beside the prover.
fn prepare_slot(
  ctx: ProveContext<'_>,
  slot_index: usize,
  children: &[Arc<Slot>],
) -> Result<StagedSlot, String> {
  let spec = ctx.specs.get(slot_index).ok_or("missing aggregate slot spec")?;
  match spec.op {
    PlanOp::Leaf(shard) => {
      let raw = verify_leaf(ctx, slot_index, shard)?;
      if spec.kind == ChildKind::Ixvm {
        return Ok(StagedSlot::Done(Arc::new(raw)));
      }
      eprintln!(
        "[aggregate] wrapping shard {} into slot {slot_index}",
        ctx.prepared[shard].original_id
      );
      // A batch of several shards becomes a range tree: leaves of the
      // requested width, or of the derived width (as few leaves as there
      // are node slots) when none was requested and slots are budgeted.
      let shards = raw.proof.preamble.headers.len();
      let ranged = shards > 1
        && (ctx.range_width > 0 && shards > ctx.range_width
          || ctx.range_width == 0 && ctx.wrap_budget.is_some());
      if ranged {
        return Ok(StagedSlot::Range(Box::new(raw)));
      }
      let staged = prepare_aggregate(ctx, spec, &raw, None, slot_index)?;
      Ok(StagedSlot::Staged(staged))
    },
    PlanOp::Join(left_index, right_index) => {
      if children.len() != 2 {
        return Err("aggregate join did not receive two children".into());
      }
      let mode = if spec.structural { "structural" } else { "flat" };
      eprintln!(
        "[aggregate] {mode}-joining slots {left_index}, {right_index} into {slot_index}"
      );
      let staged = prepare_aggregate(
        ctx,
        spec,
        &children[0],
        Some(&children[1]),
        slot_index,
      )?;
      Ok(StagedSlot::Staged(staged))
    },
  }
}

/// The proving half of [`prove_slot`].
fn finish_slot(
  ctx: ProveContext<'_>,
  slot_index: usize,
  staged: StagedSlot,
) -> Result<Arc<Slot>, String> {
  let spec = ctx.specs.get(slot_index).ok_or("missing aggregate slot spec")?;
  let (proof, proof_address) = match staged {
    StagedSlot::Done(slot) => return Ok(slot),
    StagedSlot::Range(raw) => {
      prove_range_tree(ctx, spec, &raw.proof, slot_index)?
    },
    StagedSlot::Staged(staged) => finish_aggregate(ctx, staged)?,
  };
  Ok(Arc::new(Slot {
    kind: ChildKind::Aggr,
    statement: spec.statement.clone(),
    outer_claim: spec.outer_claim.clone(),
    proof,
    proof_address,
    claims_bytes: serialize_claims(&[&spec.outer_claim]),
  }))
}

/// Prepares and proves one slot in place.
fn prove_slot(
  ctx: ProveContext<'_>,
  slot_index: usize,
  children: &[Arc<Slot>],
) -> Result<Arc<Slot>, String> {
  let staged = prepare_slot(ctx, slot_index, children)?;
  finish_slot(ctx, slot_index, staged)
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

/// What a scheduler worker reports: a slot prepared (or found complete
/// while preparing), or a slot proven.
enum SchedulerEvent {
  /// A slot prepared (the flag: it was a verify-only leaf).
  Prepared(usize, bool, Result<StagedSlot, String>),
  Finished(usize, Result<Arc<Slot>, String>),
}

/// Runs the slot plan with two lanes: `ahead` workers prepare ready slots
/// (children complete) — the CPU half: advice, execution, planning —
/// while `jobs` workers prove prepared slots — the GPU half — so a join
/// executes while the previous one proves. `ahead == 0` fuses the lanes:
/// each admitted slot prepares and proves on one worker, `jobs` at a
/// time. Slots are admitted bottom level first, then by index, so parents
/// become ready as early as possible; the RAM weights gate admission as
/// before, a slot's weight held from admission to completion.
fn run_scheduler(
  ctx: ProveContext<'_>,
  jobs: usize,
  ahead: usize,
  budget: usize,
) -> Result<Vec<Arc<Slot>>, String> {
  if budget == 0 {
    return Err("aggregate scheduler RAM budget must be positive".into());
  }
  let count = ctx.specs.len();
  let max_jobs = if jobs == 0 { count.max(1) } else { jobs.max(1) };
  let fused = ahead == 0;
  let max_ahead = if fused { max_jobs } else { ahead };
  // Raw leaves only verify: they hold no record and take no prover, so
  // they run beside both lanes, a core each.
  let max_verify = thread::available_parallelism().map_or(1, usize::from);
  // With trace shards each slot is held to its share of the budget inside
  // its proof; the static per-shape weights describe whole CPU proofs and
  // would keep every slot alone, so they gate nothing on that path.
  let weight_of = |index: usize| {
    if ctx.wrap_budget.is_some() { 0 } else { ctx.specs[index].ram_bytes }
  };
  let verify_only = |index: usize| {
    matches!(ctx.specs[index].op, PlanOp::Leaf(_))
      && ctx.specs[index].kind == ChildKind::Ixvm
  };
  let mut level = vec![0usize; count];
  for (index, spec) in ctx.specs.iter().enumerate() {
    if let PlanOp::Join(left, right) = spec.op {
      level[index] = 1 + level[left].max(level[right]);
    }
  }
  let (sender, receiver) = mpsc::channel::<SchedulerEvent>();
  thread::scope(|scope| -> Result<Vec<Arc<Slot>>, String> {
    let mut slots: Vec<Option<Arc<Slot>>> = vec![None; count];
    let mut completed = vec![false; count];
    let mut admitted = vec![false; count];
    let mut completed_count = 0usize;
    let mut verifying = 0usize;
    let mut preparing = 0usize;
    let mut proving = 0usize;
    let mut reserved = 0usize;
    let mut prepared: std::collections::VecDeque<(usize, StagedSlot)> =
      std::collections::VecDeque::new();
    let mut failures: Vec<(usize, String)> = Vec::new();

    while completed_count < count {
      if failures.is_empty() {
        // Prover lane first: prepared slots, in the order prepared.
        while proving < max_jobs {
          let Some((index, staged)) = prepared.pop_front() else { break };
          proving += 1;
          let sender = sender.clone();
          scope.spawn(move || {
            let result =
              std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                finish_slot(ctx, index, staged)
              }))
              .unwrap_or_else(|payload| {
                Err(format!(
                  "Rust proof worker panicked: {}",
                  panic_text(&payload)
                ))
              });
            let _ = sender.send(SchedulerEvent::Finished(index, result));
          });
        }
        // Prepare lane: ready slots, bottom level first; a prepared record
        // waiting for the prover counts against the lookahead, and raw
        // leaves have their own allowance.
        let mut ready: Vec<usize> = (0..count)
          .filter(|&index| {
            !admitted[index]
              && dependencies_complete(&ctx.specs[index], &completed)
          })
          .collect();
        ready.sort_unstable_by_key(|&index| (level[index], index));
        for index in ready {
          let verify = verify_only(index);
          if verify {
            if verifying >= max_verify {
              continue;
            }
          } else if preparing + prepared.len() >= max_ahead {
            continue;
          }
          let weight = weight_of(index);
          let fits = reserved.saturating_add(weight) <= budget;
          if !fits && verifying + preparing + proving + prepared.len() != 0 {
            continue;
          }
          let children = match ctx.specs[index].op {
            PlanOp::Leaf(_) => Vec::new(),
            PlanOp::Join(left, right) => vec![
              slots[left].as_ref().expect("completed left slot").clone(),
              slots[right].as_ref().expect("completed right slot").clone(),
            ],
          };
          admitted[index] = true;
          if verify {
            verifying += 1;
          } else {
            preparing += 1;
          }
          reserved = reserved.saturating_add(weight);
          if !verify {
            let over = if weight > budget {
              "; over-budget slot runs alone"
            } else {
              ""
            };
            eprintln!(
              "[aggregate] slot {index}: admitted {} GiB; reserved {}/{} GiB; preparing {preparing}/{max_ahead} (queued {}), proving {proving}/{max_jobs}{over}",
              format_gib(weight),
              format_gib(reserved),
              format_gib(budget),
              prepared.len(),
            );
          }
          let sender = sender.clone();
          scope.spawn(move || {
            let result =
              std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let staged = prepare_slot(ctx, index, &children)?;
                if fused {
                  return finish_slot(ctx, index, staged).map(StagedSlot::Done);
                }
                Ok(staged)
              }))
              .unwrap_or_else(|payload| {
                Err(format!(
                  "Rust proof worker panicked: {}",
                  panic_text(&payload)
                ))
              });
            let _ =
              sender.send(SchedulerEvent::Prepared(index, verify, result));
          });
        }
      }

      if verifying + preparing + proving == 0 {
        if failures.is_empty() {
          if !prepared.is_empty() {
            continue;
          }
          failures.push((count, "aggregate scheduler deadlocked".into()));
        }
        break;
      }

      let event = receiver.recv().map_err(|error| {
        format!("aggregate scheduler channel closed: {error}")
      })?;
      let (index, outcome) = match event {
        SchedulerEvent::Prepared(index, verify, result) => {
          if verify {
            verifying -= 1;
          } else {
            preparing -= 1;
          }
          match result {
            Ok(StagedSlot::Done(slot)) => (index, Ok(slot)),
            Ok(staged) => {
              eprintln!(
                "[aggregate] slot {index}: prepared, waiting for the prover ({} queued)",
                prepared.len() + 1
              );
              prepared.push_back((index, staged));
              continue;
            },
            Err(error) => (index, Err(error)),
          }
        },
        SchedulerEvent::Finished(index, result) => {
          proving -= 1;
          (index, result)
        },
      };
      reserved = reserved.saturating_sub(weight_of(index));
      match outcome {
        Ok(slot) => {
          slots[index] = Some(slot);
          completed[index] = true;
          completed_count += 1;
        },
        Err(error) => failures.push((index, error)),
      }
    }

    // A failure stops admission; what is running finishes, what is
    // prepared and unproven is dropped.
    while verifying + preparing + proving > 0 {
      let event = receiver.recv().map_err(|error| {
        format!("aggregate scheduler drain failed: {error}")
      })?;
      let (index, outcome) = match event {
        SchedulerEvent::Prepared(index, verify, result) => {
          if verify {
            verifying -= 1;
          } else {
            preparing -= 1;
          }
          match result {
            Ok(StagedSlot::Done(slot)) => (index, Ok(slot)),
            Ok(_) => continue,
            Err(error) => (index, Err(error)),
          }
        },
        SchedulerEvent::Finished(index, result) => {
          proving -= 1;
          (index, result)
        },
      };
      match outcome {
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
      return Err(if index < count {
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
  if !config.verify_only {
    print_plan(&specs, &prepared.shards, config.structural_above);
  }
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
  } else if !config.verify_only {
    eprintln!("[aggregate] cache disabled (--no-cache)");
  }
  if !config.write_outputs && !config.verify_only {
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
  if config.verify_only {
    let shards = prepared.shards.len();
    let proofs = proofs.as_deref().unwrap_or(&[]);
    if proofs.len() != shards {
      return Err(format!(
        "bound {} shard proofs but the manifest has {shards} shards",
        proofs.len()
      ));
    }
    let failures: Vec<String> = proofs
      .par_iter()
      .enumerate()
      .filter_map(|(shard, wrapper)| {
        let statement = &prepared.shards[shard].statement;
        let inner = inner_claim(config.verify_idx, &statement.claim_bytes);
        let proof = match AiurProof::from_bytes(&wrapper.proof) {
          Ok(proof) => proof,
          Err(error) => {
            return Some(format!("shard {shard}: proof does not decode: {error}"));
          },
        };
        config
          .ixvm_system
          .verify(&inner, &proof)
          .err()
          .map(|error| format!("shard {shard}: proof fails verification: {error:?}"))
      })
      .collect();
    if !failures.is_empty() {
      return Err(failures.join("; "));
    }
    eprintln!(
      "[verify] OK: composed verdict — all {shards} shards proven + disjoint cover ({shards} proofs verified natively in {:.1}s; claims {:.1}s)",
      proofs_at.elapsed().as_secs_f64(),
      (prepared_at - parsed_at).as_secs_f64(),
    );
    return Ok(String::new());
  }
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
    // Slots share the run's budget evenly across the concurrent jobs; with
    // every ready slot allowed at once, each gets the whole budget and the
    // scheduler's per-slot weights alone bound concurrency.
    wrap_budget: config
      .trace_shards
      .then(|| config.ram_budget_bytes / config.jobs.max(1)),
    range_width: config.range_width,
    range_jobs: config.jobs.max(1),
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
  let slots = run_scheduler(
    context,
    config.jobs,
    config.exec_ahead,
    config.ram_budget_bytes,
  )?;
  let root = slots.last().ok_or("aggregate plan produced no root slot")?;
  if root.kind != ChildKind::Aggr {
    return Err("aggregate plan produced a raw IxVM root".into());
  }
  validate_root_statement(&prepared, &root.statement)?;
  // Wrap until the final proof is a single trace shard: each wrap verifies
  // the previous proof, so its own execution shrinks with that proof's
  // shard count until one shard verifies it.
  let mut wrapped: Option<AiurProof> = None;
  if config.wrap_root {
    loop {
      let current = wrapped.as_ref().unwrap_or(&root.proof);
      let shards = current.preamble.headers.len();
      if shards <= 1 {
        break;
      }
      let next = wrap_root(context, root, current)?;
      if next.preamble.headers.len() >= shards {
        eprintln!(
          "[aggregate] root wrap did not shrink the proof ({shards} shards); keeping the previous one"
        );
        break;
      }
      wrapped = Some(next);
    }
  }
  let (proof, proof_address) = match &wrapped {
    Some(proof) => (proof, None),
    None => (&root.proof, root.proof_address.as_ref()),
  };
  config.aggr_system.verify(&root.outer_claim, proof).map_err(|error| {
    format!("aggregate root proof failed verification: {error:?}")
  })?;
  let (address, persisted) = match proof_address {
    Some(address) => (address.clone(), true),
    None if config.write_outputs => {
      (persist_wrapper(&store_dir, &root.statement, proof)?, true)
    },
    None => (wrapper_address(&root.statement, proof)?, false),
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

/// Native manifest/environment binding for `ix verify --aggregate --ixes`.
/// The returned claim comes from the exact statement builder used by Stage 2,
/// after a full constant/shard/assumption audit.
#[unsafe(no_mangle)]
extern "C" fn rs_aiur_aggregate_expected(
  env_handle: LeanExternal<EnvHandle, LeanBorrowed<'_>>,
  manifest_path: LeanString<LeanBorrowed<'_>>,
  structural_above: LeanNat<LeanBorrowed<'_>>,
) -> LeanExcept<LeanOwned> {
  let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
    let manifest_bytes =
      fs::read(Path::new(manifest_path.as_str())).map_err(|error| {
        format!("read manifest {}: {error}", manifest_path.as_str())
      })?;
    let manifest = ShardManifest::from_bytes(&manifest_bytes)
      .map_err(|error| format!("manifest parse failed: {error}"))?;
    expected_from_manifest(
      &env_handle.get().env,
      &manifest,
      lean_unbox_nat_as_usize(structural_above.inner()),
    )
  }));
  match result {
    Ok(Ok((statement, constant_count))) => {
      let expected = LeanAiurAggregateExpected::alloc(0);
      expected.set_obj(0, LeanByteArray::from_bytes(&statement.claim_bytes));
      expected.set_obj(1, LeanOwned::box_usize(constant_count));
      LeanExcept::ok(expected)
    },
    Ok(Err(error)) => LeanExcept::error_string(&error),
    Err(payload) => LeanExcept::error_string(&format!(
      "native aggregate verification setup panicked: {}",
      panic_text(&payload)
    )),
  }
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
  trace_shards: bool,
  range_width: LeanNat<LeanBorrowed<'_>>,
  wrap_root: bool,
  exec_ahead: LeanNat<LeanBorrowed<'_>>,
  verify_only: bool,
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
      trace_shards,
      range_width: lean_unbox_nat_as_usize(range_width.inner()),
      wrap_root,
      exec_ahead: lean_unbox_nat_as_usize(exec_ahead.inner()),
      verify_only,
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
    let reference_frontier =
      ixon::shard_claim::thin_frontier(&env, std::slice::from_ref(&consumer));
    let manifest = ShardManifest {
      num_shards: 2,
      shards: vec![shard(0, consumer.clone()), shard(1, dependency.clone())],
      total_cross_ingress: 0,
      tree: Some(AggNode::Internal(
        Box::new(AggNode::Leaf(0)),
        Box::new(AggNode::Leaf(1)),
      )),
    };
    let prepared = prepare_run(&env, &manifest).expect("native preparation");
    assert_eq!(
      prepared.shards[0]
        .statement
        .assumptions
        .as_ref()
        .expect("cross-shard frontier")
        .leaves
        .as_ref(),
      reference_frontier
    );
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
    let (expected, constant_count) =
      expected_from_manifest(&env, &manifest, 0).expect("native expected root");
    assert_eq!(constant_count, 2);
    assert_eq!(expected.claim, specs[2].statement.claim);
    let (flat_expected, flat_count) =
      expected_from_manifest(&env, &manifest, 8).expect("flat expected root");
    assert_eq!(flat_count, 2);
    assert_ne!(flat_expected.claim, expected.claim);
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
