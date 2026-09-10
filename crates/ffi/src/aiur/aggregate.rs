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

mod shard_pipeline;

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
use multi_stark::p3_field::{PrimeCharacteristicRing, PrimeField64};
use rayon::prelude::*;
use rustc_hash::{FxHashMap, FxHashSet};

use super::lean_unbox_nat_as_usize;
use crate::lean::LeanAiurAggregateExpected;

const CACHE_VERSION: u64 = 2;
const MIB: usize = 1024 * 1024;
const GIB: usize = 1024 * 1024 * 1024;
const WRAP_RAM_BYTES: usize = 195 * GIB;
const STRUCTURAL_RAM_BYTES: usize = 195 * GIB;
const RAW_SHARD_RAM_BYTES: usize = 4 * GIB;
const DIRECT_RAM_BYTES: usize = 180 * GIB;
// Mixed joins measured 378–385 GiB projected peak on the 2026-09-09 Mathlib
// Stage 2 against the previous 340 GiB reserve; 390 matches a direct pair.
const MIXED_RAM_BYTES: usize = 180 * GIB;
const FLAT_RAM_PER_SUBJECT: usize = 1024 * 1024;
// Structural subject roots are O(1), but assumption/path work and child
// verification can grow. Reserve a subject term plus a doubled base above
// 64k subjects: Mathlib peaks jumped to 380.5 GiB at 91,068 subjects, whereas
// a similar-sized join used 256.5 GiB. The term alone misses that trace-size
// step. A flat 195 GiB reserve caused a packed-node OOM at 187,668 subjects.
// Calibration and limitations: exp/design/numa-slot-pinning.md §12.
const STRUCTURAL_RAM_PER_SUBJECT: usize = 5 * MIB / 4;
const STRUCTURAL_LARGE_SUBJECTS: usize = 64 * 1024;

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
  /// `IX_AGGREGATE_SHARDS` restricted the run to a subset of the manifest's
  /// shards (experiments only): the root is the aggregate of that subtree and
  /// may retain assumptions on constants owned by unselected shards.
  partial: bool,
}

/// Experiment knob: `IX_AGGREGATE_SHARDS=K|a-b|a,b-c,…` aggregates only the
/// named shard ids (the manifest tree pruned to that subtree) from the
/// corresponding subset of the supplied Stage 1 proofs. Shard claims depend
/// only on a shard's own constants and frontier, so the leaf proofs of a full
/// run stay valid; the root is then a partial, assumption-carrying aggregate.
fn shard_selection() -> Result<Option<FxHashSet<u32>>, String> {
  let Ok(spec) = std::env::var("IX_AGGREGATE_SHARDS") else {
    return Ok(None);
  };
  let mut ids = FxHashSet::default();
  for piece in spec.split(',').map(str::trim).filter(|p| !p.is_empty()) {
    let bad = |error: std::num::ParseIntError| {
      format!("IX_AGGREGATE_SHARDS: malformed `{piece}`: {error}")
    };
    match piece.split_once('-') {
      Some((a, b)) => {
        let a: u32 = a.trim().parse().map_err(bad)?;
        let b: u32 = b.trim().parse().map_err(bad)?;
        if b < a {
          return Err(format!("IX_AGGREGATE_SHARDS: empty range `{piece}`"));
        }
        ids.extend(a..=b);
      },
      None => {
        ids.insert(piece.parse().map_err(bad)?);
      },
    }
  }
  if ids.is_empty() {
    return Err("IX_AGGREGATE_SHARDS: empty selection".into());
  }
  Ok(Some(ids))
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
  proofs: Option<&'a [Arc<Slot>]>,
  owner_by_address: &'a FxHashMap<Address, usize>,
  ixvm_system: &'a AiurSystem,
  aggr_system: &'a AiurSystem,
  ixvm_vk: &'a [u8],
  aggr_vk: &'a [u8],
  allowed: &'a [u8],
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
  /// `ix verify --ixes <proofs>`: stop after the parallel proof import —
  /// every shard claim reconstructed natively, every supplied proof bound
  /// to its shard and verified (IxVM or healed `ix_aggr`), exactly one per
  /// shard — and report that composed verdict instead of proving.
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

  let selection = shard_selection()?;
  let retained_old: Vec<usize> = owned
    .iter()
    .enumerate()
    .filter(|(index, _)| {
      selection
        .as_ref()
        .is_none_or(|ids| ids.contains(&manifest.shards[*index].id))
    })
    .filter_map(|(index, addresses)| (!addresses.is_empty()).then_some(index))
    .collect();
  if retained_old.is_empty() {
    return Err("manifest has no shard owning an environment constant".into());
  }
  let partial =
    selection.is_some() && retained_old.len() < manifest.shards.len();
  // A partial run's root covers only the selected shards' constants.
  let root_addresses: Vec<Address> = if partial {
    let mut selected: Vec<Address> =
      retained_old.iter().flat_map(|old| owned[*old].iter().cloned()).collect();
    selected.par_sort_unstable();
    eprintln!(
      "[aggregate] IX_AGGREGATE_SHARDS: partial aggregate over {} of {} shards ({} of {} constants); the root may retain assumptions",
      retained_old.len(),
      manifest.shards.len(),
      selected.len(),
      all_addresses.len()
    );
    selected
  } else {
    all_addresses.clone()
  };
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
    .map(|(address, old)| {
      // Constants of unselected shards keep a sentinel owner that no retained
      // index equals and no subject tree contains: they stay assumptions.
      (address, old_to_retained.get(&old).copied().unwrap_or(usize::MAX))
    })
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

  let env_root = merkle_root_canonical_sorted(&root_addresses)
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
    env_count: root_addresses.len(),
    expected_shards,
    partial,
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
    9 => {
      let weight = STRUCTURAL_RAM_BYTES.saturating_add(
        subject_count.saturating_mul(STRUCTURAL_RAM_PER_SUBJECT),
      );
      if subject_count > STRUCTURAL_LARGE_SUBJECTS {
        weight.max(2 * STRUCTURAL_RAM_BYTES)
      } else {
        weight
      }
    },
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
  if root.assumptions.is_some() && !prepared.partial {
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

fn write_store(root: &Path, bytes: &[u8]) -> Result<Address, String> {
  let address = Address::hash(bytes);
  let path = store_path(root, &address);
  write_atomic(&path, bytes)?;
  Ok(address)
}

fn write_atomic(path: &Path, bytes: &[u8]) -> Result<(), String> {
  use std::{
    io::Write,
    sync::atomic::{AtomicU64, Ordering},
    time::{SystemTime, UNIX_EPOCH},
  };
  static NEXT: AtomicU64 = AtomicU64::new(0);
  let parent = path.parent().ok_or("output path has no parent")?;
  let nonce =
    SystemTime::now().duration_since(UNIX_EPOCH).unwrap_or_default().as_nanos();
  let tmp = path.with_extension(format!(
    "{}.{nonce}.{}.tmp",
    std::process::id(),
    NEXT.fetch_add(1, Ordering::Relaxed)
  ));
  fs::create_dir_all(parent)
    .map_err(|error| format!("create {}: {error}", parent.display()))?;
  // A failed create must never remove another writer's temporary file.
  let mut file = fs::OpenOptions::new()
    .write(true)
    .create_new(true)
    .open(&tmp)
    .map_err(|error| format!("create {}: {error}", tmp.display()))?;
  let result = (|| -> std::io::Result<()> {
    file.write_all(bytes)?;
    file.sync_all()?;
    fs::rename(&tmp, path)?;
    fs::File::open(parent)?.sync_all()
  })();
  if result.is_err() {
    let _ = fs::remove_file(&tmp);
  }
  result.map_err(|error| format!("write {}: {error}", path.display()))
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
  partial: bool,
) -> Result<Vec<Arc<IxonProof>>, String> {
  let values: Vec<&str> =
    proof_hexes.lines().filter(|line| !line.is_empty()).collect();
  if !partial && values.len() != prepared.len() {
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
  // Read, hash and decode every wrapper in parallel (this was 40+ s serial
  // for 246 Mathlib proofs); claim matching and duplicate checks stay
  // sequential below so the error semantics are unchanged.
  let decoded: Vec<(Address, IxonProof)> = values
    .par_iter()
    .map(|value| -> Result<(Address, IxonProof), String> {
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
      Ok((address, wrapper))
    })
    .collect::<Result<Vec<_>, _>>()?;
  let mut proofs: Vec<Option<Arc<IxonProof>>> = vec![None; prepared.len()];
  for (address, wrapper) in decoded {
    let mut claim_bytes = Vec::new();
    wrapper.claim.put(&mut claim_bytes);
    let digest = Address::hash(&claim_bytes);
    let Some(shard) = by_digest.get(&digest).copied() else {
      if partial {
        continue; // a proof for an unselected shard
      }
      return Err(format!("proof {} matches no manifest shard", address.hex()));
    };
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

/// Authenticate a shard certificate under one of the two supported systems.
/// The backend is established by verification, never by an untrusted tag.
fn verify_shard_proof(
  ixvm: &AiurSystem,
  aggr: &AiurSystem,
  verify_idx: usize,
  aggr_idx: usize,
  allowed: &[u8],
  claim: &Claim,
  proof: &AiurProof,
) -> Result<(ChildKind, Vec<G>), String> {
  let mut bytes = Vec::new();
  claim.put(&mut bytes);
  let inner = inner_claim(verify_idx, &bytes);
  if ixvm.verify(&inner, proof).is_ok() {
    return Ok((ChildKind::Ixvm, inner));
  }
  if !matches!(claim, Claim::CheckEnv { .. }) {
    return Err("proof does not verify under the IxVM system".into());
  }
  let outer = aggregate_outer_claim(aggr_idx, allowed, &bytes);
  aggr.verify(&outer, proof).map_err(|error| {
    format!("proof verifies under neither IxVM nor ix_aggr: {error:?}")
  })?;
  Ok((ChildKind::Aggr, outer))
}

fn import_shard_proof(
  ixvm: &AiurSystem,
  aggr: &AiurSystem,
  verify_idx: usize,
  aggr_idx: usize,
  allowed: &[u8],
  statement: Arc<Statement>,
  wrapper: &IxonProof,
  proof_address: Option<Address>,
) -> Result<Arc<Slot>, String> {
  if wrapper.claim != statement.claim {
    return Err("shard proof bundles a different CheckEnv claim".into());
  }
  let proof = AiurProof::from_bytes(&wrapper.proof)
    .map_err(|error| format!("shard proof does not decode: {error}"))?;
  let (kind, outer_claim) = verify_shard_proof(
    ixvm,
    aggr,
    verify_idx,
    aggr_idx,
    allowed,
    &statement.claim,
    &proof,
  )?;
  let claims_bytes = serialize_claims(&[&outer_claim]);
  Ok(Arc::new(Slot {
    kind,
    statement,
    outer_claim,
    proof,
    proof_address,
    claims_bytes,
  }))
}

/// Statement roots and slot indices do not depend on the input proof kind.
/// Imported healed leaves are already complete; only proof shapes/reserves
/// above them change. Cache keys continue to bind the same output statements.
fn bind_imported_specs(
  specs: &mut [SlotSpec],
  inputs: &[Arc<Slot>],
  aggr_vk: &[u8],
  cache_fri_bytes: &[u8],
) {
  for index in 0..specs.len() {
    match specs[index].op {
      PlanOp::Leaf(shard) if inputs[shard].kind == ChildKind::Aggr => {
        let spec = &mut specs[index];
        spec.kind = ChildKind::Aggr;
        spec.shape = None;
        spec.outer_claim = inputs[shard].outer_claim.clone();
        spec.cache_key = cache_key(aggr_vk, cache_fri_bytes, &spec.outer_claim);
        spec.ram_bytes = RAW_SHARD_RAM_BYTES;
      },
      PlanOp::Join(left, right) => {
        let shape = if specs[index].structural {
          structural_shape_code(specs[left].kind, specs[right].kind)
        } else {
          shape_code(specs[left].kind, Some(specs[right].kind))
        };
        specs[index].shape = Some(shape);
        specs[index].ram_bytes =
          shape_ram_bytes(shape, specs[index].subject_count);
      },
      PlanOp::Leaf(_) => {},
    }
  }
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

/// Advice construction shared by Stage 2 and budgeted local shard healing.
fn aggregate_io(
  ctx: ProveContext<'_>,
  spec: &SlotSpec,
  left: &Slot,
  right: Option<&Slot>,
) -> Result<(IOBuffer, String), String> {
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
  let io = aggr_io_buffer(&AggrAdvice {
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
  let sizes = format!(
    "proof advice {}+{} MiB, {} trees/{} MiB, {} paths/{} MiB, preimages {} MiB",
    format_mib(left_advice.len()),
    format_mib(right_advice.len()),
    tree_storage.len(),
    format_mib(tree_storage.iter().map(|t| t.bytes.len()).sum()),
    path_storage.len(),
    format_mib(path_storage.iter().map(|(_, p)| p.len()).sum()),
    format_mib(preimage_storage.iter().map(|(_, p)| p.len()).sum()),
  );
  Ok((io, sizes))
}

/// Extra RAM for one lookahead execution record (measured 32.6 GiB for a
/// Mathlib direct join), charged to both the process and any bound node.
const LOOKAHEAD_RAM_BYTES: usize = 40 * GIB;

/// The overlappable front half of a slot: advice construction plus the
/// `ix_aggr` execution into a query record. Runs on a lane's prep thread
/// while that lane proves its current slot; `None` when the slot's proof is
/// already cached (nothing to prepare).
fn prepare_aggregate<'a>(
  ctx: ProveContext<'a>,
  spec: &SlotSpec,
  left: &Slot,
  right: Option<&Slot>,
  slot_index: usize,
) -> Result<Option<shard_pipeline::Execution<'a>>, String> {
  if ctx.reprove_slot != Some(slot_index)
    && load_cached(ctx, slot_index, spec).is_some()
  {
    return Ok(None);
  }
  let (io, _advice_sizes) = aggregate_io(ctx, spec, left, right)?;
  let mut public_input = packed_digest(ctx.allowed);
  public_input.extend(packed_digest(&spec.statement.claim_bytes));
  shard_pipeline::Execution::new(
    ctx.aggr_system,
    ctx.aggr_idx,
    public_input,
    io,
    execute_ix_aggr,
  )
  .map(Some)
}

/// The back half: prove from a prepared record and persist. Mirrors the
/// tail of [`prove_aggregate`].
fn prove_prepared(
  ctx: ProveContext<'_>,
  spec: &SlotSpec,
  execution: shard_pipeline::Execution<'_>,
  slot_index: usize,
) -> Result<(AiurProof, Option<Address>), String> {
  let started = Instant::now();
  let peak = execution.peak();
  let (outer_claim, proof) = execution.prove();
  let proved_at = Instant::now();
  if outer_claim != spec.outer_claim {
    return Err("aggregate prover returned an unexpected outer claim".into());
  }
  let address = persist_cached(ctx, slot_index, spec, &proof);
  eprintln!(
    "[aggregate] slot {slot_index}: prepared ahead; prove {:.1}s, persist {:.1}s, peak {} GiB",
    (proved_at - started).as_secs_f64(),
    proved_at.elapsed().as_secs_f64(),
    format_gib(peak),
  );
  Ok((proof, address))
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

  let (mut io, advice_sizes) = aggregate_io(ctx, spec, left, right)?;
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
  // Per-slot phase timings for every slot (not only replays): the numbers a
  // Stage 2 throughput model needs — how much of a slot is advice/execute
  // (overlappable) vs prove vs persistence — plus the record's peak.
  eprintln!(
    "[aggregate] slot {slot_index}: advice {:.1}s, execute+prove {:.1}s, persist {:.1}s, peak {} GiB",
    (proving_started - started).as_secs_f64(),
    (proved_at - proving_started).as_secs_f64(),
    proved_at.elapsed().as_secs_f64(),
    format_gib(peak),
  );
  if replaying {
    eprintln!(
      "[aggregate] replay slot {slot_index}: shape {}, {} subjects, assumptions {}/{}/{}, {advice_sizes}, query-record peak {} GiB ({} bytes)",
      spec.shape.expect("aggregate slot has a shape"),
      spec.subject_count,
      assumption_count(&left.statement),
      right.map_or(0, |slot| assumption_count(&slot.statement)),
      assumption_count(&spec.statement),
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
  prepared: Option<shard_pipeline::Execution<'_>>,
) -> Result<Arc<Slot>, String> {
  let spec = ctx.specs.get(slot_index).ok_or("missing aggregate slot spec")?;
  let mut prepared = prepared;
  match spec.op {
    PlanOp::Leaf(shard) => {
      let prepared_shard = &ctx.prepared[shard];
      let raw =
        ctx.proofs.and_then(|proofs| proofs.get(shard)).ok_or_else(|| {
          format!(
            "shard {} proof was not loaded for replay",
            prepared_shard.original_id
          )
        })?;
      if spec.shape.is_none() {
        if spec.outer_claim != raw.outer_claim || spec.kind != raw.kind {
          return Err("imported shard slot has an unexpected identity".into());
        }
        return Ok(raw.clone());
      }
      eprintln!(
        "[aggregate] wrapping shard {} into slot {slot_index}",
        prepared_shard.original_id
      );
      let (proof, proof_address) = match prepared.take() {
        Some(execution) => prove_prepared(ctx, spec, execution, slot_index)?,
        None => prove_aggregate(ctx, spec, raw, None, slot_index)?,
      };
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
      let (proof, proof_address) = match prepared.take() {
        Some(execution) => prove_prepared(ctx, spec, execution, slot_index)?,
        None => prove_aggregate(ctx, spec, left, Some(right), slot_index)?,
      };
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
  if spec.shape.is_none() {
    return Err(format!(
      "--reprove-slot {target} selects an imported healed leaf; it has no Stage 2 execution to replay"
    ));
  }
  let children = match spec.op {
    PlanOp::Leaf(_) => Vec::new(),
    PlanOp::Join(left, right) => vec![left, right],
  };
  let needs_input_proofs = children.is_empty()
    || children.iter().any(|index| specs[*index].shape.is_none());
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
  if spec.kind == ChildKind::Ixvm
    || (matches!(spec.op, PlanOp::Leaf(_)) && spec.shape.is_none())
  {
    return prove_slot(ctx, child_index, &[], None);
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
  let slot = prove_slot(ctx, target, &children, None)?;
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

/// One NUMA domain used as a scheduling lane: a pinned rayon pool plus its
/// own RAM reservation (see `crate::numa`). Slots proved on a lane run with
/// their threads and first-touch memory confined to that domain.
struct NumaLane {
  domain: crate::numa::Domain,
  pool: Arc<rayon::ThreadPool>,
  budget: usize,
  reserved: usize,
  active: usize,
  /// Highest resident memory observed on this lane's node at any slot
  /// completion (observability, not accounting).
  peak_resident: usize,
}

/// Resident bytes on `node` right now (0 when unreadable).
fn resident_on(node: u32) -> usize {
  crate::numa::resident_by_node()
    .into_iter()
    .find(|(n, _)| *n == node)
    .map_or(0, |(_, bytes)| bytes)
}

/// Run `work` while a sampler thread reads this process's resident memory on
/// `node` once a second; returns the work's result and the peak seen.
/// Observability only (a `/proc/self/numa_maps` parse per sample).
fn with_resident_peak<R: Send>(
  node: u32,
  work: impl FnOnce() -> R + Send,
) -> (R, usize) {
  let stop = std::sync::atomic::AtomicBool::new(false);
  thread::scope(|scope| {
    let sampler = scope.spawn(|| {
      let mut peak = 0usize;
      while !stop.load(std::sync::atomic::Ordering::Relaxed) {
        peak = peak.max(resident_on(node));
        thread::sleep(std::time::Duration::from_secs(1));
      }
      peak.max(resident_on(node))
    });
    let result = work();
    stop.store(true, std::sync::atomic::Ordering::Relaxed);
    let peak = sampler.join().unwrap_or(0);
    (result, peak)
  })
}

/// Pick the lane for a slot of `weight` bytes: an idle lane with the most free
/// RAM, else (when packing is allowed) the least-loaded lane that fits, at
/// most two slots per lane. `None` when no lane can take it now — the caller
/// then waits, or runs the slot unpinned if nothing else is in flight (the
/// over-budget-runs-alone rule).
fn choose_numa_lane(
  lanes: &[NumaLane],
  weight: usize,
  pack: bool,
) -> Option<usize> {
  let mut best: Option<((usize, usize), usize)> = None;
  for (index, lane) in lanes.iter().enumerate() {
    if weight > lane.budget.saturating_sub(lane.reserved) {
      continue;
    }
    if lane.active > 0 && (!pack || lane.active >= 2) {
      continue;
    }
    let free = lane.budget - lane.reserved;
    let key = (lane.active, usize::MAX - free);
    if best.is_none_or(|(k, _)| key < k) {
      best = Some((key, index));
    }
  }
  best.map(|(_, index)| index)
}

fn numa_lanes(budget: usize) -> Result<Vec<NumaLane>, String> {
  let numa = crate::numa::detect();
  if !numa.enabled() {
    eprintln!(
      "[aggregate] numa: disabled (single domain, IX_NUMA=off, or unsupported)"
    );
    return Ok(Vec::new());
  }
  let mut lanes = Vec::with_capacity(numa.domains.len());
  for domain in &numa.domains {
    let pool = crate::numa::pool(numa, domain)?;
    let lane_budget = (domain.mem_bytes / 10 * 9).min(budget);
    lanes.push(NumaLane {
      domain: domain.clone(),
      pool,
      budget: lane_budget,
      reserved: 0,
      active: 0,
      peak_resident: 0,
    });
  }
  let described: Vec<String> = lanes
    .iter()
    .map(|lane| {
      format!(
        "node {} ({} cpus, {} GiB)",
        lane.domain.node,
        lane.domain.cpus.len(),
        format_gib(lane.budget)
      )
    })
    .collect();
  eprintln!(
    "[aggregate] numa: {} lanes: {}; policy={:?} pack={} threads={}",
    lanes.len(),
    described.join(", "),
    numa.policy,
    numa.pack,
    numa.threads.map_or("cpuset".to_string(), |n| n.to_string()),
  );
  Ok(lanes)
}

#[derive(Debug)]
struct PipelineQueue {
  /// None uses the ordinary Rayon pool and inherits the process affinity.
  lane: Option<usize>,
  slots: Vec<usize>,
  /// Largest proving reservation in this queue, excluding lookahead.
  weight: usize,
  lookahead: bool,
}

/// Partition independent jobs without exceeding the job, process or node
/// limits. Reserve proving capacity first, then enable at most one prepared
/// record per queue from the remaining RAM. This keeps lookahead from
/// reducing the number of concurrent proofs. Unassigned jobs stay on the
/// ordinary scheduler, including its existing over-budget-runs-alone path.
fn plan_pipelines(
  batch: &[(usize, usize)],
  lane_budgets: &[usize],
  max_jobs: usize,
  budget: usize,
  per_lane: usize,
) -> Vec<PipelineQueue> {
  let mut ordered = batch.to_vec();
  ordered.sort_by_key(|&(index, weight)| (std::cmp::Reverse(weight), index));
  let mut pipelines: Vec<PipelineQueue> = Vec::new();
  let mut load = Vec::<usize>::new();
  let mut reserved = 0usize;
  // Proving reservation (plus enabled lookahead records) per NUMA lane; up
  // to `per_lane` queues share a lane's pool when both fit its budget.
  let mut lane_load = vec![0usize; lane_budgets.len()];
  let lane_count = |pipelines: &[PipelineQueue], k: usize| {
    pipelines.iter().filter(|p| p.lane == Some(k)).count()
  };
  for (index, weight) in ordered {
    if weight == 0 {
      continue;
    }
    if pipelines.len() < max_jobs && weight <= budget - reserved {
      let placement = if lane_budgets.is_empty() {
        Some(None)
      } else {
        (0..lane_budgets.len())
          .filter(|&k| {
            lane_count(&pipelines, k) < per_lane.max(1)
              && weight <= lane_budgets[k].saturating_sub(lane_load[k])
          })
          // An idle lane first, then the emptiest; ties to the lowest node.
          .min_by_key(|&k| (lane_count(&pipelines, k), lane_load[k], k))
          .map(Some)
      };
      if let Some(lane) = placement {
        if let Some(k) = lane {
          lane_load[k] += weight;
        }
        pipelines.push(PipelineQueue {
          lane,
          slots: vec![index],
          weight,
          lookahead: false,
        });
        load.push(weight);
        reserved += weight;
        continue;
      }
    }
    if let Some(k) = (0..pipelines.len())
      .filter(|&k| weight <= pipelines[k].weight)
      .min_by_key(|&k| (load[k], k))
    {
      pipelines[k].slots.push(index);
      load[k] = load[k].saturating_add(weight);
    }
  }
  for pipeline in &mut pipelines {
    pipeline.slots.sort_unstable();
    let lane_room = pipeline
      .lane
      .map_or(usize::MAX, |k| lane_budgets[k].saturating_sub(lane_load[k]));
    if pipeline.slots.len() > 1
      && LOOKAHEAD_RAM_BYTES <= budget - reserved
      && LOOKAHEAD_RAM_BYTES <= lane_room
    {
      pipeline.lookahead = true;
      reserved += LOOKAHEAD_RAM_BYTES;
      if let Some(k) = pipeline.lane {
        lane_load[k] += LOOKAHEAD_RAM_BYTES;
      }
    }
  }
  pipelines
}

/// Prove the initial independent jobs on bounded queues, overlapping the
/// next preparation where the plan has reserved room for its record. NUMA
/// placement is optional; dependent joins use the ordinary scheduler after
/// this batch. Returns completed slots and peaks keyed by NUMA lane index.
fn run_pipelines<'a>(
  ctx: ProveContext<'a>,
  lanes: &[NumaLane],
  slots: &[Option<Arc<Slot>>],
  pipelines: &[PipelineQueue],
) -> Result<(Vec<(usize, Arc<Slot>)>, Vec<(usize, usize)>), String> {
  let numa = crate::numa::detect();
  eprintln!(
    "[aggregate] pipelines: {} independent slots over {} workers ({}); prepare-next overlap on {}/{} workers",
    pipelines.iter().map(|p| p.slots.len()).sum::<usize>(),
    pipelines.len(),
    pipelines
      .iter()
      .enumerate()
      .map(|(i, p)| {
        let placement = p.lane.map_or_else(
          || format!("unpinned worker {i}"),
          |k| format!("node {}", lanes[k].domain.node),
        );
        format!(
          "{placement}: {} slots, {} GiB reserved",
          p.slots.len(),
          format_gib(
            p.weight + if p.lookahead { LOOKAHEAD_RAM_BYTES } else { 0 }
          )
        )
      })
      .collect::<Vec<_>>()
      .join(", "),
    pipelines.iter().filter(|p| p.lookahead).count(),
    pipelines.len(),
  );
  let children_of = |index: usize| -> Vec<Arc<Slot>> {
    match ctx.specs[index].op {
      PlanOp::Leaf(_) => Vec::new(),
      PlanOp::Join(left, right) => vec![
        slots[left].as_ref().expect("completed left slot").clone(),
        slots[right].as_ref().expect("completed right slot").clone(),
      ],
    }
  };
  let prepare = |index: usize,
                 children: &[Arc<Slot>]|
   -> Result<Option<shard_pipeline::Execution<'a>>, String> {
    let spec = &ctx.specs[index];
    match spec.op {
      PlanOp::Join(..) => {
        prepare_aggregate(ctx, spec, &children[0], Some(&children[1]), index)
      },
      PlanOp::Leaf(shard) => {
        let raw = ctx
          .proofs
          .and_then(|proofs| proofs.get(shard))
          .ok_or("shard proof was not loaded")?;
        prepare_aggregate(ctx, spec, raw, None, index)
      },
    }
  };
  let results: Vec<Result<(Vec<(usize, Arc<Slot>)>, usize), String>> =
    thread::scope(|scope| {
      let handles: Vec<_> = pipelines
        .iter()
        .enumerate()
        .map(|(worker, pipeline)| {
          let children_of = &children_of;
          let prepare = &prepare;
          let lane = pipeline.lane.map(|k| &lanes[k]);
          scope.spawn(move || {
            let run = || -> Result<(Vec<(usize, Arc<Slot>)>, usize), String> {
              let queue = &pipeline.slots;
              let mut done = Vec::with_capacity(queue.len());
              let mut peak_resident = 0usize;
              let mut prepared: Option<(
                usize,
                Result<Option<shard_pipeline::Execution<'a>>, String>,
              )> = None;
              for (position, &index) in queue.iter().enumerate() {
                let started = Instant::now();
                let children = children_of(index);
                // This slot's record: prepared during the previous prove, or
                // built now for the first slot of the queue.
                let execution = match prepared.take() {
                  Some((prepared_index, result)) if prepared_index == index => {
                    result?
                  },
                  _ => prepare(index, &children)?,
                };
                let next = if pipeline.lookahead {
                  queue.get(position + 1).copied()
                } else {
                  None
                };
                let (proved, node_peak, next_prepared) = thread::scope(|inner| {
                  let producer = next.map(|next_index| {
                    let next_children = children_of(next_index);
                    inner.spawn(move || {
                      if let Some(lane) = lane {
                        crate::numa::pin_current_thread(&lane.domain, numa.policy);
                      }
                      (next_index, prepare(next_index, &next_children))
                    })
                  });
                  let prove = || prove_slot(ctx, index, &children, execution);
                  let (proved, node_peak) = match lane {
                    Some(lane) => with_resident_peak(lane.domain.node, prove),
                    None => (prove(), 0),
                  };
                  let next_prepared = producer.map(|handle| {
                    handle.join().unwrap_or_else(|payload| {
                      (
                        next.expect("producer exists only with a next slot"),
                        Err(format!(
                          "preparation panicked: {}",
                          panic_text(&payload)
                        )),
                      )
                    })
                  });
                  (proved, node_peak, next_prepared)
                });
                prepared = next_prepared;
                let slot = proved?;
                let resident = node_peak;
                peak_resident = peak_resident.max(resident);
                let placement = lane.map_or_else(
                  || format!("unpinned worker {worker}"),
                  |lane| format!(
                    "node {} (node peak resident {} GiB)",
                    lane.domain.node, format_gib(resident)
                  ),
                );
                eprintln!(
                  "[aggregate] slot {index}: completed in {:.1}s on {placement} ({} GiB weight); pipeline {}/{}",
                  started.elapsed().as_secs_f64(),
                  format_gib(ctx.specs[index].ram_bytes),
                  position + 1,
                  queue.len(),
                );
                done.push((index, slot));
              }
              Ok((done, peak_resident))
            };
            match lane {
              Some(lane) => {
                crate::numa::pin_current_thread(&lane.domain, numa.policy);
                lane.pool.install(run)
              },
              None => run(),
            }
          })
        })
        .collect();
      handles
        .into_iter()
        .map(|h| {
          h.join().unwrap_or_else(|payload| {
            Err(format!(
              "aggregate pipeline panicked: {}",
              panic_text(&payload)
            ))
          })
        })
        .collect()
    });
  let mut completed =
    Vec::with_capacity(pipelines.iter().map(|p| p.slots.len()).sum());
  let mut peaks = Vec::new();
  for (pipeline, result) in pipelines.iter().zip(results) {
    let (done, peak) = result?;
    completed.extend(done);
    if let Some(k) = pipeline.lane {
      peaks.push((k, peak));
    }
  }
  Ok((completed, peaks))
}

fn run_scheduler<'a>(
  ctx: ProveContext<'a>,
  jobs: usize,
  budget: usize,
) -> Result<Vec<Arc<Slot>>, String> {
  if budget == 0 {
    return Err("aggregate scheduler RAM budget must be positive".into());
  }
  // Adapt to the cgroup this process was launched in: never admit more than
  // 92 % of its memory limit, whatever `--max-ram` or the default said.
  let budget = match crate::numa::cgroup_memory_max() {
    Some(limit) if limit / 100 * 92 < budget => {
      let clamped = limit / 100 * 92;
      eprintln!(
        "[aggregate] RAM budget {} GiB exceeds 92 % of the cgroup limit {} GiB; clamping to {} GiB",
        format_gib(budget),
        format_gib(limit),
        format_gib(clamped),
      );
      clamped
    },
    _ => budget,
  };
  let numa = crate::numa::detect();
  let mut lanes = numa_lanes(budget)?;
  // Prepare-next overlap is independent of placement. The existing switch
  // also controls unpinned workers on single-node or unsupported hosts.
  let lookahead = !matches!(
    std::env::var("IX_NUMA_LOOKAHEAD").as_deref().map(str::trim),
    Ok("0" | "off" | "false")
  );
  let max_jobs = if jobs == 0 {
    if lanes.is_empty() {
      ctx.specs.len().max(1)
    } else {
      lanes.len() * if numa.pack { 2 } else { 1 }
    }
  } else {
    jobs.max(1)
  };
  let n = ctx.specs.len();
  let mut slots: Vec<Option<Arc<Slot>>> = vec![None; n];
  let mut completed = vec![false; n];
  let mut completed_count = 0usize;

  // Imported raw leaves (no shape) complete without proving: do them inline.
  for index in 0..n {
    if ctx.specs[index].shape.is_none()
      && matches!(ctx.specs[index].op, PlanOp::Leaf(_))
    {
      let slot = prove_slot(ctx, index, &[], None)
        .map_err(|error| format!("slot {index}: {error}"))?;
      slots[index] = Some(slot);
      completed[index] = true;
      completed_count += 1;
    }
  }

  // Phase A: everything ready now has no dependency on another proof.
  if lookahead {
    let batch: Vec<(usize, usize)> = (0..n)
      .filter(|&i| {
        !completed[i]
          && ctx.specs[i].shape.is_some()
          && dependencies_complete(&ctx.specs[i], &completed)
      })
      .map(|i| (i, ctx.specs[i].ram_bytes))
      .collect();
    let lane_budgets: Vec<usize> = lanes.iter().map(|l| l.budget).collect();
    let pipelines = plan_pipelines(
      &batch,
      &lane_budgets,
      max_jobs,
      budget,
      if numa.pack { 2 } else { 1 },
    );
    // Without room or enough work to overlap, retain ordinary dynamic
    // admission and packing instead of introducing a batch barrier.
    if pipelines.iter().any(|p| p.lookahead) {
      let (done, peaks) = run_pipelines(ctx, &lanes, &slots, &pipelines)?;
      for (index, slot) in done {
        slots[index] = Some(slot);
        completed[index] = true;
        completed_count += 1;
      }
      for (k, peak) in peaks {
        lanes[k].peak_resident = lanes[k].peak_resident.max(peak);
      }
    }
  }

  let (sender, receiver) = mpsc::channel();
  thread::scope(|scope| -> Result<Vec<Arc<Slot>>, String> {
    let mut in_flight = vec![false; n];
    let mut admitted_at: Vec<Option<Instant>> = vec![None; n];
    let mut active = 0usize;
    let mut reserved = 0usize;
    let mut failures: Vec<(usize, String)> = Vec::new();

    while completed_count < n {
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
        let ready_count = ready.len();
        for index in ready {
          if active >= max_jobs {
            break;
          }
          let weight = ctx.specs[index].ram_bytes;
          let fits = weight <= budget.saturating_sub(reserved);
          if !fits && active != 0 {
            continue;
          }
          // A slot that is the only runnable work with nothing else live
          // (the dependency tail near the root) is faster unpinned: it can
          // use every core and all memory channels (measured ~12 % over one
          // domain), and there is no neighbour to isolate it from.
          let solo_tail = active == 0 && ready_count == 1;
          let lane = if solo_tail {
            None
          } else {
            choose_numa_lane(&lanes, weight, numa.pack)
          };
          if !lanes.is_empty() && lane.is_none() && active != 0 {
            // Fits the global budget but no domain can hold it yet.
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
          admitted_at[index] = Some(Instant::now());
          active += 1;
          reserved = reserved.saturating_add(weight);
          let over =
            if weight > budget { "; over-budget slot runs alone" } else { "" };
          let placement = match lane {
            Some(k) => {
              lanes[k].reserved = lanes[k].reserved.saturating_add(weight);
              lanes[k].active += 1;
              format!(
                " on node {} (node reserved {}/{} GiB, node active {})",
                lanes[k].domain.node,
                format_gib(lanes[k].reserved),
                format_gib(lanes[k].budget),
                lanes[k].active,
              )
            },
            None if !lanes.is_empty() && solo_tail => {
              " unpinned (solo tail)".to_string()
            },
            None if !lanes.is_empty() => " unpinned".to_string(),
            None => String::new(),
          };
          eprintln!(
            "[aggregate] slot {index}: admitted {} GiB{placement}; reserved {}/{} GiB; active {active}/{max_jobs}{over}",
            format_gib(weight),
            format_gib(reserved),
            format_gib(budget),
          );
          let sender = sender.clone();
          let pinned =
            lane.map(|k| (lanes[k].pool.clone(), lanes[k].domain.clone()));
          let unpin = lane.is_none() && !lanes.is_empty();
          scope.spawn(move || {
            let node = pinned.as_ref().map(|(_, domain)| domain.node);
            let (result, node_peak) =
              with_resident_peak(node.unwrap_or(0), || {
                std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                  match &pinned {
                    Some((pool, domain)) => {
                      crate::numa::pin_current_thread(domain, numa.policy);
                      pool.install(|| prove_slot(ctx, index, &children, None))
                    },
                    None => {
                      if unpin {
                        crate::numa::unpin_current_thread(numa);
                      }
                      prove_slot(ctx, index, &children, None)
                    },
                  }
                }))
                .unwrap_or_else(|payload| {
                  Err(format!(
                    "Rust proof worker panicked: {}",
                    panic_text(&payload)
                  ))
                })
              });
            let node_peak = if node.is_some() { node_peak } else { 0 };
            let _ = sender.send((index, weight, lane, node_peak, result));
          });
          if unpin {
            // No other slot is active. Wait for this one before admitting
            // neighbours: a slot too large for one node uses all nodes and
            // holds no per-node reservation, even if the global budget has
            // room left. The next completion is necessarily this slot's.
            break;
          }
        }
      }

      if active == 0 {
        if failures.is_empty() {
          failures
            .push((ctx.specs.len(), "aggregate scheduler deadlocked".into()));
        }
        break;
      }

      let (index, weight, lane, node_peak, result) =
        receiver.recv().map_err(|error| {
          format!("aggregate scheduler channel closed: {error}")
        })?;
      if !in_flight.get(index).copied().unwrap_or(false) {
        failures.push((index, "duplicate or unknown scheduler result".into()));
        continue;
      }
      in_flight[index] = false;
      active -= 1;
      reserved = reserved.saturating_sub(weight);
      if let Some(k) = lane {
        lanes[k].reserved = lanes[k].reserved.saturating_sub(weight);
        lanes[k].active = lanes[k].active.saturating_sub(1);
      }
      let elapsed = admitted_at[index]
        .take()
        .map_or(0.0, |started| started.elapsed().as_secs_f64());
      let where_ = lane.map_or(String::new(), |k| {
        lanes[k].peak_resident = lanes[k].peak_resident.max(node_peak);
        format!(
          " on node {} (node peak resident {} GiB)",
          lanes[k].domain.node,
          format_gib(node_peak)
        )
      });
      match result {
        Ok(slot) => {
          eprintln!(
            "[aggregate] slot {index}: completed in {elapsed:.1}s{where_} ({} GiB weight); active {}/{max_jobs}",
            format_gib(weight),
            active,
          );
          slots[index] = Some(slot);
          completed[index] = true;
          completed_count += 1;
        },
        Err(error) => {
          eprintln!(
            "[aggregate] slot {index}: FAILED after {elapsed:.1}s{where_}"
          );
          failures.push((index, error))
        },
      }
    }

    while active > 0 {
      let (index, weight, lane, _node_peak, result) =
        receiver.recv().map_err(|error| {
          format!("aggregate scheduler drain failed: {error}")
        })?;
      if in_flight.get(index).copied().unwrap_or(false) {
        in_flight[index] = false;
        active -= 1;
        reserved = reserved.saturating_sub(weight);
        if let Some(k) = lane {
          lanes[k].reserved = lanes[k].reserved.saturating_sub(weight);
          lanes[k].active = lanes[k].active.saturating_sub(1);
        }
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
    if !lanes.is_empty() {
      eprintln!(
        "[aggregate] lane peaks (resident at slot completions): {}",
        lanes
          .iter()
          .map(|lane| format!(
            "node {}: {} GiB of {} GiB",
            lane.domain.node,
            format_gib(lane.peak_resident),
            format_gib(lane.domain.mem_bytes)
          ))
          .collect::<Vec<_>>()
          .join(", ")
      );
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
    .filter(|spec| matches!(spec.op, PlanOp::Leaf(_)) && spec.shape.is_some())
    .count();
  let structural = specs.iter().filter(|spec| spec.structural).count();
  let imported = specs
    .iter()
    .filter(|s| {
      matches!(s.op, PlanOp::Leaf(_))
        && s.kind == ChildKind::Aggr
        && s.shape.is_none()
    })
    .count();
  let policy = format!(
    "{wraps} wraps, {imported} imported healed leaves, {} direct IxVM leaves",
    leaves - wraps - imported
  );
  eprintln!(
    "[aggregate] plan: {policy} + {} binary joins ({structural} structural; threshold > {threshold} subject leaves)",
    specs.len() - leaves
  );
  for (index, spec) in specs.iter().enumerate() {
    match spec.op {
      PlanOp::Leaf(shard) => {
        let mode = if spec.kind == ChildKind::Ixvm {
          "raw shard"
        } else if spec.shape.is_none() {
          "healed shard"
        } else {
          "wrap shard"
        };
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
  let mut specs = build_specs(
    &prepared,
    config.verify_idx,
    config.aggr_idx,
    config.structural_above,
    config.direct_joins,
    &aggr_vk,
    &allowed,
    config.cache_fri_bytes,
  )?;
  let mut replay_plan = config
    .reprove_slot
    .map(|target| plan_replay(&specs, target))
    .transpose()?;
  let specs_at = Instant::now();
  if config.plan_only {
    print_plan(&specs, &prepared.shards, config.structural_above);
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
  let needs_input_proofs = replay_plan.as_ref().is_none_or(|plan| {
    plan.needs_input_proofs
      || (!config.proof_hexes.trim().is_empty()
        && plan
          .children
          .iter()
          .any(|index| matches!(specs[*index].op, PlanOp::Leaf(_))))
  });
  let proofs = if needs_input_proofs {
    let wrappers = load_input_proofs(
      config.proof_hexes,
      &store_dir,
      &prepared.shards,
      prepared.partial,
    )?;
    let inputs = wrappers
      .into_par_iter()
      .enumerate()
      .map(|(index, wrapper)| {
        import_shard_proof(
          config.ixvm_system,
          config.aggr_system,
          config.verify_idx,
          config.aggr_idx,
          &allowed,
          prepared.shards[index].statement.clone(),
          &wrapper,
          None,
        )
      })
      .collect::<Result<Vec<_>, _>>()?;
    bind_imported_specs(&mut specs, &inputs, &aggr_vk, config.cache_fri_bytes);
    replay_plan = config
      .reprove_slot
      .map(|target| plan_replay(&specs, target))
      .transpose()?;
    Some(inputs)
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
    let imported = proofs.as_ref().map_or(0, Vec::len);
    if imported != shards {
      return Err(format!(
        "verified {imported} shard proofs but the manifest has {shards} shards"
      ));
    }
    eprintln!(
      "[verify] OK: composed verdict — all {shards} shards proven + disjoint cover ({} proofs verified natively in {:.1}s; claims {:.1}s)",
      imported,
      (proofs_at - specs_at).as_secs_f64(),
      (prepared_at - parsed_at).as_secs_f64(),
    );
    return Ok(String::new());
  }
  print_plan(&specs, &prepared.shards, config.structural_above);
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
    "[aggregate] scheduler: jobs={jobs_label}, RAM budget {} GiB; wrap/self base {} GiB, direct {} GiB, mixed {} GiB, flat self +1 MiB/subject, structural self +1.25 MiB/subject (minimum {} GiB above {} subjects)",
    format_gib(config.ram_budget_bytes),
    format_gib(STRUCTURAL_RAM_BYTES),
    format_gib(DIRECT_RAM_BYTES),
    format_gib(MIXED_RAM_BYTES),
    format_gib(2 * STRUCTURAL_RAM_BYTES),
    STRUCTURAL_LARGE_SUBJECTS,
  );
  let slots = run_scheduler(context, config.jobs, config.ram_budget_bytes)?;
  let root = slots.last().ok_or("aggregate plan produced no root slot")?;
  if root.kind != ChildKind::Aggr {
    return Err("aggregate plan produced a raw IxVM root".into());
  }
  validate_root_statement(&prepared, &root.statement)?;
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

  #[test]
  fn structural_ram_covers_measured_mathlib_peaks() {
    // Subject counts and query-record peaks (rounded up to GiB) from the
    // 2026-09-09 Mathlib run, including the slot behind the packed-node OOM.
    for (subjects, peak_gib) in [
      (5_371, 196),
      (11_972, 203),
      (19_751, 208),
      (55_496, 212),
      (91_068, 381),
      (91_620, 257),
      (96_048, 249),
      (126_527, 381),
      (187_668, 384),
      (314_195, 455),
    ] {
      assert!(shape_ram_bytes(9, subjects) >= peak_gib * GIB);
    }
    // The new term belongs to structural self-pairs. Keep flat, direct,
    // mixed and wrap reservations distinct.
    for (shape, gib) in [(0, 195), (2, 180), (5, 199), (8, 180), (9, 200)] {
      assert_eq!(shape_ram_bytes(shape, 4096), gib * GIB);
    }
    assert_eq!(shape_ram_bytes(9, 65_536), 275 * GIB);
    assert_eq!(shape_ram_bytes(9, 65_537), 390 * GIB);
  }

  /// The pre-function-groups direct-pair reservation the pipeline
  /// arithmetic below was written against (one queue per 453 GiB lane).
  const TEST_DIRECT: usize = 390 * GIB;

  fn direct_batch() -> Vec<(usize, usize)> {
    (0..6).map(|i| (i, TEST_DIRECT)).collect()
  }

  #[test]
  fn pipelines_pack_two_queues_per_lane_when_both_fit() {
    // Six 180 GiB direct joins over three 453 GiB lanes: two queues per
    // lane, each with its 40 GiB lookahead record (2 x 220 <= 453; the
    // process budget must hold all six, 6 x 220 = 1320 GiB).
    let batch: Vec<(usize, usize)> =
      (0..12).map(|i| (i, DIRECT_RAM_BYTES)).collect();
    let packed = plan_pipelines(&batch, &[453 * GIB; 3], 6, 1400 * GIB, 2);
    assert_eq!(packed.len(), 6);
    assert!(packed.iter().all(|p| p.lookahead && p.slots.len() == 2));
    for k in 0..3 {
      assert_eq!(packed.iter().filter(|p| p.lane == Some(k)).count(), 2);
    }
    assert_eq!(pipeline_reservation(&packed), 6 * 220 * GIB);
    // One queue per lane keeps the previous placement.
    let single = plan_pipelines(&batch, &[453 * GIB; 3], 6, 1400 * GIB, 1);
    assert_eq!(single.len(), 3);
    assert!(single.iter().all(|p| p.lookahead && p.slots.len() == 4));
    // A second queue that would not fit beside the first stays off the lane.
    let tight = plan_pipelines(&batch, &[300 * GIB; 3], 6, 1400 * GIB, 2);
    assert_eq!(tight.len(), 3);
    // With 1300 GiB the sixth queue has no room for its record.
    let capped = plan_pipelines(&batch, &[453 * GIB; 3], 6, 1300 * GIB, 2);
    assert_eq!(capped.len(), 6);
    assert_eq!(capped.iter().filter(|p| p.lookahead).count(), 5);
  }

  fn pipeline_reservation(pipelines: &[PipelineQueue]) -> usize {
    pipelines
      .iter()
      .map(|p| p.weight + if p.lookahead { LOOKAHEAD_RAM_BYTES } else { 0 })
      .sum()
  }

  #[test]
  fn pipelines_obey_jobs_one_on_multiple_nodes() {
    let pipelines =
      plan_pipelines(&direct_batch(), &[453 * GIB; 3], 1, 1300 * GIB, 1);
    assert_eq!(pipelines.len(), 1);
    assert_eq!(pipelines[0].slots, (0..6).collect::<Vec<_>>());
    assert!(pipelines[0].lookahead);
    assert_eq!(pipeline_reservation(&pipelines), 430 * GIB);
  }

  #[test]
  fn pipelines_obey_combined_budget_including_lookahead() {
    for (budget_gib, overlaps) in [(800, 0), (820, 1), (860, 2)] {
      let pipelines = plan_pipelines(
        &direct_batch(),
        &[453 * GIB; 3],
        6,
        budget_gib * GIB,
        1,
      );
      // Keep two concurrent provers even when neither can prepare ahead.
      assert_eq!(pipelines.len(), 2);
      assert_eq!(pipelines.iter().filter(|p| p.lookahead).count(), overlaps);
      assert!(pipeline_reservation(&pipelines) <= budget_gib * GIB);
      let mut assigned: Vec<_> =
        pipelines.iter().flat_map(|p| p.slots.iter().copied()).collect();
      assigned.sort_unstable();
      assert_eq!(assigned, (0..6).collect::<Vec<_>>());
    }
  }

  #[test]
  fn pipelines_overlap_without_numa() {
    let pipelines = plan_pipelines(&direct_batch(), &[], 3, 1300 * GIB, 1);
    assert_eq!(pipelines.len(), 3);
    assert!(pipelines.iter().all(|p| p.lane.is_none() && p.lookahead));
    assert!(pipelines.iter().all(|p| p.slots.len() == 2));
    assert_eq!(pipeline_reservation(&pipelines), 1290 * GIB);

    let single = plan_pipelines(&direct_batch(), &[], 1, 430 * GIB, 1);
    assert_eq!(single.len(), 1);
    assert!(single[0].lane.is_none() && single[0].lookahead);
  }

  #[test]
  fn pipelines_require_local_room_for_the_next_record() {
    let pipelines = plan_pipelines(
      &direct_batch(),
      &[390 * GIB, 453 * GIB],
      2,
      1000 * GIB,
      1,
    );
    assert_eq!(pipelines.len(), 2);
    let tight = pipelines.iter().find(|p| p.lane == Some(0)).unwrap();
    let roomy = pipelines.iter().find(|p| p.lane == Some(1)).unwrap();
    assert!(!tight.lookahead);
    assert!(roomy.lookahead);
    assert_eq!(pipeline_reservation(&pipelines), 820 * GIB);
  }

  #[test]
  fn pipelines_handle_mixed_weights_and_leave_oversized_jobs() {
    let batch = vec![
      (0, 500 * GIB),
      (1, TEST_DIRECT),
      (2, TEST_DIRECT),
      (3, STRUCTURAL_RAM_BYTES),
    ];
    let pipelines =
      plan_pipelines(&batch, &[453 * GIB, 220 * GIB], 3, 700 * GIB, 1);
    assert_eq!(pipelines.len(), 2);
    assert_eq!(pipelines[0].slots, vec![1, 2]);
    assert_eq!(pipelines[1].slots, vec![3]);
    assert!(pipelines[0].lookahead);
    assert!(!pipelines[1].lookahead);
    assert_eq!(pipeline_reservation(&pipelines), 625 * GIB);
  }

  #[test]
  fn pipelines_skip_overlap_without_spare_ram_or_another_job() {
    let full = plan_pipelines(&direct_batch(), &[], 1, TEST_DIRECT, 1);
    assert_eq!(full.len(), 1);
    assert!(!full[0].lookahead);
    let single = plan_pipelines(&[(0, TEST_DIRECT)], &[], 1, 1300 * GIB, 1);
    assert_eq!(single.len(), 1);
    assert!(!single[0].lookahead);
    assert!(plan_pipelines(&direct_batch(), &[], 3, 0, 1).is_empty());
    assert!(plan_pipelines(&direct_batch(), &[], 0, 1300 * GIB, 1).is_empty());
  }

  fn lane(
    node: u32,
    budget: usize,
    reserved: usize,
    active: usize,
  ) -> NumaLane {
    NumaLane {
      domain: crate::numa::Domain { node, cpus: vec![0], mem_bytes: budget },
      pool: Arc::new(
        rayon::ThreadPoolBuilder::new().num_threads(1).build().unwrap(),
      ),
      budget,
      reserved,
      active,
      peak_resident: 0,
    }
  }

  #[test]
  fn numa_lane_prefers_idle_then_most_free() {
    let lanes =
      vec![lane(0, 400, 200, 1), lane(1, 400, 0, 0), lane(2, 400, 100, 0)];
    // idle lanes 1 and 2 beat the busy lane 0; lane 1 has more free RAM.
    assert_eq!(choose_numa_lane(&lanes, 195, true), Some(1));
    // a 390 slot fits only lane 1.
    assert_eq!(choose_numa_lane(&lanes, 390, true), Some(1));
  }

  #[test]
  fn numa_lane_packs_at_most_two_and_only_when_allowed() {
    let lanes = vec![lane(0, 400, 195, 1), lane(1, 400, 390, 2)];
    assert_eq!(choose_numa_lane(&lanes, 195, true), Some(0));
    assert_eq!(choose_numa_lane(&lanes, 195, false), None);
    // lane 1 already holds two slots: never a third even when packing.
    let lanes = vec![lane(1, 900, 390, 2)];
    assert_eq!(choose_numa_lane(&lanes, 195, true), None);
  }

  #[test]
  fn numa_lane_none_when_nothing_fits() {
    let lanes = vec![lane(0, 400, 0, 0)];
    assert_eq!(choose_numa_lane(&lanes, 401, true), None);
  }

  #[test]
  fn structural_packing_preserves_small_pairs_and_rejects_oom_pair() {
    let budget = 453 * GIB;
    for (left, right, fits) in [
      (9_480, 10_271, true),
      (23_993, 24_805, true),
      (91_620, 96_048, false),
      // Mathlib slots 140/355 were live together when node 0 OOMed.
      (187_668, 13_023, false),
    ] {
      let left = shape_ram_bytes(9, left);
      let right = shape_ram_bytes(9, right);
      // Either join fits individually, but packing depends on their sum.
      assert!(left <= budget && right <= budget);
      for (reserved, weight) in [(left, right), (right, left)] {
        let lanes = vec![lane(0, budget, reserved, 1)];
        assert_eq!(choose_numa_lane(&lanes, weight, true), fits.then_some(0));
      }
    }
  }

  #[test]
  fn large_structural_join_needs_unpinned_fallback() {
    // Mathlib slot 266: larger than a node reservation, smaller than the
    // process budget. The scheduler must wait and run it alone unpinned.
    let weight = shape_ram_bytes(9, 314_195);
    assert!(weight < 1300 * GIB);
    let lanes = vec![lane(0, 453 * GIB, 0, 0), lane(1, 453 * GIB, 0, 0)];
    assert_eq!(choose_numa_lane(&lanes, weight, true), None);
  }

  #[test]
  fn structural_reservation_overflow_cannot_enable_packing() {
    let weight = shape_ram_bytes(9, usize::MAX);
    assert_eq!(weight, usize::MAX);
    let lanes = vec![lane(0, usize::MAX, GIB, 1)];
    assert_eq!(choose_numa_lane(&lanes, weight, true), None);
  }

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

  /// Small real proofs for testing host transport and backend authentication.
  /// Circuit semantics are exercised separately by the real IxVM smoke test.
  pub(super) fn transport_system(input_size: usize) -> AiurSystem {
    use aiur::bytecode::{
      Block, Circuit, Ctrl, Function, FunctionLayout, Toplevel,
    };
    use multi_stark::types::{CommitmentParameters, FriParameters};
    let layout =
      FunctionLayout { input_size, selectors: 1, auxiliaries: 1, lookups: 1 };
    AiurSystem::build(
      Toplevel {
        functions: vec![Function {
          body: Block { ops: vec![], ctrl: Ctrl::Return(0, vec![]) },
          layout,
          entry: true,
          constrained: true,
        }],
        memory_sizes: vec![],
        // The singleton partition the Lean compiler emits by default.
        circuits: vec![Circuit { members: vec![0], layout }],
      },
      CommitmentParameters { log_blowup: 1, cap_height: 0 },
      FriParameters {
        log_final_poly_len: 0,
        max_log_arity: 1,
        num_queries: 4,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: 0,
      },
    )
  }

  #[test]
  fn stage2_authenticates_healed_leaves_and_updates_mixed_shapes() {
    let env = ixon::Env::new();
    let a = store_axiom(&env, Expr::sort(0), vec![]);
    let b = store_axiom(&env, Expr::reference(0, vec![]), vec![a.clone()]);
    let manifest = ShardManifest {
      num_shards: 2,
      shards: vec![shard(0, a), shard(1, b)],
      total_cross_ingress: 0,
      tree: None,
    };
    let prepared = prepare_run(&env, &manifest).unwrap();
    let ixvm = transport_system(8);
    let aggr = transport_system(16);
    let ixvm_vk = aiur::vk_codec::aiur_system_to_bytes(&ixvm).unwrap();
    let aggr_vk = aiur::vk_codec::aiur_system_to_bytes(&aggr).unwrap();
    let allowed = allowed_blob(&ixvm_vk, 0, &aggr_vk, 0);
    let mut specs =
      build_specs(&prepared, 0, 0, 4096, true, &aggr_vk, &allowed, &[0; 40])
        .unwrap();
    let root_claim = specs[2].statement.claim_bytes.clone();
    let make_wrapper = |index: usize, healed| {
      let statement = &prepared.shards[index].statement;
      let outer = if healed {
        aggregate_outer_claim(0, &allowed, &statement.claim_bytes)
      } else {
        inner_claim(0, &statement.claim_bytes)
      };
      let mut io =
        IOBuffer { data: FxHashMap::default(), map: FxHashMap::default() };
      let system = if healed { &aggr } else { &ixvm };
      let (_, proof) = system.prove(0, &outer[2..], &mut io);
      IxonProof::new(statement.claim.clone(), proof.to_bytes().unwrap())
    };
    let healed = make_wrapper(0, true);
    let raw = make_wrapper(1, false);
    let import = |index: usize, wrapper: &IxonProof, identity: &[u8]| {
      import_shard_proof(
        &ixvm,
        &aggr,
        0,
        0,
        identity,
        prepared.shards[index].statement.clone(),
        wrapper,
        None,
      )
    };
    let inputs = vec![
      import(0, &healed, &allowed).unwrap(),
      import(1, &raw, &allowed).unwrap(),
    ];
    assert_eq!(inputs[0].kind, ChildKind::Aggr);
    assert_eq!(inputs[1].kind, ChildKind::Ixvm);
    bind_imported_specs(&mut specs, &inputs, &aggr_vk, &[0; 40]);
    assert!(specs[0].shape.is_none());
    assert_eq!(specs[2].shape, Some(4));
    assert_eq!(specs[2].statement.claim_bytes, root_claim);
    assert!(
      plan_replay(&specs, 0).unwrap_err().contains("imported healed leaf")
    );
    assert!(plan_replay(&specs, 2).unwrap().needs_input_proofs);
    assert!(import(1, &healed, &allowed).is_err());
    let mut other_identity = allowed.clone();
    other_identity[0] ^= 1;
    assert!(import(0, &healed, &other_identity).is_err());
    let malformed = IxonProof::new(healed.claim.clone(), vec![0xff; 3]);
    assert!(import(0, &malformed, &allowed).is_err());
  }
}
