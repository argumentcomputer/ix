//! Sharding: partition an environment's blocks into shards that minimize
//! cross-shard delta-unfold ingress (see `plans/sharding.md`). Two driving
//! modes share the same min-cut machinery:
//!
//! - **Fixed count** ([`Hypergraph::partition`], the `--shards N` CLI path):
//!   recursive *balanced* min-cut bisection into exactly `N` shards — even
//!   per-shard work, the bisection tree doubling as the aggregation tree.
//! - **Cap / packing** ([`partition_for_cycle_cap`], the default and
//!   `--max-cycles`/`--max-ram` paths): **bin-pack to the cap** — the fewest
//!   shards that each stay under a per-shard cycle (hence prover-RAM) budget,
//!   each filled as full as the dependency structure allows. This does *not*
//!   balance: uniformity over-shards (every shard left partly empty), whereas
//!   packing hits `≈⌈total/cap⌉` shards. It still uses a fine min-cut
//!   pre-partition for a **cut-coherent order** so dependency overlap packs into
//!   the same shard (overlap paid once, not re-ingressed per shard).
//!
//! **Why the order comes from min-cut.** Lean typecheck is reduction-dominated:
//! across Init/Std/Mathlib (mathlib's 631k blocks included) own-bytes is only
//! 2.6–7% of member cost, so on Zisk alone cross-ingress is a ≤3% cost term and a
//! plain block-id order packs within ~2% of min-cut. min-cut still earns the
//! default because the same `.ixprof`/`.ixes` also drives Aiur, where ingress is
//! a first-order cost; because it stays robust if an ingress-heavy env flips that
//! balance; and because it keeps each shard's injected closure small, which the
//! 512 MB guest heap requires. A cheaper id/dfs order trades those properties for
//! ~2% on Zisk only. The cap planner ([`partition_for_cycle_cap`]) is
//! order-agnostic, so the order is a pluggable choice.
//!
//! ## Model
//!
//! Both modes view the env as a **weighted hypergraph** under the
//! connectivity-1 (km1) metric:
//!
//! - **Vertices** are blocks, weighted by `heartbeats` (the balance metric).
//! - **Nets** are blocks `p` that get delta-unfolded by someone; the net
//!   connects `p`'s home plus every block that unfolds `p`, and is weighted by
//!   `serialized_size(p)` (the ingress cost paid to pull `p`'s body into a
//!   foreign shard).
//! - The objective is `Σ_p  size(p) · (λ(p) − 1)`, where `λ(p)` is the number
//!   of distinct shards spanning `net(p)`. Because the home block is always a
//!   pin, `λ(p) − 1` counts exactly the foreign shards that must ingress `p` —
//!   i.e. total cross-shard ingress bytes.
//!
//! ## Algorithm
//!
//! **Recursive bisection.** Balanced min-cut bisection recursively splits the
//! block hypergraph, allocating the `N`-shard budget between the two sides at
//! each step (so any `N` works, not just powers of two); the bisection tree is
//! the future proof-aggregation tree. On recursion we apply **cut-net
//! splitting**: a net already cut at an upper level is restricted to its pins
//! within each half so it is not recounted deeper.
//!
//! **Multilevel coarsening.** Each individual bisection is solved with a
//! multilevel V-cycle rather than flat local search: we *coarsen* the
//! sub-hypergraph by repeatedly merging tightly-coupled blocks into
//! supervertices (heavy-edge matching) until only a few hundred remain, decide
//! the cut once on that tiny graph (greedy graph-growing + Fiduccia–Mattheyses
//! to convergence), then *uncoarsen* — projecting the cut back down and
//! boundary-refining with FM at each level. Deciding global structure on the
//! small graph and only ever refining locally on the big ones is what keeps
//! large environments (mathlib ≈ 631k blocks) partitioning in seconds. The
//! partitioner is fully self-contained — no external partitioner dependency.

// This module works throughout with `u32` block/vertex ids, `u64`/`u128` weights
// (heartbeats, ingress bytes), and `f64` balance ratios. The narrowing/precision
// casts between them are pervasive and intentional — envs are far below `u32`
// limits and the balance arithmetic tolerates `f64` rounding — so the lossy-cast
// lints are allowed module-wide rather than annotated at ~30 sites. The binary
// manifest decoder maps decode failures to a single message (`map_err_ignore`),
// and a few matching loops mutate the array they index (`needless_range_loop`).
#![allow(
  clippy::cast_possible_truncation,
  clippy::cast_precision_loss,
  clippy::cast_sign_loss,
  clippy::map_err_ignore,
  clippy::needless_range_loop
)]

use rustc_hash::{FxHashMap, FxHashSet};
use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::sync::atomic::{AtomicU32, AtomicUsize, Ordering};
use std::time::Instant;

use crate::profile::{BlockEntry, BlockProfile};
use ix_common::address::Address;

/// Recurse the two halves of a bisection in parallel (rayon) when the parent
/// sub-problem is at least this large; below it the join overhead isn't worth
/// it. The two halves own disjoint block sets, so their writes to the shared
/// (atomic) assignment buffer never alias.
const PARALLEL_THRESHOLD: usize = 4_000;

/// Target vertex count for the coarsest graph in the multilevel V-cycle. We
/// coarsen down to roughly this many supervertices, decide the global cut there
/// (cheaply, at high quality), then uncoarsen and locally refine. Small enough
/// that greedy + full FM on it is instant; large enough to still admit a
/// balanced bisection.
const COARSEST_TARGET: usize = 256;

/// Stop coarsening if a matching pass fails to shrink the graph by at least
/// `1 − COARSEN_STALL_RATIO` (here 10%). Guards against spinning on graphs with
/// few matchable pairs (very sparse or hub-dominated subs); [`bisect`] then
/// falls back to refining whatever level was reached.
const COARSEN_STALL_RATIO: f64 = 0.90;

/// Nets larger than this are skipped when rating vertices for heavy-edge
/// matching: a co-pin of an `m`-pin net earns only `weight/(m−1)` toward a
/// match, so large nets carry negligible clustering signal while costing `O(m)`
/// to scan. Keeping the matching rating near-linear bounds coarsening time.
const MATCH_NET_CAP: usize = 100;

/// FM passes per level during uncoarsening. The projected partition is already
/// globally good, so a single boundary-refinement pass suffices to clean up each
/// level's cut frontier (passes also stop early once one yields no improvement).
const REFINE_PASSES: u32 = 1;

/// Initial-partition restarts on the (tiny) coarsest graph: greedy graph-growing
/// from this many diverse deterministic seeds, each FM-refined, keeping the
/// lowest-cut result. Graph-growing from a single seed can "leak" across a thin
/// bridge between two clusters; diverse seeds (one of which starts far from the
/// bridge) recover the clean cut. Cheap — the coarsest graph is ≈
/// [`COARSEST_TARGET`] vertices and this runs once per bisection.
const INITIAL_RESTARTS: usize = 4;

/// Bisections of at least this many vertices are logged by [`PartitionProgress`]
/// (purely an observability threshold — a slow run should never look stuck).
const PROGRESS_BISECT_LOG: usize = 50_000;

/// Nets with more pins than this are "hubs" (e.g. a core lemma delta-unfolded by
/// thousands of blocks). They are cut in essentially any balanced partition, so
/// they carry no useful refinement gradient, and visiting all their pins per
/// move would make FM O(pins-of-hub) per step. Refinement (greedy growth + FM)
/// therefore ignores them; the reported [`Hypergraph::connectivity_objective`]
/// still counts every net in full. After cut-net splitting a former hub may
/// shrink below the cap at deeper recursion levels and become active again.
const FM_NET_CAP: usize = 400;

/// Maximum FM passes per bisection (a safety bound against pathological
/// oscillation; passes normally converge well before this).
const MAX_FM_PASSES: u32 = 10;

/// Cap-sharding granularity: the fine min-cut pre-partition that supplies the
/// **cut-coherent block order** for [`partition_for_cycle_cap`] is sized to
/// roughly this many pieces per cap of work. Finer pieces let the greedy packer
/// fill each shard closer to the cap and keep dependency-overlapping blocks in
/// the same run (so cross-ingress only appears at the seams between coherent
/// runs); the count is still bounded by the block count, so the pre-partition
/// stays cheap.
const PACK_PIECES_PER_CAP: u128 = 32;

/// A weighted hypergraph derived from a [`BlockProfile`]. Vertex ids are block
/// ids (identical to the profile's). Nets are stored with global pins.
pub struct Hypergraph {
  /// Vertex (block) weights = predicted Zisk guest STEPS ([`block_step_cost`]:
  /// reduction `heartbeats` + own ingress bytes), so the balanced partition
  /// equalizes predicted per-shard *cycles* (the prover-RAM driver) rather than
  /// heartbeats alone — which underweighted ingress-heavy shards.
  vweight: Vec<u64>,
  /// Net weights = serialized_size of the unfolded block.
  net_weight: Vec<u64>,
  /// Net pins (global block ids). `pins[i]` are the pins of net `i`.
  net_pins: Vec<Vec<u32>>,
}

impl Hypergraph {
  /// Build the partition hypergraph from a profile. A net is created for every
  /// block that has at least one *external* consumer (i.e. is delta-unfolded by
  /// some other block); singleton nets are omitted as they can never be cut.
  pub fn from_profile(profile: &BlockProfile) -> Hypergraph {
    let n = profile.num_blocks();
    let vweight: Vec<u64> =
      (0..n as u32).map(|i| block_step_cost(profile.block(i))).collect();
    let (row, col) = profile.consumers_csr();
    let mut net_weight = Vec::new();
    let mut net_pins = Vec::new();
    for p in 0..n {
      let consumers = &col[row[p]..row[p + 1]];
      if consumers.is_empty() {
        continue;
      }
      let mut pins = Vec::with_capacity(consumers.len() + 1);
      pins.push(p as u32); // home pin
      pins.extend_from_slice(consumers);
      net_weight.push(u64::from(profile.block(p as u32).serialized_size));
      net_pins.push(pins);
    }
    Hypergraph { vweight, net_weight, net_pins }
  }

  pub fn num_vertices(&self) -> usize {
    self.vweight.len()
  }

  pub fn num_nets(&self) -> usize {
    self.net_pins.len()
  }

  /// The connectivity-1 (km1) objective for a given shard assignment:
  /// `Σ_net  weight · (λ − 1)`, where `λ` is the number of distinct shards the
  /// net's pins fall into. This is the total cross-shard ingress in bytes.
  pub fn connectivity_objective(&self, shard_of: &[u32]) -> u128 {
    let mut total: u128 = 0;
    let mut seen: FxHashSet<u32> = FxHashSet::default();
    for (i, pins) in self.net_pins.iter().enumerate() {
      seen.clear();
      for &v in pins {
        seen.insert(shard_of[v as usize]);
      }
      let lambda = seen.len() as u128;
      if lambda > 1 {
        total += u128::from(self.net_weight[i]) * (lambda - 1);
      }
    }
    total
  }

  /// Partition the blocks into `num_shards` shards via recursive bisection.
  /// Returns the shard id (in `0..num_shards`) for every block id. `epsilon` is
  /// the per-bisection balance tolerance (e.g. `0.05` for ±5%). `num_shards`
  /// need not be a power of two.
  pub fn partition(&self, num_shards: usize, epsilon: f64) -> Vec<u32> {
    self.partition_with_tree(num_shards, epsilon).0
  }

  /// Like [`Self::partition`], but also returns the **bisection tree** — the
  /// binary tree of min-cut splits whose leaves are the shard ids. Reusing this
  /// as the proof-aggregation tree (rather than an arbitrary flat fold)
  /// discharges each cross-shard assumption at the lowest common ancestor of the
  /// shards that share it; the per-bisection min-cut means sibling subtrees have
  /// the thinnest possible interface, so most discharge happens low in the tree.
  pub fn partition_with_tree(
    &self,
    num_shards: usize,
    epsilon: f64,
  ) -> (Vec<u32>, AggNode) {
    let n = self.num_vertices();
    if num_shards <= 1 {
      return (vec![0u32; n], AggNode::Leaf(0)); // everything in shard 0
    }
    // Cap each block's balance weight at the ideal per-shard heartbeats
    // (total / num_shards). This keeps balancing heartbeat-aware while a balanced
    // split is achievable (few shards), but stops a single oversized *atomic*
    // block from skewing every split toward it once there are many shards. The
    // resulting heartbeat imbalance is accepted; the goal is `num_shards`
    // **non-empty** parallel shards with minimal cross-shard ingress.
    let total_hb: u128 = self.vweight.iter().map(|&w| u128::from(w)).sum();
    let cap =
      (total_hb / num_shards as u128).max(1).min(u128::from(u64::MAX)) as u64;
    let sub = SubHyper::full(self, cap);
    // Atomic assignment buffer: independent subtrees own disjoint block sets, so
    // they can be partitioned on separate threads without their writes aliasing.
    let shard_of: Vec<AtomicU32> = (0..n).map(|_| AtomicU32::new(0)).collect();
    let prog = PartitionProgress::new(num_shards);
    let tree = rec_bisect(&sub, num_shards, 0, epsilon, &shard_of, &prog);
    prog.done();
    let assignment = shard_of.into_iter().map(AtomicU32::into_inner).collect();
    (assignment, tree)
  }
}

// ============================================================================
// Bisection / aggregation tree
// ============================================================================

/// The bisection tree produced by recursive min-cut partitioning: leaves are
/// shard ids, internal nodes are the two halves of a min-cut split. Reused as
/// the proof-aggregation tree so cross-shard assumptions discharge at the lowest
/// common ancestor of the shards that share them (see module docs and
/// [`agg_plan`]). Serialized into the `.ixes` manifest so the prover can fold
/// along it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AggNode {
  /// A single shard, identified by its id.
  Leaf(u32),
  /// A min-cut split into a left and right subtree.
  Internal(Box<AggNode>, Box<AggNode>),
}

impl AggNode {
  /// Number of shard leaves under this node.
  pub fn num_leaves(&self) -> usize {
    match self {
      AggNode::Leaf(_) => 1,
      AggNode::Internal(l, r) => l.num_leaves() + r.num_leaves(),
    }
  }

  /// The smallest shard id under this node — its left-to-right position. Used to
  /// keep aggregation children in shard order (so the subject merkle-fold stays
  /// the left-associative order the agg guest reproduces).
  pub fn min_leaf(&self) -> u32 {
    match self {
      AggNode::Leaf(id) => *id,
      AggNode::Internal(l, _) => l.min_leaf(),
    }
  }

  /// Prune to the leaves selected by `keep`: dropped leaves disappear and an
  /// internal node that loses one child collapses to the survivor. Returns
  /// `None` when nothing remains. Lets a prover fold along the tree even when
  /// only a subset of shards was proven (empty shards, `--only-shard`).
  pub fn prune(&self, keep: &impl Fn(u32) -> bool) -> Option<AggNode> {
    match self {
      AggNode::Leaf(id) => keep(*id).then_some(AggNode::Leaf(*id)),
      AggNode::Internal(l, r) => match (l.prune(keep), r.prune(keep)) {
        (Some(a), Some(b)) => Some(AggNode::Internal(Box::new(a), Box::new(b))),
        (Some(a), None) | (None, Some(a)) => Some(a),
        (None, None) => None,
      },
    }
  }

  /// Preorder serialization: `0u8, id(4)` for a leaf; `1u8, <left>, <right>` for
  /// an internal node.
  fn put(&self, out: &mut Vec<u8>) {
    match self {
      AggNode::Leaf(id) => {
        out.push(0);
        out.extend_from_slice(&id.to_le_bytes());
      },
      AggNode::Internal(l, r) => {
        out.push(1);
        l.put(out);
        r.put(out);
      },
    }
  }

  /// Inverse of [`Self::put`], reading from a cursor.
  fn get(c: &mut Cur<'_>) -> Result<AggNode, String> {
    match c.u8()? {
      0 => Ok(AggNode::Leaf(c.u32()?)),
      1 => {
        let l = AggNode::get(c)?;
        let r = AggNode::get(c)?;
        Ok(AggNode::Internal(Box::new(l), Box::new(r)))
      },
      t => Err(format!("bad AggNode tag {t}")),
    }
  }
}

/// One step of an aggregation fold plan, in post order: every `Agg`'s child
/// indices refer to *earlier* entries in the plan, and the last entry is the
/// root. The prover materializes a slot per entry — `Leaf(id)` is shard `id`'s
/// leaf proof; `Agg(children)` folds those slots' proofs in one agg call.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FoldOp {
  Leaf(u32),
  Agg(Vec<usize>),
}

/// Lower the bisection tree to an arity-bounded fold plan. The binary tree is
/// *collapsed* so each agg call folds up to `arity` whole subtrees (never
/// splitting a subtree across calls), keeping the agg-proof count ~`N/(arity-1)`
/// — a strict binary fold would be ~`N` agg proofs, dominating cost. Children of
/// each agg are emitted in shard order so the subject merkle-fold matches the
/// guest's left-associative join.
pub fn agg_plan(tree: &AggNode, arity: usize) -> Vec<FoldOp> {
  let arity = arity.max(2);
  let mut ops: Vec<FoldOp> = Vec::new();
  build_plan(tree, arity, &mut ops);
  ops
}

/// Emit `node`'s plan entries; return the index of the entry representing it.
fn build_plan(node: &AggNode, arity: usize, ops: &mut Vec<FoldOp>) -> usize {
  match node {
    AggNode::Leaf(id) => {
      ops.push(FoldOp::Leaf(*id));
      ops.len() - 1
    },
    AggNode::Internal(l, r) => {
      // Collapse the binary subtree into up to `arity` child subtrees: start
      // from the two halves and repeatedly split the *largest* still-internal
      // frontier node until we have `arity` children or all are leaves. This
      // keeps tightly-coupled siblings together while bounding the fan-in.
      let mut frontier: Vec<&AggNode> = vec![l, r];
      while frontier.len() < arity {
        let largest = frontier
          .iter()
          .enumerate()
          .filter(|(_, nd)| matches!(nd, AggNode::Internal(_, _)))
          .max_by_key(|(_, nd)| nd.num_leaves())
          .map(|(i, _)| i);
        let Some(i) = largest else { break }; // all leaves: cannot expand
        let AggNode::Internal(l, r) = frontier.swap_remove(i) else {
          unreachable!()
        };
        frontier.push(l);
        frontier.push(r);
      }
      // Shard order keeps the merkle subject-fold left-associative.
      frontier.sort_by_key(|nd| nd.min_leaf());
      let child_idxs: Vec<usize> =
        frontier.iter().map(|c| build_plan(c, arity, ops)).collect();
      ops.push(FoldOp::Agg(child_idxs));
      ops.len() - 1
    },
  }
}

/// A borrowed, cut-relevant view of one hypergraph level — either a top-level
/// [`SubHyper`] or a coarsened [`CoarseLevel`]. The greedy / FM machinery is
/// written against this view so it runs unchanged at every level of the
/// multilevel hierarchy. `Copy` (four slice references), so it is passed by
/// value freely.
#[derive(Clone, Copy)]
struct Level<'a> {
  /// vertex weights (heartbeats)
  vw: &'a [u64],
  /// balance weights (capped heartbeats)
  bw: &'a [u64],
  /// nets: (weight, pins)
  nets: &'a [(u64, Vec<u32>)],
  /// vertex -> incident net indices
  vnets: &'a [Vec<u32>],
}

impl<'a> Level<'a> {
  fn num_vertices(&self) -> usize {
    self.vw.len()
  }
}

/// A sub-hypergraph used during recursion, with vertices re-indexed locally and
/// nets restricted (cut-net split) to the vertices it contains.
struct SubHyper {
  /// local vertex -> global block id
  global: Vec<u32>,
  /// local vertex weights (heartbeats)
  vw: Vec<u64>,
  /// balance weights: each block's heartbeats capped at `cap` (or all 1 if every
  /// capped weight is zero in this sub)
  bw: Vec<u64>,
  /// restricted nets: (weight, local pins)
  nets: Vec<(u64, Vec<u32>)>,
  /// local vertex -> incident net indices
  vnets: Vec<Vec<u32>>,
  /// global per-shard heartbeat target used to cap `bw` (propagated unchanged
  /// through recursion)
  cap: u64,
}

impl SubHyper {
  fn full(h: &Hypergraph, cap: u64) -> SubHyper {
    let n = h.num_vertices();
    let global: Vec<u32> = (0..n as u32).collect();
    let vw = h.vweight.clone();
    let nets: Vec<(u64, Vec<u32>)> = h
      .net_pins
      .iter()
      .enumerate()
      .map(|(i, pins)| (h.net_weight[i], pins.clone()))
      .collect();
    SubHyper::assemble(global, vw, nets, cap)
  }

  fn assemble(
    global: Vec<u32>,
    vw: Vec<u64>,
    nets: Vec<(u64, Vec<u32>)>,
    cap: u64,
  ) -> SubHyper {
    let n = vw.len();
    let mut bw: Vec<u64> = vw.iter().map(|&w| w.min(cap)).collect();
    let total: u128 = bw.iter().map(|&w| u128::from(w)).sum();
    if total == 0 {
      bw = vec![1; n];
    }
    let mut vnets = vec![Vec::new(); n];
    for (i, (_, pins)) in nets.iter().enumerate() {
      for &v in pins {
        vnets[v as usize].push(i as u32);
      }
    }
    SubHyper { global, vw, bw, nets, vnets, cap }
  }

  fn num_vertices(&self) -> usize {
    self.vw.len()
  }

  /// Borrow this sub-hypergraph as a [`Level`] for the greedy / FM machinery.
  fn level(&self) -> Level<'_> {
    Level { vw: &self.vw, bw: &self.bw, nets: &self.nets, vnets: &self.vnets }
  }

  /// Induce the sub-hypergraph on the local vertices selected by `keep`,
  /// applying cut-net splitting: each net is restricted to its kept pins and
  /// dropped if fewer than two remain.
  fn induce(&self, keep: &[bool]) -> SubHyper {
    let mut remap = vec![u32::MAX; self.num_vertices()];
    let mut global = Vec::new();
    let mut vw = Vec::new();
    for v in 0..self.num_vertices() {
      if keep[v] {
        remap[v] = global.len() as u32;
        global.push(self.global[v]);
        vw.push(self.vw[v]);
      }
    }
    let mut nets = Vec::new();
    for (w, pins) in &self.nets {
      let kept: Vec<u32> = pins
        .iter()
        .filter(|&&p| keep[p as usize])
        .map(|&p| remap[p as usize])
        .collect();
      if kept.len() >= 2 {
        nets.push((*w, kept));
      }
    }
    SubHyper::assemble(global, vw, nets, self.cap)
  }
}

/// Recursively split `sub` into `k` shards (contiguous ids `base..base+k`),
/// writing shard ids into `shard_of` (indexed by global block id).
///
/// The `k` leaf budget is allocated between the two sides ~proportional to
/// heartbeat mass, but clamped so each side receives at least 1 leaf and at most
/// its own vertex count. That guarantees **every shard is non-empty** whenever
/// the subtree holds at least `k` vertices (at the top, `#blocks ≥ 2ⁿ`), so the
/// full parallelism is realized; the heartbeat-proportional split also keeps
/// per-shard work as even as the atomic blocks allow. The resulting bisection
/// tree is a (possibly unbalanced) binary tree — still a valid aggregation tree.
fn rec_bisect(
  sub: &SubHyper,
  k: usize,
  base: u32,
  epsilon: f64,
  shard_of: &[AtomicU32],
  prog: &PartitionProgress,
) -> AggNode {
  if k <= 1 || sub.num_vertices() <= 1 {
    // A leaf (or a subtree with ≤1 vertex): everything here is one shard.
    for &g in &sub.global {
      shard_of[g as usize].store(base, Ordering::Relaxed);
    }
    prog.leaf();
    return AggNode::Leaf(base);
  }
  prog.bisecting(sub.num_vertices(), k);
  let side = bisect(sub, epsilon);
  let keep0: Vec<bool> = side.iter().map(|&s| s == 0).collect();
  let keep1: Vec<bool> = side.iter().map(|&s| s == 1).collect();
  let left = sub.induce(&keep0);
  let right = sub.induce(&keep1);
  let nl = left.num_vertices();
  let nr = right.num_vertices();
  if nl == 0 || nr == 0 {
    // Degenerate split: `bisect` guarantees both sides non-empty for |sub| ≥ 2
    // (its initial partition rejects empty-sided candidates), so this is a
    // defensive backstop only — keep the subtree together as one shard.
    for &g in &sub.global {
      shard_of[g as usize].store(base, Ordering::Relaxed);
    }
    prog.leaf();
    return AggNode::Leaf(base);
  }
  // Allocate leaves ~proportional to heartbeat mass, clamped to [1, side size].
  // `lo`/`hi` are feasible (lo ≤ hi) because nl + nr ≥ k with nl, nr ≥ 1.
  let wl: u128 = left.vw.iter().map(|&w| u128::from(w)).sum();
  let wr: u128 = right.vw.iter().map(|&w| u128::from(w)).sum();
  let wsum = (wl + wr).max(1);
  let ideal = ((k as u128 * wl + wsum / 2) / wsum) as usize;
  let lo = 1.max(k.saturating_sub(nr));
  let hi = (k - 1).min(nl);
  let k_left = ideal.clamp(lo, hi);
  let rbase = base + k_left as u32;
  // The two halves are independent (disjoint blocks) — recurse them in parallel
  // when the work is large enough to amortize the join. The result is identical
  // to serial execution (each subtree is deterministic). Each call returns its
  // subtree's `AggNode`; the two combine into this node's binary split — the
  // bisection tree mirrors the recursion exactly.
  let (ln, rn) = if nl + nr >= PARALLEL_THRESHOLD {
    rayon::join(
      || rec_bisect(&left, k_left, base, epsilon, shard_of, prog),
      || rec_bisect(&right, k - k_left, rbase, epsilon, shard_of, prog),
    )
  } else {
    (
      rec_bisect(&left, k_left, base, epsilon, shard_of, prog),
      rec_bisect(&right, k - k_left, rbase, epsilon, shard_of, prog),
    )
  };
  AggNode::Internal(Box::new(ln), Box::new(rn))
}

/// Progress reporter for [`Hypergraph::partition`]. The partitioner is silent
/// otherwise (it only writes its output at the end), which makes a slow run
/// indistinguishable from a stuck one; this logs each large bisection and the
/// running shards-finalized count (to stderr, unless `IX_SHARD_QUIET` is set).
struct PartitionProgress {
  total: usize,
  finalized: AtomicUsize,
  start: Instant,
  enabled: bool,
}

impl PartitionProgress {
  fn new(total: usize) -> Self {
    PartitionProgress {
      total,
      finalized: AtomicUsize::new(0),
      start: Instant::now(),
      enabled: std::env::var("IX_SHARD_QUIET").is_err(),
    }
  }

  /// Log a large bisection about to run (the slow steps). `&self` so it can be
  /// shared across the parallel recursion.
  fn bisecting(&self, n: usize, k: usize) {
    if self.enabled && n >= PROGRESS_BISECT_LOG {
      eprintln!(
        "[shard] bisecting {n} vertices → {k} shards  ({:.1?} elapsed, {}/{} shards done)",
        self.start.elapsed(),
        self.finalized.load(Ordering::Relaxed),
        self.total
      );
    }
  }

  /// A shard leaf was finalized; log roughly every 1/16 of the shards. Uses an
  /// atomic counter so concurrent subtrees report coherently.
  fn leaf(&self) {
    let done = self.finalized.fetch_add(1, Ordering::Relaxed) + 1;
    let step = (self.total / 16).max(1);
    if self.enabled && (done.is_multiple_of(step) || done == self.total) {
      eprintln!(
        "[shard] {}/{} shards finalized  ({:.1?} elapsed)",
        done,
        self.total,
        self.start.elapsed()
      );
    }
  }

  fn done(&self) {
    if self.enabled {
      eprintln!(
        "[shard] partitioned into {} shards in {:.1?}",
        self.finalized.load(Ordering::Relaxed),
        self.start.elapsed()
      );
    }
  }
}

/// Bisect `sub` into two balanced parts minimizing cut weight. Returns a side
/// (0/1) per local vertex.
///
/// Multilevel V-cycle: coarsen `sub` into a hierarchy, decide the cut on the
/// tiny coarsest graph (greedy graph-growing + FM to convergence), then
/// uncoarsen — projecting the cut back down and boundary-refining each level.
/// When `sub` is small or won't coarsen, `levels` is empty and we partition it
/// directly, so the worst case is never worse than a flat bisection.
fn bisect(sub: &SubHyper, epsilon: f64) -> Vec<u8> {
  let n = sub.num_vertices();
  if n == 0 {
    return Vec::new();
  }
  if n == 1 {
    return vec![0];
  }
  let total_bw: u64 = sub.bw.iter().sum();
  // Balance bounds for side weights (invariant across levels — coarsening sums
  // balance weight, so the total is preserved at every level).
  let wmax = ((0.5 + epsilon) * total_bw as f64).ceil() as u64;
  let wmin = ((0.5 - epsilon) * total_bw as f64).floor() as u64;

  let levels = coarsen(sub);
  let coarsest = levels.last().map_or_else(|| sub.level(), |l| l.level());
  let side = initial_partition(coarsest, wmin, wmax);
  uncoarsen_refine(sub, &levels, side, wmin, wmax)
}

/// Greedy graph-growing: start from `seed` and repeatedly absorb the boundary
/// vertex most strongly connected (by net weight) to side 0 until side 0 reaches
/// ~half the balance weight. Remaining vertices go to side 1.
fn greedy_grow(lv: Level<'_>, total_bw: u64, seed: usize) -> Vec<u8> {
  let n = lv.num_vertices();
  let mut side = vec![1u8; n];

  // connection[v] = total weight of nets that already touch side 0 and include v.
  let mut connection = vec![0u64; n];
  let mut in_side0 = vec![false; n];
  // Whether a net already contributes to side 0. A net bumps its pins exactly
  // once (on first connection), so growth is O(Σ net_size), not O(Σ net_size²)
  // — essential on dense graphs (and it also stops over-counting connection).
  let mut net_touched = vec![false; lv.nets.len()];
  let mut heap: BinaryHeap<(u64, Reverse<u32>)> = BinaryHeap::new();
  let mut side0_bw = 0u64;
  let target = total_bw / 2;
  // Forward cursor for the disconnected-fallback path (amortized O(n) total,
  // vs. an O(n) max-scan per fallback which is O(n²) on delta-sparse envs).
  let mut fallback_cursor = 0usize;

  let mut add = |v: usize,
                 side: &mut [u8],
                 in_side0: &mut [bool],
                 connection: &mut [u64],
                 heap: &mut BinaryHeap<(u64, Reverse<u32>)>,
                 side0_bw: &mut u64| {
    side[v] = 0;
    in_side0[v] = true;
    *side0_bw += lv.bw[v];
    for &ni in &lv.vnets[v] {
      let nis = ni as usize;
      let (w, pins) = &lv.nets[nis];
      // Skip hub nets, and nets already counted toward side 0.
      if pins.len() > FM_NET_CAP || net_touched[nis] {
        continue;
      }
      net_touched[nis] = true;
      for &u in pins {
        let u = u as usize;
        if !in_side0[u] {
          connection[u] += *w;
          heap.push((connection[u], Reverse(u as u32)));
        }
      }
    }
  };

  add(
    seed,
    &mut side,
    &mut in_side0,
    &mut connection,
    &mut heap,
    &mut side0_bw,
  );

  while side0_bw < target {
    // Pop the best-connected vertex not yet in side 0 (lazy-validated).
    let mut next = None;
    while let Some((c, Reverse(v))) = heap.pop() {
      let v = v as usize;
      if !in_side0[v] && c == connection[v] {
        next = Some(v);
        break;
      }
    }
    match next {
      Some(v) => {
        add(
          v,
          &mut side,
          &mut in_side0,
          &mut connection,
          &mut heap,
          &mut side0_bw,
        );
      },
      None => {
        // No connected frontier left (graph is disconnected here); fill toward
        // balance with the next unassigned vertex by id. Disconnected vertices
        // have no incident (non-hub) nets, so their placement order is
        // cut-neutral.
        while fallback_cursor < n && in_side0[fallback_cursor] {
          fallback_cursor += 1;
        }
        if fallback_cursor < n {
          add(
            fallback_cursor,
            &mut side,
            &mut in_side0,
            &mut connection,
            &mut heap,
            &mut side0_bw,
          );
        } else {
          break;
        }
      },
    }
  }
  side
}

/// Per-net pin counts on each side, for incremental cut maintenance.
struct NetState {
  cnt: Vec<[u32; 2]>,
}

impl NetState {
  fn new(lv: Level<'_>, side: &[u8]) -> (NetState, u128) {
    let mut cnt = vec![[0u32; 2]; lv.nets.len()];
    let mut cut: u128 = 0;
    for (i, (w, pins)) in lv.nets.iter().enumerate() {
      if pins.len() > FM_NET_CAP {
        continue; // hub net: invisible to FM (counts stay zero)
      }
      for &v in pins {
        cnt[i][side[v as usize] as usize] += 1;
      }
      if cnt[i][0] > 0 && cnt[i][1] > 0 {
        cut += u128::from(*w);
      }
    }
    (NetState { cnt }, cut)
  }
}

/// FM gain of moving local vertex `v` from its side to the other.
/// `+w` for each net where `v`'s side has exactly one pin (the move uncuts it);
/// `−w` for each net fully on `v`'s side with ≥2 pins (the move newly cuts it).
fn fm_gain(lv: Level<'_>, ns: &NetState, side: &[u8], v: usize) -> i128 {
  let a = side[v] as usize;
  let b = 1 - a;
  let mut g: i128 = 0;
  for &ni in &lv.vnets[v] {
    let (w, pins) = &lv.nets[ni as usize];
    if pins.len() > FM_NET_CAP {
      continue; // hub net: ignored by FM
    }
    let ca = ns.cnt[ni as usize][a];
    let cb = ns.cnt[ni as usize][b];
    if cb >= 1 && ca == 1 {
      g += i128::from(*w);
    } else if cb == 0 && ca >= 2 {
      g -= i128::from(*w);
    }
  }
  g
}

/// Fiduccia–Mattheyses refinement (boundary variant): up to `max_passes` passes,
/// each moving every vertex at most once in decreasing-gain order subject to the
/// balance window, tracking the lowest-cut prefix and rolling back to it. Stops
/// when a pass yields no improvement.
///
/// Only **boundary** vertices (incident to a cut net) are seeded into the gain
/// heap: an interior vertex has non-positive gain (moving it can only newly-cut
/// nets), so it never improves the cut; vertices exposed to the boundary by an
/// applied move are added as that move's neighbors. This bounds a pass at
/// roughly `O(boundary + moves·degree)` rather than `O(V·degree)`, which is what
/// makes full refinement affordable even on the finest (≈`V`-sized) level.
fn fm_refine(
  lv: Level<'_>,
  side: &mut [u8],
  wmin: u64,
  wmax: u64,
  max_passes: u32,
) {
  let n = lv.num_vertices();
  if n <= 1 {
    return;
  }
  // Contribution of one net (counts `ca` on the vertex's side, `cb` on the
  // other, weight `w`) to the gain of moving that vertex: `+w` if it is the last
  // pin on its side (the move uncuts the net), `−w` if its side is full with ≥2
  // pins (the move newly cuts it), else 0.
  let contrib = |ca: u32, cb: u32, w: i128| -> i128 {
    if cb >= 1 && ca == 1 {
      w
    } else if cb == 0 && ca >= 2 {
      -w
    } else {
      0
    }
  };
  // Buffers reused across passes (no per-move allocation).
  let mut gain = vec![0i128; n];
  let mut queued = vec![false; n];
  let mut locked = vec![false; n];
  let mut heap: BinaryHeap<(i128, Reverse<u32>)> = BinaryHeap::new();
  let mut moves: Vec<usize> = Vec::new();
  let mut pass = 0u32;
  loop {
    let (mut ns, mut cut) = NetState::new(lv, side);
    let mut side0_bw: u64 =
      (0..n).filter(|&v| side[v] == 0).map(|v| lv.bw[v]).sum();

    // Full gain initialization (O(pins), cheap) so the incremental neighbor
    // updates below — which only adjust the changed net's contribution — stay
    // exact for interior vertices that later reach the boundary.
    for (v, g) in gain.iter_mut().enumerate() {
      *g = fm_gain(lv, &ns, side, v);
    }
    heap.clear();
    moves.clear();
    queued.fill(false);
    locked.fill(false);
    // Seed the cut frontier only (interior vertices have non-positive gain).
    for (i, (_, pins)) in lv.nets.iter().enumerate() {
      if pins.len() > FM_NET_CAP {
        continue; // hub net: invisible to FM
      }
      if ns.cnt[i][0] > 0 && ns.cnt[i][1] > 0 {
        for &v in pins {
          let v = v as usize;
          if !queued[v] {
            queued[v] = true;
            heap.push((gain[v], Reverse(v as u32)));
          }
        }
      }
    }

    let mut best_cut = cut;
    let mut best_prefix = 0usize; // number of moves to keep

    while let Some((g, Reverse(v))) = heap.pop() {
      let v = v as usize;
      if locked[v] || g != gain[v] {
        continue; // stale entry
      }
      // Balance check: moving v shifts bw[v] across the cut.
      let (s0_after, ok) = if side[v] == 0 {
        let s0 = side0_bw - lv.bw[v];
        (s0, s0 >= wmin)
      } else {
        let s0 = side0_bw + lv.bw[v];
        (s0, s0 <= wmax)
      };
      if !ok {
        // Infeasible right now; lock it out of this pass.
        locked[v] = true;
        continue;
      }
      // Apply the move, updating the cut and the gains of co-pins incrementally:
      // only this net's contribution to each pin changes, so a move costs
      // O(Σ pins of v's nets), not O(Σ neighbour degrees).
      let a = side[v] as usize;
      for &ni in &lv.vnets[v] {
        let nis = ni as usize;
        let (w, pins) = &lv.nets[nis];
        if pins.len() > FM_NET_CAP {
          continue; // hub net: not tracked
        }
        let wi = i128::from(*w);
        let c0 = ns.cnt[nis][0];
        let c1 = ns.cnt[nis][1];
        let (d0, d1) = if a == 0 { (c0 - 1, c1 + 1) } else { (c0 + 1, c1 - 1) };
        ns.cnt[nis][0] = d0;
        ns.cnt[nis][1] = d1;
        let before_cut = c0 > 0 && c1 > 0;
        let after_cut = d0 > 0 && d1 > 0;
        if before_cut && !after_cut {
          cut -= u128::from(*w);
        } else if !before_cut && after_cut {
          cut += u128::from(*w);
        }
        for &uu in pins {
          let u = uu as usize;
          if u == v || locked[u] {
            continue;
          }
          let su = side[u] as usize;
          let (ca, cb) = if su == 0 { (c0, c1) } else { (c1, c0) };
          let (ca2, cb2) = if su == 0 { (d0, d1) } else { (d1, d0) };
          let delta = contrib(ca2, cb2, wi) - contrib(ca, cb, wi);
          if delta != 0 {
            gain[u] += delta;
            queued[u] = true;
            heap.push((gain[u], Reverse(uu)));
          }
        }
      }
      side[v] = (1 - a) as u8;
      side0_bw = s0_after;
      locked[v] = true;
      moves.push(v);

      if cut < best_cut {
        best_cut = cut;
        best_prefix = moves.len();
      }
    }

    // Roll back moves after the best prefix.
    for &v in moves.iter().skip(best_prefix) {
      side[v] ^= 1;
    }

    pass += 1;
    if best_prefix == 0 || pass >= max_passes {
      break; // converged, or hit the pass bound
    }
  }
}

// ============================================================================
// Multilevel coarsening
// ============================================================================

/// One coarser level of a single bisection's multilevel hierarchy. Mirrors the
/// cut-relevant fields of [`SubHyper`] (`vw`/`bw`/`nets`/`vnets`) plus the
/// `match_map` that records, for each vertex of the *next-finer* level, which
/// supervertex here it was merged into — the inverse map used to project a
/// coarse partition back down during uncoarsening.
struct CoarseLevel {
  vw: Vec<u64>,
  bw: Vec<u64>,
  nets: Vec<(u64, Vec<u32>)>,
  vnets: Vec<Vec<u32>>,
  match_map: Vec<u32>,
}

impl CoarseLevel {
  fn level(&self) -> Level<'_> {
    Level { vw: &self.vw, bw: &self.bw, nets: &self.nets, vnets: &self.vnets }
  }
}

/// Build the coarsening hierarchy for one bisection: `levels[0]` is the first
/// contraction of `sub`, `levels.last()` is the coarsest graph (≈
/// [`COARSEST_TARGET`] vertices). The finest level (`sub` itself) is *not*
/// duplicated into the vector — it is supplied separately during uncoarsening.
/// Returns an empty vector when `sub` is already small or can't be coarsened, in
/// which case [`bisect`] partitions `sub` directly.
fn coarsen(sub: &SubHyper) -> Vec<CoarseLevel> {
  let total_bw: u64 = sub.bw.iter().sum();
  // Cap a supervertex's balance weight so the coarsest graph keeps at least
  // ~COARSEST_TARGET pieces and stays balanceable; never merge past it.
  let max_cluster = (total_bw / COARSEST_TARGET as u64).max(1);
  let mut levels: Vec<CoarseLevel> = Vec::new();
  loop {
    let cur: Level<'_> = match levels.last() {
      Some(l) => l.level(),
      None => sub.level(),
    };
    let n = cur.num_vertices();
    if n <= COARSEST_TARGET {
      break;
    }
    let (super_id, next) = match_vertices(cur, max_cluster);
    if (next as f64) > COARSEN_STALL_RATIO * n as f64 {
      break; // stalled: too few matchable pairs to make progress
    }
    let level = contract(cur, &super_id, next);
    levels.push(level);
    if next <= COARSEST_TARGET {
      break;
    }
  }
  levels
}

/// Heavy-edge matching pass: pair each still-unmatched vertex (visited in id
/// order) with the unmatched neighbor it co-occurs with in the heaviest small
/// nets, subject to the cluster-weight cap. A vertex with no such neighbor
/// (delta-sparse, or only in hub nets) is instead paired with the next
/// unmatched vertex — a cut-neutral merge (they share no tracked net) that keeps
/// the graph shrinking ~2× per pass so coarsening reaches [`COARSEST_TARGET`]
/// instead of stalling far above it (which would make the initial partition
/// expensive). Returns `(super_id, num_super)` where `super_id[v]` is `v`'s
/// supervertex in the next-coarser level. Deterministic — ties break to lowest
/// id.
fn match_vertices(lv: Level<'_>, max_cluster: u64) -> (Vec<u32>, usize) {
  let n = lv.num_vertices();
  let mut super_id = vec![u32::MAX; n];
  let mut next: u32 = 0;
  // Dense score accumulator, reset per vertex via the `touched` list.
  let mut score = vec![0u64; n];
  let mut touched: Vec<u32> = Vec::new();
  // Forward cursor over still-unmatched vertices for the fallback pairing
  // (advances monotonically → amortized O(n) over the whole pass).
  let mut fb = 0usize;
  for v in 0..n {
    if super_id[v] != u32::MAX {
      continue; // already claimed as an earlier vertex's partner
    }
    for &ni in &lv.vnets[v] {
      let (w, pins) = &lv.nets[ni as usize];
      let deg = pins.len();
      if !(2..=MATCH_NET_CAP).contains(&deg) {
        continue; // singleton or hub: no clustering signal worth scanning
      }
      let contrib = w / (deg as u64 - 1);
      if contrib == 0 {
        continue;
      }
      for &u in pins {
        let u = u as usize;
        if u == v || super_id[u] != u32::MAX {
          continue; // self, or already-matched vertex
        }
        if score[u] == 0 {
          touched.push(u as u32);
        }
        score[u] = score[u].saturating_add(contrib);
      }
    }
    // Pick the best-scoring partner that fits the cluster-weight cap. The
    // explicit `u < best_u` tie-break makes the result independent of the
    // (net/pin) iteration order.
    let mut best_u = usize::MAX;
    let mut best_score = 0u64;
    for &ut in &touched {
      let u = ut as usize;
      let s = score[u];
      let fits = lv.bw[v].saturating_add(lv.bw[u]) <= max_cluster;
      if fits && (s > best_score || (s == best_score && u < best_u)) {
        best_score = s;
        best_u = u;
      }
    }
    for &ut in &touched {
      score[ut as usize] = 0;
    }
    touched.clear();
    // Fallback: no heavy-edge partner — pair with the next unmatched vertex so
    // coarsening keeps making progress. Cut-neutral (no shared tracked net).
    // The cursor skips matched vertices and everything ≤ v (so never v itself).
    if best_u == usize::MAX {
      while fb < n && (super_id[fb] != u32::MAX || fb <= v) {
        fb += 1;
      }
      if fb < n && lv.bw[v].saturating_add(lv.bw[fb]) <= max_cluster {
        best_u = fb;
      }
    }
    super_id[v] = next;
    if best_u != usize::MAX {
      super_id[best_u] = next; // matched pair shares a supervertex
    }
    next += 1;
  }
  (super_id, next as usize)
}

/// Contract `lv` by `super_id` (which maps each vertex to one of `next`
/// supervertices) into the next coarser [`CoarseLevel`]. Supervertex weights are
/// member sums; each net's pins are remapped, sorted, and deduplicated, and the
/// net is dropped if it has fewer than two distinct coarse pins (it became
/// internal to a supervertex). Net weights are preserved. `super_id` is stored
/// as the level's `match_map` for the uncoarsening projection.
fn contract(lv: Level<'_>, super_id: &[u32], next: usize) -> CoarseLevel {
  let mut vw = vec![0u64; next];
  let mut bw = vec![0u64; next];
  for v in 0..lv.num_vertices() {
    let s = super_id[v] as usize;
    vw[s] = vw[s].saturating_add(lv.vw[v]);
    bw[s] = bw[s].saturating_add(lv.bw[v]);
  }
  let mut nets: Vec<(u64, Vec<u32>)> = Vec::with_capacity(lv.nets.len());
  for (w, pins) in lv.nets {
    let mut cp: Vec<u32> = pins.iter().map(|&p| super_id[p as usize]).collect();
    cp.sort_unstable();
    cp.dedup();
    if cp.len() >= 2 {
      nets.push((*w, cp));
    }
  }
  let mut vnets = vec![Vec::new(); next];
  for (i, (_, pins)) in nets.iter().enumerate() {
    for &v in pins {
      vnets[v as usize].push(i as u32);
    }
  }
  CoarseLevel { vw, bw, nets, vnets, match_map: super_id.to_vec() }
}

/// Decide the bisection on the coarsest graph: greedy graph-growing for a
/// locality-aware initial cut, then FM to (capped) convergence. The graph is
/// tiny (≈[`COARSEST_TARGET`] vertices), so this is where we spend on quality —
/// the *global* cut is decided here and only locally refined while uncoarsening.
/// We restart from several diverse seeds (see [`INITIAL_RESTARTS`]) and keep the
/// lowest-cut partition, which makes graph-growing robust to "leaking" across a
/// thin bridge between two clusters.
fn initial_partition(lv: Level<'_>, wmin: u64, wmax: u64) -> Vec<u8> {
  let n = lv.num_vertices();
  if n == 0 {
    return Vec::new();
  }
  if n == 1 {
    return vec![0];
  }
  let total_bw: u64 = lv.bw.iter().sum();
  // Diverse deterministic seeds: the heaviest vertex plus points spread evenly
  // across the id range (one tends to start far from any inter-cluster bridge).
  let heaviest = (0..n)
    .max_by(|&a, &b| lv.vw[a].cmp(&lv.vw[b]).then(Reverse(a).cmp(&Reverse(b))))
    .unwrap();
  let mut seeds = vec![heaviest];
  for i in 0..INITIAL_RESTARTS {
    let s = (i * n) / INITIAL_RESTARTS;
    if !seeds.contains(&s) {
      seeds.push(s);
    }
  }
  // Select the lowest-cut candidate, but *only* among non-degenerate splits
  // (both sides non-empty) and preferring those within the balance window. A
  // graph-growing run seeded at a light vertex can sweep an entire sub onto one
  // side (cut 0) when a single atomic block holds more than half the balance
  // weight; such a split is both unbalanced and degenerate, and accepting it
  // would leave a shard empty downstream. Key: (unbalanced?, cut), minimized.
  let mut best: Option<((u8, u128), Vec<u8>)> = None;
  for &seed in &seeds {
    let mut side = greedy_grow(lv, total_bw, seed);
    fm_refine(lv, &mut side, wmin, wmax, MAX_FM_PASSES);
    let s0 = (0..n).filter(|&v| side[v] == 0).count();
    if s0 == 0 || s0 == n {
      continue; // degenerate (one side empty) — never select
    }
    let side0_bw: u64 =
      (0..n).filter(|&v| side[v] == 0).map(|v| lv.bw[v]).sum();
    let unbalanced = u8::from(side0_bw < wmin || side0_bw > wmax);
    let (_, cut) = NetState::new(lv, &side);
    let key = (unbalanced, cut);
    if best.as_ref().is_none_or(|(bk, _)| key < *bk) {
      best = Some((key, side));
    }
  }
  // Fallback (no non-degenerate candidate — pathological): split by id so both
  // sides are non-empty and recursion can still realize every shard.
  best
    .map_or_else(|| (0..n).map(|v| u8::from(v >= n / 2)).collect(), |(_, s)| s)
}

/// Project the coarse partition down to the finest level, boundary-refining at
/// each step. `side` enters indexed by coarsest supervertex; each finer level
/// inherits its supervertex's side (`side[fine] = coarse[match_map[fine]]`) and
/// is FM-refined ([`REFINE_PASSES`] passes) to fix only its cut frontier. The
/// returned `side` is indexed by `sub` vertex — the same contract a flat
/// bisection returns.
fn uncoarsen_refine(
  sub: &SubHyper,
  levels: &[CoarseLevel],
  mut side: Vec<u8>,
  wmin: u64,
  wmax: u64,
) -> Vec<u8> {
  for i in (0..levels.len()).rev() {
    // The level finer than `levels[i]` is `levels[i-1]`, or `sub` at the bottom.
    let (finer_n, finer_lv) = if i == 0 {
      (sub.num_vertices(), sub.level())
    } else {
      (levels[i - 1].vw.len(), levels[i - 1].level())
    };
    let mm = &levels[i].match_map; // finer vertex -> levels[i] supervertex
    let mut finer_side = vec![0u8; finer_n];
    for v in 0..finer_n {
      finer_side[v] = side[mm[v] as usize];
    }
    fm_refine(finer_lv, &mut finer_side, wmin, wmax, REFINE_PASSES);
    side = finer_side;
  }
  side
}

// ============================================================================
// Manifest
// ============================================================================

/// Per-shard summary in a [`ShardManifest`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShardInfo {
  /// Shard id (an `n`-bit path through the bisection tree).
  pub id: u32,
  /// Member block addresses.
  pub blocks: Vec<Address>,
  /// Sum of member heartbeats (balance metric).
  pub heartbeats: u64,
  /// Sum of member serialized sizes (the shard's own ingress).
  pub own_size: u64,
  /// Blocks this shard ingresses but does not check — another shard owns
  /// them. Under the Aiur model this is the whole ingress set minus the
  /// owned blocks; it is what the claim's assumption tree covers.
  pub foreign_blocks: Vec<Address>,
  /// The subset of `foreign_blocks` ingressed as type-only axioms: bodies
  /// withheld, references not followed. The complement — blocks in
  /// `foreign_blocks` but not here — are ingressed whole because this shard
  /// reduces through them, and only the partition knows which those are.
  pub stubbed_blocks: Vec<Address>,
  /// Sum of `serialized_size` over `foreign_blocks` (this shard's share of the
  /// cross-shard ingress objective).
  pub cross_ingress: u64,
  /// Sound assumption-tree root for this shard's conditional proof: the Merkle
  /// root over the foreign part of the shard's static reference closure. `None`
  /// until populated by the env-aware layer (the pure partitioner has no `Env`).
  pub assumption_root: Option<Address>,
}

/// The sharding manifest: the partition plus its cost metrics. Assumption-tree
/// roots (which require the static reference closure from the `Env`) are filled
/// in by the env-aware CLI layer, not here.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShardManifest {
  /// Number of shards (the partition target == `shards.len()`).
  pub num_shards: u32,
  pub shards: Vec<ShardInfo>,
  /// Total cross-shard ingress bytes (the km1 objective).
  pub total_cross_ingress: u128,
  /// The bisection tree over the shard ids, for proof aggregation. `None` on
  /// manifests written before this section existed (the prover then falls back
  /// to a flat tree-fold). Set by [`Self::with_tree`].
  pub tree: Option<AggNode>,
}

impl ShardManifest {
  /// Build the manifest from a profile and a shard assignment (shard id in
  /// `0..num_shards` per block id).
  pub fn build(
    profile: &BlockProfile,
    shard_of: &[u32],
    num_shards: usize,
  ) -> ShardManifest {
    let mut members: Vec<Vec<u32>> = vec![Vec::new(); num_shards];
    for (b, &s) in shard_of.iter().enumerate() {
      members[s as usize].push(b as u32);
    }
    // Distinct foreign blocks per shard.
    let mut foreign: Vec<FxHashSet<u32>> =
      vec![FxHashSet::default(); num_shards];
    for b in 0..profile.num_blocks() as u32 {
      let s = shard_of[b as usize] as usize;
      for &p in profile.producers(b) {
        if shard_of[p as usize] as usize != s {
          foreign[s].insert(p);
        }
      }
    }
    let mut shards = Vec::with_capacity(num_shards);
    let mut total_cross: u128 = 0;
    for s in 0..num_shards {
      let blocks: Vec<Address> =
        members[s].iter().map(|&b| profile.block(b).addr.clone()).collect();
      let heartbeats: u64 =
        members[s].iter().map(|&b| profile.block(b).heartbeats).sum();
      let own_size: u64 = members[s]
        .iter()
        .map(|&b| u64::from(profile.block(b).serialized_size))
        .sum();
      let mut fb: Vec<u32> = foreign[s].iter().copied().collect();
      fb.sort_unstable();
      let cross_ingress: u64 =
        fb.iter().map(|&p| u64::from(profile.block(p).serialized_size)).sum();
      total_cross += u128::from(cross_ingress);
      let foreign_blocks: Vec<Address> =
        fb.iter().map(|&p| profile.block(p).addr.clone()).collect();
      shards.push(ShardInfo {
        id: s as u32,
        blocks,
        heartbeats,
        own_size,
        foreign_blocks,
        // Filled by the Aiur layer, which runs the ingress walk; the pure
        // partitioner has no notion of stubbing.
        stubbed_blocks: Vec::new(),
        cross_ingress,
        assumption_root: None,
      });
    }
    ShardManifest {
      num_shards: num_shards as u32,
      shards,
      total_cross_ingress: total_cross,
      tree: None,
    }
  }

  /// Attach the bisection tree (from [`Hypergraph::partition_with_tree`]) for
  /// tree-aligned aggregation.
  #[must_use]
  pub fn with_tree(mut self, tree: AggNode) -> Self {
    self.tree = Some(tree);
    self
  }

  /// A human-readable what-if summary line.
  pub fn summary(&self) -> String {
    let hbs: Vec<u64> = self.shards.iter().map(|s| s.heartbeats).collect();
    let nonempty: Vec<u64> = self
      .shards
      .iter()
      .filter(|s| !s.blocks.is_empty())
      .map(|s| s.heartbeats)
      .collect();
    let max = hbs.iter().copied().max().unwrap_or(0);
    let min = nonempty.iter().copied().min().unwrap_or(0);
    let total: u128 = hbs.iter().map(|&h| u128::from(h)).sum();
    let mean = if self.shards.is_empty() {
      0
    } else {
      (total / self.shards.len() as u128) as u64
    };
    let empty = self.shards.iter().filter(|s| s.blocks.is_empty()).count();
    let max_cross =
      self.shards.iter().map(|s| s.cross_ingress).max().unwrap_or(0);
    format!(
      "shards={} (empty={}) heartbeats[min={} mean={} max={}] imbalance={:.2}x \
       cross_ingress_total={} max_shard_cross={}",
      self.shards.len(),
      empty,
      min,
      mean,
      max,
      if mean == 0 { 0.0 } else { max as f64 / mean as f64 },
      self.total_cross_ingress,
      max_cross,
    )
  }

  /// Serialize to the `.ixes` binary format.
  pub fn to_bytes(&self) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(SHARD_MAGIC);
    out.extend_from_slice(&self.total_cross_ingress.to_le_bytes());
    out.extend_from_slice(&(self.shards.len() as u32).to_le_bytes());
    let put_addrs = |out: &mut Vec<u8>, addrs: &[Address]| {
      out.extend_from_slice(&(addrs.len() as u32).to_le_bytes());
      for a in addrs {
        out.extend_from_slice(a.as_bytes());
      }
    };
    for sh in &self.shards {
      out.extend_from_slice(&sh.id.to_le_bytes());
      out.extend_from_slice(&sh.heartbeats.to_le_bytes());
      out.extend_from_slice(&sh.own_size.to_le_bytes());
      out.extend_from_slice(&sh.cross_ingress.to_le_bytes());
      match &sh.assumption_root {
        Some(a) => {
          out.push(1);
          out.extend_from_slice(a.as_bytes());
        },
        None => out.push(0),
      }
      put_addrs(&mut out, &sh.blocks);
      put_addrs(&mut out, &sh.foreign_blocks);
      put_addrs(&mut out, &sh.stubbed_blocks);
    }
    // Trailing optional bisection-tree section: presence byte then preorder
    // tree. Appended after the shards so older readers that stop at the shard
    // count simply ignore it, and `from_bytes` treats end-of-input as `None`.
    match &self.tree {
      Some(t) => {
        out.push(1);
        t.put(&mut out);
      },
      None => out.push(0),
    }
    out
  }

  /// Deserialize from the `.ixes` binary format.
  pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
    let mut c = Cur { buf: bytes, pos: 0 };
    if c.take(8)? != SHARD_MAGIC {
      return Err("not an .ixes file (bad magic)".into());
    }
    let total_cross_ingress = c.u128()?;
    let num_shards = c.u32()? as usize;
    let mut shards = Vec::with_capacity(num_shards);
    for _ in 0..num_shards {
      let id = c.u32()?;
      let heartbeats = c.u64()?;
      let own_size = c.u64()?;
      let cross_ingress = c.u64()?;
      let assumption_root = if c.u8()? == 1 { Some(c.addr()?) } else { None };
      let blocks = c.addrs()?;
      let foreign_blocks = c.addrs()?;
      let stubbed_blocks = c.addrs()?;
      shards.push(ShardInfo {
        id,
        blocks,
        heartbeats,
        own_size,
        foreign_blocks,
        stubbed_blocks,
        cross_ingress,
        assumption_root,
      });
    }
    // Optional trailing tree section. Absent (end-of-input) on pre-tree
    // manifests, or an explicit `0` presence byte.
    let tree = if c.pos < c.buf.len() {
      if c.u8()? == 1 { Some(AggNode::get(&mut c)?) } else { None }
    } else {
      None
    };
    Ok(ShardManifest {
      num_shards: num_shards as u32,
      shards,
      total_cross_ingress,
      tree,
    })
  }
}

/// Magic bytes at the head of every `.ixes` file.
const SHARD_MAGIC: &[u8; 8] = b"IXES\0\0\0\0";

/// Minimal little-endian cursor for manifest decoding.
struct Cur<'a> {
  buf: &'a [u8],
  pos: usize,
}

impl<'a> Cur<'a> {
  fn take(&mut self, n: usize) -> Result<&'a [u8], String> {
    let end = self.pos.checked_add(n).ok_or("truncated .ixes")?;
    if end > self.buf.len() {
      return Err("truncated .ixes".into());
    }
    let s = &self.buf[self.pos..end];
    self.pos = end;
    Ok(s)
  }
  fn u8(&mut self) -> Result<u8, String> {
    Ok(self.take(1)?[0])
  }
  fn u32(&mut self) -> Result<u32, String> {
    Ok(u32::from_le_bytes(self.take(4)?.try_into().unwrap()))
  }
  fn u64(&mut self) -> Result<u64, String> {
    Ok(u64::from_le_bytes(self.take(8)?.try_into().unwrap()))
  }
  fn u128(&mut self) -> Result<u128, String> {
    Ok(u128::from_le_bytes(self.take(16)?.try_into().unwrap()))
  }
  fn addr(&mut self) -> Result<Address, String> {
    Address::from_slice(self.take(32)?).map_err(|_| "bad address".into())
  }
  fn addrs(&mut self) -> Result<Vec<Address>, String> {
    let n = self.u32()? as usize;
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
      v.push(self.addr()?);
    }
    Ok(v)
  }
}

/// Read a `.ixprof`, partition into `num_shards` shards, and emit a manifest with
/// per-shard cost metrics, foreign-block sets, and (delta-based) assumption
/// roots. Optionally writes the manifest (`.ixes`). Returns a what-if report.
///
/// The assumption root here is the Merkle root over the foreign *blocks* whose
/// bodies the shard must ingress (the cost-model-tight set). The fully-sound
/// variant for proof generation uses the static reference closure over member
/// constants and additionally needs the `.ixe`; see `plans/sharding.md` §4.
pub fn shard_esp(
  esp_path: &str,
  num_shards: usize,
  balance: f64,
  parallelism: usize,
  out_path: Option<&str>,
) -> Result<String, String> {
  let bytes =
    std::fs::read(esp_path).map_err(|e| format!("read {esp_path}: {e}"))?;
  let profile = BlockProfile::from_bytes(&bytes)
    .map_err(|e| format!("parse {esp_path}: {e}"))?;
  let h = Hypergraph::from_profile(&profile);
  let (shard_of, tree) = h.partition_with_tree(num_shards, balance);
  let mut manifest =
    ShardManifest::build(&profile, &shard_of, num_shards).with_tree(tree);
  for shard in &mut manifest.shards {
    shard.assumption_root =
      ixon::merkle::merkle_root_canonical(&shard.foreign_blocks);
  }
  if let Some(op) = out_path {
    std::fs::write(op, manifest.to_bytes())
      .map_err(|e| format!("write {op}: {e}"))?;
  }
  // The largest single block's heartbeats is the *floor* on achievable
  // per-shard balance: a mutual block is atomic and cannot be split, so no
  // partition can drive max-shard heartbeats below it. When the heaviest shard
  // is pinned at this floor, adding more shards only worsens imbalance — a
  // signal to stop raising the shard count or to split the block.
  let max_block_hb =
    profile.blocks().iter().map(|b| b.heartbeats).max().unwrap_or(0);
  let max_shard_hb =
    manifest.shards.iter().map(|s| s.heartbeats).max().unwrap_or(0);
  let floored =
    num_shards > 1 && max_shard_hb <= max_block_hb.saturating_mul(11) / 10;
  let note = if floored {
    "  [balance floored by largest atomic block — more shards won't help]"
  } else {
    ""
  };
  Ok(format!(
    "blocks={} delta_edges={} nets={}\n{}\n{}\nlargest_block_hb={}{}",
    profile.num_blocks(),
    profile.num_edges(),
    h.num_nets(),
    manifest.summary(),
    prove_report(&profile, &shard_of, &manifest, parallelism),
    max_block_hb,
    note,
  ))
}

/// Like [`shard_esp`] but sized to a per-shard Zisk **cycle** budget
/// (`max_cycles`) rather than a fixed shard count: grows `N` until the heaviest
/// splittable shard fits the budget (see [`partition_for_cycle_cap`]). Use
/// [`cycle_cap_for_ram`] to derive `max_cycles` from a host-RAM target.
pub fn shard_esp_cap(
  esp_path: &str,
  max_cycles: u64,
  balance: f64,
  parallelism: usize,
  out_path: Option<&str>,
) -> Result<String, String> {
  let bytes =
    std::fs::read(esp_path).map_err(|e| format!("read {esp_path}: {e}"))?;
  let profile = BlockProfile::from_bytes(&bytes)
    .map_err(|e| format!("parse {esp_path}: {e}"))?;
  let plan = partition_for_cycle_cap(&profile, max_cycles, balance);
  let mut manifest =
    ShardManifest::build(&profile, &plan.shard_of, plan.num_shards)
      .with_tree(plan.tree);
  for shard in &mut manifest.shards {
    shard.assumption_root =
      ixon::merkle::merkle_root_canonical(&shard.foreign_blocks);
  }
  if let Some(op) = out_path {
    std::fs::write(op, manifest.to_bytes())
      .map_err(|e| format!("write {op}: {e}"))?;
  }
  let note = if plan.infeasible_atomic_floor {
    "\n  [INFEASIBLE: a single atomic block exceeds the cap — split it upstream, raise the cap, or use a bigger box]"
  } else {
    ""
  };
  Ok(format!(
    "blocks={} delta_edges={} max_cycles={} → {} shards (packed to cap)\n{}\n{}\nmax_shard_steps={} (cap {}, incl. floor {} + cross-ingress) largest_block_steps={}{}",
    profile.num_blocks(),
    profile.num_edges(),
    max_cycles,
    plan.num_shards,
    manifest.summary(),
    prove_report(&profile, &plan.shard_of, &manifest, parallelism),
    plan.max_shard_steps,
    max_cycles,
    SHARD_STEP_FLOOR,
    plan.largest_block_steps,
    note,
  ))
}

/// Like [`shard_esp_cap`] but sized to a per-shard **Aiur host-RAM** budget
/// (GiB) via the calibrated Aiur cost model (see [`partition_for_aiur_ram`]).
/// The manifest format is backend-neutral; only the packing objective and the
/// report change.
/// Parse a per-shard promotion spec into [`ShardPromotion`]s.
///
/// Grammar (comma-separated entries):
/// - `K:N` — shard K gets N whole-frontier promotion rounds;
/// - `K:+HEX` — shard K additionally ships the block with address `HEX`
///   whole (a wanted-stub report); repeatable per shard;
/// - a bare `N` — N rounds for every shard.
pub fn parse_promote_spec(
  spec: &str,
  profile: &BlockProfile,
  num_shards: usize,
) -> Result<Vec<ShardPromotion>, String> {
  let mut promotions = vec![ShardPromotion::default(); num_shards];
  let spec = spec.trim();
  if spec.is_empty() {
    return Ok(promotions);
  }
  if let Ok(n) = spec.parse::<usize>() {
    for p in &mut promotions {
      p.rounds = n;
    }
    return Ok(promotions);
  }
  let id_of: FxHashMap<&Address, u32> = profile
    .blocks()
    .iter()
    .enumerate()
    .map(|(i, b)| (&b.addr, i as u32))
    .collect();
  for part in spec.split(',').filter(|p| !p.is_empty()) {
    let (shard, rhs) = part
      .split_once(':')
      .ok_or_else(|| format!("promote spec: bad entry {part:?}"))?;
    let s: usize = shard
      .trim()
      .parse()
      .map_err(|_| format!("promote spec: bad shard in {part:?}"))?;
    let p = promotions
      .get_mut(s)
      .ok_or_else(|| format!("promote spec: shard {s} out of range"))?;
    let rhs = rhs.trim();
    if let Some(hex) = rhs.strip_prefix('+') {
      let addr = Address::from_hex(hex)
        .ok_or_else(|| format!("promote spec: bad address in {part:?}"))?;
      let id = *id_of.get(&addr).ok_or_else(|| {
        format!("promote spec: address {hex} is not a profile block")
      })?;
      p.extra_full.push(id);
    } else {
      p.rounds = rhs
        .parse()
        .map_err(|_| format!("promote spec: bad rounds in {part:?}"))?;
    }
  }
  Ok(promotions)
}

pub fn shard_esp_aiur(
  esp_path: &str,
  ram_budget_gib: f64,
  balance: f64,
  parallelism: usize,
  out_path: Option<&str>,
  promote_spec: &str,
) -> Result<String, String> {
  let bytes =
    std::fs::read(esp_path).map_err(|e| format!("read {esp_path}: {e}"))?;
  let profile = BlockProfile::from_bytes(&bytes)
    .map_err(|e| format!("parse {esp_path}: {e}"))?;
  if !profile.has_ref_graph() {
    return Err(format!(
      "{esp_path} has no reference graph — Aiur packing needs the closure \
       accounting it drives; regenerate with the current `ix profile`"
    ));
  }
  if !profile.has_type_ref_graph() {
    return Err(format!(
      "{esp_path} has no type-reference sub-graph — the ingress model needs \
       it (and the block kind flags); regenerate with the current \
       `ix profile`"
    ));
  }
  let mut plan = partition_for_aiur_ram(&profile, ram_budget_gib, balance);
  // Replace the partitioner's delta-frontier with the real ingress
  // classification: what this shard loads but does not check, and which of
  // those are type-only stubs. The witness builders cannot derive this from
  // the environment — "reduces through" lives in the profile's delta graph.
  //
  // `promote_spec` is the per-shard escalation for replay divergence
  // (see `parse_promote_spec`); the repair driver accumulates it across
  // retry iterations, and `ix shard --promote` exposes it manually.
  let promotions = parse_promote_spec(promote_spec, &profile, plan.num_shards)?;
  let sets = aiur_shard_ingress_sets(
    &profile,
    &plan.shard_of,
    plan.num_shards,
    &promotions,
  );
  // Re-price union bytes from the EMITTED sets. The pack walk priced the
  // round-0 frontier; promotion rounds grow what a shard actually
  // ingresses, and the costs sidecar and cap report must describe the
  // manifest that ships, not the estimate that packed it.
  let mut owned_bytes = vec![0u64; plan.num_shards];
  for (b, &s) in plan.shard_of.iter().enumerate() {
    owned_bytes[s as usize] = owned_bytes[s as usize]
      .saturating_add(u64::from(profile.block(b as u32).serialized_size));
  }
  for (s, (full_extra, stubbed)) in sets.iter().enumerate() {
    let cross: u64 = full_extra
      .iter()
      .chain(stubbed.iter())
      .map(|&b| u64::from(profile.block(b).serialized_size))
      .sum();
    plan.shard_costs[s].union_bytes = owned_bytes[s].saturating_add(cross);
  }
  plan.max_shard_ram_gib = plan
    .shard_costs
    .iter()
    .map(|c| aiur_ram_gib(c.union_bytes, c.hb))
    .fold(0.0, f64::max);
  let mut manifest =
    ShardManifest::build(&profile, &plan.shard_of, plan.num_shards)
      .with_tree(plan.tree);
  for (shard, (full_extra, stubbed)) in manifest.shards.iter_mut().zip(&sets) {
    let addr = |b: &u32| profile.block(*b).addr.clone();
    let mut foreign: Vec<Address> =
      full_extra.iter().chain(stubbed.iter()).map(addr).collect();
    foreign.sort();
    shard.cross_ingress = full_extra
      .iter()
      .chain(stubbed.iter())
      .map(|&b| u64::from(profile.block(b).serialized_size))
      .sum();
    shard.foreign_blocks = foreign;
    shard.stubbed_blocks = stubbed.iter().map(addr).collect();
    shard.assumption_root =
      ixon::merkle::merkle_root_canonical(&shard.foreign_blocks);
  }
  if let Some(op) = out_path {
    std::fs::write(op, manifest.to_bytes())
      .map_err(|e| format!("write {op}: {e}"))?;
  }
  // Per-shard predicted prove time from the packer's own accounting: the
  // closure-union ingress bytes plus the owned blocks' substitution volume.
  let prove_secs: Vec<f64> = plan
    .shard_costs
    .iter()
    .map(|c| aiur_prove_secs(c.union_bytes, c.subst))
    .collect();
  // Costs sidecar (`<out>.costs.csv`): the packer's per-shard accounting and
  // predictions, for measured-vs-predicted comparison and refits.
  if let Some(op) = out_path {
    let mut csv = String::from(
      "shard,union_bytes,hb,subst,whnf,def_eq,nat_arith,pred_ram_gib,pred_prove_s\n",
    );
    for (i, c) in plan.shard_costs.iter().enumerate() {
      csv.push_str(&format!(
        "{},{},{},{},{},{},{},{:.2},{:.2}\n",
        i,
        c.union_bytes,
        c.hb,
        c.subst,
        c.whnf,
        c.def_eq,
        c.nat_arith,
        aiur_ram_gib(c.union_bytes, c.hb),
        prove_secs[i],
      ));
    }
    let cp = format!("{op}.costs.csv");
    std::fs::write(&cp, csv).map_err(|e| format!("write {cp}: {e}"))?;
  }
  let seq_secs: f64 = prove_secs.iter().sum();
  let max_secs = prove_secs.iter().fold(0.0f64, |a, &s| a.max(s));
  let p = parallelism.max(1);
  let wall_secs = (seq_secs / p as f64).max(max_secs);
  let note = if plan.infeasible_atomic_floor {
    "\n  [INFEASIBLE: a single atomic block exceeds the RAM cap — split it upstream, raise the budget, or use a bigger box]"
  } else {
    ""
  };
  Ok(format!(
    "blocks={} delta_edges={} aiur ram_budget={:.0} GiB (cap {:.1} at {:.0}% usable) → {} shards (packed to cap)\n{}\nprove est ~{} wall at parallelism={} (sequential ~{})\nmax_shard_ram={:.1} GiB largest_block_ram={:.1} GiB{}",
    profile.num_blocks(),
    profile.num_edges(),
    ram_budget_gib,
    plan.ram_cap_gib,
    AIUR_RAM_USABLE_FRAC * 100.0,
    plan.num_shards,
    manifest.summary(),
    fmt_duration(wall_secs),
    p,
    fmt_duration(seq_secs),
    plan.max_shard_ram_gib,
    plan.largest_block_ram_gib,
    note,
  ))
}

/// Calibrated Zisk guest-STEP cost model — the **single source of truth** for
/// predicting a block's in-circuit step contribution: reduction work
/// (`heartbeats` + substitution-node visits `subst`) plus a small ingress term
/// (`serialized_size` bytes). These are **best-fit** coefficients (over 76
/// Init/Std/Mathlib constants + 12 shards; the cycle model is `180M floor +
/// 162k·hb + 4.3k·subst + 0.65k·bytes`, MAPE 9%). One definition, used
/// everywhere: the `ix profile` breakdown, per-shard prediction, and the packer's
/// cap test. No conservatism is baked into the coefficients — that would distort
/// packing; the cap's safety margin is [`RAM_USABLE_FRAC`] in
/// [`cycle_cap_for_ram`], reinforced by the model's own ~1.1× over-prediction.
pub const STEPS_PER_HEARTBEAT: u64 = 162_339;
pub const STEPS_PER_SUBST: u64 = 4_276;
pub const STEPS_PER_INGRESS_BYTE: u64 = 652;
/// Fixed per-shard (per-leaf) guest-STEP floor (the model intercept): proof/base
/// setup plus the foreign-dependency ingress a shard re-pays.
pub const SHARD_STEP_FLOOR: u64 = 180_000_000;

/// Predicted Zisk guest STEPS contributed by a single block (reduction + its own
/// ingress). The per-shard floor and any cross-shard re-ingress are added at the
/// shard level, not here.
pub fn block_step_cost(b: &BlockEntry) -> u64 {
  STEPS_PER_HEARTBEAT
    .saturating_mul(b.heartbeats)
    .saturating_add(STEPS_PER_SUBST.saturating_mul(b.subst))
    .saturating_add(
      STEPS_PER_INGRESS_BYTE.saturating_mul(u64::from(b.serialized_size)),
    )
}

/// The per-shard cycle cap implied by a machine's total RAM — so callers can
/// size shards straight from `MemTotal` without ever picking a budget. Inverts
/// the measured single-leaf prover model on this setup
/// (`peak_RAM_GiB ≈ 50 + 33 × steps_billions`, measured by a guarded 7-shard GPU
/// prove sweep over 0.27–3.79e9-step Init shards, R²=0.99) at
/// [`RAM_USABLE_FRAC`] of RAM (reserving the rest for the OS, cross-shard
/// re-ingress, and run-to-run variance). Returns 0 when the box can't even hold the ~50 GiB
/// prover base (nothing will prove). Approximate by design — pair with
/// [`partition_for_cycle_cap`] to get N. The earlier `45 + 32` model was
/// optimistic on both base and slope (a 4.84e9-step shard it sized for a 200 GB
/// target actually used ~225 GB).
/// Measured prover-RAM model (the single source of truth, used by both
/// [`cycle_cap_for_ram`] and [`ram_gib_for_steps`]): peak host RAM ≈
/// `RAM_BASE_GIB + RAM_GIB_PER_BCYCLE × steps_billions`.
pub const RAM_BASE_GIB: f64 = 50.0;
pub const RAM_GIB_PER_BCYCLE: f64 = 33.0;
/// Usable fraction of a host-RAM budget (headroom for OS + variance) — applied
/// to whatever budget the caller gives (explicit `--max-ram`, or detected
/// system RAM by default).
pub const RAM_USABLE_FRAC: f64 = 0.85;

/// Predicted peak prover RAM (GiB) for a leaf of `steps` guest STEPS.
pub fn ram_gib_for_steps(steps: u64) -> f64 {
  RAM_BASE_GIB + RAM_GIB_PER_BCYCLE * (steps as f64 / 1e9)
}

pub fn cycle_cap_for_ram(ram_gb: f64) -> u64 {
  let headroom = ram_gb * RAM_USABLE_FRAC - RAM_BASE_GIB;
  if headroom <= 0.0 {
    return 0;
  }
  (headroom / RAM_GIB_PER_BCYCLE * 1e9) as u64
}

/// Measured single-GPU **leaf prove time**: `≈ PROVE_SETUP_SECS +
/// PROVE_SECS_PER_BCYCLE × steps_billions` per shard (RTX PRO 6000).
/// Aggregation adds a smaller per-fold term this model
/// omits — minutes next to hours of leaf proving at large shard counts.
pub const PROVE_SETUP_SECS: f64 = 54.0;
pub const PROVE_SECS_PER_BCYCLE: f64 = 158.0;

/// Predicted single-shard leaf prove time (seconds) for a leaf of `steps`.
pub fn shard_prove_secs(steps: u64) -> f64 {
  PROVE_SETUP_SECS + PROVE_SECS_PER_BCYCLE * (steps as f64 / 1e9)
}

/// `x·log₂(x+2)` — the feature form of the Aiur cost model. Aiur's prover work
/// is a sum of `width·height·log₂(height)` FFTs over its circuits, and each
/// dominant circuit family's height tracks one kernel counter, so a counter's
/// cost contribution is super-linear with exactly this shape. The `+2` keeps
/// the log positive at zero.
#[allow(clippy::cast_precision_loss)] // counters are far below 2^53
fn nlogn(x: u64) -> f64 {
  let x = x as f64;
  x * (x + 2.0).log2()
}

/// Calibrated Aiur cost model — predicts a **run's** (one Aiur prove: a whole
/// closure or one shard) prove time and peak host RAM directly from the kernel
/// profile counters, no Aiur execution needed. Features are run-level
/// aggregates: `bytes` is every serialized byte the run ingresses (member
/// blocks *plus* cross-shard foreign blocks — Aiur hashes all of it, so
/// duplication costs real prove work), `hb`/`subst` are the run's summed
/// reduction counters. Fit against measured `aiur-check-prove` bench-suite
/// runs (bencher.dev `ix` project); coefficients and fit quality live in the
/// calibrating commit's message. Known limit: constants whose Aiur cost is
/// dominated by big-Nat limb gadgets have no native-counter signal and
/// under-predict; [`AIUR_RAM_USABLE_FRAC`] carries that risk.
pub const AIUR_PROVE_BASE_SECS: f64 = 1.43;
pub const AIUR_PROVE_SECS_PER_NLOGN_INGRESS_BYTE: f64 = 2.38e-7;
pub const AIUR_PROVE_SECS_PER_NLOGN_SUBST: f64 = 9.06e-7;
pub const AIUR_RAM_BASE_GIB: f64 = 3.67;
pub const AIUR_RAM_GIB_PER_NLOGN_INGRESS_BYTE: f64 = 1.18e-6;
pub const AIUR_RAM_GIB_PER_NLOGN_HEARTBEAT: f64 = 1.57e-5;
/// Usable fraction of an Aiur host-RAM budget. Lower than the Zisk
/// [`RAM_USABLE_FRAC`]: it also absorbs the model's blind spot on
/// limb-arithmetic-heavy blocks, not just OS overhead and variance.
pub const AIUR_RAM_USABLE_FRAC: f64 = 0.7;

/// Predicted Aiur prove time (seconds) for one run ingressing `bytes` and
/// performing `subst` substitution-node visits.
pub fn aiur_prove_secs(bytes: u64, subst: u64) -> f64 {
  AIUR_PROVE_BASE_SECS
    + AIUR_PROVE_SECS_PER_NLOGN_INGRESS_BYTE * nlogn(bytes)
    + AIUR_PROVE_SECS_PER_NLOGN_SUBST * nlogn(subst)
}

/// Predicted Aiur peak host RAM (GiB) for one run ingressing `bytes` at `hb`
/// heartbeats of reduction.
pub fn aiur_ram_gib(bytes: u64, hb: u64) -> f64 {
  AIUR_RAM_BASE_GIB
    + AIUR_RAM_GIB_PER_NLOGN_INGRESS_BYTE * nlogn(bytes)
    + AIUR_RAM_GIB_PER_NLOGN_HEARTBEAT * nlogn(hb)
}

/// A block's marginal predicted Aiur prove time (seconds), `nlogn` taken at
/// block granularity and the per-run base omitted. Slightly under-counts a
/// block's share inside a large run (whose `log` factor is bigger), which is
/// fine for its purpose: ranking blocks in the `ix profile` leaderboards.
pub fn aiur_block_prove_secs(b: &BlockEntry) -> f64 {
  AIUR_PROVE_SECS_PER_NLOGN_INGRESS_BYTE * nlogn(u64::from(b.serialized_size))
    + AIUR_PROVE_SECS_PER_NLOGN_SUBST * nlogn(b.subst)
}

/// Calibrated Aiur **execute** (witness-generation, no prove) cost model —
/// same feature form and calibration pipeline as the prove model above, fit
/// against the `aiur-check-execute` bench suite. Execute RAM is bytes-only:
/// the retained query record is dominated by ingress/hashing rows, and no
/// second feature survives a non-negative fit.
pub const AIUR_EXEC_BASE_SECS: f64 = 0.146;
pub const AIUR_EXEC_SECS_PER_NLOGN_INGRESS_BYTE: f64 = 8.54e-8;
pub const AIUR_EXEC_SECS_PER_NLOGN_SUBST: f64 = 6.77e-8;
pub const AIUR_EXEC_RAM_BASE_GIB: f64 = 4.72;
pub const AIUR_EXEC_RAM_GIB_PER_NLOGN_INGRESS_BYTE: f64 = 8.50e-8;

/// Predicted Aiur execute time (seconds) for one run.
pub fn aiur_exec_secs(bytes: u64, subst: u64) -> f64 {
  AIUR_EXEC_BASE_SECS
    + AIUR_EXEC_SECS_PER_NLOGN_INGRESS_BYTE * nlogn(bytes)
    + AIUR_EXEC_SECS_PER_NLOGN_SUBST * nlogn(subst)
}

/// Predicted Aiur execute peak host RAM (GiB) for one run.
pub fn aiur_exec_ram_gib(bytes: u64) -> f64 {
  AIUR_EXEC_RAM_BASE_GIB
    + AIUR_EXEC_RAM_GIB_PER_NLOGN_INGRESS_BYTE * nlogn(bytes)
}

/// Whole-workload prove-time estimate over a partition's per-shard step counts.
pub struct ProveEstimate {
  /// Σ predicted guest STEPS over all shards (incl. per-shard floor + ingress).
  pub total_steps: u64,
  /// Sum of per-shard leaf prove times — wall clock with a single prover.
  pub seq_secs: f64,
  /// Wall clock with `parallelism` provers; `seq_secs` at parallelism 1.
  pub wall_secs: f64,
  /// Provers assumed (≥1).
  pub parallelism: usize,
}

/// Estimate whole-workload prove time from per-shard predicted STEPS. With
/// `parallelism` provers the wall clock is bounded below by both an even split
/// and the single slowest shard (a makespan can beat neither); for the
/// near-uniform shards the packer produces the even split dominates.
pub fn prove_estimate(
  per_shard_steps: &[u64],
  parallelism: usize,
) -> ProveEstimate {
  let p = parallelism.max(1);
  let total_steps =
    per_shard_steps.iter().fold(0u64, |a, &s| a.saturating_add(s));
  let seq_secs: f64 =
    per_shard_steps.iter().map(|&s| shard_prove_secs(s)).sum();
  let max_secs =
    per_shard_steps.iter().map(|&s| shard_prove_secs(s)).fold(0.0, f64::max);
  let wall_secs = (seq_secs / p as f64).max(max_secs);
  ProveEstimate { total_steps, seq_secs, wall_secs, parallelism: p }
}

/// Per-shard predicted full STEPS (floor + member step-cost + cross-ingress),
/// indexed by shard id, from a built manifest and its block assignment.
fn per_shard_steps(
  profile: &BlockProfile,
  shard_of: &[u32],
  manifest: &ShardManifest,
) -> Vec<u64> {
  let mut steps = vec![0u64; manifest.shards.len()];
  for (b, &s) in shard_of.iter().enumerate() {
    steps[s as usize] = steps[s as usize]
      .saturating_add(block_step_cost(profile.block(b as u32)));
  }
  for sh in &manifest.shards {
    let i = sh.id as usize;
    steps[i] = steps[i]
      .saturating_add(SHARD_STEP_FLOOR)
      .saturating_add(STEPS_PER_INGRESS_BYTE.saturating_mul(sh.cross_ingress));
  }
  steps
}

/// Human-readable duration for the prove-time report.
fn fmt_duration(secs: f64) -> String {
  if secs >= 3600.0 {
    format!("{:.1}h", secs / 3600.0)
  } else if secs >= 60.0 {
    format!("{:.0}m", secs / 60.0)
  } else {
    format!("{secs:.0}s")
  }
}

/// One-line prove-time report fragment shared by [`shard_esp`] and
/// [`shard_esp_cap`]: total steps across all shards plus the wall-clock estimate
/// at the requested `parallelism` (and the sequential baseline).
fn prove_report(
  profile: &BlockProfile,
  shard_of: &[u32],
  manifest: &ShardManifest,
  parallelism: usize,
) -> String {
  let est =
    prove_estimate(&per_shard_steps(profile, shard_of, manifest), parallelism);
  format!(
    "total_steps={} → prove est ~{} wall at parallelism={} (sequential ~{}); \
     leaf model {PROVE_SETUP_SECS:.0}s + {PROVE_SECS_PER_BCYCLE:.0}s·Bsteps/shard, aggregation extra",
    est.total_steps,
    fmt_duration(est.wall_secs),
    est.parallelism,
    fmt_duration(est.seq_secs),
  )
}

/// A partition sized to a per-shard Zisk **cycle** budget (rather than a fixed
/// shard count). See [`partition_for_cycle_cap`].
pub struct BudgetPlan {
  /// Chosen shard count.
  pub num_shards: usize,
  /// Shard assignment per block id (as [`Hypergraph::partition`] returns).
  pub shard_of: Vec<u32>,
  /// The bisection tree for the chosen partition, for tree-aligned aggregation.
  pub tree: AggNode,
  /// Per-shard predicted-STEPS cap: `max_cycles − SHARD_STEP_FLOOR` (the block
  /// step-costs that may sum into one shard before the floor pushes it over
  /// `max_cycles`).
  pub step_cap: u64,
  /// Heaviest shard's **full** predicted guest STEPS — `SHARD_STEP_FLOOR +
  /// Σ block_step_cost + STEPS_PER_INGRESS_BYTE × cross_ingress_bytes`. The
  /// packer keeps this `≤ max_cycles` (cross-ingress included), so it is the
  /// tightest single number to compare against the cap / RAM budget.
  pub max_shard_steps: u64,
  /// Largest single (atomic) block's [`block_step_cost`] — the hard floor on
  /// `max_shard_steps` that no shard count can beat.
  pub largest_block_steps: u64,
  /// True when the largest atomic block alone exceeds the cap: the budget is
  /// infeasible by sharding (split that mutual block upstream, or raise the cap
  /// / use a bigger box).
  pub infeasible_atomic_floor: bool,
}

/// Size a partition to a per-shard **cycle** (guest-STEP) budget by **bin-packing
/// to the cap**, not by balancing into a fixed shard count.
///
/// `max_cycles` is the ceiling on a single shard's in-circuit Zisk guest steps
/// — the leaf prover's trace size, which is what sets peak prover RAM. Get it
/// from a host-RAM budget with [`cycle_cap_for_ram`] (the measured prover model
/// `peak_RAM_GiB ≈ 50 + 33 × steps_billions`).
///
/// **Why packing, not balancing.** A shard's predicted STEPS is
/// `SHARD_STEP_FLOOR + Σ block_step_cost + STEPS_PER_INGRESS_BYTE ×
/// cross_ingress_bytes` (member reduction + own ingress, plus the foreign
/// dependencies it re-ingresses). The goal is the *fewest* shards that each stay
/// under the cap — not uniform shards. Balancing into `N = ⌈total/cap⌉` and
/// growing `N` whenever imbalance pushed the heaviest shard over the cap (the
/// old approach) *over-sharded*: it spread work evenly, so every shard sat
/// partially full and a single un-equalizable block forced extra shards. Packing
/// instead fills each shard as close to the cap as the dependency structure
/// allows and only opens a new shard when the next block won't fit — giving
/// `⌈total/cap⌉` shards plus a small packing remainder, each maximally
/// performant. Lumpy (a near-full shard beside a partial one) is fine.
///
/// **How dependency overlap is packed.** We first cut a *fine* min-cut partition
/// ([`PACK_PIECES_PER_CAP`] pieces per cap) purely to obtain a **cut-coherent
/// order**: a DFS of the bisection tree visits each tightly-coupled subtree
/// before moving on, so dependency-overlapping blocks are contiguous. Greedy
/// next-fit along that order therefore packs overlapping blocks into the same
/// shard — keeping their shared dependencies in-shard so they are not re-paid as
/// cross-ingress — and only the thin seams between coherent runs cross a shard
/// boundary. The cap test includes the live cross-ingress, so a shard packed
/// "to the cap" still executes under it.
///
/// Flags `infeasible_atomic_floor` when one block alone (its floor + reduction +
/// own + dependency ingress) exceeds the cap — it cannot be split, so the cap is
/// unreachable by sharding (split that mutual block upstream, or use a bigger
/// box). The block is still emitted in its own shard, best-effort.
pub fn partition_for_cycle_cap(
  profile: &BlockProfile,
  max_cycles: u64,
  epsilon: f64,
) -> BudgetPlan {
  // Safety margin lives in `cycle_cap_for_ram` (`RAM_USABLE_FRAC` withholds 15%
  // of the RAM budget) plus the model's own ~1.1× over-prediction — so the cap is
  // applied directly, no extra factor.
  let step_cap = max_cycles.saturating_sub(SHARD_STEP_FLOOR).max(1);
  let nblocks = profile.num_blocks();
  let largest_block =
    profile.blocks().iter().map(block_step_cost).max().unwrap_or(0);
  let size = |b: u32| u64::from(profile.block(b).serialized_size);

  if nblocks == 0 {
    return BudgetPlan {
      num_shards: 1,
      shard_of: Vec::new(),
      tree: AggNode::Leaf(0),
      step_cap,
      max_shard_steps: SHARD_STEP_FLOOR,
      largest_block_steps: 0,
      infeasible_atomic_floor: false,
    };
  }

  // 1. Cut-coherent block order, sized to ~PACK_PIECES_PER_CAP pieces per cap.
  let total: u128 =
    profile.blocks().iter().map(|b| u128::from(block_step_cost(b))).sum();
  let pieces = ((total.saturating_mul(PACK_PIECES_PER_CAP))
    / u128::from(step_cap)) as usize;
  let order = cut_coherent_order(profile, pieces, epsilon);

  // 2. Greedy next-fit packing to the cap, with live cross-ingress accounting.
  //    A shard accumulates members until adding the next block would push its
  //    full predicted STEPS over `max_cycles`, then a new shard opens. Foreign
  //    dependency bytes (`foreign`) shrink when a later member is itself one of
  //    the current shard's pending dependencies — exactly the overlap packing
  //    saves.
  let mut shard_of = vec![0u32; nblocks];
  let mut members: FxHashSet<u32> = FxHashSet::default();
  let mut foreign: FxHashSet<u32> = FxHashSet::default();
  let mut seen: FxHashSet<u32> = FxHashSet::default();
  let mut member_cost = 0u64;
  let mut foreign_bytes = 0u64;
  let mut cur = 0u32;
  let mut max_shard_steps = 0u64;
  let mut infeasible = false;
  let predicted = |member_cost: u64, foreign_bytes: u64| -> u64 {
    SHARD_STEP_FLOOR
      .saturating_add(member_cost)
      .saturating_add(STEPS_PER_INGRESS_BYTE.saturating_mul(foreign_bytes))
  };

  for (i, &b) in order.iter().enumerate() {
    let bc = block_step_cost(profile.block(b));
    // Foreign-byte delta if `b` joins the current shard: `b` itself drops out of
    // foreign if a prior member depended on it; `b`'s own producers join unless
    // already member/foreign.
    seen.clear();
    let mut added = 0u64;
    for &p in profile.producers(b) {
      if p != b
        && !members.contains(&p)
        && !foreign.contains(&p)
        && seen.insert(p)
      {
        added = added.saturating_add(size(p));
      }
    }
    let removed = if foreign.contains(&b) { size(b) } else { 0 };
    let tent_fbytes =
      foreign_bytes.saturating_add(added).saturating_sub(removed);
    let tentative = predicted(member_cost.saturating_add(bc), tent_fbytes);

    // Open a new shard when the current one is non-empty and `b` won't fit. The
    // first block of a run always goes in (a lone over-cap block is flagged
    // infeasible below, not split — it can't be).
    if !members.is_empty() && tentative > max_cycles {
      max_shard_steps =
        max_shard_steps.max(predicted(member_cost, foreign_bytes));
      cur += 1;
      members.clear();
      foreign.clear();
      member_cost = 0;
      foreign_bytes = 0;
    }

    // Commit `b` into the current shard.
    if foreign.remove(&b) {
      foreign_bytes = foreign_bytes.saturating_sub(size(b));
    }
    members.insert(b);
    member_cost = member_cost.saturating_add(bc);
    for &p in profile.producers(b) {
      if p != b && !members.contains(&p) && foreign.insert(p) {
        foreign_bytes = foreign_bytes.saturating_add(size(p));
      }
    }
    shard_of[b as usize] = cur;
    if members.len() == 1 && predicted(member_cost, foreign_bytes) > max_cycles
    {
      infeasible = true; // this block alone overflows the cap
    }
    if i == order.len() - 1 {
      max_shard_steps =
        max_shard_steps.max(predicted(member_cost, foreign_bytes));
    }
  }

  let num_shards = (cur + 1) as usize;
  // 3. Balanced aggregation tree over the shard sequence. Shards are numbered in
  //    packing (cut-coherent) order, so adjacent ids are coupled — a balanced
  //    binary tree over `0..num_shards` keeps coupled shards as siblings, so
  //    cross-shard assumptions discharge low in the fold.
  let tree = balanced_agg_tree(0, num_shards as u32);

  BudgetPlan {
    num_shards,
    shard_of,
    tree,
    step_cap,
    max_shard_steps,
    largest_block_steps: largest_block,
    infeasible_atomic_floor: infeasible,
  }
}

/// A partition sized to a per-shard Aiur host-RAM budget. The Aiur analog of
/// [`BudgetPlan`], reported in the Aiur model's native unit (GiB) rather than
/// guest steps.
/// One shard's Aiur cost aggregates as the packer accounted them: the
/// closure-union ingress bytes plus the owned blocks' checking counters.
#[derive(Clone, Copy, Debug, Default)]
pub struct AiurShardCost {
  /// Serialized bytes of the shard's full reference-closure union (owned ∪
  /// every transitively referenced block) — what the shard's CheckEnv claim
  /// ingresses and hashes.
  pub union_bytes: u64,
  /// Σ heartbeats over owned blocks only (frontier constants are assumptions,
  /// never re-checked).
  pub hb: u64,
  /// Σ substitution-node visits over owned blocks only.
  pub subst: u64,
  /// Σ `whnf` entries over owned blocks only.
  pub whnf: u64,
  /// Σ definitional-equality checks over owned blocks only.
  pub def_eq: u64,
  /// Σ big-Nat limb-work units over owned blocks only — the klimbs
  /// circuit family's only recorded signal; persisted per shard so the
  /// RAM model's content residual can eventually be fit against it.
  pub nat_arith: u64,
}

pub struct AiurBudgetPlan {
  /// Chosen shard count.
  pub num_shards: usize,
  /// Shard assignment per block id.
  pub shard_of: Vec<u32>,
  /// The bisection tree for the chosen partition, for tree-aligned aggregation.
  pub tree: AggNode,
  /// Per-shard predicted-RAM cap actually enforced:
  /// `budget × AIUR_RAM_USABLE_FRAC`.
  pub ram_cap_gib: f64,
  /// Per-shard cost aggregates, indexed by shard id.
  pub shard_costs: Vec<AiurShardCost>,
  /// Heaviest shard's full predicted RAM — the tightest number to compare
  /// against the cap.
  pub max_shard_ram_gib: f64,
  /// Largest single block's predicted RAM with its full closure ingress —
  /// the hard floor no shard count can beat: every shard containing the
  /// block ingresses at least that closure.
  pub largest_block_ram_gib: f64,
  /// True when one block alone (closure included) exceeds the cap.
  pub infeasible_atomic_floor: bool,
}

/// Per-shard ingress classification under the frontier-trusted model, as block
/// ids: `(unchecked_full, stubbed)`.
///
/// Runs the same two-state walk the packer costs with, but per finished shard,
/// and reports what the witness builder needs rather than a byte total:
///
/// - `stubbed` — reached only as a type-only axiom. Its body is withheld and
///   its references are not followed.
/// - `unchecked_full` — ingressed whole but owned by another shard: every
///   block the owned checks CONSULTED per the profile's touch graph (type and
///   height reads included), plus any block reduction consumes, which cannot
///   be a stub.
///
/// With a touch graph (v4 profile) the full set is a *measurement*: what the
/// recording run's lazy checker faulted in, which is exactly what the shard's
/// replay consults. Without one the walk falls back to the delta closure —
/// a prediction known to under-ingress (stubbing erases definitional height,
/// which changes lazy-delta's unfold order), kept only so old profiles still
/// produce manifests.
///
/// Owned blocks appear in neither list.
///
/// `promotions[s]` is shard `s`'s escalation state for replay divergence
/// (the Aiur kernel's caches are not the Rust kernel's, so it occasionally
/// reduces where the recording short-circuited and reaches a stub):
///
/// - `extra_full` — specific blocks seeded FULL, on top of the measured
///   set. This is the constant-precision rung: when a failing shard NAMES
///   the stub it needs (the kernel's wanted-stub report), only that block
///   is promoted and only its refs join the stub frontier.
/// - `rounds` — the blunt rung: each round promotes every current stub to
///   FULL and re-expands, pushing the whole frontier one reference hop
///   out (~1.5x union bytes per round — check the re-priced cap).
///
/// Round 0 with no extras is the measured baseline. Per-shard because an
/// ingress-set change shifts the replay's execution paths, so a global
/// promotion can flip a previously-green shard; each shard settles at its
/// own working escalation.
#[derive(Clone, Default, Debug, PartialEq, Eq)]
pub struct ShardPromotion {
  /// Whole-frontier promotion rounds.
  pub rounds: usize,
  /// Specific block ids seeded FULL (from wanted-stub reports).
  pub extra_full: Vec<u32>,
}

pub fn aiur_shard_ingress_sets(
  profile: &BlockProfile,
  shard_of: &[u32],
  num_shards: usize,
  promotions: &[ShardPromotion],
) -> Vec<(Vec<u32>, Vec<u32>)> {
  assert_eq!(promotions.len(), num_shards);
  let nblocks = profile.num_blocks();
  let mut owned_of: Vec<Vec<u32>> = vec![Vec::new(); num_shards];
  for (b, &s) in shard_of.iter().enumerate() {
    owned_of[s as usize].push(b as u32);
  }
  let measured = profile.has_touch_graph();
  // Three independent marks. Conflating "expanded as full" with "expanded as
  // axiom" loses blocks: the work stack is LIFO, so an owned block can be
  // popped as a stub (reached from some ref) before its own FULL entry comes
  // up, and a guard that tests both marks then skips the FULL expansion and
  // never follows that block's references.
  let mut full_mark = vec![u32::MAX; nblocks];
  let mut axiom_mark = vec![u32::MAX; nblocks];
  let mut out = Vec::with_capacity(num_shards);
  for (s, owned) in owned_of.iter().enumerate() {
    let epoch = s as u32;
    let is_owned = |b: u32| shard_of[b as usize] as usize == s;
    let mut work: Vec<(u32, bool)> = owned.iter().map(|&b| (b, true)).collect();
    if measured {
      // Everything the owned checks consulted ships whole, heights intact,
      // so the decisions the recording run made replay identically.
      for &b in owned {
        work.extend(profile.touched_blocks(b).iter().map(|&t| (t, true)));
      }
    }
    // Constant-precision escalations: named blocks ship whole.
    work.extend(promotions[s].extra_full.iter().map(|&b| (b, true)));
    let (mut full_extra, mut stubbed) = (Vec::new(), Vec::new());
    for round in 0..=promotions[s].rounds {
      if round > 0 {
        // Escalate: every stub still standing becomes FULL and re-expands.
        // `full_mark` overrides `axiom_mark`, so the final retain drops the
        // promoted entries from `stubbed`.
        work.extend(
          stubbed
            .iter()
            .filter(|&&b| full_mark[b as usize] != epoch)
            .map(|&b| (b, true)),
        );
        if work.is_empty() {
          break;
        }
      }
      while let Some((x, is_full)) = work.pop() {
        if is_full {
          if full_mark[x as usize] == epoch {
            continue;
          }
          full_mark[x as usize] = epoch;
          if !is_owned(x) {
            full_extra.push(x);
          }
          // Prediction-only cascade: anything ingressed whole may be REDUCED
          // through, so whatever it unfolds must be whole as well. Measured
          // sets don't need it — a consulted body's unfolds were consulted
          // too, and recorded against the owned consumer directly.
          if !measured {
            for &p in profile.producers(x) {
              work.push((p, true));
            }
          }
          for &r in profile.refs(x) {
            work.push((r, !profile.block(r).axiomatizable()));
          }
        } else {
          if full_mark[x as usize] == epoch || axiom_mark[x as usize] == epoch {
            continue;
          }
          axiom_mark[x as usize] = epoch;
          if !is_owned(x) {
            stubbed.push(x);
          }
          for &r in profile.type_refs(x) {
            work.push((r, !profile.block(r).axiomatizable()));
          }
        }
      }
    }
    // A block promoted stub -> full must not stay in `stubbed`, and an owned
    // block is never either.
    stubbed.retain(|&b| full_mark[b as usize] != epoch && !is_owned(b));
    full_extra.retain(|&b| !is_owned(b));
    full_extra.sort_unstable();
    full_extra.dedup();
    stubbed.sort_unstable();
    stubbed.dedup();
    out.push((full_extra, stubbed));
  }
  out
}

/// Size a partition to a per-shard Aiur host-RAM budget by bin-packing to the
/// cap — the Aiur counterpart of [`partition_for_cycle_cap`], with the same
/// cut-coherent-order + greedy next-fit structure but **ingress-union byte
/// accounting**.
///
/// A shard's CheckEnv claim ingresses and hashes a union of blocks in one of
/// two states, and pays each block's serialized bytes once either way — only
/// the recursion differs:
///
/// - **full**: the block is ingressed whole, so every reference it carries
///   must be present. Owned blocks are full, as is everything they
///   delta-unfold (an unfolded body's references must resolve) and any block
///   reduction can consume ([`BlockEntry::NOT_AXIOMATIZABLE`] — inductives,
///   constructors, recursors, quotients, projections).
/// - **axiom**: a frontier block, ingressed as a type-only stub. It is
///   trusted rather than re-checked and never unfolded, so the walk continues
///   through its TYPE references only.
///
/// Checking counters (hb/subst) stay owned-blocks-only. Grouping blocks with
/// overlapping ingress is therefore the packing objective that matters: a
/// shared dependency's bytes are paid once per shard that reaches it.
///
/// When the profile carries a **touch graph** (v4, recorded by a lazy
/// profiling run), each owned block additionally seeds every block its check
/// CONSULTED as FULL. Consultation includes type and height reads, so all
/// information that steered the recording run's lazy-delta decisions ships
/// in the witness and the run replays identically; only never-consulted
/// blocks are left as type-only stubs. Without a touch graph the seeding
/// falls back to the delta closure alone (predicted, known to under-ingress
/// in def-eq-heavy shards).
///
/// Requires the profile's reference graph, type-reference sub-graph and block
/// flags; without them the walk would silently under-count, so the caller
/// must reject such profiles.
pub fn partition_for_aiur_ram(
  profile: &BlockProfile,
  ram_budget_gib: f64,
  epsilon: f64,
) -> AiurBudgetPlan {
  let ram_cap_gib = ram_budget_gib * AIUR_RAM_USABLE_FRAC;
  let nblocks = profile.num_blocks();
  let size = |b: u32| u64::from(profile.block(b).serialized_size);

  if nblocks == 0 {
    return AiurBudgetPlan {
      num_shards: 1,
      shard_of: Vec::new(),
      tree: AggNode::Leaf(0),
      ram_cap_gib,
      shard_costs: Vec::new(),
      max_shard_ram_gib: AIUR_RAM_BASE_GIB,
      largest_block_ram_gib: 0.0,
      infeasible_atomic_floor: false,
    };
  }

  // Per-block closure bytes (the block's lone-shard ingress) — the RAM floor
  // per block and the infeasibility test. Parallel walk with per-worker
  // epoch-marked state arrays.
  let closure_bytes: Vec<u64> = {
    use rayon::prelude::*;
    (0..nblocks as u32)
      .into_par_iter()
      .map_init(
        || {
          (
            vec![0u32; nblocks],
            0u32,
            Vec::<u32>::new(),
            vec![0u32; nblocks],
            vec![0u32; nblocks],
          )
        },
        |(visited, epoch, stack, full_mark, axiom_mark), b| {
          *epoch += 1;
          let mut bytes = 0u64;
          // Two node states. FULL: ingressed whole, so every reference it
          // carries must be present — owned blocks, everything they reduce
          // through, and any block whose body reduction can consume.
          // AXIOM: ingressed as a type-only stub, so only its TYPE
          // references follow. Bytes are identical either way (the whole
          // constant is hashed); only the recursion differs.
          let mut work: Vec<(u32, bool)> = Vec::new();
          // Seed: `b` plus everything it delta-unfolds, all FULL.
          stack.clear();
          stack.push(b);
          visited[b as usize] = *epoch;
          work.push((b, true));
          while let Some(x) = stack.pop() {
            for &p in profile.producers(x) {
              if visited[p as usize] != *epoch {
                visited[p as usize] = *epoch;
                stack.push(p);
                work.push((p, true));
              }
            }
          }
          // Measured ingress: every block the check CONSULTED (type or
          // height reads included, not just unfolds) is ingressed FULL so
          // the lazy-delta decisions the recording run made replay
          // identically. Only blocks the check never looked at are left
          // to the type-only stub expansion below.
          for &t in profile.touched_blocks(b) {
            if visited[t as usize] != *epoch {
              visited[t as usize] = *epoch;
              work.push((t, true));
            }
          }
          // `visited` doubles as the byte-charged set and the delta seed
          // already claimed its members, so charge them up front; the main
          // loop's `visited` test then skips them.
          for &(x, _) in &work {
            bytes = bytes.saturating_add(size(x));
          }
          while let Some((x, is_full)) = work.pop() {
            if is_full {
              if full_mark[x as usize] == *epoch {
                continue;
              }
              full_mark[x as usize] = *epoch;
              if visited[x as usize] != *epoch {
                visited[x as usize] = *epoch;
                bytes = bytes.saturating_add(size(x));
              }
              for &p in profile.producers(x) {
                work.push((p, true));
              }
              for &r in profile.refs(x) {
                work.push((r, !profile.block(r).axiomatizable()));
              }
            } else {
              if full_mark[x as usize] == *epoch
                || axiom_mark[x as usize] == *epoch
              {
                continue;
              }
              axiom_mark[x as usize] = *epoch;
              if visited[x as usize] != *epoch {
                visited[x as usize] = *epoch;
                bytes = bytes.saturating_add(size(x));
              }
              for &r in profile.type_refs(x) {
                work.push((r, !profile.block(r).axiomatizable()));
              }
            }
          }
          bytes
        },
      )
      .collect()
  };
  let lone_block_ram = |b: u32| {
    aiur_ram_gib(closure_bytes[b as usize], profile.block(b).heartbeats)
  };
  let largest_block_ram_gib =
    (0..nblocks as u32).map(lone_block_ram).fold(0.0, f64::max);

  // 1. Cut-coherent block order. Piece sizing uses the own-bytes total as a
  //    granularity proxy (union bytes are not additive across pieces); the
  //    order's job is only to keep closure-overlapping blocks adjacent, which
  //    the min-cut on shared-dependency nets already does.
  let total_bytes: u64 = profile
    .blocks()
    .iter()
    .fold(0u64, |a, b| a.saturating_add(u64::from(b.serialized_size)));
  let total_hb: u64 =
    profile.blocks().iter().fold(0u64, |a, b| a.saturating_add(b.heartbeats));
  let total_ram = aiur_ram_gib(total_bytes, total_hb) - AIUR_RAM_BASE_GIB;
  let headroom = (ram_cap_gib - AIUR_RAM_BASE_GIB).max(f64::MIN_POSITIVE);
  let pieces = (total_ram / headroom * PACK_PIECES_PER_CAP as f64) as usize;
  let order = cut_coherent_order(profile, pieces, epsilon);

  // 2. Greedy next-fit packing to the RAM cap with live closure-union
  //    accounting. `member_mark[x] == shard_epoch` ⇔ x is in the current
  //    shard's closure union; a candidate's byte delta is a BFS that stops at
  //    union members, so each block's closure is walked at most twice (once
  //    tentatively against a full shard, once fresh in the next).
  let mut shard_of = vec![0u32; nblocks];
  let mut member_mark = vec![0u32; nblocks];
  let mut walk_mark = vec![0u32; nblocks];
  // FrontierAxiom state, per shard epoch: which blocks are in the union as
  // full ingests, which as type-only axioms, and which have had their bytes
  // charged (a block can be charged once but upgraded axiom -> full later).
  let mut full_mark = vec![0u32; nblocks];
  let mut axiom_mark = vec![0u32; nblocks];
  let mut charged_mark = vec![0u32; nblocks];
  let mut shard_epoch = 1u32;
  let mut walk_epoch = 0u32;
  let mut stack: Vec<u32> = Vec::new();
  let mut collected: Vec<u32> = Vec::new();
  let mut cur_cost = AiurShardCost::default();
  let mut shard_costs: Vec<AiurShardCost> = Vec::new();
  let mut cur = 0u32;
  let mut owned_in_cur = 0usize;
  let mut infeasible = false;
  let predicted = |c: &AiurShardCost| aiur_ram_gib(c.union_bytes, c.hb);

  // Incremental ingress walk against the shard's live union: fills
  // `collected` with the blocks `b` newly drags in and returns their byte
  // sum. `full_mark`/`axiom_mark` persist across calls within a shard, so a
  // block already present as a type-only axiom is re-expanded when a later
  // owned block needs it in full.
  let mut union_delta = |b: u32,
                         member_mark: &[u32],
                         shard_epoch: u32,
                         walk_epoch: &mut u32,
                         stack: &mut Vec<u32>,
                         collected: &mut Vec<u32>|
   -> u64 {
    *walk_epoch += 1;
    stack.clear();
    collected.clear();
    let mut bytes = 0u64;
    let mut work: Vec<(u32, bool)> = Vec::new();
    walk_mark[b as usize] = *walk_epoch;
    stack.push(b);
    work.push((b, true));
    while let Some(x) = stack.pop() {
      for &p in profile.producers(x) {
        if walk_mark[p as usize] != *walk_epoch {
          walk_mark[p as usize] = *walk_epoch;
          stack.push(p);
          work.push((p, true));
        }
      }
    }
    // Measured ingress: consulted blocks join FULL (see the closure walk).
    for &t in profile.touched_blocks(b) {
      if walk_mark[t as usize] != *walk_epoch {
        walk_mark[t as usize] = *walk_epoch;
        work.push((t, true));
      }
    }
    while let Some((x, is_full)) = work.pop() {
      let seen = if is_full {
        full_mark[x as usize] == shard_epoch
      } else {
        full_mark[x as usize] == shard_epoch
          || axiom_mark[x as usize] == shard_epoch
      };
      if seen {
        continue;
      }
      if is_full {
        full_mark[x as usize] = shard_epoch;
      } else {
        axiom_mark[x as usize] = shard_epoch;
      }
      if member_mark[x as usize] != shard_epoch
        && charged_mark[x as usize] != shard_epoch
      {
        charged_mark[x as usize] = shard_epoch;
        collected.push(x);
        bytes = bytes.saturating_add(size(x));
      }
      let next: &[u32] =
        if is_full { profile.refs(x) } else { profile.type_refs(x) };
      for &r in next {
        work.push((r, !profile.block(r).axiomatizable()));
      }
    }
    bytes
  };

  for &b in &order {
    let e = profile.block(b);
    let delta = union_delta(
      b,
      &member_mark,
      shard_epoch,
      &mut walk_epoch,
      &mut stack,
      &mut collected,
    );
    let tentative = AiurShardCost {
      union_bytes: cur_cost.union_bytes.saturating_add(delta),
      hb: cur_cost.hb.saturating_add(e.heartbeats),
      subst: cur_cost.subst.saturating_add(e.subst),
      whnf: cur_cost.whnf.saturating_add(e.whnf),
      def_eq: cur_cost.def_eq.saturating_add(e.def_eq),
      nat_arith: cur_cost.nat_arith.saturating_add(e.nat_arith),
    };

    if owned_in_cur > 0 && predicted(&tentative) > ram_cap_gib {
      // Close the shard, open a fresh union, re-walk b's full closure.
      shard_costs.push(cur_cost);
      cur += 1;
      shard_epoch += 1;
      owned_in_cur = 0;
      cur_cost = AiurShardCost::default();
      let delta = union_delta(
        b,
        &member_mark,
        shard_epoch,
        &mut walk_epoch,
        &mut stack,
        &mut collected,
      );
      cur_cost.union_bytes = delta;
    } else {
      cur_cost.union_bytes = tentative.union_bytes;
    }
    for &x in &collected {
      member_mark[x as usize] = shard_epoch;
    }
    cur_cost.hb = cur_cost.hb.saturating_add(e.heartbeats);
    cur_cost.subst = cur_cost.subst.saturating_add(e.subst);
    cur_cost.whnf = cur_cost.whnf.saturating_add(e.whnf);
    cur_cost.def_eq = cur_cost.def_eq.saturating_add(e.def_eq);
    cur_cost.nat_arith = cur_cost.nat_arith.saturating_add(e.nat_arith);
    owned_in_cur += 1;
    shard_of[b as usize] = cur;
    if owned_in_cur == 1 && predicted(&cur_cost) > ram_cap_gib {
      infeasible = true;
    }
  }
  shard_costs.push(cur_cost);
  let max_shard_ram_gib = shard_costs.iter().map(predicted).fold(0.0, f64::max);

  let num_shards = (cur + 1) as usize;
  let tree = balanced_agg_tree(0, num_shards as u32);

  AiurBudgetPlan {
    num_shards,
    shard_of,
    tree,
    ram_cap_gib,
    shard_costs,
    max_shard_ram_gib,
    largest_block_ram_gib,
    infeasible_atomic_floor: infeasible,
  }
}

/// A cut-coherent block order for greedy cap-packing: a fine min-cut
/// pre-partition's bisection tree, read in DFS order, lays tightly-coupled
/// blocks contiguously so a next-fit packer keeps dependency overlap within a
/// shard. `pieces` is the requested fine-partition size (~[`PACK_PIECES_PER_CAP`]
/// per cap, in the caller's cost unit), bounded by the block count; when
/// everything fits one cap this collapses to the trivial order.
fn cut_coherent_order(
  profile: &BlockProfile,
  pieces: usize,
  epsilon: f64,
) -> Vec<u32> {
  let nblocks = profile.num_blocks();
  let n_fine = pieces.clamp(1, nblocks);
  if n_fine < 2 {
    return (0..nblocks as u32).collect();
  }
  let h = Hypergraph::from_profile(profile);
  let (fine_of, fine_tree) = h.partition_with_tree(n_fine, epsilon);
  let mut leaf_order = Vec::with_capacity(n_fine);
  dfs_leaf_order(&fine_tree, &mut leaf_order);
  let mut rank = vec![0u32; n_fine];
  for (r, &sid) in leaf_order.iter().enumerate() {
    rank[sid as usize] = r as u32;
  }
  let mut order: Vec<u32> = (0..nblocks as u32).collect();
  order.sort_by_key(|&b| (rank[fine_of[b as usize] as usize], b));
  order
}

/// Collect the leaf shard ids of an [`AggNode`] in left-to-right DFS order.
fn dfs_leaf_order(node: &AggNode, out: &mut Vec<u32>) {
  match node {
    AggNode::Leaf(id) => out.push(*id),
    AggNode::Internal(l, r) => {
      dfs_leaf_order(l, out);
      dfs_leaf_order(r, out);
    },
  }
}

/// A balanced binary [`AggNode`] over the contiguous shard-id range `lo..hi`.
fn balanced_agg_tree(lo: u32, hi: u32) -> AggNode {
  debug_assert!(hi > lo);
  if hi - lo <= 1 {
    AggNode::Leaf(lo)
  } else {
    let mid = lo + (hi - lo) / 2;
    AggNode::Internal(
      Box::new(balanced_agg_tree(lo, mid)),
      Box::new(balanced_agg_tree(mid, hi)),
    )
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::profile::{BlockCounters, ProfileBuilder};

  fn addr(byte: u8) -> Address {
    Address::from_slice(&[byte; 32]).unwrap()
  }

  /// Fixture counters: (heartbeats, subst, subst_unique); other counters zero.
  fn bc(heartbeats: u64, subst: u64, subst_unique: u64) -> BlockCounters {
    BlockCounters { heartbeats, subst, subst_unique, ..Default::default() }
  }

  /// A distinct address for each `n` (more than the 256 `addr(u8)` affords),
  /// for fixtures large enough to exercise the multilevel coarsening path.
  /// Big-endian so that address-sort order (which fixes block ids) matches
  /// numeric order, keeping cluster members id-contiguous in the fixtures below.
  fn addr_u32(n: u32) -> Address {
    let mut b = [0u8; 32];
    b[..4].copy_from_slice(&n.to_be_bytes());
    Address::from_slice(&b).unwrap()
  }

  /// Two tight clusters {1,2,3} and {4,5,6} with heavy intra-cluster delta and a
  /// single thin cross edge. A good bisection cuts only the thin edge.
  fn two_clusters() -> BlockProfile {
    let mut b = ProfileBuilder::new();
    for i in 1..=6u8 {
      b.block(addr(i), bc(100, 0, 0), 1000, 1);
    }
    // intra cluster A
    b.delta_edge(addr(1), addr(2));
    b.delta_edge(addr(2), addr(3));
    b.delta_edge(addr(3), addr(1));
    // intra cluster B
    b.delta_edge(addr(4), addr(5));
    b.delta_edge(addr(5), addr(6));
    b.delta_edge(addr(6), addr(4));
    // thin cross edge A->B
    b.delta_edge(addr(3), addr(4));
    b.finish()
  }

  #[test]
  fn bisect_separates_clusters() {
    let p = two_clusters();
    let h = Hypergraph::from_profile(&p);
    let shard_of = h.partition(2, 0.10);
    // Blocks 0,1,2 (addr 1,2,3) should share a shard; 3,4,5 (addr 4,5,6) the other.
    assert_eq!(shard_of[0], shard_of[1]);
    assert_eq!(shard_of[1], shard_of[2]);
    assert_eq!(shard_of[3], shard_of[4]);
    assert_eq!(shard_of[4], shard_of[5]);
    assert_ne!(shard_of[0], shard_of[3]);
    // Objective: only the cross net (addr 4, size 1000) is cut, λ=2 → 1000.
    assert_eq!(h.connectivity_objective(&shard_of), 1000);
  }

  #[test]
  fn objective_matches_manifest_cross_ingress() {
    let p = two_clusters();
    let h = Hypergraph::from_profile(&p);
    let shard_of = h.partition(2, 0.10);
    let m = ShardManifest::build(&p, &shard_of, 2);
    // Σ per-shard cross-ingress must equal the km1 objective.
    assert_eq!(m.total_cross_ingress, h.connectivity_objective(&shard_of));
  }

  #[test]
  fn balanced_partition() {
    let p = two_clusters();
    let h = Hypergraph::from_profile(&p);
    let shard_of = h.partition(2, 0.10);
    let m = ShardManifest::build(&p, &shard_of, 2);
    assert_eq!(m.shards.len(), 2);
    // Each cluster has 3 blocks × 100 heartbeats = 300; perfectly balanced.
    assert_eq!(m.shards[0].heartbeats, 300);
    assert_eq!(m.shards[1].heartbeats, 300);
  }

  #[test]
  fn four_shards_perfect_split() {
    // Four clusters of 4 blocks each, heavy intra, no cross: perfect 4-way split.
    let mut b = ProfileBuilder::new();
    for c in 0..4u8 {
      let base = c * 4 + 1;
      for k in 0..4u8 {
        b.block(addr(base + k), bc(100, 0, 0), 500, 1);
      }
      b.delta_edge(addr(base), addr(base + 1));
      b.delta_edge(addr(base + 1), addr(base + 2));
      b.delta_edge(addr(base + 2), addr(base + 3));
      b.delta_edge(addr(base + 3), addr(base));
    }
    let p = b.finish();
    let h = Hypergraph::from_profile(&p);
    let shard_of = h.partition(4, 0.10);
    let m = ShardManifest::build(&p, &shard_of, 4);
    assert_eq!(m.shards.len(), 4);
    // No cross-cluster edges → zero cross ingress achievable.
    assert_eq!(m.total_cross_ingress, 0);
    // Each non-empty shard should hold exactly one cluster (4×100).
    for s in &m.shards {
      assert_eq!(s.heartbeats, 400);
    }
  }

  #[test]
  fn manifest_roundtrip_serialization() {
    let p = two_clusters();
    let h = Hypergraph::from_profile(&p);
    let shard_of = h.partition(2, 0.10);
    let mut m = ShardManifest::build(&p, &shard_of, 2);
    // Simulate the env layer filling in an assumption root on one shard.
    m.shards[0].assumption_root = Some(addr(42));
    let bytes = m.to_bytes();
    let q = ShardManifest::from_bytes(&bytes).unwrap();
    assert_eq!(m, q);
    assert_eq!(q.shards[0].assumption_root, Some(addr(42)));
    assert_eq!(q.shards[1].assumption_root, None);
  }

  #[test]
  fn cap_keeps_shards_non_empty_under_skew() {
    // A heavy atomic block among many light ones. Capping the balance weight at
    // total/num_shards (plus leaf-count allocation) must keep every shard
    // non-empty (parallelism is the goal), even though heartbeat balance is
    // impossible.
    let mut b = ProfileBuilder::new();
    b.block(addr(1), bc(30_000, 0, 0), 100, 1); // ~30x a light block
    for i in 2..=65u8 {
      b.block(addr(i), bc(1000, 0, 0), 100, 1);
    }
    for i in 2..=64u8 {
      b.delta_edge(addr(i), addr(i + 1));
    }
    let p = b.finish();
    let h = Hypergraph::from_profile(&p);
    let shard_of = h.partition(8, 0.20); // 8 shards from 65 blocks
    let m = ShardManifest::build(&p, &shard_of, 8);
    assert_eq!(m.shards.len(), 8);
    assert_eq!(
      m.shards.iter().filter(|s| s.blocks.is_empty()).count(),
      0,
      "capping must keep all shards non-empty"
    );
  }

  /// Full predicted STEPS of a shard under a partition: floor + member step-cost
  /// + cross-ingress (foreign producers' bytes). Mirrors the packer's cap test.
  fn shard_predicted(p: &BlockProfile, shard_of: &[u32], s: u32) -> u64 {
    let members: FxHashSet<u32> = (0..p.num_blocks() as u32)
      .filter(|&b| shard_of[b as usize] == s)
      .collect();
    let member_cost: u64 =
      members.iter().map(|&b| block_step_cost(p.block(b))).sum();
    let mut foreign: FxHashSet<u32> = FxHashSet::default();
    for &b in &members {
      for &pr in p.producers(b) {
        if !members.contains(&pr) {
          foreign.insert(pr);
        }
      }
    }
    let foreign_bytes: u64 =
      foreign.iter().map(|&pr| u64::from(p.block(pr).serialized_size)).sum();
    SHARD_STEP_FLOOR + member_cost + STEPS_PER_INGRESS_BYTE * foreign_bytes
  }

  #[test]
  fn cap_packs_to_minimal_shards_under_cap() {
    // 40 blocks, each ≈162.339M steps (hb=1000), no ingress. With a 1e9 cap the
    // floor is 180M, leaving room for 5 blocks/shard (5×162.339M = 811.7M ≤
    // 820M; a 6th overflows). Packing should produce exactly ⌈40/5⌉ = 8 shards,
    // each under the cap — no over-sharding from balancing.
    let mut b = ProfileBuilder::new();
    for i in 1..=40u8 {
      b.block(addr(i), bc(1000, 0, 0), 0, 0);
    }
    for i in 1..40u8 {
      b.delta_edge(addr(i), addr(i + 1));
    }
    let p = b.finish();
    let max_cycles = 1_000_000_000u64;
    let plan = partition_for_cycle_cap(&p, max_cycles, 0.05);
    assert_eq!(plan.num_shards, 8, "should pack to the minimal 8 shards");
    assert!(!plan.infeasible_atomic_floor);
    for s in 0..plan.num_shards as u32 {
      let pred = shard_predicted(&p, &plan.shard_of, s);
      assert!(
        pred <= max_cycles,
        "shard {s} predicted {pred} exceeds cap {max_cycles}"
      );
    }
    assert!(plan.max_shard_steps <= max_cycles);
    // Every block assigned to a real shard; tree leaves match the shard ids.
    assert_eq!(plan.tree.num_leaves(), plan.num_shards);
  }

  #[test]
  fn cap_cross_ingress_counts_against_the_cap() {
    // Two blocks that each delta-unfold a heavy shared dependency `dep` (large
    // serialized_size). If they land in different shards, BOTH re-ingress `dep`.
    // The packer must keep them together (coherent order) so `dep` is paid once,
    // and must count `dep`'s bytes when deciding the cap.
    let mut b = ProfileBuilder::new();
    b.block(addr(1), bc(10, 0, 0), 4_000_000, 0); // dep: ~2.6e9 ingress steps if foreign
    b.block(addr(2), bc(100, 0, 0), 0, 0);
    b.block(addr(3), bc(100, 0, 0), 0, 0);
    b.delta_edge(addr(2), addr(1)); // 2 unfolds dep
    b.delta_edge(addr(3), addr(1)); // 3 unfolds dep
    let p = b.finish();
    // Cap large enough to hold everything in one shard.
    let plan = partition_for_cycle_cap(&p, 10_000_000_000, 0.05);
    for s in 0..plan.num_shards as u32 {
      let pred = shard_predicted(&p, &plan.shard_of, s);
      assert!(pred <= 10_000_000_000, "shard {s} over cap: {pred}");
    }
  }

  #[test]
  fn cap_flags_infeasible_atomic_block() {
    // A single block whose own predicted STEPS exceed the cap cannot be split —
    // it is emitted alone and the plan is flagged infeasible.
    let mut b = ProfileBuilder::new();
    b.block(addr(1), bc(100_000, 0, 0), 0, 0); // ~16.2e9 steps, far over a 1e9 cap
    b.block(addr(2), bc(100, 0, 0), 0, 0);
    let p = b.finish();
    let plan = partition_for_cycle_cap(&p, 1_000_000_000, 0.05);
    assert!(plan.infeasible_atomic_floor, "oversized atomic block must flag");
  }

  #[test]
  fn aiur_model_monotone() {
    // The packer's greedy cap test is only sound if the model never decreases
    // when a shard grows in either aggregate.
    let base = aiur_ram_gib(1_000_000, 10_000);
    assert!(aiur_ram_gib(2_000_000, 10_000) > base);
    assert!(aiur_ram_gib(1_000_000, 20_000) > base);
    let p = aiur_prove_secs(1_000_000, 100_000);
    assert!(aiur_prove_secs(2_000_000, 100_000) > p);
    assert!(aiur_prove_secs(1_000_000, 200_000) > p);
  }

  /// Attach a reference graph given per-block (sorted, deduped) ref lists.
  fn with_refs(mut p: BlockProfile, adj: &[Vec<u32>]) -> BlockProfile {
    p.set_ref_graph(adj);
    p
  }

  #[test]
  fn aiur_ram_cap_respected() {
    // 40-block chain (each references the next), uniform weights: the packer
    // must split into multiple shards each under the (usable-fraction) cap,
    // where a shard's bytes are its closure UNION — for a chain, everything
    // downstream of its first member.
    let mut b = ProfileBuilder::new();
    for i in 1..=40u8 {
      b.block(addr(i), bc(10_000, 100_000, 0), 20_000, 1);
    }
    for i in 1..40u8 {
      b.delta_edge(addr(i), addr(i + 1));
    }
    let adj: Vec<Vec<u32>> =
      (0..40u32).map(|i| if i < 39 { vec![i + 1] } else { vec![] }).collect();
    let p = with_refs(b.finish(), &adj);
    let budget = 64.0;
    let plan = partition_for_aiur_ram(&p, budget, 0.05);
    assert!(plan.num_shards > 1, "must shard: whole env exceeds the budget");
    assert!(
      plan.max_shard_ram_gib <= plan.ram_cap_gib,
      "heaviest shard {} exceeds cap {}",
      plan.max_shard_ram_gib,
      plan.ram_cap_gib,
    );
    // Every block is assigned, ids contiguous.
    assert_eq!(plan.shard_of.len(), 40);
    let max_id = plan.shard_of.iter().copied().max().unwrap() as usize;
    assert_eq!(max_id + 1, plan.num_shards);
  }

  #[test]
  fn aiur_union_counts_shared_dep_once() {
    // Blocks 0 and 1 both reference deep dep 2 (which references 3). Packed
    // into one shard, the union must charge {0,1,2,3} once — NOT
    // closure(0)+closure(1).
    let mut b = ProfileBuilder::new();
    for i in 1..=4u8 {
      b.block(addr(i), bc(10, 0, 0), 1000, 1);
    }
    let p = with_refs(b.finish(), &[vec![2], vec![2], vec![3], vec![]]);
    let plan = partition_for_aiur_ram(&p, 1000.0, 0.05);
    assert_eq!(plan.num_shards, 1);
    assert_eq!(plan.shard_costs[0].union_bytes, 4000);
    assert_eq!(plan.shard_costs[0].hb, 40);
  }

  #[test]
  fn aiur_ingress_follows_type_refs_not_value_refs() {
    // refs:      0→1→2→{3,4}
    // type-refs: 0→1→2→{3}      (4 is reachable only through 2's VALUE)
    //
    // Floors are the max over every block, so pick a shape where block 0's
    // reach is the discriminator. Frontier-stop halts one hop out, and its
    // heaviest block is 2 ({2,3,4} = 3000). FrontierAxiom keeps 1 and 2 as
    // axioms and follows their TYPE refs, so block 0 reaches {0,1,2,3} =
    // 4000 — and must NOT reach 4, which would make it 5000.
    let mut b = ProfileBuilder::new();
    for i in 1..=5u8 {
      b.block(addr(i), bc(10, 0, 0), 1000, 1);
    }
    let mut p =
      with_refs(b.finish(), &[vec![1], vec![2], vec![3, 4], vec![], vec![]]);
    p.set_type_ref_graph(&[vec![1], vec![2], vec![3], vec![], vec![]]);
    let ax = partition_for_aiur_ram(&p, 1000.0, 0.05);
    assert!((ax.largest_block_ram_gib - aiur_ram_gib(4000, 10)).abs() < 1e-9);
  }

  #[test]
  fn aiur_ingress_expands_non_axiomatizable_in_full() {
    // Same shape as above, but block 2 holds a recursor: it cannot stand in
    // as a type-only axiom, so its FULL refs are followed and block 0 now
    // reaches 4 as well — {0,1,2,3,4} = 5000 instead of 4000.
    let mut b = ProfileBuilder::new();
    for i in 1..=5u8 {
      b.block(addr(i), bc(10, 0, 0), 1000, 1);
    }
    let mut p =
      with_refs(b.finish(), &[vec![1], vec![2], vec![3, 4], vec![], vec![]]);
    p.set_type_ref_graph(&[vec![1], vec![2], vec![3], vec![], vec![]]);
    let mut flags = vec![0u32; 5];
    flags[2] = BlockEntry::NOT_AXIOMATIZABLE;
    p.set_block_flags(&flags);
    let ax = partition_for_aiur_ram(&p, 1000.0, 0.05);
    assert!((ax.largest_block_ram_gib - aiur_ram_gib(5000, 10)).abs() < 1e-9);
  }

  #[test]
  fn aiur_ingress_seeds_touched_blocks_full() {
    // refs: 0→1, 1→{2,3}; type-refs: 0→1, 1→2. Predicted (no touch graph):
    // block 0 ingresses 1 as a type-only stub, whose TYPE refs reach only 2
    // — {0,1,2} = 3000. Measured: block 0's check CONSULTED 1, so 1 is
    // ingressed FULL and its full refs drag in 3 too — {0,1,2,3} = 4000.
    let build = |touch: bool| {
      let mut b = ProfileBuilder::new();
      for i in 1..=4u8 {
        b.block(addr(i), bc(10, 0, 0), 1000, 1);
      }
      if touch {
        b.touch_edge(addr(1), addr(2));
      }
      let mut p = with_refs(b.finish(), &[vec![1], vec![2, 3], vec![], vec![]]);
      p.set_type_ref_graph(&[vec![1], vec![2], vec![], vec![]]);
      p
    };
    let predicted = partition_for_aiur_ram(&build(false), 1000.0, 0.05);
    assert!(
      (predicted.largest_block_ram_gib - aiur_ram_gib(3000, 10)).abs() < 1e-9
    );
    let measured = partition_for_aiur_ram(&build(true), 1000.0, 0.05);
    assert!(
      (measured.largest_block_ram_gib - aiur_ram_gib(4000, 10)).abs() < 1e-9
    );
  }

  #[test]
  fn aiur_ingress_sets_split_stubs_from_full() {
    // 0 owns nothing but itself; refs 0→1→2 and 1 also type-refs 3.
    // Shard {0}: 1 is reached from a FULL block, is axiomatizable, so it is
    // a stub; the walk then follows only 1's TYPE refs, reaching 3 as a stub
    // and never 2.
    let mut b = ProfileBuilder::new();
    for i in 1..=4u8 {
      b.block(addr(i), bc(10, 0, 0), 1000, 1);
    }
    let mut p = with_refs(b.finish(), &[vec![1], vec![2, 3], vec![], vec![]]);
    p.set_type_ref_graph(&[vec![1], vec![3], vec![], vec![]]);
    // Each block its own shard so shard 0 owns only block 0.
    let shard_of = vec![0u32, 1, 2, 3];
    let sets = aiur_shard_ingress_sets(
      &p,
      &shard_of,
      4,
      &vec![ShardPromotion::default(); 4],
    );
    let (full_extra, stubbed) = &sets[0];
    assert!(full_extra.is_empty(), "unexpected full ingest: {full_extra:?}");
    assert_eq!(stubbed, &vec![1, 3]);
  }

  #[test]
  fn aiur_ingress_sets_expand_owned_reached_as_a_ref_first() {
    // Shard 0 owns {0,1,2}; block 2 refs block 0, and block 0 refs block 3.
    //
    // The work stack is LIFO, so block 0 is reached as a REF (a stub
    // candidate) while its own owned FULL entry is still further down. If the
    // stub visit is allowed to mark block 0 as done, its FULL expansion is
    // skipped and block 3 never enters the ingress set — the shard then asks
    // the kernel for a constant the manifest never listed.
    let mut b = ProfileBuilder::new();
    for i in 1..=4u8 {
      b.block(addr(i), bc(10, 0, 0), 1000, 1);
    }
    let mut p = with_refs(b.finish(), &[vec![3], vec![], vec![0], vec![]]);
    p.set_type_ref_graph(&[vec![], vec![], vec![], vec![]]);
    let shard_of = vec![0u32, 0, 0, 1];
    let sets = aiur_shard_ingress_sets(
      &p,
      &shard_of,
      2,
      &vec![ShardPromotion::default(); 2],
    );
    let (full_extra, stubbed) = &sets[0];
    assert!(full_extra.is_empty(), "unexpected full ingest: {full_extra:?}");
    assert_eq!(
      stubbed,
      &vec![3],
      "owned block 0 must still expand its refs after being seen as a ref"
    );
  }

  #[test]
  fn aiur_ingress_sets_measured_touch_full_no_producer_cascade() {
    // refs 0→1→2; block 0's check CONSULTED 1 (touch edge), and 1's own
    // check unfolds 2 (delta edge). Measured semantics: 1 ships whole
    // because it was consulted, but 1's delta edge is NOT cascaded — what
    // block 0's check did to 2 would be in 0's own touched set, and it is
    // not, so 2 is reachable only as 1's ref: a stub. The predicted
    // fallback stubs 1 outright (0 never unfolds it) and reaches 2 not at
    // all — the exact under-ingress that fails at k_check.
    let build = |touch: bool| {
      let mut b = ProfileBuilder::new();
      for i in 1..=3u8 {
        b.block(addr(i), bc(10, 0, 0), 1000, 1);
      }
      b.delta_edge(addr(2), addr(3));
      if touch {
        b.touch_edge(addr(1), addr(2));
      }
      let mut p = with_refs(b.finish(), &[vec![1], vec![2], vec![]]);
      p.set_type_ref_graph(&[vec![1], vec![], vec![]]);
      p
    };
    let shard_of = vec![0u32, 1, 2];
    let (full_extra, stubbed) = aiur_shard_ingress_sets(
      &build(true),
      &shard_of,
      3,
      &vec![ShardPromotion::default(); 3],
    )[0]
      .clone();
    assert_eq!(full_extra, vec![1], "consulted block must ship whole");
    assert_eq!(stubbed, vec![2], "unconsulted ref stays a stub");
    let (full_extra, stubbed) = aiur_shard_ingress_sets(
      &build(false),
      &shard_of,
      3,
      &vec![ShardPromotion::default(); 3],
    )[0]
      .clone();
    assert!(full_extra.is_empty(), "prediction never promotes 1");
    assert_eq!(stubbed, vec![1], "prediction stops at the stub frontier");
    // One promotion round: the stub becomes FULL and re-expands.
    let (full_extra, stubbed) = aiur_shard_ingress_sets(
      &build(true),
      &shard_of,
      3,
      &vec![ShardPromotion { rounds: 1, extra_full: vec![] }; 3],
    )[0]
      .clone();
    assert_eq!(full_extra, vec![1, 2], "promotion lifts the stub to full");
    assert!(stubbed.is_empty(), "2 has no refs, so no new frontier");
    // Targeted promotion of exactly block 2 (a wanted-stub report): 2
    // ships whole without touching the rest of the frontier.
    let mut promos = vec![ShardPromotion::default(); 3];
    promos[0].extra_full.push(2);
    let (full_extra, stubbed) =
      aiur_shard_ingress_sets(&build(true), &shard_of, 3, &promos)[0].clone();
    assert_eq!(full_extra, vec![1, 2], "named block ships whole");
    assert!(stubbed.is_empty());
  }

  #[test]
  fn promote_spec_parses_rounds_and_addresses() {
    let mut b = ProfileBuilder::new();
    for i in 1..=3u8 {
      b.block(addr(i), bc(10, 0, 0), 1000, 1);
    }
    let p = b.finish();
    let hex1 = addr(2).hex();
    let spec = format!("0:2,1:+{hex1},1:1");
    let promos = parse_promote_spec(&spec, &p, 3).unwrap();
    assert_eq!(promos[0], ShardPromotion { rounds: 2, extra_full: vec![] });
    assert_eq!(promos[1], ShardPromotion { rounds: 1, extra_full: vec![1] });
    assert_eq!(promos[2], ShardPromotion::default());
    // Bare N applies everywhere; empty spec is all-defaults.
    assert!(
      parse_promote_spec("3", &p, 2).unwrap().iter().all(|q| q.rounds == 3)
    );
    assert!(
      parse_promote_spec("", &p, 2)
        .unwrap()
        .iter()
        .all(|q| *q == ShardPromotion::default())
    );
    // Errors: bad shard, unknown address.
    assert!(parse_promote_spec("9:1", &p, 3).is_err());
    assert!(parse_promote_spec("0:+deadbeef", &p, 3).is_err());
  }

  #[test]
  fn aiur_ingress_sets_keep_reduced_through_blocks_full() {
    // Shard 0 owns block 0, which UNFOLDS block 1: block 1 must be ingressed
    // whole (not stubbed) even though shard 1 checks it, and 1's own refs
    // then follow in full.
    let mut b = ProfileBuilder::new();
    for i in 1..=3u8 {
      b.block(addr(i), bc(10, 0, 0), 1000, 1);
    }
    b.delta_edge(addr(1), addr(2));
    let mut p = with_refs(b.finish(), &[vec![1], vec![2], vec![]]);
    p.set_type_ref_graph(&[vec![1], vec![], vec![]]);
    let shard_of = vec![0u32, 1, 2];
    let sets = aiur_shard_ingress_sets(
      &p,
      &shard_of,
      3,
      &vec![ShardPromotion::default(); 3],
    );
    let (full_extra, stubbed) = &sets[0];
    assert_eq!(full_extra, &vec![1], "delta target must be ingressed whole");
    assert_eq!(stubbed, &vec![2], "1's ref is reachable only as a stub");
  }

  #[test]
  fn aiur_ingress_charges_the_reduction_closure() {
    // refs chain 0→1→2→3; block 0 additionally UNFOLDS 1, and 1 unfolds 2.
    // Everything a block reduces through is ingressed FULL, so block 0 pays
    // for {0,1,2} plus one hop off each of them, which drags in 3.
    let mut b = ProfileBuilder::new();
    for i in 1..=4u8 {
      b.block(addr(i), bc(10, 0, 0), 1000, 1);
    }
    b.delta_edge(addr(1), addr(2));
    b.delta_edge(addr(2), addr(3));
    let mut p = with_refs(b.finish(), &[vec![1], vec![2], vec![3], vec![]]);
    p.set_type_ref_graph(&[vec![1], vec![2], vec![3], vec![]]);
    let plan = partition_for_aiur_ram(&p, 1000.0, 0.05);
    assert!((plan.largest_block_ram_gib - aiur_ram_gib(4000, 10)).abs() < 1e-9);
  }

  #[test]
  fn aiur_ingress_expands_refs_when_member_becomes_owned() {
    // Block 0 refs 1; block 1 refs 2. Packing 0 first pulls 1 in as a
    // frontier member; when 1 is then packed as OWNED, its ref 2 must join
    // the union. A membership test on 1 alone would price that at zero and
    // silently under-charge the shard.
    let mut b = ProfileBuilder::new();
    for i in 1..=3u8 {
      b.block(addr(i), bc(10, 0, 0), 1000, 1);
    }
    let p = with_refs(b.finish(), &[vec![1], vec![2], vec![]]);
    let plan = partition_for_aiur_ram(&p, 1000.0, 0.05);
    assert_eq!(plan.num_shards, 1);
    assert_eq!(plan.shard_costs[0].union_bytes, 3000);
  }

  #[test]
  fn aiur_floor_is_closure_bytes() {
    // A cheap block referencing a huge dependency: its lone-shard RAM floor
    // must include the dependency's bytes even though its own are tiny.
    let mut b = ProfileBuilder::new();
    b.block(addr(1), bc(10, 0, 0), 100, 1);
    b.block(addr(2), bc(10, 0, 0), 3_000_000, 1);
    let p = with_refs(b.finish(), &[vec![1], vec![]]);
    let plan = partition_for_aiur_ram(&p, 1000.0, 0.05);
    let floor = aiur_ram_gib(3_000_100, 10);
    assert!(
      (plan.largest_block_ram_gib - floor).abs() < 1e-9,
      "floor {} != closure-based {}",
      plan.largest_block_ram_gib,
      floor,
    );
  }

  #[test]
  fn aiur_flags_infeasible_atomic_block() {
    // One block so hot its lone predicted RAM exceeds the cap: emitted alone,
    // flagged infeasible.
    let mut b = ProfileBuilder::new();
    b.block(addr(1), bc(u64::MAX / 2, 1000, 0), 1000, 1);
    b.block(addr(2), bc(10, 0, 0), 1000, 1);
    let p = with_refs(b.finish(), &[vec![], vec![]]);
    let plan = partition_for_aiur_ram(&p, 8.0, 0.05);
    assert!(plan.infeasible_atomic_floor, "oversized atomic block must flag");
  }

  #[test]
  fn ref_graph_roundtrips_through_ixprof() {
    let mut b = ProfileBuilder::new();
    for i in 1..=3u8 {
      b.block(addr(i), bc(1, 2, 3), 10, 1);
    }
    let p = with_refs(b.finish(), &[vec![1, 2], vec![2], vec![]]);
    let q = BlockProfile::from_bytes(&p.to_bytes()).unwrap();
    assert!(q.has_ref_graph());
    assert_eq!(q.refs(0), &[1, 2]);
    assert_eq!(q.refs(1), &[2]);
    assert_eq!(q.refs(2), &[] as &[u32]);
    assert_eq!(p, q);
  }

  #[test]
  fn shard_esp_file_roundtrip() {
    // Exercise the CLI's shard path: write a .ixprof, run shard_esp, read back
    // the .ixes manifest.
    let p = two_clusters();
    let dir = std::env::temp_dir();
    let pid = std::process::id();
    let prof = dir.join(format!("ix_shard_rt_{pid}.ixprof"));
    let shard = dir.join(format!("ix_shard_rt_{pid}.ixes"));
    std::fs::write(&prof, p.to_bytes()).unwrap();

    let report = shard_esp(
      prof.to_str().unwrap(),
      2,
      0.10,
      1,
      Some(shard.to_str().unwrap()),
    )
    .unwrap();
    assert!(report.contains("shards=2"), "report was: {report}");

    let m = ShardManifest::from_bytes(&std::fs::read(&shard).unwrap()).unwrap();
    assert_eq!(m.shards.len(), 2);
    assert_eq!(m.total_cross_ingress, 1000);

    let _ = std::fs::remove_file(&prof);
    let _ = std::fs::remove_file(&shard);
  }

  #[test]
  fn contract_sums_weights_and_drops_internal_nets() {
    // 4 vertices, 3 nets. Merge {0,1}->super0 and {2,3}->super1.
    let global = vec![0u32, 1, 2, 3];
    let vw = vec![10u64, 20, 30, 40];
    let nets = vec![
      (100u64, vec![0u32, 1]), // becomes internal to super0 -> dropped
      (200u64, vec![0u32, 2]), // crosses -> kept
      (300u64, vec![2u32, 3]), // becomes internal to super1 -> dropped
    ];
    let sub = SubHyper::assemble(global, vw, nets, 1_000_000);
    let super_id = vec![0u32, 0, 1, 1];
    let cl = contract(sub.level(), &super_id, 2);

    assert_eq!(cl.vw, vec![30, 70], "supervertex weights are member sums");
    assert_eq!(cl.bw, vec![30, 70]);
    assert_eq!(cl.match_map, super_id);
    // Only the crossing net survives, with its weight preserved.
    assert_eq!(cl.nets.len(), 1);
    assert_eq!(cl.nets[0].0, 200);
    assert_eq!(cl.nets[0].1, vec![0u32, 1]);
    // vnets rebuilt to reference the surviving net.
    assert_eq!(cl.vnets, vec![vec![0u32], vec![0u32]]);
  }

  #[test]
  fn match_respects_cluster_weight_cap() {
    // 0 and 1 share a heavy net; 2 is isolated. bw is each 10.
    let sub = SubHyper::assemble(
      vec![0u32, 1, 2],
      vec![10u64, 10, 10],
      vec![(100u64, vec![0u32, 1])],
      1_000_000,
    );
    // Generous cap: 0 and 1 merge, 2 stays singleton -> 2 supervertices.
    let (sid, k) = match_vertices(sub.level(), 100);
    assert_eq!(sid[0], sid[1]);
    assert_ne!(sid[0], sid[2]);
    assert_eq!(k, 2);
    // Cap below the combined weight (10+10=20): no merge -> 3 supervertices.
    let (sid2, k2) = match_vertices(sub.level(), 19);
    assert_ne!(sid2[0], sid2[1]);
    assert_eq!(k2, 3);
  }

  /// Two tight clusters of `m` blocks each (intra-cluster delta cycles) joined by
  /// a single thin cross edge — large enough (`2m > COARSEST_TARGET`) to drive
  /// the full coarsen → uncoarsen path.
  fn two_big_clusters(m: u32) -> BlockProfile {
    let mut b = ProfileBuilder::new();
    for i in 0..2 * m {
      b.block(addr_u32(i + 1), bc(100, 0, 0), 1000, 1);
    }
    for i in 0..m {
      // cluster A cycle over addrs 1..=m
      b.delta_edge(addr_u32(1 + i), addr_u32(1 + (i + 1) % m));
      // cluster B cycle over addrs m+1..=2m
      b.delta_edge(addr_u32(1 + m + i), addr_u32(1 + m + (i + 1) % m));
    }
    // single thin cross edge: A_0 unfolds B_0
    b.delta_edge(addr_u32(1), addr_u32(1 + m));
    b.finish()
  }

  #[test]
  fn multilevel_separates_large_clusters() {
    // 1024 blocks: past the cap "dead-zone" (n < 2·COARSEST_TARGET), so heavy-
    // edge matching contracts the graph across multiple levels.
    let m = 512u32;
    let p = two_big_clusters(m);
    let h = Hypergraph::from_profile(&p);
    let shard_of = h.partition(2, 0.10);

    // Optimal cut is exactly the single cross net (size 1000). Any split that
    // also breaks a cluster cycle would cut an intra net (also 1000), so this
    // equality certifies clean cluster separation.
    assert_eq!(h.connectivity_objective(&shard_of), 1000);

    // Cluster coherence, mapping addresses to (sorted) block ids.
    let id_of: std::collections::HashMap<Address, u32> = (0..p.num_blocks()
      as u32)
      .map(|i| (p.block(i).addr.clone(), i))
      .collect();
    let sid = |n: u32| shard_of[id_of[&addr_u32(n)] as usize];
    let shard_a = sid(1);
    let shard_b = sid(1 + m);
    assert_ne!(shard_a, shard_b);
    for i in 0..m {
      assert_eq!(sid(1 + i), shard_a, "cluster A must be coherent");
      assert_eq!(sid(1 + m + i), shard_b, "cluster B must be coherent");
    }
  }

  #[test]
  fn multilevel_partition_is_deterministic() {
    // 360 blocks > COARSEST_TARGET, partitioned into 4 (exercises recursion +
    // coarsening). The partition must be byte-for-byte reproducible.
    let p = two_big_clusters(180);
    let h = Hypergraph::from_profile(&p);
    let a = h.partition(4, 0.10);
    let b = h.partition(4, 0.10);
    assert_eq!(a, b);
  }

  #[test]
  fn multilevel_no_empty_shards_with_dominant_block() {
    // One block far heavier than all others, among enough light blocks to drive
    // coarsening. During recursion a sub can be dominated by the giant; a
    // restart seeded at a light block then sweeps the whole sub onto one side
    // (cut 0). The initial-partition selection must reject such degenerate
    // candidates, or a shard ends up empty. (Regression guard.)
    let mut b = ProfileBuilder::new();
    let m = 800u32;
    b.block(addr_u32(1), bc(5_000_000, 0, 0), 100, 1); // the giant
    for i in 2..=m {
      b.block(addr_u32(i), bc(1000, 0, 0), 100, 1);
    }
    for i in 1..m {
      b.delta_edge(addr_u32(i), addr_u32(i + 1)); // a chain (incl. the giant)
    }
    let p = b.finish();
    let h = Hypergraph::from_profile(&p);
    for n in [16usize, 64, 200] {
      let shard_of = h.partition(n, 0.05);
      let mani = ShardManifest::build(&p, &shard_of, n);
      assert_eq!(
        mani.shards.iter().filter(|s| s.blocks.is_empty()).count(),
        0,
        "n={n}: every shard must be non-empty despite the dominant block"
      );
    }
  }

  // ---- Bisection / aggregation tree ----

  fn leaf(id: u32) -> AggNode {
    AggNode::Leaf(id)
  }
  fn node(l: AggNode, r: AggNode) -> AggNode {
    AggNode::Internal(Box::new(l), Box::new(r))
  }

  #[test]
  fn partition_with_tree_leaves_match_shards() {
    // 360 blocks → 4 shards. The tree's leaves must be exactly shard ids 0..4.
    let p = two_big_clusters(180);
    let h = Hypergraph::from_profile(&p);
    let (shard_of, tree) = h.partition_with_tree(4, 0.10);
    assert_eq!(tree.num_leaves(), 4);
    let mut ids = Vec::new();
    fn collect(n: &AggNode, out: &mut Vec<u32>) {
      match n {
        AggNode::Leaf(id) => out.push(*id),
        AggNode::Internal(l, r) => {
          collect(l, out);
          collect(r, out);
        },
      }
    }
    collect(&tree, &mut ids);
    ids.sort_unstable();
    assert_eq!(ids, vec![0, 1, 2, 3]);
    // Every shard id assigned to some block must appear as a leaf.
    let used: std::collections::BTreeSet<u32> =
      shard_of.iter().copied().collect();
    assert!(used.iter().all(|s| ids.contains(s)));
  }

  #[test]
  fn agg_plan_arity_and_coverage() {
    // Balanced 8-leaf tree: ((0 1)(2 3)) ((4 5)(6 7)).
    let t = node(
      node(node(leaf(0), leaf(1)), node(leaf(2), leaf(3))),
      node(node(leaf(4), leaf(5)), node(leaf(6), leaf(7))),
    );
    for arity in [2usize, 3, 4, 8] {
      let plan = agg_plan(&t, arity);
      // Every Agg has 2..=arity children; the last op is the root Agg.
      let mut seen_leaves: Vec<u32> = Vec::new();
      for op in &plan {
        match op {
          FoldOp::Leaf(id) => seen_leaves.push(*id),
          FoldOp::Agg(ch) => {
            assert!(
              ch.len() >= 2 && ch.len() <= arity,
              "arity {arity}: {ch:?}"
            );
            // children reference earlier entries (post order)
            assert!(ch.iter().all(|&i| i < plan.len()));
          },
        }
      }
      assert!(matches!(plan.last(), Some(FoldOp::Agg(_))));
      seen_leaves.sort_unstable();
      assert_eq!(seen_leaves, (0..8).collect::<Vec<_>>(), "arity {arity}");
    }
  }

  #[test]
  fn agg_plan_children_in_shard_order() {
    // Children of each agg must be emitted in increasing min-leaf order so the
    // subject merkle-fold stays left-associative.
    let t = node(node(leaf(0), leaf(1)), node(leaf(2), leaf(3)));
    let plan = agg_plan(&t, 2);
    // Root folds two subtrees; the left subtree's leaves precede the right's.
    if let Some(FoldOp::Agg(ch)) = plan.last() {
      // Map each child slot to its min leaf and assert ascending.
      let mins: Vec<u32> = ch
        .iter()
        .map(|&i| match &plan[i] {
          FoldOp::Leaf(id) => *id,
          FoldOp::Agg(g) => g
            .iter()
            .map(
              |&j| if let FoldOp::Leaf(x) = &plan[j] { *x } else { u32::MAX },
            )
            .min()
            .unwrap_or(u32::MAX),
        })
        .collect();
      let mut sorted = mins.clone();
      sorted.sort_unstable();
      assert_eq!(mins, sorted);
    } else {
      panic!("root must be an Agg");
    }
  }

  #[test]
  fn prune_collapses_and_preserves() {
    // ((0 1)(2 3)): pruning leaf 1 collapses its parent to leaf 0; pruning a
    // whole side collapses the root; keep-all is identity; keep-none is None.
    let t = node(node(leaf(0), leaf(1)), node(leaf(2), leaf(3)));
    assert_eq!(t.prune(&|_| true), Some(t.clone()));
    assert_eq!(t.prune(&|_| false), None);
    assert_eq!(
      t.prune(&|id| id != 1),
      Some(node(leaf(0), node(leaf(2), leaf(3))))
    );
    assert_eq!(t.prune(&|id| id >= 2), Some(node(leaf(2), leaf(3))));
    assert_eq!(t.prune(&|id| id == 3), Some(leaf(3)));
  }

  #[test]
  fn manifest_tree_roundtrip() {
    let p = two_clusters();
    let h = Hypergraph::from_profile(&p);
    let (shard_of, tree) = h.partition_with_tree(2, 0.10);
    let m = ShardManifest::build(&p, &shard_of, 2).with_tree(tree.clone());
    let bytes = m.to_bytes();
    let q = ShardManifest::from_bytes(&bytes).unwrap();
    assert_eq!(q.tree, Some(tree));
    // A pre-tree manifest (tree = None) still roundtrips.
    let m0 = ShardManifest::build(&p, &shard_of, 2);
    let q0 = ShardManifest::from_bytes(&m0.to_bytes()).unwrap();
    assert_eq!(q0.tree, None);
  }
}
