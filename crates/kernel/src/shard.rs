//! Sharding: partition an environment's blocks into `N` shards that are
//! balanced by heartbeats and minimize cross-shard delta-unfold ingress
//! (see `plans/sharding.md`).
//!
//! ## Model
//!
//! We solve a **weighted hypergraph partitioning** problem under the
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

use rustc_hash::FxHashSet;
use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::sync::atomic::{AtomicU32, AtomicUsize, Ordering};
use std::time::Instant;

use ix_common::address::Address;
use crate::profile::BlockProfile;

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

/// A weighted hypergraph derived from a [`BlockProfile`]. Vertex ids are block
/// ids (identical to the profile's). Nets are stored with global pins.
pub struct Hypergraph {
  /// Vertex (block) weights = heartbeats.
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
      (0..n as u32).map(|i| profile.block(i).heartbeats).collect();
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
    let n = self.num_vertices();
    if num_shards <= 1 {
      return vec![0u32; n]; // everything in shard 0
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
    rec_bisect(&sub, num_shards, 0, epsilon, &shard_of, &prog);
    prog.done();
    shard_of.into_iter().map(AtomicU32::into_inner).collect()
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
) {
  if k <= 1 || sub.num_vertices() <= 1 {
    // A leaf (or a subtree with ≤1 vertex): everything here is one shard.
    for &g in &sub.global {
      shard_of[g as usize].store(base, Ordering::Relaxed);
    }
    prog.leaf();
    return;
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
    return;
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
  // to serial execution (each subtree is deterministic).
  if nl + nr >= PARALLEL_THRESHOLD {
    rayon::join(
      || rec_bisect(&left, k_left, base, epsilon, shard_of, prog),
      || rec_bisect(&right, k - k_left, rbase, epsilon, shard_of, prog),
    );
  } else {
    rec_bisect(&left, k_left, base, epsilon, shard_of, prog);
    rec_bisect(&right, k - k_left, rbase, epsilon, shard_of, prog);
  }
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
  /// Foreign blocks delta-unfolded by members but proven in other shards.
  pub foreign_blocks: Vec<Address>,
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
        cross_ingress,
        assumption_root: None,
      });
    }
    ShardManifest {
      num_shards: num_shards as u32,
      shards,
      total_cross_ingress: total_cross,
    }
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
      shards.push(ShardInfo {
        id,
        blocks,
        heartbeats,
        own_size,
        foreign_blocks,
        cross_ingress,
        assumption_root,
      });
    }
    Ok(ShardManifest {
      num_shards: num_shards as u32,
      shards,
      total_cross_ingress,
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

/// Read a `.ixesp`, partition into `num_shards` shards, and emit a manifest with
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
  out_path: Option<&str>,
) -> Result<String, String> {
  let bytes =
    std::fs::read(esp_path).map_err(|e| format!("read {esp_path}: {e}"))?;
  let profile = BlockProfile::from_bytes(&bytes)
    .map_err(|e| format!("parse {esp_path}: {e}"))?;
  let h = Hypergraph::from_profile(&profile);
  let shard_of = h.partition(num_shards, balance);
  let mut manifest = ShardManifest::build(&profile, &shard_of, num_shards);
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
    "blocks={} delta_edges={} nets={}\n{}\nlargest_block_hb={}{}",
    profile.num_blocks(),
    profile.num_edges(),
    h.num_nets(),
    manifest.summary(),
    max_block_hb,
    note,
  ))
}

/// A partition sized to a per-shard Zisk **cycle** budget (rather than a fixed
/// shard count). See [`partition_for_cycle_cap`].
pub struct BudgetPlan {
  /// Chosen shard count.
  pub num_shards: usize,
  /// Shard assignment per block id (as [`Hypergraph::partition`] returns).
  pub shard_of: Vec<u32>,
  /// Per-shard heartbeat cap derived from the cycle cap
  /// (`max_cycles / cycles_per_heartbeat`).
  pub heartbeat_cap: u64,
  /// Heaviest shard's heartbeats in the chosen partition.
  pub max_shard_heartbeats: u64,
  /// Largest single (atomic) block's heartbeats — the hard floor on
  /// `max_shard_heartbeats` that no shard count can beat.
  pub largest_block_heartbeats: u64,
  /// True when the largest atomic block alone exceeds the cap: the budget is
  /// infeasible by sharding (split that mutual block upstream, or raise the cap
  /// / use a bigger box).
  pub infeasible_atomic_floor: bool,
}

/// Size a partition to a per-shard **cycle** budget, then partition.
///
/// `max_cycles` is the ceiling on a single shard's in-circuit Zisk guest steps
/// — the leaf prover's trace size, which is what sets peak prover RAM. Convert
/// it from a host-RAM budget with the empirical single-leaf model measured on
/// this prover:
///
/// ```text
///   peak_RAM_GB ≈ 45 + 32 × cycles_billions
///   ⇒ max_cycles ≈ (target_peak_GB − 45) / 32 × 1e9
/// ```
///
/// e.g. a 256 GB box with a ~195 GB safe target (≈ 50 GB headroom for OS +
/// run-to-run variance) → `(195 − 45) / 32 ≈ 4.7` → `max_cycles ≈ 4.5e9`.
///
/// `cycles_per_heartbeat` converts the planner's heartbeat balance metric to
/// guest cycles. Measured across 12 envs: large shardable envs cluster at
/// 194–208k whole-env, and the per-shard ratio runs ~5–8% higher (a shard
/// memoizes less) — mergesort's heaviest shard is ≈ 216k, so ~215k is the
/// conservative default for the regime that needs sharding. It is genuinely
/// workload-dependent though (tiny arithmetic envs ~130–160k; heavy-def-eq envs
/// like array/string-assoc ~258k), so recalibrate per environment with one
/// `--execute`: a shard's reported steps ÷ that shard's heartbeats. The cycle
/// cap's RAM headroom (target well under the wall) absorbs the residual error.
///
/// Picks the smallest `N` whose heaviest shard fits `max_cycles /
/// cycles_per_heartbeat`, growing `N` proportionally to any overshoot and
/// re-partitioning (partitioning is milliseconds-to-seconds, negligible beside
/// proving). Stops at the **atomic-block floor**: a mutual block cannot be
/// split, so once the heaviest shard is pinned to the largest block, more shards
/// only worsen balance — `infeasible_atomic_floor` then flags that the cap is
/// unreachable and the block must be dealt with upstream.
pub fn partition_for_cycle_cap(
  profile: &BlockProfile,
  max_cycles: u64,
  cycles_per_heartbeat: u64,
  epsilon: f64,
) -> BudgetPlan {
  let h = Hypergraph::from_profile(profile);
  let hb_cap = (max_cycles / cycles_per_heartbeat.max(1)).max(1);
  let largest_block =
    profile.blocks().iter().map(|b| b.heartbeats).max().unwrap_or(0);
  let total_hb = profile.total_heartbeats();
  let nblocks = profile.num_blocks().max(1);

  let max_shard_hb_of = |shard_of: &[u32], n: usize| -> u64 {
    let mut sums = vec![0u64; n];
    for (b, &s) in shard_of.iter().enumerate() {
      sums[s as usize] =
        sums[s as usize].saturating_add(profile.block(b as u32).heartbeats);
    }
    sums.into_iter().max().unwrap_or(0)
  };

  // Initial estimate from the average load; refine against the real partition.
  let mut n = ((total_hb / u128::from(hb_cap)).max(1) as usize).min(nblocks);
  let mut shard_of = h.partition(n, epsilon);
  let mut max_shard_hb = max_shard_hb_of(&shard_of, n);

  // Grow N until the heaviest shard fits the cap, or we hit the atomic-block
  // floor / the block count. Proportional growth converges in a few re-cuts.
  let mut guard = 0;
  while max_shard_hb > hb_cap
    && n < nblocks
    && max_shard_hb > largest_block.saturating_mul(11) / 10
    && guard < 24
  {
    // Next estimate: scale N by the overshoot ratio (so a 2× overshoot doubles
    // N), but always advance by ≥1 to guarantee progress. Re-checking the real
    // partition each round converges to the *minimal* N that fits.
    let scaled = ((n as f64) * (max_shard_hb as f64 / hb_cap as f64)).ceil() as usize;
    n = scaled.max(n + 1).min(nblocks);
    shard_of = h.partition(n, epsilon);
    max_shard_hb = max_shard_hb_of(&shard_of, n);
    guard += 1;
  }

  BudgetPlan {
    num_shards: n,
    shard_of,
    heartbeat_cap: hb_cap,
    max_shard_heartbeats: max_shard_hb,
    largest_block_heartbeats: largest_block,
    infeasible_atomic_floor: largest_block > hb_cap,
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::profile::ProfileBuilder;

  fn addr(byte: u8) -> Address {
    Address::from_slice(&[byte; 32]).unwrap()
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
      b.block(addr(i), 100, 1000, 1);
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
        b.block(addr(base + k), 100, 500, 1);
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
    b.block(addr(1), 30_000, 100, 1); // ~30x a light block
    for i in 2..=65u8 {
      b.block(addr(i), 1000, 100, 1);
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

  #[test]
  fn shard_esp_file_roundtrip() {
    // Exercise the CLI's shard path: write a .ixesp, run shard_esp, read back
    // the .ixes manifest.
    let p = two_clusters();
    let dir = std::env::temp_dir();
    let pid = std::process::id();
    let prof = dir.join(format!("ix_shard_rt_{pid}.ixesp"));
    let shard = dir.join(format!("ix_shard_rt_{pid}.ixes"));
    std::fs::write(&prof, p.to_bytes()).unwrap();

    let report =
      shard_esp(prof.to_str().unwrap(), 2, 0.10, Some(shard.to_str().unwrap()))
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
      b.block(addr_u32(i + 1), 100, 1000, 1);
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
    b.block(addr_u32(1), 5_000_000, 100, 1); // the giant
    for i in 2..=m {
      b.block(addr_u32(i), 1000, 100, 1);
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
}
