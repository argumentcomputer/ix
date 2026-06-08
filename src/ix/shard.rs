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
//! the future proof-aggregation tree.
//! Each bisection uses greedy graph-growing for a locality-aware initial cut
//! followed by Fiduccia–Mattheyses (FM) refinement. On recursion we apply
//! **cut-net splitting**: a net already cut at an upper level is restricted to
//! its pins within each half so it is not recounted deeper.
//!
//! Multilevel coarsening (a further quality boost) is intentionally left as a
//! follow-up; the recursive bisection + FM here is fully self-contained (no
//! external partitioner dependency) and ample for the ~100k-block environments
//! this targets.

use rustc_hash::FxHashSet;
use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::sync::atomic::{AtomicU32, AtomicUsize, Ordering};
use std::time::Instant;

use crate::ix::address::Address;
use crate::ix::profile::BlockProfile;

/// Recurse the two halves of a bisection in parallel (rayon) when the parent
/// sub-problem is at least this large; below it the join overhead isn't worth
/// it. The two halves own disjoint block sets, so their writes to the shared
/// (atomic) assignment buffer never alias.
const PARALLEL_THRESHOLD: usize = 4_000;

/// Sub-problems larger than this skip Fiduccia–Mattheyses refinement entirely
/// and rely on the greedy graph-growing cut alone. FM is ~O(V·d²) per pass, so
/// on dense graphs (mathlib ≈ 20 edges/block) running it at the top of the
/// recursion is the dominant cost; the few biggest cuts are coarse anyway.
const FM_SKIP_VERTICES: usize = 50_000;

/// Vertex count below which FM runs to (capped) convergence; between this and
/// [`FM_SKIP_VERTICES`] it runs a few passes only.
const FM_FULL_VERTICES: usize = 10_000;

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
      net_weight.push(profile.block(p as u32).serialized_size as u64);
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
        total += self.net_weight[i] as u128 * (lambda - 1);
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
    let total_hb: u128 = self.vweight.iter().map(|&w| w as u128).sum();
    let cap =
      (total_hb / num_shards as u128).max(1).min(u64::MAX as u128) as u64;
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
    let total: u128 = bw.iter().map(|&w| w as u128).sum();
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
    // Degenerate split (shouldn't happen for |sub| ≥ 2): keep together.
    for &g in &sub.global {
      shard_of[g as usize].store(base, Ordering::Relaxed);
    }
    prog.leaf();
    return;
  }
  // Allocate leaves ~proportional to heartbeat mass, clamped to [1, side size].
  // `lo`/`hi` are feasible (lo ≤ hi) because nl + nr ≥ k with nl, nr ≥ 1.
  let wl: u128 = left.vw.iter().map(|&w| w as u128).sum();
  let wr: u128 = right.vw.iter().map(|&w| w as u128).sum();
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
    if self.enabled && n >= FM_SKIP_VERTICES {
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
    if self.enabled && (done % step == 0 || done == self.total) {
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
/// (0/1) per local vertex. Greedy graph-growing initial partition + FM.
fn bisect(sub: &SubHyper, epsilon: f64) -> Vec<u8> {
  let n = sub.num_vertices();
  if n == 0 {
    return Vec::new();
  }
  if n == 1 {
    return vec![0];
  }
  let total_bw: u64 = sub.bw.iter().sum();
  // Balance bounds for side weights.
  let wmax = ((0.5 + epsilon) * total_bw as f64).ceil() as u64;
  let wmin = ((0.5 - epsilon) * total_bw as f64).floor() as u64;

  let mut side = greedy_grow(sub, total_bw);
  fm_refine(sub, &mut side, wmin, wmax);
  side
}

/// Greedy graph-growing: start from the heaviest vertex and repeatedly absorb
/// the boundary vertex most strongly connected (by net weight) to side 0 until
/// side 0 reaches ~half the balance weight. Remaining vertices go to side 1.
fn greedy_grow(sub: &SubHyper, total_bw: u64) -> Vec<u8> {
  let n = sub.num_vertices();
  let mut side = vec![1u8; n];
  // Seed: heaviest vertex (deterministic; ties broken by lowest id).
  let seed = (0..n)
    .max_by(|&a, &b| {
      sub.vw[a].cmp(&sub.vw[b]).then(Reverse(a).cmp(&Reverse(b)))
    })
    .unwrap();

  // connection[v] = total weight of nets that already touch side 0 and include v.
  let mut connection = vec![0u64; n];
  let mut in_side0 = vec![false; n];
  // Whether a net already contributes to side 0. A net bumps its pins exactly
  // once (on first connection), so growth is O(Σ net_size), not O(Σ net_size²)
  // — essential on dense graphs (and it also stops over-counting connection).
  let mut net_touched = vec![false; sub.nets.len()];
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
    *side0_bw += sub.bw[v];
    for &ni in &sub.vnets[v] {
      let nis = ni as usize;
      let (w, pins) = &sub.nets[nis];
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
  fn new(sub: &SubHyper, side: &[u8]) -> (NetState, u128) {
    let mut cnt = vec![[0u32; 2]; sub.nets.len()];
    let mut cut: u128 = 0;
    for (i, (w, pins)) in sub.nets.iter().enumerate() {
      if pins.len() > FM_NET_CAP {
        continue; // hub net: invisible to FM (counts stay zero)
      }
      for &v in pins {
        cnt[i][side[v as usize] as usize] += 1;
      }
      if cnt[i][0] > 0 && cnt[i][1] > 0 {
        cut += *w as u128;
      }
    }
    (NetState { cnt }, cut)
  }
}

/// FM gain of moving local vertex `v` from its side to the other.
/// `+w` for each net where `v`'s side has exactly one pin (the move uncuts it);
/// `−w` for each net fully on `v`'s side with ≥2 pins (the move newly cuts it).
fn fm_gain(sub: &SubHyper, ns: &NetState, side: &[u8], v: usize) -> i128 {
  let a = side[v] as usize;
  let b = 1 - a;
  let mut g: i128 = 0;
  for &ni in &sub.vnets[v] {
    let (w, pins) = &sub.nets[ni as usize];
    if pins.len() > FM_NET_CAP {
      continue; // hub net: ignored by FM
    }
    let ca = ns.cnt[ni as usize][a];
    let cb = ns.cnt[ni as usize][b];
    if cb >= 1 && ca == 1 {
      g += *w as i128;
    } else if cb == 0 && ca >= 2 {
      g -= *w as i128;
    }
  }
  g
}

/// Fiduccia–Mattheyses refinement: repeated passes, each moving every vertex at
/// most once in decreasing-gain order subject to the balance window, tracking
/// the lowest-cut prefix and rolling back to it. Stops when a pass yields no
/// improvement.
fn fm_refine(sub: &SubHyper, side: &mut [u8], wmin: u64, wmax: u64) {
  let n = sub.num_vertices();
  // Greedy-only above the skip threshold (FM is too slow on huge dense subs);
  // a few passes in the middle band; full (capped) convergence when small.
  if n <= 1 || n > FM_SKIP_VERTICES {
    return;
  }
  let budget = if n > FM_FULL_VERTICES { 3 } else { MAX_FM_PASSES };
  let mut pass = 0u32;
  loop {
    let (mut ns, mut cut) = NetState::new(sub, side);
    let mut side0_bw: u64 =
      (0..n).filter(|&v| side[v] == 0).map(|v| sub.bw[v]).sum();

    let mut heap: BinaryHeap<(i128, Reverse<u32>)> = BinaryHeap::new();
    let mut cur_gain = vec![0i128; n];
    for v in 0..n {
      let g = fm_gain(sub, &ns, side, v);
      cur_gain[v] = g;
      heap.push((g, Reverse(v as u32)));
    }

    let mut locked = vec![false; n];
    let mut moves: Vec<usize> = Vec::new();
    let mut best_cut = cut;
    let mut best_prefix = 0usize; // number of moves to keep

    while let Some((g, Reverse(v))) = heap.pop() {
      let v = v as usize;
      if locked[v] || g != cur_gain[v] {
        continue; // stale entry
      }
      // Balance check: moving v shifts bw[v] across the cut.
      let (s0_after, ok) = if side[v] == 0 {
        let s0 = side0_bw - sub.bw[v];
        (s0, s0 >= wmin)
      } else {
        let s0 = side0_bw + sub.bw[v];
        (s0, s0 <= wmax)
      };
      if !ok {
        // Infeasible right now; lock it out of this pass.
        locked[v] = true;
        continue;
      }
      // Apply the move.
      let a = side[v] as usize;
      let b = 1 - a;
      for &ni in &sub.vnets[v] {
        let (w, pins) = &sub.nets[ni as usize];
        if pins.len() > FM_NET_CAP {
          continue; // hub net: not tracked, skip cnt update
        }
        let before = ns.cnt[ni as usize][0] > 0 && ns.cnt[ni as usize][1] > 0;
        ns.cnt[ni as usize][a] -= 1;
        ns.cnt[ni as usize][b] += 1;
        let after = ns.cnt[ni as usize][0] > 0 && ns.cnt[ni as usize][1] > 0;
        if before && !after {
          cut -= *w as u128;
        } else if !before && after {
          cut += *w as u128;
        }
      }
      side[v] = b as u8;
      side0_bw = s0_after;
      locked[v] = true;
      moves.push(v);

      // Recompute gains of neighbors (and v's net co-pins).
      let mut touched: FxHashSet<u32> = FxHashSet::default();
      for &ni in &sub.vnets[v] {
        let pins = &sub.nets[ni as usize].1;
        if pins.len() > FM_NET_CAP {
          continue; // hub net: ignored by FM
        }
        for &u in pins {
          if !locked[u as usize] {
            touched.insert(u);
          }
        }
      }
      for u in touched {
        let ng = fm_gain(sub, &ns, side, u as usize);
        if ng != cur_gain[u as usize] {
          cur_gain[u as usize] = ng;
          heap.push((ng, Reverse(u)));
        }
      }

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
    if best_prefix == 0 || pass >= budget {
      break; // converged, or hit the pass bound
    }
  }
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
        .map(|&b| profile.block(b).serialized_size as u64)
        .sum();
      let mut fb: Vec<u32> = foreign[s].iter().copied().collect();
      fb.sort_unstable();
      let cross_ingress: u64 =
        fb.iter().map(|&p| profile.block(p).serialized_size as u64).sum();
      total_cross += cross_ingress as u128;
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
    let total: u128 = hbs.iter().map(|&h| h as u128).sum();
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
      crate::ix::ixon::merkle::merkle_root_canonical(&shard.foreign_blocks);
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

#[cfg(test)]
mod tests {
  use super::*;
  use crate::ix::profile::ProfileBuilder;

  fn addr(byte: u8) -> Address {
    Address::from_slice(&[byte; 32]).unwrap()
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
}
