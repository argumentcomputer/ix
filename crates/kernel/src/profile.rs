//! Out-of-circuit kernel profile (`.ixprof`) — the cost + delta-graph hints
//! that drive the sharding strategy (see `plans/sharding.md`).
//!
//! A profile is computed by running the Rust kernel **out of circuit** over an
//! environment and recording, per *block*:
//!
//! - `heartbeats`: total recursive fuel consumed checking the block's members
//!   (the balance metric for partitioning),
//! - `serialized_size`: the block's serialized byte length (the ingress-cost
//!   metric — net weight in the partition hypergraph),
//! - `const_count`: number of constants in the block,
//! - the set of *other blocks whose definition bodies the block delta-unfolds*
//!   (the delta edges — the cost graph the partitioner cuts on).
//!
//! A "block" is the ingress unit: a `Muts` mutual block or a standalone
//! constant. Projection constants (`*Prj { block, .. }`) are attributed to
//! their `block` address; everything else is its own block.
//!
//! The delta graph is stored in compressed-sparse-row (CSR) form keyed by
//! stable block ids (assigned by sorting block addresses), and the on-disk
//! `.ixprof` format is an explicit little-endian binary so it does not depend
//! on the optional `serde`/`bincode` feature.

// Block ids and counts are `u32` (envs are far below the limit); the binary
// decoder maps decode failures to a single message. Both are intentional here.
#![allow(clippy::cast_possible_truncation, clippy::map_err_ignore)]

#[cfg(not(target_os = "zkvm"))]
use std::cell::Cell;

use rustc_hash::{FxHashMap, FxHashSet};

use ix_common::address::Address;

// ─────────────────────────────────────────────────────────────────────────────
// Per-constant operation counters (richer cost features than `heartbeats`).
//
// Heartbeats count kernel reduction *steps* but not the SIZE of the term each
// step touches, so they mispredict in-circuit Zisk cycles ~3× for def-eq-dense
// constants. These thread-local counters record the actual work volume —
// substitution-node visits, whnf/def-eq calls — which tracks guest cycles far
// more tightly, and `subst` feeds the planner's per-shard cost model. The
// profiler runs one constant per worker thread, so a thread-local accumulator
// captures one constant's totals with no arg threading through the
// (free-function) hot paths. Always recorded on native targets (every
// `ix profile` run needs them); compiled out entirely on the zkvm guest, which
// never records, so the in-circuit kernel pays nothing.
// ─────────────────────────────────────────────────────────────────────────────

// thread_local! needs threads — only declared off the (single-threaded,
// no-std-ish) zkvm guest target, where every bump/take below compiles to a
// no-op.
#[cfg(not(target_os = "zkvm"))]
thread_local! {
  static SUBST_NODES: Cell<u64> = const { Cell::new(0) };
  static SUBST_UNIQUE: Cell<u64> = const { Cell::new(0) };
  static SUBST_CTX: Cell<u64> = const { Cell::new(0) };
  static SUBST_SEEN: std::cell::RefCell<FxHashSet<u64>> =
    std::cell::RefCell::new(FxHashSet::default());
  static WHNF_CALLS: Cell<u64> = const { Cell::new(0) };
  static DEF_EQ_CALLS: Cell<u64> = const { Cell::new(0) };
  static NAT_ARITH: Cell<u64> = const { Cell::new(0) };
}

/// Count one substitution-node visit (called per node in `instantiate_rev`).
#[inline(always)]
pub fn bump_subst_nodes() {
  #[cfg(not(target_os = "zkvm"))]
  SUBST_NODES.with(|c| c.set(c.get().wrapping_add(1)));
}

/// Set the substitution-context component of the unique-work key: a fold
/// of the substitution arguments' identities, computed once per top-level
/// `instantiate_rev` call (the recursion never re-enters subst, so one
/// slot suffices). Mixed into every node key by [`bump_subst_unique`].
#[inline(always)]
pub fn set_subst_ctx(ctx: u64) {
  #[cfg(not(target_os = "zkvm"))]
  SUBST_CTX.with(|c| c.set(ctx));
  #[cfg(target_os = "zkvm")]
  let _ = ctx;
}

/// Count one substitution-node visit deduplicated by its work identity:
/// (expression `expr_key`, binder `depth`, the current substitution
/// context from [`set_subst_ctx`]). A memoizing executor (Aiur proves
/// each unique query once; repeats are memo-table lookups) pays only for
/// distinct work, so `subst_unique`, not the raw visit count, is the
/// substitution-volume feature for an Aiur cost model. The seen-set
/// spans one constant's check — the same scope as the other counters
/// (cleared by [`take_op_counts`]).
#[inline(always)]
pub fn bump_subst_unique(expr_key: u64, depth: u64) {
  #[cfg(not(target_os = "zkvm"))]
  {
    // splitmix64 finalizer over the mixed triple — collisions only cost
    // model accuracy, never soundness.
    let mut k = expr_key
      ^ SUBST_CTX.with(Cell::get)
      ^ depth.wrapping_mul(0x9E37_79B9_7F4A_7C15);
    k = (k ^ (k >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    k = (k ^ (k >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    k ^= k >> 31;
    SUBST_SEEN.with(|s| {
      if s.borrow_mut().insert(k) {
        SUBST_UNIQUE.with(|c| c.set(c.get().wrapping_add(1)));
      }
    });
  }
  #[cfg(target_os = "zkvm")]
  let _ = (expr_key, depth);
}

/// Count one `whnf` entry.
#[inline(always)]
pub fn bump_whnf() {
  #[cfg(not(target_os = "zkvm"))]
  WHNF_CALLS.with(|c| c.set(c.get().wrapping_add(1)));
}

/// Count one `is_def_eq` entry.
#[inline(always)]
pub fn bump_def_eq() {
  #[cfg(not(target_os = "zkvm"))]
  DEF_EQ_CALLS.with(|c| c.set(c.get().wrapping_add(1)));
}

/// Add `work` units of big-Nat arithmetic limb-work (called per native Nat
/// binop in `compute_nat_bin`, weighted by operand limb sizes). Tracks the
/// cost of the Aiur `klimbs_*`/`u64_*` arithmetic circuits, which scale with
/// limb count and are invisible to the hb/subst/def_eq counters.
#[inline(always)]
pub fn bump_nat_arith(work: u64) {
  #[cfg(not(target_os = "zkvm"))]
  NAT_ARITH.with(|c| c.set(c.get().wrapping_add(work)));
  #[cfg(target_os = "zkvm")]
  let _ = work;
}

/// Richer per-constant cost features, recorded alongside `fuel`/heartbeats.
#[derive(Default, Debug, Clone, Copy)]
pub struct OpCounts {
  pub subst_nodes: u64,
  /// Distinct substitution work items (see [`bump_subst_unique`]) — the
  /// post-memoization substitution volume a memoizing executor pays.
  pub subst_unique: u64,
  pub whnf_calls: u64,
  pub def_eq_calls: u64,
  pub nat_arith: u64,
}

/// Read and reset the thread-local op counters (call at each constant boundary).
pub fn take_op_counts() -> OpCounts {
  #[cfg(not(target_os = "zkvm"))]
  {
    SUBST_SEEN.with(|s| s.borrow_mut().clear());
    OpCounts {
      subst_nodes: SUBST_NODES.with(|c| c.replace(0)),
      subst_unique: SUBST_UNIQUE.with(|c| c.replace(0)),
      whnf_calls: WHNF_CALLS.with(|c| c.replace(0)),
      def_eq_calls: DEF_EQ_CALLS.with(|c| c.replace(0)),
      nat_arith: NAT_ARITH.with(|c| c.replace(0)),
    }
  }
  #[cfg(target_os = "zkvm")]
  OpCounts::default()
}

/// Magic bytes at the head of every `.ixprof` file.
const MAGIC: &[u8; 8] = b"IXPROF\0\0";
/// On-disk format version. Bump on any incompatible layout change.
const VERSION: u32 = 2;

/// Per-block operation counters recorded while checking the block's members —
/// the profiler's persisted feature vector, grouped so builder signatures stay
/// stable as counters grow.
#[derive(Default, Debug, Clone, Copy, PartialEq, Eq)]
pub struct BlockCounters {
  /// Total recursive fuel (heartbeats) consumed.
  pub heartbeats: u64,
  /// Substitution-node visits (`instantiate_rev`) — the dominant
  /// reduction-volume cost driver.
  pub subst: u64,
  /// Distinct substitution work items — the post-memoization substitution
  /// volume (see `bump_subst_unique`); the memoizing-executor counterpart of
  /// `subst`.
  pub subst_unique: u64,
  /// `whnf` entries.
  pub whnf: u64,
  /// Definitional-equality checks.
  pub def_eq: u64,
  /// Big-Nat limb-work units (op-weighted; see `bump_nat_arith`) — the only
  /// recorded signal for the limb-arithmetic circuit family no other counter
  /// tracks.
  pub nat_arith: u64,
}

/// Per-block recorded statistics.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BlockEntry {
  /// Content address of the block (a `Muts` block or a standalone constant).
  pub addr: Address,
  /// Total recursive fuel (heartbeats) consumed checking this block's members.
  pub heartbeats: u64,
  /// Serialized byte length of the block (ingress cost / net weight).
  pub serialized_size: u32,
  /// Number of constants in the block (1 for standalone constants).
  pub const_count: u32,
  /// Substitution-node visits (`instantiate_rev`) checking this block — the
  /// dominant reduction-volume cost driver. Recorded when profiled with op
  /// counters enabled; 0 otherwise.
  pub subst: u64,
  /// Distinct substitution work items checking this block — the
  /// post-memoization substitution volume (see `bump_subst_unique`);
  /// the Aiur-relevant counterpart of `subst`.
  pub subst_unique: u64,
  /// `whnf` entries checking this block.
  pub whnf: u64,
  /// Definitional-equality checks checking this block.
  pub def_eq: u64,
  /// Big-Nat limb-work units checking this block.
  pub nat_arith: u64,
}

/// A recorded kernel profile over an environment.
///
/// Blocks are indexed by stable id `0..num_blocks`. The delta graph is stored
/// in CSR form: `producers(c)` are the block ids whose definition bodies block
/// `c` delta-unfolds (the "consumer → producer" direction). Self-edges are
/// dropped; producer lists are sorted and deduplicated.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BlockProfile {
  blocks: Vec<BlockEntry>,
  /// CSR row offsets into `delta_col`, length `blocks.len() + 1`.
  delta_row: Vec<usize>,
  /// CSR column indices: producer block ids, grouped by consumer.
  delta_col: Vec<u32>,
  /// CSR row offsets into `ref_col`, length `blocks.len() + 1`. The
  /// **reference** graph (every cross-block `Constant.refs` edge, projections
  /// and mutual members folded into home blocks) — a superset of the delta
  /// graph. Reachability over it is a block's full dependency closure, which
  /// is what an Aiur shard ingresses (`shardCheckEnvClaim` builds its env
  /// tree over the owned blocks' whole closure), so the Aiur packer's byte
  /// accounting runs on this graph, not the delta graph.
  ref_row: Vec<usize>,
  /// CSR column indices: referenced block ids, grouped by referrer.
  ref_col: Vec<u32>,
}

impl BlockProfile {
  /// Number of blocks (vertices).
  pub fn num_blocks(&self) -> usize {
    self.blocks.len()
  }

  /// Number of delta edges (consumer → producer pairs).
  pub fn num_edges(&self) -> usize {
    self.delta_col.len()
  }

  /// The block entries, indexed by block id.
  pub fn blocks(&self) -> &[BlockEntry] {
    &self.blocks
  }

  /// The entry for block id `i`.
  pub fn block(&self, i: u32) -> &BlockEntry {
    &self.blocks[i as usize]
  }

  /// Producer block ids unfolded by consumer block `c` (sorted, deduped, no
  /// self-edges).
  pub fn producers(&self, c: u32) -> &[u32] {
    let lo = self.delta_row[c as usize];
    let hi = self.delta_row[c as usize + 1];
    &self.delta_col[lo..hi]
  }

  /// Build the reverse delta adjacency: for each producer block, the sorted set
  /// of consumer blocks that unfold it. This is the natural form for the
  /// partition hypergraph, where `net(p) = {p} ∪ consumers_of(p)`.
  pub fn consumers_csr(&self) -> (Vec<usize>, Vec<u32>) {
    let n = self.num_blocks();
    let mut counts = vec![0usize; n + 1];
    for &p in &self.delta_col {
      counts[p as usize + 1] += 1;
    }
    for i in 0..n {
      counts[i + 1] += counts[i];
    }
    let row = counts.clone();
    let mut col = vec![0u32; self.delta_col.len()];
    let mut cursor = counts;
    for c in 0..n as u32 {
      for &p in self.producers(c) {
        let slot = cursor[p as usize];
        col[slot] = c;
        cursor[p as usize] += 1;
      }
    }
    (row, col)
  }

  /// Total heartbeats across all blocks.
  pub fn total_heartbeats(&self) -> u128 {
    self.blocks.iter().map(|b| u128::from(b.heartbeats)).sum()
  }

  /// Whether the reference graph is present (older recordings may lack it).
  pub fn has_ref_graph(&self) -> bool {
    !self.ref_row.is_empty()
  }

  /// Referenced block ids of block `b` (sorted, deduped, no self-edges).
  /// Empty when no reference graph was recorded.
  pub fn refs(&self, b: u32) -> &[u32] {
    if self.ref_row.is_empty() {
      return &[];
    }
    let lo = self.ref_row[b as usize];
    let hi = self.ref_row[b as usize + 1];
    &self.ref_col[lo..hi]
  }

  /// Attach the block-level reference graph (per-block sorted, deduped,
  /// self-edge-free referenced ids; one row per block).
  pub fn set_ref_graph(&mut self, adj: &[Vec<u32>]) {
    assert_eq!(adj.len(), self.blocks.len());
    self.ref_row = Vec::with_capacity(adj.len() + 1);
    self.ref_row.push(0);
    self.ref_col = Vec::with_capacity(adj.iter().map(Vec::len).sum());
    for row in adj {
      self.ref_col.extend_from_slice(row);
      self.ref_row.push(self.ref_col.len());
    }
  }

  /// Serialize to the `.ixprof` binary format.
  pub fn to_bytes(&self) -> Vec<u8> {
    let n = self.blocks.len();
    let mut out = Vec::with_capacity(
      8 + 4 + 4 + n * 88 + 8 + (n + 1) * 8 + self.delta_col.len() * 4,
    );
    out.extend_from_slice(MAGIC);
    out.extend_from_slice(&VERSION.to_le_bytes());
    out.extend_from_slice(&(n as u32).to_le_bytes());
    for b in &self.blocks {
      out.extend_from_slice(b.addr.as_bytes());
      out.extend_from_slice(&b.heartbeats.to_le_bytes());
      out.extend_from_slice(&b.serialized_size.to_le_bytes());
      out.extend_from_slice(&b.const_count.to_le_bytes());
      out.extend_from_slice(&b.subst.to_le_bytes());
      out.extend_from_slice(&b.subst_unique.to_le_bytes());
      out.extend_from_slice(&b.whnf.to_le_bytes());
      out.extend_from_slice(&b.def_eq.to_le_bytes());
      out.extend_from_slice(&b.nat_arith.to_le_bytes());
    }
    out.extend_from_slice(&(self.delta_col.len() as u64).to_le_bytes());
    // CSR row offsets (n+1 entries) as u64.
    for &off in &self.delta_row {
      out.extend_from_slice(&(off as u64).to_le_bytes());
    }
    for &p in &self.delta_col {
      out.extend_from_slice(&p.to_le_bytes());
    }
    // Trailing reference-graph CSR, same layout as the delta section.
    // Readers treat end-of-input here as "no reference graph".
    if !self.ref_row.is_empty() {
      out.extend_from_slice(&(self.ref_col.len() as u64).to_le_bytes());
      for &off in &self.ref_row {
        out.extend_from_slice(&(off as u64).to_le_bytes());
      }
      for &r in &self.ref_col {
        out.extend_from_slice(&r.to_le_bytes());
      }
    }
    out
  }

  /// Deserialize from the `.ixprof` binary format.
  pub fn from_bytes(bytes: &[u8]) -> Result<Self, ProfileError> {
    let mut r = Reader::new(bytes);
    let magic = r.take(8)?;
    if magic != MAGIC {
      return Err(ProfileError::BadMagic);
    }
    let version = r.u32()?;
    if version != VERSION {
      return Err(ProfileError::BadVersion(version));
    }
    let n = r.u32()? as usize;
    let mut blocks = Vec::with_capacity(n);
    for _ in 0..n {
      let addr = Address::from_slice(r.take(32)?)
        .map_err(|_| ProfileError::Truncated)?;
      let heartbeats = r.u64()?;
      let serialized_size = r.u32()?;
      let const_count = r.u32()?;
      let subst = r.u64()?;
      let subst_unique = r.u64()?;
      let whnf = r.u64()?;
      let def_eq = r.u64()?;
      let nat_arith = r.u64()?;
      blocks.push(BlockEntry {
        addr,
        heartbeats,
        serialized_size,
        const_count,
        subst,
        subst_unique,
        whnf,
        def_eq,
        nat_arith,
      });
    }
    let num_edges = r.u64()? as usize;
    let mut delta_row = Vec::with_capacity(n + 1);
    for _ in 0..n + 1 {
      delta_row.push(r.u64()? as usize);
    }
    let mut delta_col = Vec::with_capacity(num_edges);
    for _ in 0..num_edges {
      delta_col.push(r.u32()?);
    }
    // Structural validation: monotone offsets bounded by edge count, in-range ids.
    if delta_row.len() != n + 1
      || delta_row.first() != Some(&0)
      || delta_row.last() != Some(&num_edges)
    {
      return Err(ProfileError::Corrupt);
    }
    for w in delta_row.windows(2) {
      if w[0] > w[1] {
        return Err(ProfileError::Corrupt);
      }
    }
    for &p in &delta_col {
      if p as usize >= n {
        return Err(ProfileError::Corrupt);
      }
    }
    // Optional trailing reference-graph section (same layout). End-of-input
    // here means the profile predates reference recording.
    let (mut ref_row, mut ref_col) = (Vec::new(), Vec::new());
    if r.remaining() > 0 {
      let num_refs = r.u64()? as usize;
      ref_row = Vec::with_capacity(n + 1);
      for _ in 0..n + 1 {
        ref_row.push(r.u64()? as usize);
      }
      ref_col = Vec::with_capacity(num_refs);
      for _ in 0..num_refs {
        ref_col.push(r.u32()?);
      }
      if ref_row.first() != Some(&0)
        || ref_row.last() != Some(&num_refs)
        || ref_row.windows(2).any(|w| w[0] > w[1])
        || ref_col.iter().any(|&x| x as usize >= n)
      {
        return Err(ProfileError::Corrupt);
      }
    }
    Ok(BlockProfile { blocks, delta_row, delta_col, ref_row, ref_col })
  }
}

/// Errors from decoding a `.ixprof` file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProfileError {
  BadMagic,
  BadVersion(u32),
  Truncated,
  Corrupt,
}

impl std::fmt::Display for ProfileError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      ProfileError::BadMagic => write!(f, "not an .ixprof file (bad magic)"),
      ProfileError::BadVersion(v) => {
        write!(f, "unsupported .ixprof version {v}")
      },
      ProfileError::Truncated => write!(f, "truncated .ixprof file"),
      ProfileError::Corrupt => write!(f, "corrupt .ixprof file"),
    }
  }
}

impl std::error::Error for ProfileError {}

/// Minimal little-endian byte reader with bounds checking.
struct Reader<'a> {
  buf: &'a [u8],
  pos: usize,
}

impl<'a> Reader<'a> {
  fn new(buf: &'a [u8]) -> Self {
    Reader { buf, pos: 0 }
  }
  fn remaining(&self) -> usize {
    self.buf.len() - self.pos
  }
  fn take(&mut self, n: usize) -> Result<&'a [u8], ProfileError> {
    let end = self.pos.checked_add(n).ok_or(ProfileError::Truncated)?;
    if end > self.buf.len() {
      return Err(ProfileError::Truncated);
    }
    let s = &self.buf[self.pos..end];
    self.pos = end;
    Ok(s)
  }
  fn u32(&mut self) -> Result<u32, ProfileError> {
    Ok(u32::from_le_bytes(self.take(4)?.try_into().unwrap()))
  }
  fn u64(&mut self) -> Result<u64, ProfileError> {
    Ok(u64::from_le_bytes(self.take(8)?.try_into().unwrap()))
  }
}

/// Accumulates block-level statistics and delta edges (keyed by address), then
/// freezes into a [`BlockProfile`] with stable, address-sorted block ids.
///
/// Phase A (the kernel recorder) feeds this with one `block(..)` per checked
/// block and one `delta_edge(consumer, producer)` per recorded cross-block
/// unfold. The builder is the merge point for per-worker accumulators: calling
/// `block`/`delta_edge` is commutative and idempotent w.r.t. edge sets, so
/// merge order does not affect the result.
#[derive(Default)]
pub struct ProfileBuilder {
  blocks: FxHashMap<Address, Accum>,
}

#[derive(Default)]
struct Accum {
  counters: BlockCounters,
  serialized_size: u32,
  const_count: u32,
  producers: FxHashSet<Address>,
}

impl ProfileBuilder {
  pub fn new() -> Self {
    Self::default()
  }

  /// Record (or accumulate into) a block's statistics. Counters and
  /// const_count accumulate additively; serialized_size is set (idempotent for
  /// a fixed block).
  pub fn block(
    &mut self,
    addr: Address,
    counters: BlockCounters,
    serialized_size: u32,
    const_count: u32,
  ) {
    let e = self.blocks.entry(addr).or_default();
    let c = &mut e.counters;
    c.heartbeats = c.heartbeats.saturating_add(counters.heartbeats);
    c.subst = c.subst.saturating_add(counters.subst);
    c.subst_unique = c.subst_unique.saturating_add(counters.subst_unique);
    c.whnf = c.whnf.saturating_add(counters.whnf);
    c.def_eq = c.def_eq.saturating_add(counters.def_eq);
    c.nat_arith = c.nat_arith.saturating_add(counters.nat_arith);
    e.serialized_size = serialized_size;
    e.const_count = e.const_count.saturating_add(const_count);
  }

  /// Record that `consumer` delta-unfolds the body of `producer`. Self-edges
  /// are ignored. Ensures both endpoints exist as blocks (with zeroed stats if
  /// not yet seen) so the graph is well-formed even if a producer is only ever
  /// referenced, never directly checked.
  pub fn delta_edge(&mut self, consumer: Address, producer: Address) {
    if consumer == producer {
      return;
    }
    self.blocks.entry(producer.clone()).or_default();
    self.blocks.entry(consumer).or_default().producers.insert(producer);
  }

  /// Freeze into an immutable [`BlockProfile`]. Block ids are assigned by
  /// sorting addresses, so the result is deterministic regardless of insertion
  /// order.
  pub fn finish(self) -> BlockProfile {
    let mut addrs: Vec<Address> = self.blocks.keys().cloned().collect();
    addrs.sort();
    let id_of: FxHashMap<Address, u32> =
      addrs.iter().enumerate().map(|(i, a)| (a.clone(), i as u32)).collect();

    let mut blocks = Vec::with_capacity(addrs.len());
    let mut delta_row = Vec::with_capacity(addrs.len() + 1);
    let mut delta_col = Vec::new();
    delta_row.push(0usize);

    for addr in &addrs {
      let a = &self.blocks[addr];
      blocks.push(BlockEntry {
        addr: addr.clone(),
        heartbeats: a.counters.heartbeats,
        serialized_size: a.serialized_size,
        const_count: a.const_count,
        subst: a.counters.subst,
        subst_unique: a.counters.subst_unique,
        whnf: a.counters.whnf,
        def_eq: a.counters.def_eq,
        nat_arith: a.counters.nat_arith,
      });
      let mut prods: Vec<u32> = a.producers.iter().map(|p| id_of[p]).collect();
      prods.sort_unstable();
      prods.dedup();
      delta_col.extend_from_slice(&prods);
      delta_row.push(delta_col.len());
    }

    BlockProfile {
      blocks,
      delta_row,
      delta_col,
      ref_row: Vec::new(),
      ref_col: Vec::new(),
    }
  }
}

/// Per-worker raw accumulator filled by the out-of-circuit kernel recorder: for
/// each *constant* (by address) checked on this worker, its heartbeats and the
/// set of constant addresses whose definition bodies it delta-unfolded. The
/// env-aware layer later maps these constant addresses to their home blocks and
/// attaches serialized sizes to produce a [`BlockProfile`].
#[derive(Default, Debug)]
pub struct ProfileSink {
  /// When true, the kernel clears its reduction-memo caches between constants
  /// so recording is sound (no unfolds skipped by cross-constant cache hits)
  /// and heartbeats reflect the no-cross-constant-memo in-circuit cost.
  pub isolate: bool,
  /// Consumer constant address → record.
  pub records: FxHashMap<Address, ConstRecord>,
}

/// One constant's recorded statistics (pre block-aggregation).
#[derive(Default, Debug, Clone)]
pub struct ConstRecord {
  /// Recursive fuel (heartbeats) consumed checking this constant.
  pub fuel: u64,
  /// Constant addresses whose bodies were delta-unfolded during the check.
  pub producers: FxHashSet<Address>,
  /// Richer cost features (substitution-node visits, whnf/def-eq calls),
  /// recorded on every native profiling run; compiled out (all zero) on the
  /// zkvm target.
  pub ops: OpCounts,
}

impl ProfileSink {
  pub fn new(isolate: bool) -> Self {
    ProfileSink { isolate, records: FxHashMap::default() }
  }

  /// Accumulate one constant's record (additive in fuel + op counts, set-union
  /// in producers) so repeated flushes for the same constant combine correctly.
  pub fn record(
    &mut self,
    consumer: Address,
    fuel: u64,
    producers: impl IntoIterator<Item = Address>,
    ops: OpCounts,
  ) {
    let rec = self.records.entry(consumer).or_default();
    rec.fuel = rec.fuel.saturating_add(fuel);
    rec.producers.extend(producers);
    rec.ops.subst_nodes = rec.ops.subst_nodes.saturating_add(ops.subst_nodes);
    rec.ops.subst_unique =
      rec.ops.subst_unique.saturating_add(ops.subst_unique);
    rec.ops.whnf_calls = rec.ops.whnf_calls.saturating_add(ops.whnf_calls);
    rec.ops.def_eq_calls =
      rec.ops.def_eq_calls.saturating_add(ops.def_eq_calls);
    rec.ops.nat_arith = rec.ops.nat_arith.saturating_add(ops.nat_arith);
  }

  /// Merge another worker's sink into this one (order-independent).
  pub fn merge(&mut self, other: ProfileSink) {
    for (addr, rec) in other.records {
      let e = self.records.entry(addr).or_default();
      e.fuel = e.fuel.saturating_add(rec.fuel);
      e.producers.extend(rec.producers);
      e.ops.subst_nodes = e.ops.subst_nodes.saturating_add(rec.ops.subst_nodes);
      e.ops.subst_unique =
        e.ops.subst_unique.saturating_add(rec.ops.subst_unique);
      e.ops.whnf_calls = e.ops.whnf_calls.saturating_add(rec.ops.whnf_calls);
      e.ops.def_eq_calls =
        e.ops.def_eq_calls.saturating_add(rec.ops.def_eq_calls);
      e.ops.nat_arith = e.ops.nat_arith.saturating_add(rec.ops.nat_arith);
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  fn addr(byte: u8) -> Address {
    Address::from_slice(&[byte; 32]).unwrap()
  }

  /// Fixture counters: (heartbeats, subst, subst_unique); other counters zero.
  fn bc(heartbeats: u64, subst: u64, subst_unique: u64) -> BlockCounters {
    BlockCounters { heartbeats, subst, subst_unique, ..Default::default() }
  }

  fn sample() -> BlockProfile {
    let mut b = ProfileBuilder::new();
    // Three blocks a<b<c by address ordering.
    b.block(addr(1), bc(100, 50, 50), 10, 1);
    b.block(addr(2), bc(200, 100, 100), 20, 3);
    b.block(addr(3), bc(300, 150, 150), 30, 1);
    // a unfolds b and c; c unfolds b; self-edge ignored.
    b.delta_edge(addr(1), addr(2));
    b.delta_edge(addr(1), addr(3));
    b.delta_edge(addr(3), addr(2));
    b.delta_edge(addr(2), addr(2));
    b.finish()
  }

  #[test]
  fn builder_assigns_sorted_ids_and_stats() {
    let p = sample();
    assert_eq!(p.num_blocks(), 3);
    assert_eq!(p.block(0).addr, addr(1));
    assert_eq!(p.block(0).heartbeats, 100);
    assert_eq!(p.block(1).heartbeats, 200);
    assert_eq!(p.block(1).const_count, 3);
    assert_eq!(p.total_heartbeats(), 600);
  }

  #[test]
  fn producers_sorted_and_self_edge_dropped() {
    let p = sample();
    // block 0 (addr 1) unfolds blocks 1 and 2.
    assert_eq!(p.producers(0), &[1, 2]);
    // block 1 (addr 2): self-edge dropped → no producers.
    assert_eq!(p.producers(1), &[]);
    // block 2 (addr 3) unfolds block 1.
    assert_eq!(p.producers(2), &[1]);
    assert_eq!(p.num_edges(), 3);
  }

  #[test]
  fn consumers_reverse_adjacency() {
    let p = sample();
    let (row, col) = p.consumers_csr();
    // block 1 (addr 2) is unfolded by blocks 0 and 2.
    let lo = row[1];
    let hi = row[2];
    let mut got: Vec<u32> = col[lo..hi].to_vec();
    got.sort_unstable();
    assert_eq!(got, vec![0, 2]);
  }

  #[test]
  fn roundtrip_serialization() {
    let p = sample();
    let bytes = p.to_bytes();
    let q = BlockProfile::from_bytes(&bytes).unwrap();
    assert_eq!(p, q);
  }

  #[test]
  fn rejects_bad_magic_and_truncation() {
    assert_eq!(
      BlockProfile::from_bytes(b"nope").unwrap_err(),
      ProfileError::Truncated
    );
    let mut bytes = sample().to_bytes();
    bytes[0] = b'X';
    assert_eq!(
      BlockProfile::from_bytes(&bytes).unwrap_err(),
      ProfileError::BadMagic
    );
  }

  #[test]
  fn merge_order_independent() {
    // Build the same logical profile with edges added in a different order and
    // via separate builders merged conceptually; result must be identical.
    let mut b = ProfileBuilder::new();
    b.delta_edge(addr(3), addr(2));
    b.block(addr(3), bc(300, 150, 150), 30, 1);
    b.delta_edge(addr(1), addr(3));
    b.block(addr(2), bc(200, 100, 100), 20, 3);
    b.delta_edge(addr(1), addr(2));
    b.block(addr(1), bc(100, 50, 50), 10, 1);
    b.delta_edge(addr(2), addr(2));
    assert_eq!(b.finish(), sample());
  }
}
