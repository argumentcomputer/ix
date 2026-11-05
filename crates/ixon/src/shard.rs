//! Static DAG hypergraph sharder and sub-environment extraction.

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

use crate::constant::ConstantInfo as IxonCI;
use crate::env::Env as IxonEnv;
use crate::lazy::ConstVariantTag;
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

// ===========================================================================
// Cost model
// ===========================================================================

/// Calibrated instruction weight per substitution step.
pub const COST_PER_SUBST: u64 = 196_600;
/// Calibrated instruction weight per WHNF step.
pub const COST_PER_WHNF: u64 = 1_797_600;
/// Calibrated instruction weight per definitional-equality step.
pub const COST_PER_DEF_EQ: u64 = 567_100;
/// Calibrated instruction weight per arena-interning step.
pub const COST_PER_INTERN: u64 = 28_400;
/// Fraction of host RAM considered usable when sizing shards.
pub const RAM_USABLE_FRAC: f64 = 0.85;

/// Compute the weighted cycle estimate for a single [`BlockEntry`].
pub fn block_step_cost(b: &BlockEntry) -> u64 {
  COST_PER_SUBST
    .saturating_mul(b.subst)
    .saturating_add(COST_PER_WHNF.saturating_mul(b.whnf))
    .saturating_add(COST_PER_DEF_EQ.saturating_mul(b.def_eq))
    .saturating_add(COST_PER_INTERN.saturating_mul(b.intern))
}

#[derive(Default, Debug, Clone, Copy)]
pub struct OpCounts {
  pub subst_nodes: u64,
  pub whnf_calls: u64,
  pub def_eq_calls: u64,
  pub nat_arith: u64,
  pub intern_nodes: u64,
}

impl OpCounts {
  /// Saturating field-wise accumulation.
  pub fn add(&mut self, o: &OpCounts) {
    self.subst_nodes = self.subst_nodes.saturating_add(o.subst_nodes);
    self.whnf_calls = self.whnf_calls.saturating_add(o.whnf_calls);
    self.def_eq_calls = self.def_eq_calls.saturating_add(o.def_eq_calls);
    self.nat_arith = self.nat_arith.saturating_add(o.nat_arith);
    self.intern_nodes = self.intern_nodes.saturating_add(o.intern_nodes);
  }
}

/// Magic bytes at the head of every `.ixprof` file.
const MAGIC: &[u8; 8] = b"IXPROF\0\0";
/// On-disk format version. Bump on any incompatible layout change.
const VERSION: u32 = 2;

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
  /// `whnf` entries checking this block (counted before cache probes).
  pub whnf: u64,
  /// `is_def_eq` entries checking this block.
  pub def_eq: u64,
  /// Limb-weighted native Nat-arithmetic work checking this block.
  pub nat_arith: u64,
  /// Intern-table node visits checking this block (term-construction volume).
  pub intern: u64,
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

  /// Serialize to the `.ixprof` binary format.
  pub fn to_bytes(&self) -> Vec<u8> {
    let n = self.blocks.len();
    let mut out = Vec::with_capacity(
      8 + 4 + 4 + n * 80 + 8 + (n + 1) * 8 + self.delta_col.len() * 4,
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
      out.extend_from_slice(&b.whnf.to_le_bytes());
      out.extend_from_slice(&b.def_eq.to_le_bytes());
      out.extend_from_slice(&b.nat_arith.to_le_bytes());
      out.extend_from_slice(&b.intern.to_le_bytes());
    }
    out.extend_from_slice(&(self.delta_col.len() as u64).to_le_bytes());
    // CSR row offsets (n+1 entries) as u64.
    for &off in &self.delta_row {
      out.extend_from_slice(&(off as u64).to_le_bytes());
    }
    for &p in &self.delta_col {
      out.extend_from_slice(&p.to_le_bytes());
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
      let whnf = r.u64()?;
      let def_eq = r.u64()?;
      let nat_arith = r.u64()?;
      let intern = r.u64()?;
      blocks.push(BlockEntry {
        addr,
        heartbeats,
        serialized_size,
        const_count,
        subst,
        whnf,
        def_eq,
        nat_arith,
        intern,
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
    Ok(BlockProfile { blocks, delta_row, delta_col })
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
  heartbeats: u64,
  serialized_size: u32,
  const_count: u32,
  ops: OpCounts,
  producers: FxHashSet<Address>,
}

impl ProfileBuilder {
  pub fn new() -> Self {
    Self::default()
  }

  /// Record (or accumulate into) a block's statistics. Heartbeats,
  /// const_count, and the op counters accumulate additively; serialized_size
  /// is set (idempotent for a fixed block).
  pub fn block(
    &mut self,
    addr: Address,
    heartbeats: u64,
    serialized_size: u32,
    const_count: u32,
    ops: OpCounts,
  ) {
    let e = self.blocks.entry(addr).or_default();
    e.heartbeats = e.heartbeats.saturating_add(heartbeats);
    e.serialized_size = serialized_size;
    e.const_count = e.const_count.saturating_add(const_count);
    e.ops.add(&ops);
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
        heartbeats: a.heartbeats,
        serialized_size: a.serialized_size,
        const_count: a.const_count,
        subst: a.ops.subst_nodes,
        whnf: a.ops.whnf_calls,
        def_eq: a.ops.def_eq_calls,
        nat_arith: a.ops.nat_arith,
        intern: a.ops.intern_nodes,
      });
      let mut prods: Vec<u32> = a.producers.iter().map(|p| id_of[p]).collect();
      prods.sort_unstable();
      prods.dedup();
      delta_col.extend_from_slice(&prods);
      delta_row.push(delta_col.len());
    }

    BlockProfile { blocks, delta_row, delta_col }
  }
}

#[derive(Clone, Debug)]
pub enum AnonWorkItem {
  /// A standalone (Defn/Recr/Axio/Quot) constant. `addr` is both the
  /// kernel-checked target and the only address this item covers.
  Standalone { addr: Address },
  /// A Muts block. Checking `primary` (the first member's projection
  /// address) drives the kernel's block coordination, which in turn
  /// typechecks every entry in `targets`. `targets[0] == primary`.
  /// `block_addr` is the block's own `env.consts` key (the `Tag::Muts`
  /// entry) — distinct from the projection `targets`, and the address
  /// other constants' `refs` use to reference the block. Carried so the
  /// set of `consts` keys a checked item certifies ([`proven_targets`])
  /// is in the same address space as `Constant.refs`.
  ///
  /// [`proven_targets`]: AnonWorkItem::proven_targets
  Block { block_addr: Address, primary: Address, targets: Vec<Address> },
}

impl AnonWorkItem {
  /// The address to pass to the Ixon whole-unit checking entry.
  pub fn primary(&self) -> &Address {
    match self {
      AnonWorkItem::Standalone { addr } => addr,
      AnonWorkItem::Block { primary, .. } => primary,
    }
  }

  /// Every kernel-checked target this item covers (one for
  /// `Standalone`, `targets.len()` for `Block`).
  pub fn targets(&self) -> &[Address] {
    match self {
      AnonWorkItem::Standalone { addr } => core::slice::from_ref(addr),
      AnonWorkItem::Block { targets, .. } => targets,
    }
  }

  /// Every `env.consts` key this item certifies (proves) well-typed when
  /// its `primary` is checked — the *proven targets*, in the same address
  /// space as `Constant.refs`, so a dependency ref can be matched against
  /// the union of `proven_targets()` over all checked items: refs in that
  /// union are already certified, the rest are the claim's open assumptions
  /// (resolved later against other proofs). Unlike
  /// [`targets`](Self::targets) (the addresses the kernel actually walks),
  /// a `Block`'s proven set also includes the block's own `consts` key:
  /// for a `Standalone` it's just its address; for a `Block` it's
  /// `block_addr` plus every projection target (members + ctors). The
  /// set includes synthesized semantic members whose projection records the
  /// input may omit. It is not a physical-record coverage set; a host checks
  /// carried records separately and does not add synthetic bytes to its input.
  pub fn proven_targets(&self) -> Vec<Address> {
    match self {
      AnonWorkItem::Standalone { addr } => vec![addr.clone()],
      AnonWorkItem::Block { block_addr, targets, .. } => {
        let mut v = Vec::with_capacity(1 + targets.len());
        v.push(block_addr.clone());
        v.extend(targets.iter().cloned());
        v
      },
    }
  }
}

fn mutual_work(
  address: &Address,
  members: &[crate::constant::MutConst],
) -> Result<AnonWorkItem, String> {
  use crate::constant::MutConst;
  if members.is_empty() {
    return Err("empty mutual block".into());
  }
  let has_defn = members.iter().any(|m| matches!(m, MutConst::Defn(_)));
  let has_indc = members.iter().any(|m| matches!(m, MutConst::Indc(_)));
  let has_recr = members.iter().any(|m| matches!(m, MutConst::Recr(_)));
  if has_defn && (has_indc || has_recr) {
    return Err("mixed mutual block".into());
  }
  let mut targets = Vec::new();
  for (index, member) in members.iter().enumerate() {
    let index = u64::try_from(index).map_err(|error| error.to_string())?;
    targets.push(match member {
      MutConst::Defn(_) => crate::constant::defn_proj_address(index, address),
      MutConst::Indc(_) => crate::constant::indc_proj_address(index, address),
      MutConst::Recr(_) => crate::constant::recr_proj_address(index, address),
    });
    if let MutConst::Indc(inductive) = member {
      for constructor in 0..inductive.ctors.len() {
        targets.push(crate::constant::ctor_proj_address(
          index,
          u64::try_from(constructor).map_err(|error| error.to_string())?,
          address,
        ));
      }
    }
  }
  Ok(AnonWorkItem::Block {
    block_addr: address.clone(),
    primary: targets[0].clone(),
    targets,
  })
}

/// Enumerate the anon-mode kernel work set from `env.consts`.
///
/// Returns one `AnonWorkItem` per kernel-checkable group of
/// constants. The total number of checked target addresses is
/// `work.iter().map(|w| w.targets().len()).sum()`.
///
/// Refuses corrupted entries and unsupported serialized mutual shapes before
/// promising coverage for their member targets.
pub fn build_anon_work(env: &IxonEnv) -> Result<Vec<AnonWorkItem>, String> {
  use crate::constant::ConstantInfo as CI;
  use ConstVariantTag as Tag;

  let mut work: Vec<AnonWorkItem> = Vec::new();

  // Sort keys for deterministic ordering across runs.
  let mut keys: Vec<Address> =
    env.consts.iter().map(|e| e.key().clone()).collect();
  keys.sort_unstable();

  for addr in keys {
    let lc = env.consts.get(&addr).ok_or_else(|| {
      format!("build_anon_work: missing const at {}", addr.hex())
    })?;
    let tag = lc.value().peek_variant().map_err(|e| {
      format!("build_anon_work: peek_variant {}: {e}", addr.hex())
    })?;
    match tag {
      Tag::IPrj | Tag::CPrj | Tag::RPrj | Tag::DPrj => {
        // Skip — covered by parent block.
      },
      Tag::Defn | Tag::Recr | Tag::Axio | Tag::Quot => {
        work.push(AnonWorkItem::Standalone { addr: addr.clone() });
      },
      Tag::Muts => {
        // Materialize once to enumerate members; the `Arc<Constant>`
        // drops at the end of this arm — no cache retention.
        let constant = lc.value().get().map_err(|e| {
          format!("build_anon_work: materialize Muts {}: {e}", addr.hex())
        })?;
        let CI::Muts(members) = &constant.info else {
          return Err(format!(
            "build_anon_work: Tag::Muts but ConstantInfo is {:?} at {}",
            constant.info.variant(),
            addr.hex()
          ));
        };
        work.push(mutual_work(&addr, members)?);
      },
    }
  }

  Ok(work)
}

/// The full dependency-closure address set of `roots`: their transitive Expr
/// `refs` PLUS each projection's structural `block: Address`. A refs-only walk
/// misses the block — projections (IPrj/CPrj/RPrj/DPrj) point at their Muts
/// block via a struct field, not the Expr ref table — so the kernel couldn't
/// resolve the projection and would spuriously fail. The returned set includes
/// constant AND referenced-blob addresses (external refs absent from `source`
/// are included as addresses but have no bytes to copy).
pub fn closure_addrs(
  source: &IxonEnv,
  roots: &[Address],
) -> std::collections::HashSet<Address> {
  // The traversal lives in `ixon` (`Env::bfs_closure`) so bundle
  // pruning/validation and the shard sub-env share one edge
  // definition; this wrapper keeps the kernel-side std-HashSet
  // signature.
  source.bfs_closure(roots).into_iter().collect()
}

/// Build a closure sub-env: serialize only the BFS dependency closure of
/// `roots` (their transitive `Constant.refs` plus referenced literal blobs),
/// copying each constant's GENUINE bytes via `store_const_lazy` so the guest's
/// per-const integrity check (`hash(bytes) == addr`) and the env merkle root
/// still hold. The guest decodes this instead of the whole env, so it pays only
/// its closure's decode, bounding memory use for large environments.
/// Missing hints are
/// performance-only: ingress falls back to `Regular(0)`, so the typecheck
/// result — and thus the committed claim — is unchanged.
/// External refs (not in `source`) are omitted and remain open assumptions,
/// exactly as in whole-env.
///
/// Host-only: builds an `Env` via the `store_*` helpers, which are gated to
/// non-riscv64 (see `Env::store_blob`). The guest receives an already-built
/// sub-env from the host and only enumerates it via `build_anon_work`.
#[cfg(not(target_arch = "riscv64"))]
pub fn build_sub_env(
  source: &IxonEnv,
  roots: &[Address],
) -> Result<Vec<u8>, String> {
  let sub = sub_env_of(source, roots);
  let mut buf = Vec::new();
  sub.put(&mut buf).map_err(|e| format!("sub-env serialize: {e}"))?;
  Ok(buf)
}

/// The in-memory closure sub-env behind [`build_sub_env`]: copy the BFS
/// dependency closure of `roots` (genuine bytes + blobs + reducibility
/// hints), no Named section. A bound source's binding is copied with the
/// closure of the records it names, so the sub-env carries every record its
/// role admission reads and every unit a verdict on `roots` rests on (see
/// [`verdict_work`]). A binding that does not decode is copied as is, and
/// the sub-env's reader refuses it.
#[cfg(not(target_arch = "riscv64"))]
fn sub_env_of(source: &IxonEnv, roots: &[Address]) -> IxonEnv {
  let mut roots = roots.to_vec();
  if let Some(binding) = &source.role_binding
    && let Ok(table) = crate::role_table::RoleTable::from_bytes(&binding.bytes)
  {
    roots.extend(table.records().cloned());
  }
  let closure = closure_addrs(source, &roots);
  let mut sub = IxonEnv::new();
  sub.role_binding = source.role_binding.clone();
  for addr in &closure {
    if let Some(bytes) = source.get_const_bytes(addr) {
      sub.store_const_lazy(addr.clone(), bytes);
    } else if let Some(blob) = source.get_blob(addr) {
      sub.store_blob(blob);
    }
    // else: external ref absent from `source` — omit; stays an open assumption.
    // Carry the constant's reducibility hint so the guest reproduces vanilla
    // kernel behavior; without hints the kernel forces `Regular(0)` and does
    // extra def-eq work (the ~30% check overhead).
    if let Some(h) = source.anon_hints.get(addr) {
      sub.anon_hints.insert(addr.clone(), *h);
    }
  }
  sub
}

/// [`build_sub_env`] plus a name→address entry for every closure constant
/// named in the FULL view of the same env — a standalone `.ixe` whose names
/// still resolve (for `--consts`-style tools), extracted without recompiling
/// from source.
///
/// METADATA IS DROPPED: each copied entry is `Named::with_addr` (empty
/// `ConstantMeta`), because real metadata references name addresses
/// throughout its tree and carrying it would require the full env's
/// hash-consed name index. The extract serves the ANON pipeline
/// (`check-rs --anon`, the zkVM hosts, `ix profile`/`ix shard`,
/// `bench-typecheck`), where metadata is never read and reducibility hints
/// travel in the `anon_hints` section instead. Meta-mode tools need the
/// source env.
#[cfg(not(target_arch = "riscv64"))]
pub fn build_sub_env_named(
  source: &IxonEnv,
  full: &IxonEnv,
  roots: &[Address],
) -> Result<Vec<u8>, String> {
  use ix_common::env::NameData;

  let sub = sub_env_of(source, roots);
  // The Named section serializes keys as name HASHES resolved through the
  // names section, so each key's component chain must be interned too.
  fn intern_chain(sub: &IxonEnv, name: &ix_common::env::Name) {
    let addr = Address::from_blake3_hash(*name.get_hash());
    if sub.get_name(&addr).is_some() {
      return;
    }
    match name.as_data() {
      NameData::Anonymous(_) => {},
      NameData::Str(parent, _, _) | NameData::Num(parent, _, _) => {
        intern_chain(sub, parent);
      },
    }
    sub.store_name(addr, name.clone());
  }
  for e in full.named.iter() {
    if sub.get_const(&e.value().addr).is_some() {
      intern_chain(&sub, e.key());
      sub.register_name(
        e.key().clone(),
        crate::env::Named::with_addr(e.value().addr.clone()),
      );
    }
  }
  let mut buf = Vec::new();
  sub.put(&mut buf).map_err(|e| format!("sub-env serialize: {e}"))?;
  Ok(buf)
}

/// The ingress-block address that owns `addr`: a projection (IPrj/CPrj/RPrj/
/// DPrj) maps to its Muts `block`; anything else is its own block. Used to map
/// a resolved constant address to the `build_anon_work` item that covers it
/// (standalone → itself; a mutual-block member → the whole block).
pub fn block_of_addr(env: &IxonEnv, addr: &Address) -> Address {
  use crate::constant::ConstantInfo as CI;
  match env.get_const(addr) {
    Some(c) => match &c.info {
      CI::IPrj(p) => p.block.clone(),
      CI::CPrj(p) => p.block.clone(),
      CI::RPrj(p) => p.block.clone(),
      CI::DPrj(p) => p.block.clone(),
      _ => addr.clone(),
    },
    None => addr.clone(),
  }
}

/// The ingress-block address of a work item's `primary` — the key for matching
/// a resolved target constant to the work item that covers it.
pub fn work_block_addr(env: &IxonEnv, item: &AnonWorkItem) -> Address {
  block_of_addr(env, item.primary())
}

/// Build the STATIC block profile of an env — derived from
/// the serialized constants alone, no kernel run.
///
/// - Vertices: ingress units (a Muts block or a standalone constant),
///   `serialized_size` real, `const_count` = member constants,
///   `heartbeats` := size (report-only).
/// - Balance weight: the partitioner's vertex weight is `block_step_cost`
///   (a linear model over the op counters), so the byte weight is carried
///   in `subst` — `vweight ∝ size` exactly, matching the measured-best
///   bisection weight ([`STATIC_OWNED_PER_BYTE`] docs).
/// - Edges: the claim-walk relation (`crate::shard_claim::walk_edges` —
///   positively-used refs + projection block pointers) at block
///   granularity, deduped, self-edges dropped. These are exactly the
///   edges that generate a shard's thin frontier, i.e. its ingress.
#[allow(clippy::cast_possible_truncation)] // block sizes clamped to u32::MAX
pub fn static_block_profile(env: &IxonEnv) -> BlockProfile {
  use rayon::prelude::*;
  let addrs: Vec<Address> =
    env.consts.iter().map(|e| e.key().clone()).collect();
  // Phase 1 (parallel): parse each constant exactly ONCE. Lazy mmap
  // entries re-parse on every `get()` (see `LazyConstant`'s cache
  // policy), so the home block is derived from the constant we already
  // hold instead of `profile_block_of` (which would parse again), and
  // edge targets are kept as raw addresses to be resolved in phase 2
  // through the addr→home table this pass produces.
  struct ConstRow {
    addr: Address,
    home: Address,
    targets: Vec<Address>,
  }
  let rows: Vec<ConstRow> = addrs
    .par_iter()
    .filter_map(|addr| {
      let c = env.get_const(addr)?;
      let home = match &c.info {
        IxonCI::IPrj(p) => p.block.clone(),
        IxonCI::CPrj(p) => p.block.clone(),
        IxonCI::RPrj(p) => p.block.clone(),
        IxonCI::DPrj(p) => p.block.clone(),
        _ => addr.clone(),
      };
      let mut targets = Vec::new();
      crate::shard_claim::walk_edges(&c, &mut targets);
      Some(ConstRow { addr: addr.clone(), home, targets })
    })
    .collect();
  // Phase 2 (serial, no parsing): addr→home table, per-block member
  // counts, and block-level edges. A target absent from the table is a
  // blob payload (or an unparseable constant) — skipped, matching the
  // claim walk's blob sentinel.
  let home_of: FxHashMap<&Address, &Address> =
    rows.iter().map(|r| (&r.addr, &r.home)).collect();
  let mut counts: FxHashMap<&Address, u32> = FxHashMap::default();
  for r in &rows {
    *counts.entry(&r.home).or_insert(0) += 1;
  }
  let mut builder = ProfileBuilder::new();
  for r in &rows {
    for t in &r.targets {
      if let Some(&pb) = home_of.get(t)
        && *pb != r.home
      {
        builder.delta_edge(r.home.clone(), pb.clone());
      }
    }
  }
  for (home, cnt) in counts {
    // Size without materializing: `raw_bytes().len()` on the lazy entry
    // (`profile_block_size` would copy the bytes into a fresh Arc).
    let size = env
      .consts
      .get(home)
      .map_or(0, |e| e.value().raw_bytes().len().min(u32::MAX as usize))
      as u32;
    let ops = OpCounts { subst_nodes: u64::from(size), ..OpCounts::default() };
    builder.block(home.clone(), u64::from(size), size, cnt, ops);
  }
  builder.finish()
}

/// The blocks each block of `profile` references, by block id — every
/// constant's `refs` mapped to their home blocks, the edges a byte scope
/// (`Env::bfs_closure`) follows between blocks; projections reference
/// their own block and a block its wrappers, so those edges never leave a
/// block — and the blocks of the primitives the environment carries, which
/// every byte scope also starts from. A superset of the profile's walk
/// edges, which follow only the references a constant's body uses.
pub fn static_block_dependencies(
  env: &IxonEnv,
  profile: &BlockProfile,
) -> (Vec<Vec<u32>>, Vec<u32>) {
  use ix_common::prim_addrs::PrimAddrs;
  use rayon::prelude::*;
  let id_of: FxHashMap<&Address, u32> = profile
    .blocks()
    .iter()
    .enumerate()
    .map(|(i, b)| (&b.addr, u32::try_from(i).expect("block ids are u32")))
    .collect();
  let addrs: Vec<Address> =
    env.consts.iter().map(|e| e.key().clone()).collect();
  let rows: Vec<(Address, Address, Vec<Address>)> = addrs
    .par_iter()
    .filter_map(|addr| {
      let c = env.get_const(addr)?;
      let home = match &c.info {
        IxonCI::IPrj(p) => p.block.clone(),
        IxonCI::CPrj(p) => p.block.clone(),
        IxonCI::RPrj(p) => p.block.clone(),
        IxonCI::DPrj(p) => p.block.clone(),
        _ => addr.clone(),
      };
      Some((addr.clone(), home, c.refs.clone()))
    })
    .collect();
  // Every constant's block id, projections included; a blob has none.
  let block_of: FxHashMap<&Address, u32> = rows
    .iter()
    .filter_map(|(addr, home, _)| id_of.get(home).map(|&id| (addr, id)))
    .collect();
  let mut depends: Vec<Vec<u32>> = vec![Vec::new(); profile.num_blocks()];
  for (addr, _, refs) in &rows {
    let Some(&consumer) = block_of.get(addr) else { continue };
    for r in refs {
      if let Some(&producer) = block_of.get(r)
        && producer != consumer
      {
        depends[consumer as usize].push(producer);
      }
    }
  }
  for d in &mut depends {
    d.sort_unstable();
    d.dedup();
  }
  let mut primitives: Vec<u32> = PrimAddrs::lean_parity_table()
    .iter()
    .filter_map(|(_, hex)| Address::from_hex(hex))
    .chain(PrimAddrs::reserved_marker_addrs().iter().map(|(_, a)| a.clone()))
    .filter_map(|a| block_of.get(&a).copied())
    .collect();
  primitives.sort_unstable();
  primitives.dedup();
  (depends, primitives)
}

/// A weighted hypergraph derived from a [`BlockProfile`]. Vertex ids are block
/// ids (identical to the profile's). Nets are stored with global pins.
pub struct Hypergraph {
  /// Vertex (block) weights = estimated guest cost ([`block_step_cost`]:
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

  fn bisect_subset(&self, vertices: &[u32], epsilon: f64) -> [Vec<u32>; 2] {
    let mut local = vec![u32::MAX; self.num_vertices()];
    let mut weights = Vec::with_capacity(vertices.len());
    for (index, &vertex) in vertices.iter().enumerate() {
      local[vertex as usize] = index as u32;
      weights.push(self.vweight[vertex as usize]);
    }
    let cap = (weights.iter().map(|&w| u128::from(w)).sum::<u128>() / 2)
      .clamp(1, u128::from(u64::MAX)) as u64;
    let nets = self
      .net_pins
      .iter()
      .zip(&self.net_weight)
      .filter_map(|(pins, &weight)| {
        let pins: Vec<_> = pins
          .iter()
          .map(|&v| local[v as usize])
          .filter(|&v| v != u32::MAX)
          .collect();
        (pins.len() >= 2).then_some((weight, pins))
      })
      .collect();
    let sub = SubHyper::assemble(vertices.to_vec(), weights, nets, cap);
    let side = bisect(&sub, epsilon);
    let mut parts = [Vec::new(), Vec::new()];
    for (&vertex, side) in vertices.iter().zip(side) {
      parts[side as usize].push(vertex);
    }
    parts
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

  /// Append every leaf's shard id (left-to-right).
  pub fn collect_leaves(&self, out: &mut Vec<u32>) {
    match self {
      AggNode::Leaf(id) => out.push(*id),
      AggNode::Internal(l, r) => {
        l.collect_leaves(out);
        r.collect_leaves(out);
      },
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
    self.filter_map_leaves(&|id| keep(id).then_some(id))
  }

  /// Generalized pruning used when a manifest writer drops empty shards and
  /// densely renumbers the retained leaves.
  fn filter_map_leaves(
    &self,
    map: &impl Fn(u32) -> Option<u32>,
  ) -> Option<AggNode> {
    match self {
      AggNode::Leaf(id) => map(*id).map(AggNode::Leaf),
      AggNode::Internal(l, r) => {
        match (l.filter_map_leaves(map), r.filter_map_leaves(map)) {
          (Some(a), Some(b)) => {
            Some(AggNode::Internal(Box::new(a), Box::new(b)))
          },
          (Some(a), None) | (None, Some(a)) => Some(a),
          (None, None) => None,
        }
      },
    }
  }

  /// A balanced binary tree over `ids`, left to right: the left half takes
  /// `len / 2` leaves, exactly the shape the Lean consumer builds with
  /// `AggregationTree.balancedRange` for manifests that carry no tree.
  /// `None` for an empty slice.
  pub fn balanced(ids: &[u32]) -> Option<AggNode> {
    match ids {
      [] => None,
      [id] => Some(AggNode::Leaf(*id)),
      _ => {
        let (l, r) = ids.split_at(ids.len() / 2);
        Some(AggNode::Internal(
          Box::new(AggNode::balanced(l)?),
          Box::new(AggNode::balanced(r)?),
        ))
      },
    }
  }

  /// The tree with `Leaf(id)` replaced by a copy of `subtree`. Every other
  /// node is unchanged, so an untouched sibling subtree still folds to the
  /// same slot statements — and the same aggregate cache keys — as before.
  pub fn replace_leaf(&self, id: u32, subtree: &AggNode) -> AggNode {
    match self {
      AggNode::Leaf(x) if *x == id => subtree.clone(),
      AggNode::Leaf(x) => AggNode::Leaf(*x),
      AggNode::Internal(l, r) => AggNode::Internal(
        Box::new(l.replace_leaf(id, subtree)),
        Box::new(r.replace_leaf(id, subtree)),
      ),
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

  /// Inverse of [`Self::put`], reading from a cursor, with at most `depth`
  /// internal nodes on any path (see [`AGG_TREE_MAX_DEPTH`]).
  fn get(c: &mut Cur<'_>, depth: usize) -> Result<AggNode, String> {
    match c.u8()? {
      0 => Ok(AggNode::Leaf(c.u32()?)),
      1 => {
        let depth = depth.checked_sub(1).ok_or_else(|| {
          format!(
            "ixes: aggregation tree is deeper than {AGG_TREE_MAX_DEPTH} levels"
          )
        })?;
        let l = AggNode::get(c, depth)?;
        let r = AggNode::get(c, depth)?;
        Ok(AggNode::Internal(Box::new(l), Box::new(r)))
      },
      t => Err(format!("ixes: invalid aggregation-tree tag {t}")),
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
  /// Foreign blocks delta-unfolded by members but proven in other shards.
  pub foreign_blocks: Vec<Address>,
  /// Sum of `serialized_size` over `foreign_blocks` (this shard's share of the
  /// cross-shard ingress objective).
  pub cross_ingress: u64,
  /// Sound assumption-tree root for this shard's conditional proof: the Merkle
  /// root over the foreign part of the shard's static reference closure. `None`
  /// until populated by the env-aware layer (the pure partitioner has no `Env`).
  pub assumption_root: Option<Address>,
  /// Measured projected prover peak of this shard's executed record
  /// (`AiurSystem::peak_prove_bytes`), recorded when the manifest was
  /// emitted from a run that executed the shard; 0 = unmeasured (planner
  /// output). The scheduling signal: STARK prove wall is ~linear in it.
  pub measured_peak_bytes: u64,
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
        cross_ingress,
        assumption_root: None,
        measured_peak_bytes: 0,
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
    let peaks: Vec<u64> = self
      .shards
      .iter()
      .map(|s| s.measured_peak_bytes)
      .filter(|&p| p != 0)
      .collect();
    #[allow(clippy::cast_precision_loss)]
    let measured = if peaks.is_empty() {
      String::new()
    } else {
      let gib = |b: u64| b as f64 / (1u64 << 30) as f64;
      format!(
        " measured-peaks[{}/{} shards, min={:.1} max={:.1} GiB]",
        peaks.len(),
        self.shards.len(),
        gib(peaks.iter().copied().min().unwrap_or(0)),
        gib(peaks.iter().copied().max().unwrap_or(0)),
      )
    };
    format!(
      "shards={} (empty={}) heartbeats[min={} mean={} max={}] imbalance={:.2}x \
       cross_ingress_total={} max_shard_cross={}{measured}",
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
    use rustc_hash::FxHashMap;

    // Older/fixed-count planners can leave block-empty shard records when the
    // requested count exceeds the realizable partition. Never persist those
    // leaves: omit them, contract the aggregation tree, and densely renumber
    // the survivors. The Lean consumer additionally prunes zero-*constant*
    // legacy leaves after validating them against the environment.
    let retained: Vec<&ShardInfo> =
      self.shards.iter().filter(|shard| !shard.blocks.is_empty()).collect();
    let remap: FxHashMap<u32, u32> = retained
      .iter()
      .enumerate()
      .map(|(new_id, shard)| (shard.id, new_id as u32))
      .collect();
    let tree = self
      .tree
      .as_ref()
      .and_then(|tree| tree.filter_map_leaves(&|id| remap.get(&id).copied()));
    let total_cross_ingress = retained
      .iter()
      .map(|shard| u128::from(shard.cross_ingress))
      .sum::<u128>();

    let mut out = Vec::new();
    out.extend_from_slice(SHARD_MAGIC);
    out.extend_from_slice(&total_cross_ingress.to_le_bytes());
    out.extend_from_slice(&(retained.len() as u32).to_le_bytes());
    let put_addrs = |out: &mut Vec<u8>, addrs: &[Address]| {
      out.extend_from_slice(&(addrs.len() as u32).to_le_bytes());
      for a in addrs {
        out.extend_from_slice(a.as_bytes());
      }
    };
    for (new_id, sh) in retained.iter().enumerate() {
      out.extend_from_slice(&(new_id as u32).to_le_bytes());
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
    // Trailing optional bisection-tree section: presence byte then preorder
    // tree. Appended after the shards so older readers that stop at the shard
    // count simply ignore it, and `from_bytes` treats end-of-input as `None`.
    match &tree {
      Some(t) => {
        out.push(1);
        t.put(&mut out);
      },
      None => out.push(0),
    }
    // Trailing measured-peaks section (same older-readers-ignore contract
    // as the tree): presence byte, then one u64 LE per shard in order.
    // Absent when nothing was measured, so planner manifests stay
    // byte-identical to the pre-peaks format. The peaks follow the shard
    // section, so they are written for the retained shards only.
    if retained.iter().any(|s| s.measured_peak_bytes != 0) {
      out.push(1);
      for sh in &retained {
        out.extend_from_slice(&sh.measured_peak_bytes.to_le_bytes());
      }
    } else {
      out.push(0);
    }
    out
  }

  /// Deserialize from the `.ixes` binary format, exactly as the Lean parser
  /// (`parseIxesManifest`) does: at least one shard, each shard's id its
  /// position, presence bytes 0 or 1, a tree whose leaves are the shard ids
  /// once each, and nothing after the last section. No count allocates more
  /// than the remaining input could fill, and the tree is read without
  /// recursion.
  pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
    let mut c = Cur { buf: bytes, pos: 0 };
    if c.take(8)? != SHARD_MAGIC {
      return Err("not an .ixes file (bad magic)".into());
    }
    let total_cross_ingress = c.u128()?;
    let num_shards = c.u32()? as usize;
    if num_shards == 0 {
      return Err("ixes: manifest contains no shards".into());
    }
    // A shard entry is at least its id, three counters, a presence byte and
    // two address counts.
    if num_shards > c.remaining() / SHARD_ENTRY_MIN_BYTES {
      return Err(format!(
        "ixes: shard count {num_shards} exceeds the remaining input"
      ));
    }
    let mut shards = Vec::with_capacity(num_shards);
    for index in 0..num_shards {
      let id = c.u32()?;
      if id as usize != index {
        return Err(format!("ixes: shard entry {index} has id {id}"));
      }
      let heartbeats = c.u64()?;
      let own_size = c.u64()?;
      let cross_ingress = c.u64()?;
      let assumption_root = match c.u8()? {
        0 => None,
        1 => Some(c.addr()?),
        tag => {
          return Err(format!(
            "ixes: invalid assumption-root presence tag {tag}"
          ));
        },
      };
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
        measured_peak_bytes: 0,
      });
    }
    // Optional trailing tree section. Absent (end-of-input) on pre-tree
    // manifests, or an explicit `0` presence byte.
    let tree = if c.remaining() > 0 {
      match c.u8()? {
        0 => None,
        1 => Some(AggNode::get(&mut c, AGG_TREE_MAX_DEPTH)?),
        tag => {
          return Err(format!(
            "ixes: invalid aggregation-tree presence tag {tag}"
          ));
        },
      }
    } else {
      None
    };
    // Optional trailing measured-peaks section; absent on older manifests.
    if c.remaining() > 0 {
      match c.u8()? {
        0 => {},
        1 => {
          for sh in &mut shards {
            sh.measured_peak_bytes = c.u64()?;
          }
        },
        tag => {
          return Err(format!(
            "ixes: invalid measured-peaks presence tag {tag}"
          ));
        },
      }
    }
    if c.remaining() > 0 {
      return Err(format!(
        "ixes: {} trailing bytes after the measured-peaks section",
        c.remaining()
      ));
    }
    // The tree is the aggregation plan: a leaf set that is not exactly the
    // shard id set (each id once) would silently drop or duplicate proven
    // shards in the fold, so a manifest carrying such a tree is invalid.
    if let Some(t) = &tree {
      let mut leaf_ids = Vec::with_capacity(num_shards);
      t.collect_leaves(&mut leaf_ids);
      leaf_ids.sort_unstable();
      let mut shard_ids: Vec<u32> = shards.iter().map(|s| s.id).collect();
      shard_ids.sort_unstable();
      if leaf_ids != shard_ids {
        return Err(format!(
          "bisection tree leaves ({} ids) do not match the manifest's shard \
           id set ({num_shards} shards)",
          leaf_ids.len()
        ));
      }
    }
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

/// The fewest bytes a shard entry takes: id (4), heartbeats, own size and
/// cross ingress (8 each), the assumption-root presence byte, and the two
/// address counts (4 each).
const SHARD_ENTRY_MIN_BYTES: usize = 4 + 3 * 8 + 1 + 2 * 4;

/// The deepest aggregation tree a manifest may carry, in internal nodes on a
/// path. A planner tree comes from recursive bisection, so its depth stays
/// far below this; the bound keeps every recursive walk of a parsed tree (and
/// its drop) shallow. The Lean parser (`ixesTreeMaxDepth`) uses the same.
pub const AGG_TREE_MAX_DEPTH: usize = 4096;

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
  fn remaining(&self) -> usize {
    self.buf.len() - self.pos
  }
  fn addrs(&mut self) -> Result<Vec<Address>, String> {
    let n = self.u32()? as usize;
    if n > self.remaining() / 32 {
      return Err("truncated .ixes".into());
    }
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
      v.push(self.addr()?);
    }
    Ok(v)
  }
}

// ============================================================================
// Static (profile-free) sharding — the `ix shard <env.ixe>` path
// ============================================================================

/// Fitted per-shard Aiur FFT cost model driving the static strategy:
///
/// ```text
///   cost(S) ≈ STATIC_OWNED_PER_BYTE      · owned_bytes(S)
///           + STATIC_OWNED_SUPERLINEAR   · Σ_{b∈S} size(b)^1.5
///           + STATIC_FRONTIER_PER_BYTE   · frontier_bytes(S)
/// ```
///
/// where `size(b)` is a block's serialized byte length and
/// `frontier_bytes(S)` sums the sizes of foreign producer blocks referenced
/// by S's members (the thin frontier the kernel ingresses). A frontier byte
/// pays ingress only (blake3 + parse); an owned byte additionally pays
/// typechecking, which concentrates superlinearly in large proof bodies —
/// hence the per-block `^1.5` term (NOT `(Σ size)^1.5`: how bytes are
/// packaged into constants is exactly what it measures).
///
/// Fit: least squares over 56 measured shards from 7 different 8-shard
/// partitions of Init (native IxVM, real blake3, `Total FFT cost` from
/// `ix check --stats-out`), mean |err| 4.7% on shards ≥ 3e11. Validated
/// without refit on Std at 24 shards (4.5% aggregate bias) — the constants
/// are Aiur-kernel physics, not env-specific. The fit's intercept
/// (−2.3e10) cancels in balance comparisons and is omitted.
pub const STATIC_OWNED_PER_BYTE: f64 = 28_201.0;
/// See [`STATIC_OWNED_PER_BYTE`].
pub const STATIC_OWNED_SUPERLINEAR: f64 = 681.08;
/// See [`STATIC_OWNED_PER_BYTE`].
pub const STATIC_FRONTIER_PER_BYTE: f64 = 38_000.0;

/// Reference point for the profile-free shard-count seed: Mathlib's static
/// owned-side score under this model. At a 400 GiB prover budget, 233 seed
/// shards gave the established Mathlib-class behavior (a small number of
/// heavy-tail splits, corrected by the execution gate).
pub const STATIC_SEED_REFERENCE_SCORE: f64 = 1.254e14;
/// Mathlib seed count at [`STATIC_SEED_REFERENCE_RAM_GIB`].
pub const STATIC_SEED_REFERENCE_SHARDS: f64 = 233.0;
/// Prover-RAM budget of the reference calibration.
pub const STATIC_SEED_REFERENCE_RAM_GIB: f64 = 400.0;
/// Mild superlinear scale correction over the static owned-side score.
///
/// A linear score model still over-counted the small environments: cross-shard
/// duplication and the heavy-tail risk both grow with library scale. The 1.10
/// exponent preserves the Mathlib reference while fitting the measured knees
/// at Init (8 shards) and ISLB (23) at the 400 GiB reference budget.
pub const STATIC_SEED_SCORE_EXPONENT: f64 = 1.10;
/// Superlinear correction when scaling the seed away from 400 GiB.
///
/// Fitted on the 2026-08-28 100 GiB calibration: linear scaling caused broad
/// correction (Init 32→48 leaves; ISLB 93→123), while 1.20 seeded Init at 43
/// (42 measured clean) and ISLB at 122 (four initial misses, 128 leaves).
/// Out-of-sample Batteries seeded 74 with one initial miss and 79 leaves. The
/// discarded 1.36 candidate over-seeded ISLB at 152→156. Unlike the score
/// exponent, this changes no reference-budget prediction.
pub const STATIC_SEED_BUDGET_EXPONENT: f64 = 1.20;

/// Reference point for the shard-count seed of the trace-shard prover
/// (the CUDA build): Mathlib's serialized block bytes and its 78-way cut
/// proven on four RTX PRO 6000 on 2026-09-15 (`--max-ram 230`, three
/// executions ahead of each prover, 1.5e9 cells: a 41.4 GiB record
/// share). 78 is the p90-scaled candidate of the 111-shard seed, and its
/// own run confirmed it: claim records mean 29.3 GiB, p90 33.9 GiB at a
/// 36.5 GiB initial reservation, no growth waits.
pub const GPU_SEED_REFERENCE_BYTES: f64 = 1_468_041_216.0;
/// Shards of the reference cut.
pub const GPU_SEED_REFERENCE_SHARDS: f64 = 78.0;
/// Record share of the reference calibration, GiB.
pub const GPU_SEED_REFERENCE_SHARE_GIB: f64 = 41.4;

/// Seed count for the trace-shard prover: the reference count scaled by
/// serialized block bytes and inversely by the record share, so the
/// seed owns the reference's bytes per shard at the reference share.
///
/// A claim's execution record is close to linear in the bytes its shard
/// owns, about 1,700 bytes of record per serialized byte, from Mathlib's
/// ordinary shards (18.8 MB, 29.3 GiB) to Anthropic FLT's single-constant
/// outliers (58.5 MB, 89.5 GiB), so matching bytes per shard reproduces
/// the reference's record distribution. The static score's per-block
/// `size^1.5` term is deliberately left out: it dominates environments
/// with multi-megabyte proof bodies (93% of FLT's score) while their
/// measured records stay linear, and would seed them several times too
/// fine. Like [`static_seed_shards`] it is a seed, not a bound; the
/// record cap names any shard whose record exceeds its share, and atomic
/// blocks above the share are isolated by the balance-weight cap.
pub fn gpu_seed_shards(profile: &BlockProfile, share_gib: f64) -> usize {
  let scaled = GPU_SEED_REFERENCE_SHARDS
    * (static_env_bytes(profile) / GPU_SEED_REFERENCE_BYTES)
    * (GPU_SEED_REFERENCE_SHARE_GIB / share_gib.max(f64::EPSILON));
  (scaled.round().max(1.0) as usize).min(profile.num_blocks().max(1))
}

/// Serialized bytes over every block: what the trace-shard seed scales
/// with, and the balance weight the static cut distributes.
pub fn static_env_bytes(profile: &BlockProfile) -> f64 {
  profile.blocks().iter().map(|b| f64::from(b.serialized_size)).sum()
}

/// Predicted owned-side cost of one block under the static model.
fn static_owned_weight(size: u32) -> f64 {
  let s = f64::from(size);
  STATIC_OWNED_PER_BYTE * s + STATIC_OWNED_SUPERLINEAR * s * s.sqrt()
}

/// Whole-environment owned-side score used only to seed a shard count.
///
/// There is no frontier when the environment is viewed as one set, so this is
/// just the sum of [`static_owned_weight`] over blocks. Unlike raw `.ixe` file
/// bytes, it sees how bytes are packaged: the superlinear term distinguishes a
/// large reduction-heavy proof body from the same bytes spread over many small
/// declarations. The actual partition still includes frontier cost and is
/// always checked by the execution-time prover-RAM gate.
pub fn static_env_score(profile: &BlockProfile) -> f64 {
  profile.blocks().iter().map(|b| static_owned_weight(b.serialized_size)).sum()
}

/// Score/budget model for the profile-free shard-count seed.
///
/// This deliberately rounds to the nearest shard instead of always rounding
/// upward: it is a seed, not a safety boundary, and the prove/check execution
/// gate measures and splits every over-budget shard before a STARK starts.
/// Avoiding an unconditional upward bias matters most for small environments.
fn static_seed_shards_for_score(score: f64, ram_gib: u64) -> usize {
  let budget = ram_gib.max(1) as f64;
  let scaled = STATIC_SEED_REFERENCE_SHARDS
    * (score / STATIC_SEED_REFERENCE_SCORE).powf(STATIC_SEED_SCORE_EXPONENT)
    * (STATIC_SEED_REFERENCE_RAM_GIB / budget)
      .powf(STATIC_SEED_BUDGET_EXPONENT);
  scaled.round().max(1.0) as usize
}

/// Suggested static seed count for `profile` at a per-shard prover-RAM budget.
/// The result is capped at one shard per atomic block; finer partitioning could
/// only create empty shards and cannot make an oversized block splittable.
pub fn static_seed_shards(profile: &BlockProfile, ram_gib: u64) -> usize {
  static_seed_shards_for_score(static_env_score(profile), ram_gib)
    .min(profile.num_blocks().max(1))
}

/// Greedy global rebalance toward equal predicted per-shard cost under the
/// static model. Repeatedly moves the best block from the most expensive
/// shard to the cheapest until the hot/cold gap is within 1% of the mean
/// or no single move lowers the pair's max. Returns the move count.
///
/// Why a post-pass at all: recursive bisection enforces balance only per
/// cut (±ε), which compounds to ~1.6–1.9× max/min over log₂(N) levels of
/// proportional integer budget splits; and no vertex-weight balance can
/// see the frontier term, which depends on the cut itself. Measured on the
/// 8-shard Init harness this pass took realized FFT stddev 14.7% → 7.1%
/// and the max shard down 6% on top of the byte-balanced min-cut.
///
/// Move evaluation is exact under the model: moving `b` from `src` to
/// `dst` shifts its owned weight and updates both shards' frontiers —
/// producers of `b` may enter `dst`'s frontier or leave `src`'s (when `b`
/// was their only consumer there), and `b` itself may enter `src`'s
/// frontier (if consumers remain) or leave `dst`'s. Other shards are
/// unaffected: their view of `b` depends only on `b` being outside them.
pub fn rebalance_static(
  profile: &BlockProfile,
  shard_of: &mut [u32],
  num_shards: usize,
) -> usize {
  use rustc_hash::FxHashMap;
  let n = profile.num_blocks();
  if num_shards <= 1 || n == 0 {
    return 0;
  }
  let size = |b: u32| profile.block(b).serialized_size;
  let (crow, ccol) = profile.consumers_csr();
  let consumers = |b: u32| &ccol[crow[b as usize]..crow[b as usize + 1]];

  let mut owned = vec![0.0f64; num_shards];
  for b in 0..n {
    owned[shard_of[b] as usize] += static_owned_weight(size(b as u32));
  }
  // fcnt[k][p] = number of k-owned consumers of foreign producer p;
  // fbytes[k] = Σ size(p) over k's frontier (fcnt keys).
  let mut fcnt: Vec<FxHashMap<u32, u32>> =
    vec![FxHashMap::default(); num_shards];
  let mut fbytes = vec![0.0f64; num_shards];
  for c in 0..n as u32 {
    let kc = shard_of[c as usize];
    for &p in profile.producers(c) {
      if shard_of[p as usize] != kc {
        let e = fcnt[kc as usize].entry(p).or_insert(0);
        if *e == 0 {
          fbytes[kc as usize] += f64::from(size(p));
        }
        *e += 1;
      }
    }
  }

  let mut moves = 0usize;
  loop {
    let costs: Vec<f64> = (0..num_shards)
      .map(|k| owned[k] + STATIC_FRONTIER_PER_BYTE * fbytes[k])
      .collect();
    let hot =
      (0..num_shards).max_by(|&a, &b| costs[a].total_cmp(&costs[b])).unwrap();
    let cold =
      (0..num_shards).min_by(|&a, &b| costs[a].total_cmp(&costs[b])).unwrap();
    let gap = costs[hot] - costs[cold];
    let mean = costs.iter().sum::<f64>() / num_shards as f64;
    if gap <= 0.01 * mean {
      break;
    }
    // Best move: lexicographically minimize (new max(hot', cold'), total
    // cost increase). Deterministic: blocks scanned in id order, strict <.
    let mut best: Option<(u32, f64, f64)> = None;
    for b in 0..n as u32 {
      if shard_of[b as usize] != hot as u32 {
        continue;
      }
      let w = static_owned_weight(size(b));
      if w > gap {
        continue; // moving it would overshoot the gap
      }
      // Δcost(src): lose w(b); b's producers leave the frontier when b was
      // their only src consumer; b enters it if src still consumes it.
      let mut df_src = 0.0f64;
      for &p in profile.producers(b) {
        if shard_of[p as usize] != hot as u32 && fcnt[hot].get(&p) == Some(&1) {
          df_src -= f64::from(size(p));
        }
      }
      if consumers(b)
        .iter()
        .any(|&c| c != b && shard_of[c as usize] == hot as u32)
      {
        df_src += f64::from(size(b));
      }
      // Δcost(dst): gain w(b); b leaves dst's frontier if present; b's
      // foreign producers enter it if not already there.
      let mut df_dst = 0.0f64;
      if fcnt[cold].contains_key(&b) {
        df_dst -= f64::from(size(b));
      }
      for &p in profile.producers(b) {
        if shard_of[p as usize] != cold as u32 && !fcnt[cold].contains_key(&p) {
          df_dst += f64::from(size(p));
        }
      }
      let ds = -w + STATIC_FRONTIER_PER_BYTE * df_src;
      let dd = w + STATIC_FRONTIER_PER_BYTE * df_dst;
      let key = ((costs[hot] + ds).max(costs[cold] + dd), ds + dd);
      if best
        .is_none_or(|(_, k0, k1)| key.0 < k0 || (key.0 == k0 && key.1 < k1))
      {
        best = Some((b, key.0, key.1));
      }
    }
    let Some((b, new_max, _)) = best else { break };
    if new_max >= costs[hot] {
      break; // no move improves the pair
    }
    // Apply: owned weights, then frontier bookkeeping for src and dst.
    let (src, dst) = (hot, cold);
    shard_of[b as usize] = dst as u32;
    let wb = static_owned_weight(size(b));
    owned[src] -= wb;
    owned[dst] += wb;
    for &p in profile.producers(b) {
      if shard_of[p as usize] != src as u32
        && let Some(e) = fcnt[src].get_mut(&p)
      {
        *e -= 1;
        if *e == 0 {
          fcnt[src].remove(&p);
          fbytes[src] -= f64::from(size(p));
        }
      }
      if shard_of[p as usize] != dst as u32 {
        let e = fcnt[dst].entry(p).or_insert(0);
        if *e == 0 {
          fbytes[dst] += f64::from(size(p));
        }
        *e += 1;
      }
    }
    let src_consumers = consumers(b)
      .iter()
      .filter(|&&c| c != b && shard_of[c as usize] == src as u32)
      .count() as u32;
    if src_consumers > 0 {
      let e = fcnt[src].entry(b).or_insert(0);
      if *e == 0 {
        fbytes[src] += f64::from(size(b));
      }
      *e = src_consumers;
    }
    if fcnt[dst].remove(&b).is_some() {
      fbytes[dst] -= f64::from(size(b));
    }
    moves += 1;
  }
  moves
}

/// Predicted per-shard costs under the static model for a given assignment
/// (fresh recomputation — used for reports and tests).
pub fn static_predicted_costs(
  profile: &BlockProfile,
  shard_of: &[u32],
  num_shards: usize,
) -> Vec<f64> {
  use rustc_hash::FxHashMap;
  let mut owned = vec![0.0f64; num_shards];
  let mut fr: Vec<FxHashMap<u32, ()>> = vec![FxHashMap::default(); num_shards];
  for b in 0..profile.num_blocks() as u32 {
    let k = shard_of[b as usize] as usize;
    owned[k] += static_owned_weight(profile.block(b).serialized_size);
    for &p in profile.producers(b) {
      if shard_of[p as usize] != k as u32 {
        fr[k].insert(p, ());
      }
    }
  }
  (0..num_shards)
    .map(|k| {
      let fb: f64 = fr[k]
        .keys()
        .map(|&p| f64::from(profile.block(p).serialized_size))
        .sum();
      owned[k] + STATIC_FRONTIER_PER_BYTE * fb
    })
    .collect()
}

/// Partition a STATIC block profile (reference graph + sizes, no kernel
/// run — see `ix shard graph` / the FFI static-profile builder) into
/// `num_shards` shards: byte-balanced min-cut over the walk-edge nets,
/// then the [`rebalance_static`] post-pass toward equal predicted cost.
/// Writes the same `.ixes` manifest as [`shard_esp`]. This is the
/// `ix shard <env.ixe>` (no `--profile`) strategy; measured against the
/// profiled strategy it cut mean shard FFT ~30% and the max shard
/// 44–51% on the Init(8)/Std(24) harnesses.
pub fn shard_static(
  profile: &BlockProfile,
  num_shards: usize,
  balance: f64,
  out_path: Option<&str>,
) -> Result<String, String> {
  let t0 = Instant::now();
  let h = Hypergraph::from_profile(profile);
  let t_graph = t0.elapsed();
  let t1 = Instant::now();
  let (mut shard_of, tree) = h.partition_with_tree(num_shards, balance);
  let t_part = t1.elapsed();
  let t2 = Instant::now();
  let moves = rebalance_static(profile, &mut shard_of, num_shards);
  eprintln!(
    "[shard_static] hypergraph {t_graph:.1?}, partition {t_part:.1?}, rebalance {:.1?} ({moves} moves)",
    t2.elapsed()
  );
  let mut manifest =
    ShardManifest::build(profile, &shard_of, num_shards).with_tree(tree);
  seal_and_write(&mut manifest, out_path)?;
  let costs = static_predicted_costs(profile, &shard_of, num_shards);
  let (mut lo, mut hi, mut sum) = (f64::INFINITY, 0.0f64, 0.0f64);
  for &c in &costs {
    lo = lo.min(c);
    hi = hi.max(c);
    sum += c;
  }
  Ok(format!(
    "blocks={} static_edges={} nets={}\n{}\nrebalance moves={}  predicted FFT/shard mean={:.3e} min={:.3e} max={:.3e} spread={:.2}x",
    profile.num_blocks(),
    profile.num_edges(),
    h.num_nets(),
    manifest.summary(),
    moves,
    sum / num_shards as f64,
    lo,
    hi,
    hi / lo.max(1.0),
  ))
}

/// Lay the blocks out as `num_shards` contiguous ranges of a dependency
/// order, cut at equal predicted cost, numbered from the top down: shard 0
/// holds the blocks nothing depends on, the last shard the blocks
/// everything depends on. `depends[b]` lists the blocks `b` references
/// through any edge the byte scope follows, so a shard's reference closure
/// lies in its own shard and higher-numbered ones. The distributed prover's
/// static caller graph over such a manifest is acyclic, and its records
/// commit one at a time in shard order. The blocks in `first` and their
/// dependencies are laid out at the bottom of the order, ahead of
/// everything else: the primitives the kernel reaches from any constant
/// without a reference belong there. Blocks on a reference cycle keep the
/// order they are first reached in; the report counts the edges that
/// point from a shard to a lower-numbered one. No aggregation tree is
/// attached.
pub fn shard_static_ordered(
  profile: &BlockProfile,
  depends: &[Vec<u32>],
  first: &[u32],
  num_shards: usize,
  out_path: Option<&str>,
) -> Result<String, String> {
  let n = profile.num_blocks();
  if num_shards == 0 || num_shards > n {
    return Err(format!(
      "shard_static_ordered: {num_shards} shards for {n} blocks"
    ));
  }
  let t0 = Instant::now();
  let (shard_of, backward) =
    ordered_layout(profile, depends, first, num_shards);
  let mut manifest = ShardManifest::build(profile, &shard_of, num_shards);
  seal_and_write(&mut manifest, out_path)?;
  let costs = static_predicted_costs(profile, &shard_of, num_shards);
  let (mut lo, mut hi, mut sum) = (f64::INFINITY, 0.0f64, 0.0f64);
  for &c in &costs {
    lo = lo.min(c);
    hi = hi.max(c);
    sum += c;
  }
  Ok(format!(
    "blocks={} dependency_edges={} layout=ordered ({:.1?})\n{}\nbackward edges={backward}  predicted FFT/shard mean={:.3e} min={:.3e} max={:.3e} spread={:.2}x",
    n,
    depends.iter().map(Vec::len).sum::<usize>(),
    t0.elapsed(),
    manifest.summary(),
    sum / num_shards as f64,
    lo,
    hi,
    hi / lo.max(1.0),
  ))
}

/// The shard of every block under the ordered layout (see
/// [`shard_static_ordered`]) and the number of dependency edges that point
/// to a lower-numbered shard, zero when `depends` is acyclic.
fn ordered_layout(
  profile: &BlockProfile,
  depends: &[Vec<u32>],
  first: &[u32],
  num_shards: usize,
) -> (Vec<u32>, usize) {
  let n = profile.num_blocks();
  // Post-order of a depth-first walk along `depends`: every block after the
  // blocks it references, from the bottom of the environment upward.
  let mut order: Vec<u32> = Vec::with_capacity(n);
  let mut state = vec![0u8; n]; // 0 unseen, 1 on the stack, 2 emitted
  for root in first.iter().copied().chain(0..n as u32) {
    if state[root as usize] != 0 {
      continue;
    }
    let mut stack: Vec<(u32, usize)> = vec![(root, 0)];
    state[root as usize] = 1;
    while let Some(top) = stack.len().checked_sub(1) {
      let (b, next) = stack[top];
      if let Some(&d) = depends[b as usize].get(next) {
        stack[top].1 = next + 1;
        if state[d as usize] == 0 {
          state[d as usize] = 1;
          stack.push((d, 0));
        }
      } else {
        state[b as usize] = 2;
        order.push(b);
        stack.pop();
      }
    }
  }
  // Cut the order at equal predicted owned cost, every range non-empty;
  // the range index counts from the bottom, the shard id from the top.
  let weight = |b: u32| static_owned_weight(profile.block(b).serialized_size);
  let total: f64 = order.iter().map(|&b| weight(b)).sum();
  let mut shard_of = vec![0u32; n];
  let mut range = 0usize;
  let mut range_blocks = 0usize;
  let mut cumulative = 0.0f64;
  for (position, &b) in order.iter().enumerate() {
    let remaining_blocks = n - position;
    let remaining_ranges = num_shards - range;
    let boundary = total * (range + 1) as f64 / num_shards as f64;
    if range_blocks > 0
      && range + 1 < num_shards
      && (cumulative >= boundary || remaining_blocks == remaining_ranges)
    {
      range += 1;
      range_blocks = 0;
    }
    cumulative += weight(b);
    range_blocks += 1;
    shard_of[b as usize] = (num_shards - 1 - range) as u32;
  }
  let backward: usize = (0..n as u32)
    .map(|b| {
      depends[b as usize]
        .iter()
        .filter(|&&d| shard_of[d as usize] < shard_of[b as usize])
        .count()
    })
    .sum();
  (shard_of, backward)
}

/// Seal every shard's assumption root (the canonical merkle root over
/// its foreign blocks) and write the manifest when a path is given.
/// Shared tail of every manifest-producing entry point.
fn seal_and_write(
  manifest: &mut ShardManifest,
  out_path: Option<&str>,
) -> Result<(), String> {
  for shard in &mut manifest.shards {
    shard.assumption_root =
      crate::merkle::merkle_root_canonical(&shard.foreign_blocks);
  }
  if let Some(op) = out_path {
    std::fs::write(op, manifest.to_bytes())
      .map_err(|e| format!("write {op}: {e}"))?;
  }
  Ok(())
}

/// One leaf of a source manifest cut into parts: the parts' block lists in
/// order (each a nonempty subset of the leaf's blocks) and, per part, the
/// measured prover peak (`0` = unmeasured).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LeafRefinement {
  pub id: u32,
  pub parts: Vec<Vec<Address>>,
  pub part_peaks: Vec<u64>,
}

impl ShardManifest {
  /// Bisect selected leaves along their internal dependency edges. Every
  /// block remains atomic, and unaffected leaves keep their IDs and tree
  /// positions so their claim and aggregate proofs remain reusable.
  pub fn bisect_leaves(
    &self,
    profile: &BlockProfile,
    ids: &[u32],
  ) -> Result<(ShardManifest, Vec<Vec<u32>>), String> {
    let block_ids: FxHashMap<_, _> = profile
      .blocks()
      .iter()
      .enumerate()
      .map(|(i, b)| (&b.addr, i as u32))
      .collect();
    let graph = Hypergraph::from_profile(profile);
    let mut refinements = Vec::with_capacity(ids.len());
    for &id in ids {
      let shard = self
        .shards
        .iter()
        .find(|shard| shard.id == id)
        .ok_or_else(|| format!("cannot split missing shard {id}"))?;
      if shard.blocks.len() < 2 {
        return Err(format!(
          "shard {id} contains {} atomic block(s) and cannot be split further",
          shard.blocks.len()
        ));
      }
      let vertices = shard
        .blocks
        .iter()
        .map(|block| {
          block_ids.get(block).copied().ok_or_else(|| {
            format!(
              "shard {id}: block {} is absent from the profile",
              block.hex()
            )
          })
        })
        .collect::<Result<Vec<_>, _>>()?;
      let parts = graph
        .bisect_subset(&vertices, 0.05)
        .into_iter()
        .map(|part| {
          part.into_iter().map(|b| profile.block(b).addr.clone()).collect()
        })
        .collect();
      refinements.push(LeafRefinement { id, parts, part_peaks: vec![0, 0] });
    }
    let (mut refined, part_ids) = self.refine(profile, &refinements, &[])?;
    seal_and_write(&mut refined, None)?;
    Ok((refined, part_ids))
  }

  /// Refine this manifest by cutting some of its leaves into parts, leaving
  /// every other leaf — block list, record, and place in the aggregation
  /// tree — exactly as it was.
  ///
  /// Id policy: part 0 of a refined leaf keeps the leaf's id; the remaining
  /// parts take fresh ids after the last existing one (ascending by refined
  /// leaf id, then part order), so ids stay dense and untouched shards keep
  /// their numbers. Each refined leaf's place in the tree becomes a balanced
  /// subtree over its parts; a source without a tree first gets the balanced
  /// tree its Lean consumer would have used. `measured` (empty, or one value
  /// per source shard) overrides the carried-forward peak of unsplit shards
  /// where nonzero.
  ///
  /// The whole new partition is validated as an exact, disjoint cover of the
  /// profile's blocks. Returns the refined manifest (unsealed: the caller
  /// fills assumption roots) and, per refinement, its parts' new ids.
  pub fn refine(
    &self,
    profile: &BlockProfile,
    refinements: &[LeafRefinement],
    measured: &[u64],
  ) -> Result<(ShardManifest, Vec<Vec<u32>>), String> {
    use rustc_hash::FxHashMap;

    let n = self.shards.len();
    if n == 0 {
      return Err("refine: source manifest has no shards".into());
    }
    for (i, sh) in self.shards.iter().enumerate() {
      if sh.id as usize != i {
        return Err(format!(
          "refine: source shard ids are not dense (entry {i} has id {})",
          sh.id
        ));
      }
    }
    if !measured.is_empty() && measured.len() != n {
      return Err(format!(
        "refine: measured peaks: {} values for {n} shards",
        measured.len()
      ));
    }
    let mut by_id: FxHashMap<u32, usize> = FxHashMap::default();
    for (i, r) in refinements.iter().enumerate() {
      if r.id as usize >= n {
        return Err(format!(
          "refine: shard {} is out of range ({n} shards)",
          r.id
        ));
      }
      if r.parts.len() < 2 {
        return Err(format!(
          "refine: shard {} needs at least two parts, got {}",
          r.id,
          r.parts.len()
        ));
      }
      if r.part_peaks.len() != r.parts.len() {
        return Err(format!(
          "refine: shard {}: {} peaks for {} parts",
          r.id,
          r.part_peaks.len(),
          r.parts.len()
        ));
      }
      if let Some(k) = r.parts.iter().position(Vec::is_empty) {
        return Err(format!("refine: shard {} part {k} is empty", r.id));
      }
      if by_id.insert(r.id, i).is_some() {
        return Err(format!("refine: shard {} listed twice", r.id));
      }
    }

    // The new shard list in id order: slots 0..n keep their ids (part 0 of a
    // refined leaf inherits the leaf's), then the extra parts are appended.
    let mut new_shards: Vec<(&[Address], u64)> = Vec::with_capacity(n);
    let mut part_ids: Vec<Vec<u32>> = vec![Vec::new(); refinements.len()];
    for sh in &self.shards {
      match by_id.get(&sh.id) {
        None => {
          let carried = measured
            .get(sh.id as usize)
            .copied()
            .filter(|&p| p != 0)
            .unwrap_or(sh.measured_peak_bytes);
          new_shards.push((&sh.blocks, carried));
        },
        Some(&i) => {
          let r = &refinements[i];
          new_shards.push((&r.parts[0], r.part_peaks[0]));
          part_ids[i].push(sh.id);
        },
      }
    }
    let mut refined_ids: Vec<u32> = by_id.keys().copied().collect();
    refined_ids.sort_unstable();
    for id in refined_ids {
      let i = by_id[&id];
      let r = &refinements[i];
      for (part, &peak) in r.parts.iter().zip(&r.part_peaks).skip(1) {
        let new_id = u32::try_from(new_shards.len())
          .map_err(|_| "refine: too many shards".to_string())?;
        new_shards.push((part, peak));
        part_ids[i].push(new_id);
      }
    }

    // Exact cover over the profile's blocks.
    let block_id: FxHashMap<&Address, u32> = profile
      .blocks()
      .iter()
      .enumerate()
      .map(|(i, b)| (&b.addr, i as u32))
      .collect();
    let mut shard_of = vec![u32::MAX; profile.num_blocks()];
    for (k, (blocks, _)) in new_shards.iter().enumerate() {
      for a in *blocks {
        let Some(&b) = block_id.get(a) else {
          return Err(format!(
            "refine: shard {k}: block {} not in the env's block profile",
            a.hex()
          ));
        };
        if shard_of[b as usize] != u32::MAX {
          return Err(format!(
            "refine: block {} appears in shards {} and {k}",
            a.hex(),
            shard_of[b as usize]
          ));
        }
        shard_of[b as usize] = k as u32;
      }
    }
    let uncovered = shard_of.iter().filter(|&&s| s == u32::MAX).count();
    if uncovered > 0 {
      return Err(format!(
        "refine: partition covers {} of {} blocks ({uncovered} missing)",
        profile.num_blocks() - uncovered,
        profile.num_blocks()
      ));
    }

    let mut manifest =
      ShardManifest::build(profile, &shard_of, new_shards.len());
    for (sh, (_, peak)) in manifest.shards.iter_mut().zip(&new_shards) {
      sh.measured_peak_bytes = *peak;
    }
    let all_ids: Vec<u32> = (0..n as u32).collect();
    let mut tree = self
      .tree
      .clone()
      .unwrap_or_else(|| AggNode::balanced(&all_ids).expect("n > 0 leaves"));
    for (r, ids) in refinements.iter().zip(&part_ids) {
      let sub = AggNode::balanced(ids).expect("at least two parts");
      tree = tree.replace_leaf(r.id, &sub);
    }
    manifest.tree = Some(tree);
    Ok((manifest, part_ids))
  }
}

/// Refine a source manifest ([`ShardManifest::refine`]), seal the result and
/// write it to `out_path`. Returns the manifest summary and, per refinement,
/// its parts' new ids.
pub fn shard_manifest_refine(
  profile: &BlockProfile,
  source: &ShardManifest,
  refinements: &[LeafRefinement],
  measured: &[u64],
  out_path: &str,
) -> Result<(String, Vec<Vec<u32>>), String> {
  let (mut manifest, part_ids) =
    source.refine(profile, refinements, measured)?;
  seal_and_write(&mut manifest, Some(out_path))?;
  Ok((manifest.summary(), part_ids))
}

#[cfg(test)]
mod tests {
  use super::*;

  fn addr(byte: u8) -> Address {
    Address::from_slice(&[byte; 32]).unwrap()
  }

  fn ops(subst: u64) -> OpCounts {
    OpCounts { subst_nodes: subst, ..OpCounts::default() }
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
      b.block(addr(i), 100, 1000, 1, ops(100));
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

  /// Blocks 1 → 2 → 3 and 4 → 3 (`→` = depends on), equal sizes, two
  /// shards: the bottom half {3, 2} is shard 1, the top half {1, 4} shard
  /// 0, and every dependency points to the same or a higher-numbered shard.
  #[test]
  fn ordered_layout_puts_dependencies_in_later_shards() {
    let mut b = ProfileBuilder::new();
    for i in 1..=4u8 {
      b.block(addr(i), 100, 1000, 1, ops(100));
    }
    let profile = b.finish();
    let depends = vec![vec![1], vec![2], vec![], vec![2]];
    let (shard_of, backward) = ordered_layout(&profile, &depends, &[], 2);
    assert_eq!(shard_of, vec![0, 1, 1, 0]);
    assert_eq!(backward, 0);
    for (block, deps) in depends.iter().enumerate() {
      for &d in deps {
        assert!(shard_of[d as usize] >= shard_of[block]);
      }
    }
    // A block laid out first sinks to the bottom with its dependencies.
    let (with_first, backward) = ordered_layout(&profile, &depends, &[3], 2);
    assert_eq!(with_first, vec![0, 0, 1, 1]);
    assert_eq!(backward, 0);
    // Every shard is non-empty even when the cut lands on the last blocks.
    let (four, _) = ordered_layout(&profile, &depends, &[], 4);
    let mut seen = four.clone();
    seen.sort_unstable();
    assert_eq!(seen, vec![0, 1, 2, 3]);
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

  /// `rebalance_static` must (a) keep its incremental owned/frontier
  /// bookkeeping consistent with a from-scratch recomputation (the greedy
  /// loop trusts those numbers for every move decision) and (b) actually
  /// close the hot/cold gap on a skewed assignment.
  #[test]
  fn rebalance_static_balances_and_bookkeeping_is_exact() {
    // 12 blocks, sizes 1000..12000, a producer chain i -> i+1, all
    // initially dumped into shard 0 of 3.
    let mut b = ProfileBuilder::new();
    for i in 1..=12u8 {
      b.block(addr(i), 0, 1000 * u32::from(i), 1, OpCounts::default());
    }
    for i in 1..12u8 {
      b.delta_edge(addr(i), addr(i + 1));
    }
    let p = b.finish();
    let mut shard_of = vec![0u32; 12];
    let moves = rebalance_static(&p, &mut shard_of, 3);
    assert!(moves > 0, "skewed assignment must produce moves");
    let costs = static_predicted_costs(&p, &shard_of, 3);
    let mean = costs.iter().sum::<f64>() / 3.0;
    let gap = costs.iter().fold(0.0f64, |m, &c| m.max(c))
      - costs.iter().fold(f64::INFINITY, |m, &c| m.min(c));
    // The loop exits either within 1% of the mean or when no single move
    // helps; on this fixture the largest block (12000 bytes) bounds the
    // achievable gap — assert we got under that, not stuck near the start.
    assert!(
      gap <= static_owned_weight(12000) + STATIC_FRONTIER_PER_BYTE * 12000.0,
      "gap {gap} vs mean {mean}: rebalance made no progress"
    );
    // Every shard non-empty (nothing collapsed to zero).
    for k in 0..3u32 {
      assert!(shard_of.contains(&k), "shard {k} emptied");
    }
    // Bookkeeping exactness via idempotence: a second pass rebuilds its
    // owned/frontier state from scratch, so if the first pass's incremental
    // accounting was truthful, its stopping condition also holds on fresh
    // state and the second pass has nothing to do. Drifted bookkeeping
    // would leave the second pass a real gap to close.
    let again = rebalance_static(&p, &mut shard_of, 3);
    assert_eq!(
      again, 0,
      "second pass moved {again} blocks — bookkeeping drift"
    );
  }

  #[test]
  fn static_seed_model_scales_by_score_and_budget() {
    // 400 GiB calibration points from the 2026-08-28 sweep. Init and ISLB
    // are the small/mid-size knees; Mathlib is the normalization point. FLT
    // records the large-env extrapolation, not an optimum (its old corrected
    // leaf count depended on the previous seed). These are scores, not raw
    // env bytes.
    assert_eq!(static_seed_shards_for_score(6.010e12, 400), 8); // Init
    assert_eq!(static_seed_shards_for_score(1.536e13, 400), 23); // ISLB
    assert_eq!(
      static_seed_shards_for_score(STATIC_SEED_REFERENCE_SCORE, 400),
      233
    );
    assert_eq!(static_seed_shards_for_score(1.316e14, 400), 246); // FLT

    // The 100 GiB calibration keeps broad split correction out of Init and
    // ISLB without the 1.36 experiment's over-sharding.
    assert_eq!(static_seed_shards_for_score(6.010e12, 100), 43); // Init
    assert_eq!(static_seed_shards_for_score(1.536e13, 100), 122); // ISLB
    assert_eq!(
      static_seed_shards_for_score(STATIC_SEED_REFERENCE_SCORE, 100),
      1230
    );

    // An empty or vanishingly small score still produces a usable one-shard
    // seed.
    assert_eq!(static_seed_shards_for_score(0.0, 400), 1);
  }

  #[test]
  fn static_env_score_distinguishes_block_shape() {
    let mut concentrated = ProfileBuilder::new();
    concentrated.block(addr(1), 0, 4000, 1, OpCounts::default());

    let mut spread = ProfileBuilder::new();
    for i in 1..=4u8 {
      spread.block(addr(i), 0, 1000, 1, OpCounts::default());
    }

    assert!(
      static_env_score(&concentrated.finish())
        > static_env_score(&spread.finish())
    );
  }

  #[test]
  fn static_seed_count_never_exceeds_atomic_blocks() {
    let mut b = ProfileBuilder::new();
    for i in 1..=6u8 {
      // Force the uncapped estimate far above six shards.
      b.block(addr(i), 0, u32::MAX, 1, OpCounts::default());
    }
    let p = b.finish();
    assert_eq!(static_seed_shards(&p, 1), p.num_blocks());
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
        b.block(addr(base + k), 100, 500, 1, ops(100));
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
    b.block(addr(1), 30_000, 100, 1, ops(30_000)); // ~30x a light block
    for i in 2..=65u8 {
      b.block(addr(i), 1000, 100, 1, ops(1000));
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
      b.block(addr_u32(i + 1), 100, 1000, 1, ops(100));
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
    b.block(addr_u32(1), 5_000_000, 100, 1, ops(5_000_000)); // the giant
    for i in 2..=m {
      b.block(addr_u32(i), 1000, 100, 1, ops(1000));
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

  #[test]
  fn manifest_writer_prunes_empty_shards_and_contracts_tree() {
    let p = two_clusters();
    // Keep the two clusters in old shards 0 and 2, deliberately leaving shard
    // 1 empty. Serialization must emit dense ids 0/1 and contract leaf 1.
    let shard_of = vec![0, 0, 0, 2, 2, 2];
    let tree = node(leaf(0), node(leaf(1), leaf(2)));
    let m = ShardManifest::build(&p, &shard_of, 3).with_tree(tree);
    assert!(m.shards[1].blocks.is_empty());

    let q = ShardManifest::from_bytes(&m.to_bytes()).unwrap();
    assert_eq!(q.num_shards, 2);
    assert_eq!(q.shards.len(), 2);
    assert_eq!(
      q.shards.iter().map(|shard| shard.id).collect::<Vec<_>>(),
      vec![0, 1]
    );
    assert!(q.shards.iter().all(|shard| !shard.blocks.is_empty()));
    assert_eq!(q.tree, Some(node(leaf(0), leaf(1))));
  }

  fn three_way() -> (BlockProfile, ShardManifest) {
    let p = two_clusters();
    let shard_of = vec![0, 0, 1, 1, 2, 2];
    let tree = node(leaf(0), node(leaf(1), leaf(2)));
    let mut m = ShardManifest::build(&p, &shard_of, 3).with_tree(tree);
    for sh in &mut m.shards {
      sh.assumption_root =
        crate::merkle::merkle_root_canonical(&sh.foreign_blocks);
    }
    (p, m)
  }

  fn halves(blocks: &[Address]) -> Vec<Vec<Address>> {
    let (a, b) = blocks.split_at(blocks.len() / 2);
    vec![a.to_vec(), b.to_vec()]
  }

  #[test]
  fn balanced_matches_lean_balanced_range() {
    fn check(t: &AggNode, ids: &[u32]) {
      let mut leaves = Vec::new();
      t.collect_leaves(&mut leaves);
      assert_eq!(leaves, ids);
      if let AggNode::Internal(l, r) = t {
        assert_eq!(l.num_leaves(), ids.len() / 2);
        check(l, &ids[..ids.len() / 2]);
        check(r, &ids[ids.len() / 2..]);
      } else {
        assert_eq!(ids.len(), 1);
      }
    }
    assert_eq!(AggNode::balanced(&[]), None);
    for n in 1..=9u32 {
      let ids: Vec<u32> = (10..10 + n).collect();
      check(&AggNode::balanced(&ids).unwrap(), &ids);
    }
  }

  #[test]
  fn replace_leaf_keeps_siblings() {
    let t = node(leaf(0), node(leaf(1), leaf(2)));
    let sub = node(leaf(1), leaf(3));
    assert_eq!(
      t.replace_leaf(1, &sub),
      node(leaf(0), node(node(leaf(1), leaf(3)), leaf(2)))
    );
    assert_eq!(t.replace_leaf(7, &sub), t);
  }

  #[test]
  fn refine_replaces_one_leaf_keeps_others_identical() {
    let (p, m) = three_way();
    let parts = halves(&m.shards[1].blocks);
    let r = LeafRefinement { id: 1, parts, part_peaks: vec![10, 20] };
    let (q, ids) = m.refine(&p, &[r], &[]).unwrap();
    assert_eq!(ids, vec![vec![1, 3]]);
    assert_eq!(q.num_shards, 4);
    assert_eq!(q.shards.iter().map(|s| s.id).collect::<Vec<_>>(), [0, 1, 2, 3]);
    // Untouched leaves: same record, sealed the same way.
    let mut sealed = q.clone();
    for sh in &mut sealed.shards {
      sh.assumption_root =
        crate::merkle::merkle_root_canonical(&sh.foreign_blocks);
    }
    assert_eq!(sealed.shards[0], m.shards[0]);
    assert_eq!(sealed.shards[2], m.shards[2]);
    // The split leaf: part 0 keeps id 1, part 1 is appended as id 3.
    assert_eq!(q.shards[1].blocks, m.shards[1].blocks[..1]);
    assert_eq!(q.shards[3].blocks, m.shards[1].blocks[1..]);
    assert_eq!(q.shards[1].measured_peak_bytes, 10);
    assert_eq!(q.shards[3].measured_peak_bytes, 20);
    assert_eq!(
      q.tree,
      Some(node(leaf(0), node(node(leaf(1), leaf(3)), leaf(2))))
    );
    // Round trip keeps the tree and the peaks.
    let back = ShardManifest::from_bytes(&sealed.to_bytes()).unwrap();
    assert_eq!(back, sealed);
  }

  #[test]
  fn bisect_leaves_preserves_other_claims_and_repeated_splits_progress() {
    let (profile, original) = three_way();
    let (refined, ids) = original.bisect_leaves(&profile, &[1]).unwrap();
    assert_eq!(ids, vec![vec![1, 3]]);
    assert_eq!(refined.shards[0], original.shards[0]);
    assert_eq!(refined.shards[2], original.shards[2]);
    let mut before = original.shards[1].blocks.clone();
    before.sort_unstable();
    let mut after = refined.shards[1].blocks.clone();
    after.extend_from_slice(&refined.shards[3].blocks);
    after.sort_unstable();
    assert_eq!(before, after);
    assert!(refined.shards[1].blocks.len() < before.len());
    assert!(refined.shards[3].blocks.len() < before.len());
    assert_eq!(
      refined.tree,
      original
        .tree
        .as_ref()
        .map(|tree| tree.replace_leaf(1, &node(leaf(1), leaf(3))))
    );
    assert_eq!(
      ShardManifest::from_bytes(&refined.to_bytes()).unwrap(),
      refined
    );
    assert!(
      refined
        .bisect_leaves(&profile, &[1])
        .unwrap_err()
        .contains("atomic block")
    );
    assert!(
      original
        .bisect_leaves(&profile, &[99])
        .unwrap_err()
        .contains("missing shard")
    );
    assert!(
      original
        .bisect_leaves(&profile, &[1, 1])
        .unwrap_err()
        .contains("listed twice")
    );
  }

  #[test]
  fn bisect_leaves_handles_several_oversized_claims_in_one_pass() {
    let (profile, original) = three_way();
    let (refined, ids) = original.bisect_leaves(&profile, &[0, 2]).unwrap();
    assert_eq!(ids, vec![vec![0, 3], vec![2, 4]]);
    assert_eq!(refined.shards[1], original.shards[1]);
    let mut blocks: Vec<_> =
      refined.shards.iter().flat_map(|s| s.blocks.clone()).collect();
    blocks.sort_unstable();
    let mut expected: Vec<_> =
      profile.blocks().iter().map(|b| b.addr.clone()).collect();
    expected.sort_unstable();
    assert_eq!(blocks, expected);
    assert_eq!(refined.num_shards, original.num_shards + 2);
  }

  #[test]
  fn refine_id_policy_reuse_then_append() {
    let (p, m) = three_way();
    let r0 = LeafRefinement {
      id: 0,
      parts: halves(&m.shards[0].blocks),
      part_peaks: vec![0, 0],
    };
    let r2 = LeafRefinement {
      id: 2,
      parts: halves(&m.shards[2].blocks),
      part_peaks: vec![0, 0],
    };
    // Order of the refinement list does not matter: fresh ids ascend by
    // refined leaf id.
    let (q, ids) = m.refine(&p, &[r2.clone(), r0.clone()], &[]).unwrap();
    assert_eq!(ids, vec![vec![2, 4], vec![0, 3]]);
    assert_eq!(q.shards[0].blocks, r0.parts[0]);
    assert_eq!(q.shards[3].blocks, r0.parts[1]);
    assert_eq!(q.shards[2].blocks, r2.parts[0]);
    assert_eq!(q.shards[4].blocks, r2.parts[1]);
    let mut sealed = q.clone();
    for sh in &mut sealed.shards {
      sh.assumption_root =
        crate::merkle::merkle_root_canonical(&sh.foreign_blocks);
    }
    assert_eq!(sealed.shards[1], m.shards[1]);
    assert_eq!(
      q.tree,
      Some(node(node(leaf(0), leaf(3)), node(leaf(1), node(leaf(2), leaf(4)))))
    );
  }

  #[test]
  fn refine_empty_is_fixed_point_and_carries_peaks() {
    let (p, mut m) = three_way();
    m.shards[1].measured_peak_bytes = 7;
    let (q, ids) = m.refine(&p, &[], &[]).unwrap();
    assert!(ids.is_empty());
    let mut sealed = q;
    for sh in &mut sealed.shards {
      sh.assumption_root =
        crate::merkle::merkle_root_canonical(&sh.foreign_blocks);
    }
    assert_eq!(sealed.to_bytes(), m.to_bytes());
    // A nonzero measurement overrides a carried peak; zero keeps it.
    let (q2, _) = m.refine(&p, &[], &[5, 0, 9]).unwrap();
    assert_eq!(
      q2.shards.iter().map(|s| s.measured_peak_bytes).collect::<Vec<_>>(),
      [5, 7, 9]
    );
  }

  #[test]
  fn refine_without_source_tree_uses_balanced_range() {
    let (p, mut m) = three_way();
    m.tree = None;
    let r = LeafRefinement {
      id: 2,
      parts: halves(&m.shards[2].blocks),
      part_peaks: vec![0, 0],
    };
    let (q, _) = m.refine(&p, &[r], &[]).unwrap();
    // balancedRange 0 3 = node(leaf 0, node(leaf 1, leaf 2)), then leaf 2 →
    // node(leaf 2, leaf 3).
    assert_eq!(
      q.tree,
      Some(node(leaf(0), node(leaf(1), node(leaf(2), leaf(3)))))
    );
  }

  #[test]
  fn refine_rejects_bad_partitions() {
    let (p, m) = three_way();
    let blocks = m.shards[1].blocks.clone();
    let err = |r: LeafRefinement, measured: &[u64]| {
      m.refine(&p, &[r], measured).unwrap_err()
    };
    let one = LeafRefinement {
      id: 1,
      parts: vec![blocks.clone()],
      part_peaks: vec![0],
    };
    assert!(err(one, &[]).contains("at least two parts"));
    let oor =
      LeafRefinement { id: 9, parts: halves(&blocks), part_peaks: vec![0, 0] };
    assert!(err(oor, &[]).contains("out of range"));
    let foreign = LeafRefinement {
      id: 1,
      parts: vec![vec![blocks[0].clone()], vec![addr(200)]],
      part_peaks: vec![0, 0],
    };
    assert!(err(foreign, &[]).contains("not in the env's block profile"));
    let dup = LeafRefinement {
      id: 1,
      parts: vec![vec![blocks[0].clone()], vec![blocks[0].clone()]],
      part_peaks: vec![0, 0],
    };
    assert!(err(dup, &[]).contains("appears in shards"));
    let missing = LeafRefinement {
      id: 1,
      parts: vec![vec![blocks[0].clone()], vec![m.shards[0].blocks[0].clone()]],
      part_peaks: vec![0, 0],
    };
    let e = err(missing, &[]);
    assert!(e.contains("appears in shards") || e.contains("missing"), "{e}");
    let peaks =
      LeafRefinement { id: 1, parts: halves(&blocks), part_peaks: vec![0] };
    assert!(err(peaks, &[]).contains("peaks for"));
    let ok =
      LeafRefinement { id: 1, parts: halves(&blocks), part_peaks: vec![0, 0] };
    assert!(err(ok, &[1, 2]).contains("measured peaks"));
  }

  #[test]
  fn manifest_rejects_tree_shard_mismatch() {
    let p = two_clusters();
    let h = Hypergraph::from_profile(&p);
    let (shard_of, _) = h.partition_with_tree(2, 0.10);
    let m = ShardManifest::build(&p, &shard_of, 2);
    // Tree missing shard 1: that shard's proof would be silently dropped
    // from the fold.
    let err =
      ShardManifest::from_bytes(&m.clone().with_tree(leaf(0)).to_bytes())
        .unwrap_err();
    assert!(err.contains("do not match"), "got: {err}");
    // Tree duplicating a shard id is equally invalid.
    let err = ShardManifest::from_bytes(
      &m.clone().with_tree(node(leaf(0), leaf(0))).to_bytes(),
    )
    .unwrap_err();
    assert!(err.contains("do not match"), "got: {err}");
    // Tree naming a shard id outside the manifest is invalid.
    let err = ShardManifest::from_bytes(
      &m.with_tree(node(leaf(0), leaf(7))).to_bytes(),
    )
    .unwrap_err();
    assert!(err.contains("do not match"), "got: {err}");
  }
}
