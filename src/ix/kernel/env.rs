//! Zero kernel environment.
//!
//! `KEnv<M>` maps `KId<M>` to `KConst<M>`, and owns all shared kernel state:
//! the intern table, type-checking caches, and resolved primitives.
//!
//! All mutable state uses `DashMap`/`DashSet` for lock-free concurrent access.
//! Multiple `TypeChecker` instances can share one `Arc<KEnv>` and run in parallel.

use std::collections::{BTreeSet, HashSet};
use std::sync::{Arc, Condvar, LazyLock, Mutex, OnceLock};
use std::time::Instant;

use dashmap::{DashMap, DashSet};
use rayon::iter::{IntoParallelIterator, ParallelIterator};

use crate::ix::address::Address;

use super::constant::{KConst, RecRule};
use super::error::TcError;
use super::expr::KExpr;
use super::id::KId;
use super::level::KUniv;
use super::mode::KernelMode;
use super::perf::PerfCounters;
use super::primitive::Primitives;

/// Shared Merkle hash. Cheap to clone (Arc refcount bump).
pub type Addr = Arc<blake3::Hash>;

/// Process-wide hash-cons for [`Addr`]. Interning makes
/// `Arc::ptr_eq(a, b)` an exact equivalence to `**a == **b`, which is
/// the basis for [`KExpr::hash_eq`](super::expr::KExpr::hash_eq)'s 8-byte
/// pointer fast path before the 32-byte Blake3 fallback (audit Tier 1 #1
/// in `plans/kernel-perf-adversarial-audit-2026-04-26.md` §6.1).
///
/// We use a process-global `DashMap` rather than per-`KEnv` interning so
/// the change is local to `mk_info` (`expr.rs`) and the universe info
/// helper (`level.rs`); threading an `&InternTable` through every
/// `KExpr::var`/`sort`/etc. constructor would touch 300+ call sites for
/// no observable benefit (KEnvs don't outlive the process and the Addr
/// content space is the same regardless of which session created it).
///
/// Memory cost: one [`Addr`] entry per distinct content hash for the
/// lifetime of the process. A typical kernel-check-env run holds a few
/// million distinct hashes, so on the order of 10s of MB; trivially
/// dominated by the constants table itself.
static ADDR_INTERN: LazyLock<DashMap<blake3::Hash, Addr>> =
  LazyLock::new(DashMap::default);

/// Return the canonical [`Addr`] for `hash`. After this returns, every
/// caller that interns the same content gets the same `Arc` allocation —
/// `Arc::ptr_eq` between any two interned addresses is iff their hashes
/// are equal.
///
/// Atomic via `DashMap::entry`; safe under parallel ingress and
/// type-checking.
#[inline]
pub fn intern_addr(hash: blake3::Hash) -> Addr {
  ADDR_INTERN.entry(hash).or_insert_with(|| Arc::new(hash)).value().clone()
}

/// Hash-consing intern table for expressions and universes.
///
/// Thread-safe via `DashMap`: usable from parallel ingress and
/// sequential type checking alike. Guarantees pointer uniqueness
/// by blake3 hash: `ptr(a) == ptr(b)` iff `hash(a) == hash(b)`.
pub struct InternTable<M: KernelMode> {
  univs: DashMap<blake3::Hash, KUniv<M>>,
  exprs: DashMap<blake3::Hash, KExpr<M>>,
}

impl<M: KernelMode> Default for InternTable<M> {
  fn default() -> Self {
    Self::new()
  }
}

impl<M: KernelMode> InternTable<M> {
  pub fn new() -> Self {
    InternTable { univs: DashMap::default(), exprs: DashMap::default() }
  }

  /// Intern a universe: if one with the same hash exists, return the
  /// existing Arc (ensuring pointer uniqueness). Otherwise insert and return.
  /// Atomic via DashMap entry — safe for concurrent access.
  pub fn intern_univ(&self, u: KUniv<M>) -> KUniv<M> {
    let key = **u.addr();
    self.univs.entry(key).or_insert(u).value().clone()
  }

  /// Intern an expression: same pointer-uniqueness guarantee as `intern_univ`.
  pub fn intern_expr(&self, e: KExpr<M>) -> KExpr<M> {
    let key = **e.addr();
    self.exprs.entry(key).or_insert(e).value().clone()
  }
}

/// Generated recursor, cached after inductive validation.
#[derive(Clone, Debug)]
pub struct GeneratedRecursor<M: KernelMode> {
  pub ind_addr: Address,
  pub ty: KExpr<M>,
  pub rules: Vec<RecRule<M>>,
}

/// Which nested-auxiliary order generated recursor validation should use.
///
/// Lean's original environment emits nested auxiliary recursors in the
/// source/queue order used by `elim_nested_inductive_fn`. Ix's compiled
/// environment canonicalizes the aux portion with `sort_consts` partition
/// refinement, so its stored recursors must be regenerated in canonical order.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RecursorAuxOrder {
  Source,
  Canonical,
}

/// Result of entering the block-check coordinator.
pub enum BlockCheckStart<M: KernelMode> {
  /// A finished result was already cached, or another owner finished while
  /// this caller waited.
  Cached(Result<(), TcError<M>>),
  /// This caller owns the check and must publish the result.
  Owner(BlockCheckToken<M>),
}

/// Ownership token for a block currently being checked.
pub struct BlockCheckToken<M: KernelMode> {
  block: KId<M>,
}

/// The global zero kernel environment.
///
/// Thread-safe via `DashMap`/`DashSet`: supports concurrent reads and writes
/// from multiple `TypeChecker` instances running in parallel. Contains all
/// shared kernel state: constants, intern table, and type-checking caches.
///
/// `get()` returns owned `KConst`/`Vec` (cheap Arc clones) to avoid
/// holding DashMap guards across call boundaries.
pub struct KEnv<M: KernelMode> {
  // -- Constants --
  /// Loaded constants keyed by `KId`.
  pub consts: DashMap<KId<M>, KConst<M>>,
  /// Block membership: block id → ordered member ids.
  pub blocks: DashMap<KId<M>, Vec<KId<M>>>,

  // -- Intern table (hash-consing for pointer dedup) --
  pub intern: InternTable<M>,

  // -- Primitives (resolved lazily from consts) --
  prims: OnceLock<Primitives<M>>,

  // -- Global caches (grow monotonically, keyed by content hash) --
  // All cache keys use `Addr` (= `Arc<blake3::Hash>`, content-addressed) rather
  // than `Arc::as_ptr` pointers, avoiding the ABA problem where deallocated
  // pointers are reused by the allocator for semantically different expressions.
  /// WHNF cache (full, with delta): (expr_hash, ctx_hash)-keyed.
  pub whnf_cache: DashMap<(Addr, Addr), KExpr<M>>,
  /// WHNF cache (no delta): (expr_hash, ctx_hash)-keyed.
  pub whnf_no_delta_cache: DashMap<(Addr, Addr), KExpr<M>>,
  /// WHNF core cache: structural-only reduction (beta/iota/zeta/proj),
  /// no native primitives, no delta. Mirrors lean4lean's `whnfCoreCache`
  /// (refs/lean4lean/Lean4Lean/TypeChecker.lean:19) and lean4 C++'s
  /// `m_whnf_core`. Populated only when flags are FULL — cheap-projection
  /// results are not safe to share with full callers.
  pub whnf_core_cache: DashMap<(Addr, Addr), KExpr<M>>,
  /// Infer cache: keyed by (expr_hash, ctx_hash). Context-dependent.
  /// Populated only from full-mode `infer` (i.e. not from `with_infer_only`),
  /// so every cached result has passed the validation `infer_only` skips.
  /// Both modes read from this same cache — an `infer_only` lookup happily
  /// consumes a full-mode result since it's strictly stronger.
  pub infer_cache: DashMap<(Addr, Addr), KExpr<M>>,
  /// Infer-only cache: keyed like `infer_cache`, but populated only by
  /// `with_infer_only` synthesis and read only while infer-only is active.
  /// This keeps unchecked results out of the validated full-mode cache while
  /// still sharing repeated proof-irrelevance/projection probes.
  pub infer_only_cache: DashMap<(Addr, Addr), KExpr<M>>,
  /// Full def-eq cache: keyed by (expr_hash, expr_hash, ctx_hash).
  /// Context-dependent. Entries in this cache are valid for both full and
  /// cheap def-eq callers.
  pub def_eq_cache: DashMap<(Addr, Addr, Addr), bool>,
  /// Cheap def-eq cache: same key as `def_eq_cache`, but only for comparisons
  /// performed inside cheap projection reductions. Cheap `false` can be a
  /// full-mode false negative, so those entries must not be visible to full
  /// callers.
  pub def_eq_cheap_cache: DashMap<(Addr, Addr, Addr), bool>,
  /// Failed def-eq pairs in lazy delta: canonical ordering by hash.
  pub def_eq_failure: DashSet<(Addr, Addr, Addr)>,
  /// Constant-instantiation cache: caches the result of
  /// `instantiate_univ_params(val, us)` for each `Const(id, us)` head encountered
  /// during delta unfolding. Keyed by the head expression's content hash, which
  /// already content-addresses `(id, us)` (the head's address derives from id +
  /// universe args). Mirrors lean4 C++ `m_unfold` cache. Cross-call sharing of
  /// universe-substituted bodies eliminates O(body) walks on every unfold.
  pub unfold_cache: DashMap<Addr, KExpr<M>>,
  /// Ingress cache: LeanExpr → KExpr conversion results.
  /// Keyed by (expr_hash, param_names_hash) to account for different
  /// level param bindings producing different KExprs from the same LeanExpr.
  pub ingress_cache: DashMap<(Addr, Addr), KExpr<M>>,
  /// Generated recursors, keyed by inductive Muts block id.
  pub recursor_cache: DashMap<KId<M>, Vec<GeneratedRecursor<M>>>,
  /// Nested-auxiliary order expected by stored recursors in this environment.
  pub recursor_aux_order: RecursorAuxOrder,
  /// Maps the set of major inductive KIds to the inductive block id.
  pub rec_majors_cache: DashMap<BTreeSet<KId<M>>, KId<M>>,
  /// Mutual-block peer-agreement cache: records block ids whose peers have
  /// already been verified to share the same universe (S3) and parameter
  /// prefix (S3b). Populated by `check_inductive` after the per-peer loop
  /// succeeds; collapses the naturally O(N²) per-peer iteration to O(N)
  /// total work per block across all the peers' individual checks.
  pub block_peer_agreement_cache: DashSet<KId<M>>,
  /// Whole-block type-check results. Both successes and failures are cached,
  /// so every member of a bad block reports the same structured failure.
  pub block_check_results: DashMap<KId<M>, Result<(), TcError<M>>>,
  /// Blocks currently owned by a checker thread.
  pub block_checks_in_progress: Mutex<HashSet<KId<M>>>,
  /// Waiters park here while another thread checks their block.
  pub block_check_cv: Condvar,

  // -- Performance counters (audit §10) --
  /// Cache hit/miss and fuel-consumption counters, gated by
  /// `IX_PERF_COUNTERS=1`. When the env var is unset the counters are
  /// no-ops; when set, the totals are dumped from the `Drop` impl below.
  pub perf: PerfCounters,
}

impl<M: KernelMode> Default for KEnv<M> {
  fn default() -> Self {
    Self::new()
  }
}

/// Dump performance counters when the env is dropped, but only when
/// `IX_PERF_COUNTERS=1` is set. This piggybacks on `KEnv`'s natural
/// teardown (e.g. at the end of `rs_kernel_check_consts`) so any harness
/// that drives a check-env run picks up the totals automatically.
///
/// Then tear down the heavy `DashMap` fields in parallel across their shards.
/// A fully-loaded `KEnv` after a mathlib-scale ingress holds millions of
/// `Arc<ExprData>` / `Arc<UnivData>` allocations across its `consts` map,
/// `intern` table, and (post type-check) WHNF/infer caches. The default
/// `drop(DashMap)` walks shards single-threaded, taking ~200s; using
/// `into_par_iter().for_each(drop)` brings that to seconds. `mem::take`
/// pulls each `DashMap` out into a local that we then parallel-drop;
/// the now-empty `Default` left in `*self` drops trivially when this
/// function returns.
///
/// Set `IX_SEQ_KENV_DROP=1` to fall back to the old single-threaded path
/// for measurement comparisons.
impl<M: KernelMode> Drop for KEnv<M> {
  fn drop(&mut self) {
    if super::perf::enabled() {
      let summary = self.perf.summary();
      if !summary.is_empty() {
        eprint!("{summary}");
      }
    }

    if std::env::var_os("IX_SEQ_KENV_DROP").is_some() {
      // Skip the parallel teardown — let the auto-derived field drops run
      // sequentially as before.
      return;
    }

    let quiet = std::env::var_os("IX_QUIET").is_some();
    let total_start = Instant::now();

    // Snapshot lengths up-front for logging before we move the maps out.
    let consts_len = self.consts.len();
    let blocks_len = self.blocks.len();
    let intern_exprs_len = self.intern.exprs.len();
    let intern_univs_len = self.intern.univs.len();
    let ingress_cache_len = self.ingress_cache.len();
    let whnf_total = self.whnf_cache.len()
      + self.whnf_no_delta_cache.len()
      + self.whnf_core_cache.len();
    let infer_total = self.infer_cache.len() + self.infer_only_cache.len();
    // Only log when the env actually held something — empty
    // create-and-immediately-drop sites in the compile/ingress pipeline
    // would otherwise produce noisy `0.00s ... 0/0 ...` lines.
    let nonempty = consts_len
      + blocks_len
      + intern_exprs_len
      + intern_univs_len
      + ingress_cache_len
      + whnf_total
      + infer_total
      > 0;

    // Drop each heavy DashMap/DashSet in parallel via rayon work-stealing
    // across shards. Maps are dropped sequentially with respect to each
    // other so we don't fight for the global rayon pool; each one
    // saturates the pool internally.
    //
    // Order doesn't matter for correctness — shared `Arc` content is
    // refcounted, and the last decrementer destroys exactly once.
    let consts_start = Instant::now();
    std::mem::take(&mut self.consts).into_par_iter().for_each(drop);
    let consts_ns = consts_start.elapsed();

    let blocks_start = Instant::now();
    std::mem::take(&mut self.blocks).into_par_iter().for_each(drop);
    let blocks_ns = blocks_start.elapsed();

    let intern_start = Instant::now();
    std::mem::take(&mut self.intern.univs).into_par_iter().for_each(drop);
    std::mem::take(&mut self.intern.exprs).into_par_iter().for_each(drop);
    let intern_ns = intern_start.elapsed();

    let caches_start = Instant::now();
    std::mem::take(&mut self.whnf_cache).into_par_iter().for_each(drop);
    std::mem::take(&mut self.whnf_no_delta_cache)
      .into_par_iter()
      .for_each(drop);
    std::mem::take(&mut self.whnf_core_cache).into_par_iter().for_each(drop);
    std::mem::take(&mut self.infer_cache).into_par_iter().for_each(drop);
    std::mem::take(&mut self.infer_only_cache)
      .into_par_iter()
      .for_each(drop);
    std::mem::take(&mut self.def_eq_cache).into_par_iter().for_each(drop);
    std::mem::take(&mut self.def_eq_cheap_cache)
      .into_par_iter()
      .for_each(drop);
    std::mem::take(&mut self.def_eq_failure).into_par_iter().for_each(drop);
    std::mem::take(&mut self.unfold_cache).into_par_iter().for_each(drop);
    std::mem::take(&mut self.ingress_cache).into_par_iter().for_each(drop);
    std::mem::take(&mut self.recursor_cache).into_par_iter().for_each(drop);
    std::mem::take(&mut self.rec_majors_cache).into_par_iter().for_each(drop);
    std::mem::take(&mut self.block_peer_agreement_cache)
      .into_par_iter()
      .for_each(drop);
    std::mem::take(&mut self.block_check_results)
      .into_par_iter()
      .for_each(drop);
    let caches_ns = caches_start.elapsed();

    if !quiet && nonempty {
      eprintln!(
        "[kenv_drop] {:.2}s parallel threads={} \
         (consts {:.2}s/{} blocks {:.2}s intern {:.2}s/{}+{} \
         caches {:.2}s/whnf={} infer={} ingress={})",
        total_start.elapsed().as_secs_f32(),
        rayon::current_num_threads(),
        consts_ns.as_secs_f32(),
        consts_len,
        blocks_ns.as_secs_f32(),
        intern_ns.as_secs_f32(),
        intern_univs_len,
        intern_exprs_len,
        caches_ns.as_secs_f32(),
        whnf_total,
        infer_total,
        ingress_cache_len,
      );
    }
  }
}

impl<M: KernelMode> KEnv<M> {
  pub fn new() -> Self {
    Self::new_with_recursor_aux_order(RecursorAuxOrder::Canonical)
  }

  pub fn new_with_recursor_aux_order(
    recursor_aux_order: RecursorAuxOrder,
  ) -> Self {
    KEnv {
      consts: DashMap::default(),
      blocks: DashMap::default(),
      intern: InternTable::new(),
      prims: OnceLock::new(),
      whnf_cache: DashMap::default(),
      whnf_no_delta_cache: DashMap::default(),
      whnf_core_cache: DashMap::default(),
      infer_cache: DashMap::default(),
      infer_only_cache: DashMap::default(),
      def_eq_cache: DashMap::default(),
      def_eq_cheap_cache: DashMap::default(),
      def_eq_failure: DashSet::default(),
      unfold_cache: DashMap::default(),
      ingress_cache: DashMap::default(),
      recursor_cache: DashMap::default(),
      recursor_aux_order,
      rec_majors_cache: DashMap::default(),
      block_peer_agreement_cache: DashSet::default(),
      block_check_results: DashMap::default(),
      block_checks_in_progress: Mutex::new(HashSet::new()),
      block_check_cv: Condvar::new(),
      perf: PerfCounters::default(),
    }
  }

  /// Resolve primitives from the environment (cached via OnceLock).
  pub fn prims(&self) -> &Primitives<M> {
    self.prims.get_or_init(|| Primitives::from_env(self))
  }

  /// Pre-initialize the primitives cache with an externally-resolved
  /// `Primitives<M>`. Returns `Ok(())` on success, `Err(p)` if `prims()`
  /// has already been called (the OnceLock is full).
  ///
  /// Used by `lean_ingress` to install `Primitives::from_env_orig`
  /// (LEON-addressed) before any `TypeChecker::new(orig_kenv)` triggers
  /// the default canonical-addressed `from_env`.
  ///
  /// `Primitives<M>` is large (~2 KB), so the error path is allowed to be
  /// big — the caller hands ownership in and only retrieves it on failure.
  #[allow(clippy::result_large_err)]
  pub fn set_prims(&self, p: Primitives<M>) -> Result<(), Primitives<M>> {
    self.prims.set(p)
  }

  pub fn get(&self, id: &KId<M>) -> Option<KConst<M>> {
    self.consts.get(id).map(|r| r.value().clone())
  }

  pub fn insert(&self, id: KId<M>, c: KConst<M>) {
    if let Some(marker) = super::primitive::reserved_marker_name(&id.addr) {
      panic!(
        "attempted to insert {id} at reserved kernel marker address {marker} ({})",
        id.addr.hex()
      );
    }
    self.consts.insert(id, c);
  }

  pub fn len(&self) -> usize {
    self.consts.len()
  }

  pub fn is_empty(&self) -> bool {
    self.consts.is_empty()
  }

  pub fn contains_key(&self, id: &KId<M>) -> bool {
    self.consts.contains_key(id)
  }

  /// Iterate over all constants. Returns owned (KId, KConst) pairs.
  /// Internally snapshots the DashMap — safe for concurrent access.
  pub fn iter(&self) -> impl Iterator<Item = (KId<M>, KConst<M>)> + '_ {
    self.consts.iter().map(|r| (r.key().clone(), r.value().clone()))
  }

  /// Get block members. Returns owned Vec (cheap KId clones).
  pub fn get_block(&self, id: &KId<M>) -> Option<Vec<KId<M>>> {
    self.blocks.get(id).map(|r| r.value().clone())
  }

  /// Insert a block membership entry.
  pub fn insert_block(&self, id: KId<M>, members: Vec<KId<M>>) {
    self.blocks.insert(id, members);
  }

  /// Enter the shared whole-block checker.
  ///
  /// The first caller for `block` becomes owner. Concurrent callers wait on the
  /// condition variable until the owner publishes a cached result.
  pub fn begin_block_check(&self, block: &KId<M>) -> BlockCheckStart<M> {
    loop {
      if let Some(result) = self.block_check_results.get(block) {
        return BlockCheckStart::Cached(result.value().clone());
      }

      let mut in_progress = self.block_checks_in_progress.lock().unwrap();
      if let Some(result) = self.block_check_results.get(block) {
        return BlockCheckStart::Cached(result.value().clone());
      }
      if in_progress.insert(block.clone()) {
        return BlockCheckStart::Owner(BlockCheckToken {
          block: block.clone(),
        });
      }

      while in_progress.contains(block) {
        in_progress = self.block_check_cv.wait(in_progress).unwrap();
        if let Some(result) = self.block_check_results.get(block) {
          return BlockCheckStart::Cached(result.value().clone());
        }
      }
    }
  }

  /// Publish a completed block-check result and wake all waiters.
  ///
  /// The token is consumed deliberately: it's a one-shot RAII handle that
  /// must not be reused after publishing the result.
  #[allow(clippy::needless_pass_by_value)]
  pub fn finish_block_check(
    &self,
    token: BlockCheckToken<M>,
    result: Result<(), TcError<M>>,
  ) -> Result<(), TcError<M>> {
    self.block_check_results.insert(token.block.clone(), result.clone());
    let mut in_progress = self.block_checks_in_progress.lock().unwrap();
    in_progress.remove(&token.block);
    drop(in_progress);
    self.block_check_cv.notify_all();
    result
  }
}

#[cfg(test)]
mod tests {
  use super::super::mode::Anon;
  use super::super::primitive::PrimAddrs;
  use super::*;
  use crate::ix::address::Address;

  fn mk_addr(s: &str) -> Address {
    Address::hash(s.as_bytes())
  }

  fn mk_id(s: &str) -> KId<Anon> {
    KId::new(mk_addr(s), ())
  }

  fn mk_axio(_s: &str) -> KConst<Anon> {
    KConst::Axio {
      name: (),
      level_params: (),
      is_unsafe: false,
      lvls: 0,
      ty: KExpr::sort(KUniv::zero()),
    }
  }

  #[test]
  fn new_env_is_empty() {
    let env = KEnv::<Anon>::new();
    assert!(env.is_empty());
    assert_eq!(env.len(), 0);
  }

  #[test]
  fn insert_and_get() {
    let env = KEnv::<Anon>::new();
    let id = mk_id("Nat");
    env.insert(id.clone(), mk_axio("Nat"));
    assert_eq!(env.len(), 1);
    assert!(env.get(&id).is_some());
  }

  #[test]
  #[should_panic(expected = "reserved kernel marker")]
  fn insert_reserved_marker_panics() {
    let env = KEnv::<Anon>::new();
    let id = KId::new(PrimAddrs::new().eager_reduce, ());
    env.insert(id, mk_axio("eager_reduce"));
  }

  #[test]
  fn contains_key_works() {
    let env = KEnv::<Anon>::new();
    let id = mk_id("Nat");
    assert!(!env.contains_key(&id));
    env.insert(id.clone(), mk_axio("Nat"));
    assert!(env.contains_key(&id));
  }

  #[test]
  fn get_missing_returns_none() {
    let env = KEnv::<Anon>::new();
    assert!(env.get(&mk_id("missing")).is_none());
  }

  #[test]
  fn get_by_id_works() {
    let env = KEnv::<Anon>::new();
    let id = mk_id("Nat");
    env.insert(id.clone(), mk_axio("Nat"));
    assert!(env.get(&id).is_some());
    assert!(env.get(&mk_id("missing")).is_none());
  }

  #[test]
  fn intern_univ_dedup() {
    let it = InternTable::<Anon>::new();
    let z1 = KUniv::zero();
    let z2 = KUniv::zero();
    // Before interning, same hash but different Arcs
    assert!(!z1.ptr_eq(&z2));
    let i1 = it.intern_univ(z1);
    let i2 = it.intern_univ(z2);
    assert!(i1.ptr_eq(&i2));
  }

  #[test]
  fn intern_univ_different() {
    let it = InternTable::<Anon>::new();
    let z = it.intern_univ(KUniv::zero());
    let s = it.intern_univ(KUniv::succ(KUniv::zero()));
    assert!(!z.ptr_eq(&s));
  }

  #[test]
  fn intern_expr_dedup() {
    let it = InternTable::<Anon>::new();
    let v1 = KExpr::var(0, ());
    let v2 = KExpr::var(0, ());
    assert!(!v1.ptr_eq(&v2));
    let i1 = it.intern_expr(v1);
    let i2 = it.intern_expr(v2);
    assert!(i1.ptr_eq(&i2));
  }

  #[test]
  fn intern_expr_different() {
    let it = InternTable::<Anon>::new();
    let v0 = it.intern_expr(KExpr::var(0, ()));
    let v1 = it.intern_expr(KExpr::var(1, ()));
    assert!(!v0.ptr_eq(&v1));
  }

  #[test]
  fn iter_all_entries() {
    let env = KEnv::<Anon>::new();
    env.insert(mk_id("A"), mk_axio("A"));
    env.insert(mk_id("B"), mk_axio("B"));
    assert_eq!(env.iter().count(), 2);
  }
}
