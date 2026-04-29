//! Zero kernel environment.
//!
//! `KEnv<M>` maps `KId<M>` to `KConst<M>`, and owns all shared kernel state:
//! the intern table, type-checking caches, and resolved primitives.
//!
//! The environment is single-threaded. Worker pools own one `KEnv` per worker
//! and move parallelism above the kernel state boundary.

use std::collections::BTreeSet;

use rustc_hash::{FxHashMap, FxHashSet};
use std::cell::OnceCell;

use crate::ix::address::Address;

use super::constant::{KConst, RecRule};
use super::error::TcError;
use super::expr::KExpr;
use super::id::KId;
use super::level::KUniv;
use super::mode::KernelMode;
use super::perf::PerfCounters;
use super::primitive::Primitives;

/// Content-addressed Merkle hash. 32 bytes, `Copy`, no allocation.
///
/// Earlier revisions stored `Addr = Arc<blake3::Hash>` and threaded all
/// constructions through a process-global `DashMap` intern table to dedup
/// the inner allocation. On full-mathlib kernel-check runs that table grew
/// to 100M+ entries (≈8+ GiB) and dominated RSS, even though the per-worker
/// `KEnv` caches were correctly cleared per scheduled block. Switching to a
/// `Copy` value drops the global intern, eliminates one allocation per
/// `KExpr`/`KUniv` construction, and reduces per-`ExprData` overhead
/// from `Arc<Hash>` (8-byte pointer + 16-byte heap header + 32-byte
/// Hash) to a single in-place 32-byte field. Identity comparison falls
/// back from `Arc::ptr_eq` (single pointer compare) to a 32-byte memcmp,
/// which is a single AVX2 cycle on modern x86 and dominated by the
/// surrounding kernel work.
pub type Addr = blake3::Hash;

/// Hash-consing intern table for expressions and universes.
///
/// Single-threaded and owned by one `KEnv`. Guarantees pointer uniqueness
/// by blake3 hash within that environment: `ptr(a) == ptr(b)` iff
/// `hash(a) == hash(b)`.
///
/// Also owns reusable scratch buffers used by `subst`, `simul_subst`, and
/// `lift` to memoize content-addressed sub-traversals within a single
/// call. Allocating these as `FxHashMap::default()` per call shows up in
/// profiles for big mathlib blocks where beta/zeta reductions fire
/// millions of times; threading the scratch through the `&mut InternTable`
/// already passed for hash-consing eliminates the malloc/free churn while
/// keeping the per-call invariant (caches are cleared on entry).
pub struct InternTable<M: KernelMode> {
  pub(crate) univs: FxHashMap<blake3::Hash, KUniv<M>>,
  pub(crate) exprs: FxHashMap<blake3::Hash, KExpr<M>>,
  /// Scratch buffer for `subst` / `simul_subst` per-call memoization,
  /// keyed by `(addr, depth)`. Cleared on entry. Owned here so the
  /// allocation persists across calls.
  pub(crate) subst_scratch: FxHashMap<(Addr, u64), KExpr<M>>,
  /// Scratch buffer for `lift` per-call memoization, keyed by
  /// `(addr, cutoff)`. Cleared on entry. Separate from `subst_scratch`
  /// because `lift` is invoked from inside `subst_cached`, and the two
  /// caches have different semantics, so they must not share entries.
  pub(crate) lift_scratch: FxHashMap<(Addr, u64), KExpr<M>>,
}

impl<M: KernelMode> Default for InternTable<M> {
  fn default() -> Self {
    Self::new()
  }
}

impl<M: KernelMode> InternTable<M> {
  pub fn new() -> Self {
    InternTable {
      univs: FxHashMap::default(),
      exprs: FxHashMap::default(),
      subst_scratch: FxHashMap::default(),
      lift_scratch: FxHashMap::default(),
    }
  }

  /// Read-only fast path: return the canonical interned universe for
  /// `hash` if already present. Used by instrumented callers that want
  /// to record hit/miss separately; plain callers should use
  /// `intern_univ`.
  #[inline]
  pub fn try_get_univ(&self, hash: &blake3::Hash) -> Option<KUniv<M>> {
    self.univs.get(hash).cloned()
  }

  /// Read-only fast path counterpart of `try_get_univ` for expressions.
  #[inline]
  pub fn try_get_expr(&self, hash: &blake3::Hash) -> Option<KExpr<M>> {
    self.exprs.get(hash).cloned()
  }

  /// Intern a universe: if one with the same hash exists, return the
  /// existing Arc (ensuring pointer uniqueness). Otherwise insert and
  /// return.
  pub fn intern_univ(&mut self, u: KUniv<M>) -> KUniv<M> {
    let key = *u.addr();
    if let Some(existing) = self.univs.get(&key) {
      return existing.clone();
    }
    self.univs.entry(key).or_insert(u).clone()
  }

  /// Intern an expression: same pointer-uniqueness guarantee as
  /// `intern_univ`.
  pub fn intern_expr(&mut self, e: KExpr<M>) -> KExpr<M> {
    let key = *e.addr();
    if let Some(existing) = self.exprs.get(&key) {
      return existing.clone();
    }
    self.exprs.entry(key).or_insert(e).clone()
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

/// Snapshot of all `KEnv` cache sizes at a point in time.
///
/// Used by the parallel kernel-check diagnostic mode (gated on
/// `IX_KERNEL_CHECK_DIAG=1`) to surface which scheduled blocks ratchet
/// per-worker cache memory. Each field is the entry count of one of
/// `KEnv`'s `FxHashMap`/`FxHashSet` caches at the moment of snapshotting.
#[derive(Clone, Copy, Debug, Default)]
pub struct KEnvCacheSizes {
  pub consts: usize,
  pub blocks: usize,
  pub intern_exprs: usize,
  pub intern_univs: usize,
  pub whnf: usize,
  pub whnf_no_delta: usize,
  pub whnf_core: usize,
  pub infer: usize,
  pub infer_only: usize,
  pub def_eq: usize,
  pub def_eq_cheap: usize,
  pub def_eq_failure: usize,
  pub unfold: usize,
  pub ingress: usize,
  pub is_prop: usize,
  pub recursor: usize,
  pub rec_majors: usize,
  pub block_peer_agreement: usize,
  pub block_check_results: usize,
}

impl KEnvCacheSizes {
  /// Largest single cache size. Cheap proxy for "how big did this block
  /// get" without summing. (Sum is misleading because the same content
  /// hash can appear in multiple caches.)
  pub fn max(&self) -> usize {
    [
      self.consts,
      self.blocks,
      self.intern_exprs,
      self.intern_univs,
      self.whnf,
      self.whnf_no_delta,
      self.whnf_core,
      self.infer,
      self.infer_only,
      self.def_eq,
      self.def_eq_cheap,
      self.def_eq_failure,
      self.unfold,
      self.ingress,
      self.is_prop,
      self.recursor,
      self.rec_majors,
      self.block_peer_agreement,
      self.block_check_results,
    ]
    .into_iter()
    .max()
    .unwrap_or(0)
  }
}

impl std::fmt::Display for KEnvCacheSizes {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(
      f,
      "consts={} intern_exprs={} intern_univs={} whnf={}/{}/{} infer={}/{} def_eq={}/{}/{} unfold={} ingress={} is_prop={}",
      self.consts,
      self.intern_exprs,
      self.intern_univs,
      self.whnf,
      self.whnf_no_delta,
      self.whnf_core,
      self.infer,
      self.infer_only,
      self.def_eq,
      self.def_eq_cheap,
      self.def_eq_failure,
      self.unfold,
      self.ingress,
      self.is_prop,
    )
  }
}

/// The global zero kernel environment.
///
/// Single-threaded: one worker owns one environment at a time. Contains all
/// kernel state for that worker: constants, intern table, and type-checking
/// caches.
///
/// `get()` returns owned `KConst`/`Vec` (cheap Arc clones) to avoid
/// tying callers to internal map borrows.
pub struct KEnv<M: KernelMode> {
  // -- Constants --
  /// Loaded constants keyed by `KId`.
  pub consts: FxHashMap<KId<M>, KConst<M>>,
  /// Block membership: block id → ordered member ids.
  pub blocks: FxHashMap<KId<M>, Vec<KId<M>>>,

  // -- Intern table (hash-consing for pointer dedup) --
  pub intern: InternTable<M>,

  // -- Primitives (resolved lazily from consts) --
  prims: OnceCell<Primitives<M>>,

  // -- Global caches (grow monotonically, keyed by content hash) --
  // All cache keys use `Addr` (= `Arc<blake3::Hash>`, content-addressed) rather
  // than `Arc::as_ptr` pointers, avoiding the ABA problem where deallocated
  // pointers are reused by the allocator for semantically different expressions.
  /// WHNF cache (full, with delta): (expr_hash, ctx_hash)-keyed.
  pub whnf_cache: FxHashMap<(Addr, Addr), KExpr<M>>,
  /// WHNF cache (no delta): (expr_hash, ctx_hash)-keyed.
  pub whnf_no_delta_cache: FxHashMap<(Addr, Addr), KExpr<M>>,
  /// WHNF core cache: structural-only reduction (beta/iota/zeta/proj),
  /// no native primitives, no delta. Mirrors lean4lean's `whnfCoreCache`
  /// (refs/lean4lean/Lean4Lean/TypeChecker.lean:19) and lean4 C++'s
  /// `m_whnf_core`. Populated only when flags are FULL — cheap-projection
  /// results are not safe to share with full callers.
  pub whnf_core_cache: FxHashMap<(Addr, Addr), KExpr<M>>,
  /// Infer cache: keyed by (expr_hash, ctx_hash). Context-dependent.
  /// Populated only from full-mode `infer` (i.e. not from `with_infer_only`),
  /// so every cached result has passed the validation `infer_only` skips.
  /// Both modes read from this same cache — an `infer_only` lookup happily
  /// consumes a full-mode result since it's strictly stronger.
  pub infer_cache: FxHashMap<(Addr, Addr), KExpr<M>>,
  /// Infer-only cache: keyed like `infer_cache`, but populated only by
  /// `with_infer_only` synthesis and read only while infer-only is active.
  /// This keeps unchecked results out of the validated full-mode cache while
  /// still sharing repeated proof-irrelevance/projection probes.
  pub infer_only_cache: FxHashMap<(Addr, Addr), KExpr<M>>,
  /// Full def-eq cache: keyed by (expr_hash, expr_hash, ctx_hash).
  /// Context-dependent. Entries in this cache are valid for both full and
  /// cheap def-eq callers.
  pub def_eq_cache: FxHashMap<(Addr, Addr, Addr), bool>,
  /// Cheap def-eq cache: same key as `def_eq_cache`, but only for comparisons
  /// performed inside cheap projection reductions. Cheap `false` can be a
  /// full-mode false negative, so those entries must not be visible to full
  /// callers.
  pub def_eq_cheap_cache: FxHashMap<(Addr, Addr, Addr), bool>,
  /// Failed def-eq pairs in lazy delta: canonical ordering by hash.
  pub def_eq_failure: FxHashSet<(Addr, Addr, Addr)>,
  /// Constant-instantiation cache: caches the result of
  /// `instantiate_univ_params(val, us)` for each `Const(id, us)` head encountered
  /// during delta unfolding. Keyed by the head expression's content hash, which
  /// already content-addresses `(id, us)` (the head's address derives from id +
  /// universe args). Mirrors lean4 C++ `m_unfold` cache. Cross-call sharing of
  /// universe-substituted bodies eliminates O(body) walks on every unfold.
  pub unfold_cache: FxHashMap<Addr, KExpr<M>>,
  /// Ingress cache: LeanExpr → KExpr conversion results.
  /// Keyed by (expr_hash, param_names_hash) to account for different
  /// level param bindings producing different KExprs from the same LeanExpr.
  pub ingress_cache: FxHashMap<(Addr, Addr), KExpr<M>>,
  /// "Is this type Prop?" cache, keyed by (type_hash, ctx_hash).
  ///
  /// `try_proof_irrel` is called on essentially every `is_def_eq`
  /// invocation, and its uncached path costs `infer ∘ infer ∘ whnf` —
  /// two type-inference runs and one full WHNF — to decide whether the
  /// term's type is `Prop`. Because the answer depends only on the
  /// *type* (not on the term whose type was inferred), caching by the
  /// type's content hash + suffix-aware context lets every subsequent
  /// proof-irrelevance probe skip those three calls. Empirically this
  /// is the dominant cost on mathlib proof-heavy blocks, where the same
  /// propositions are tested for equality thousands of times.
  pub is_prop_cache: FxHashMap<(Addr, Addr), bool>,
  /// Generated recursors, keyed by inductive Muts block id.
  pub recursor_cache: FxHashMap<KId<M>, Vec<GeneratedRecursor<M>>>,
  /// Nested-auxiliary order expected by stored recursors in this environment.
  pub recursor_aux_order: RecursorAuxOrder,
  /// Maps the set of major inductive KIds to the inductive block id.
  pub rec_majors_cache: FxHashMap<BTreeSet<KId<M>>, KId<M>>,
  /// Mutual-block peer-agreement cache: records block ids whose peers have
  /// already been verified to share the same universe (S3) and parameter
  /// prefix (S3b). Populated by `check_inductive` after the per-peer loop
  /// succeeds; collapses the naturally O(N²) per-peer iteration to O(N)
  /// total work per block across all the peers' individual checks.
  pub block_peer_agreement_cache: FxHashSet<KId<M>>,
  /// Whole-block type-check results. Both successes and failures are cached,
  /// so every member of a bad block reports the same structured failure.
  pub block_check_results: FxHashMap<KId<M>, Result<(), TcError<M>>>,

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
/// `IX_PERF_COUNTERS=1` is set. Serial `FxHashMap` teardown is left to
/// normal Rust drop order.
impl<M: KernelMode> Drop for KEnv<M> {
  fn drop(&mut self) {
    if super::perf::enabled() {
      let summary = self.perf.summary();
      if !summary.is_empty() {
        eprint!("{summary}");
      }
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
      consts: FxHashMap::default(),
      blocks: FxHashMap::default(),
      intern: InternTable::new(),
      prims: OnceCell::new(),
      whnf_cache: FxHashMap::default(),
      whnf_no_delta_cache: FxHashMap::default(),
      whnf_core_cache: FxHashMap::default(),
      infer_cache: FxHashMap::default(),
      infer_only_cache: FxHashMap::default(),
      def_eq_cache: FxHashMap::default(),
      def_eq_cheap_cache: FxHashMap::default(),
      def_eq_failure: FxHashSet::default(),
      unfold_cache: FxHashMap::default(),
      ingress_cache: FxHashMap::default(),
      is_prop_cache: FxHashMap::default(),
      recursor_cache: FxHashMap::default(),
      recursor_aux_order,
      rec_majors_cache: FxHashMap::default(),
      block_peer_agreement_cache: FxHashSet::default(),
      block_check_results: FxHashMap::default(),
      perf: PerfCounters::default(),
    }
  }

  /// Resolve primitives from the environment (cached via `OnceCell`).
  pub fn prims(&self) -> &Primitives<M> {
    self.prims.get_or_init(|| Primitives::from_env(self))
  }

  /// Pre-initialize the primitives cache with an externally-resolved
  /// `Primitives<M>`. Returns `Ok(())` on success, `Err(p)` if `prims()`
  /// has already been called (the `OnceCell` is full).
  ///
  /// Used by `TypeChecker::new_with_lazy_ixon` to install primitives
  /// resolved from the IxonIngressLookups address→name map *before* any
  /// constants have been faulted into the local KEnv — without this
  /// seeding, `prims()` would derive primitives from an empty env and
  /// return synthetic `@<hex>` KIds that wouldn't match the real names
  /// later faulted in.
  ///
  /// `Primitives<M>` is large (~2 KB), so the error path is allowed to
  /// be big — the caller hands ownership in and only retrieves it on
  /// failure.
  #[allow(clippy::result_large_err)]
  pub fn set_prims(&mut self, p: Primitives<M>) -> Result<(), Primitives<M>> {
    self.prims.set(p)
  }

  pub fn has_prims(&self) -> bool {
    self.prims.get().is_some()
  }

  pub fn get(&self, id: &KId<M>) -> Option<KConst<M>> {
    self.consts.get(id).cloned()
  }

  pub fn insert(&mut self, id: KId<M>, c: KConst<M>) {
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
  pub fn iter(&self) -> impl Iterator<Item = (KId<M>, KConst<M>)> + '_ {
    self.consts.iter().map(|(id, c)| (id.clone(), c.clone()))
  }

  /// Get block members. Returns owned Vec (cheap KId clones).
  pub fn get_block(&self, id: &KId<M>) -> Option<Vec<KId<M>>> {
    self.blocks.get(id).cloned()
  }

  /// Insert a block membership entry.
  pub fn insert_block(&mut self, id: KId<M>, members: Vec<KId<M>>) {
    self.blocks.insert(id, members);
  }

  /// Clear all worker-local kernel state before checking another scheduled
  /// block or when a caller needs a fresh environment.
  pub fn clear(&mut self) {
    self.consts.clear();
    self.blocks.clear();
    self.intern.univs.clear();
    self.intern.exprs.clear();
    // Scratch buffers retain entries from the most recent subst/lift call;
    // emptying them releases the KExpr Arc references they hold so the
    // intern.exprs cleanup above can actually drop ExprData allocations.
    self.intern.subst_scratch.clear();
    self.intern.lift_scratch.clear();
    let _ = self.prims.take();
    self.whnf_cache.clear();
    self.whnf_no_delta_cache.clear();
    self.whnf_core_cache.clear();
    self.infer_cache.clear();
    self.infer_only_cache.clear();
    self.def_eq_cache.clear();
    self.def_eq_cheap_cache.clear();
    self.def_eq_failure.clear();
    self.unfold_cache.clear();
    self.ingress_cache.clear();
    self.is_prop_cache.clear();
    self.recursor_cache.clear();
    self.rec_majors_cache.clear();
    self.block_peer_agreement_cache.clear();
    self.block_check_results.clear();
  }

  /// Snapshot of all per-worker cache sizes. Cheap (each `len()` is O(1));
  /// useful as diagnostic input to identify which blocks blow up
  /// individual caches before `clear_releasing_memory` reclaims them.
  pub fn cache_sizes(&self) -> KEnvCacheSizes {
    KEnvCacheSizes {
      consts: self.consts.len(),
      blocks: self.blocks.len(),
      intern_exprs: self.intern.exprs.len(),
      intern_univs: self.intern.univs.len(),
      whnf: self.whnf_cache.len(),
      whnf_no_delta: self.whnf_no_delta_cache.len(),
      whnf_core: self.whnf_core_cache.len(),
      infer: self.infer_cache.len(),
      infer_only: self.infer_only_cache.len(),
      def_eq: self.def_eq_cache.len(),
      def_eq_cheap: self.def_eq_cheap_cache.len(),
      def_eq_failure: self.def_eq_failure.len(),
      unfold: self.unfold_cache.len(),
      ingress: self.ingress_cache.len(),
      is_prop: self.is_prop_cache.len(),
      recursor: self.recursor_cache.len(),
      rec_majors: self.rec_majors_cache.len(),
      block_peer_agreement: self.block_peer_agreement_cache.len(),
      block_check_results: self.block_check_results.len(),
    }
  }

  /// Clear worker-local state and drop backing allocations.
  ///
  /// `clear()` preserves `HashMap` capacity, which is useful for reuse but
  /// problematic for full-env checking: one very large block can permanently
  /// ratchet a worker's retained cache allocation. This variant is for
  /// scheduled-block boundaries where memory pressure matters more than
  /// preserving buckets for the next unrelated block.
  pub fn clear_releasing_memory(&mut self) {
    self.consts = FxHashMap::default();
    self.blocks = FxHashMap::default();
    self.intern = InternTable::new();
    self.prims = OnceCell::new();
    self.whnf_cache = FxHashMap::default();
    self.whnf_no_delta_cache = FxHashMap::default();
    self.whnf_core_cache = FxHashMap::default();
    self.infer_cache = FxHashMap::default();
    self.infer_only_cache = FxHashMap::default();
    self.def_eq_cache = FxHashMap::default();
    self.def_eq_cheap_cache = FxHashMap::default();
    self.def_eq_failure = FxHashSet::default();
    self.unfold_cache = FxHashMap::default();
    self.ingress_cache = FxHashMap::default();
    self.is_prop_cache = FxHashMap::default();
    self.recursor_cache = FxHashMap::default();
    self.rec_majors_cache = FxHashMap::default();
    self.block_peer_agreement_cache = FxHashSet::default();
    self.block_check_results = FxHashMap::default();
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
    let mut env = KEnv::<Anon>::new();
    let id = mk_id("Nat");
    env.insert(id.clone(), mk_axio("Nat"));
    assert_eq!(env.len(), 1);
    assert!(env.get(&id).is_some());
  }

  #[test]
  #[should_panic(expected = "reserved kernel marker")]
  fn insert_reserved_marker_panics() {
    let mut env = KEnv::<Anon>::new();
    let id = KId::new(PrimAddrs::new().eager_reduce, ());
    env.insert(id, mk_axio("eager_reduce"));
  }

  #[test]
  fn contains_key_works() {
    let mut env = KEnv::<Anon>::new();
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
    let mut env = KEnv::<Anon>::new();
    let id = mk_id("Nat");
    env.insert(id.clone(), mk_axio("Nat"));
    assert!(env.get(&id).is_some());
    assert!(env.get(&mk_id("missing")).is_none());
  }

  #[test]
  fn intern_univ_dedup() {
    let mut it = InternTable::<Anon>::new();
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
    let mut it = InternTable::<Anon>::new();
    let z = it.intern_univ(KUniv::zero());
    let s = it.intern_univ(KUniv::succ(KUniv::zero()));
    assert!(!z.ptr_eq(&s));
  }

  #[test]
  fn intern_expr_dedup() {
    let mut it = InternTable::<Anon>::new();
    let v1 = KExpr::var(0, ());
    let v2 = KExpr::var(0, ());
    assert!(!v1.ptr_eq(&v2));
    let i1 = it.intern_expr(v1);
    let i2 = it.intern_expr(v2);
    assert!(i1.ptr_eq(&i2));
  }

  #[test]
  fn intern_expr_different() {
    let mut it = InternTable::<Anon>::new();
    let v0 = it.intern_expr(KExpr::var(0, ()));
    let v1 = it.intern_expr(KExpr::var(1, ()));
    assert!(!v0.ptr_eq(&v1));
  }

  #[test]
  fn iter_all_entries() {
    let mut env = KEnv::<Anon>::new();
    env.insert(mk_id("A"), mk_axio("A"));
    env.insert(mk_id("B"), mk_axio("B"));
    assert_eq!(env.iter().count(), 2);
  }
}
