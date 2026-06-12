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

use ix_common::address::Address;

use super::constant::{KConst, RecRule};
use super::error::TcError;
use super::expr::{FVarId, KExpr};
use super::id::KId;
use super::level::KUniv;
use super::mode::KernelMode;
use super::perf::PerfCounters;
use super::primitive::Primitives;

/// Canonical identity of an expression or universe node: the
/// intern-assigned uid. Plain `u64`, allocated from a process-global
/// counter (`expr.rs::fresh_uid`) and NEVER reused, so uid equality
/// implies structural equality and cache keys built from uids cannot
/// alias across intern-table clears (a stale key can only miss).
///
/// This is KERNEL-INTERNAL identity for ephemeral in-memory nodes —
/// distinct from the Ixon `Address` layer (blake3 over serialized
/// content) that constants/blobs carry into claims, Merkle roots, and
/// the proof store. Uids must never escape into a serialized artifact;
/// see `docs/kernel_identity.md` for the boundary rule and the
/// proof-carrying-code implications.
///
/// Earlier revisions stored the blake3 content hash of every node here,
/// computed at construction: profiling on the Zisk guest put that hashing
/// (`app_hash` + the blake3 wrapper) at ~20% of guest cycles on
/// reduction-heavy constants. Identity is now assigned by the intern
/// table from shallow structural keys ([`ExprKey`]/[`UnivKey`]) instead
/// of computed from content.
pub type Addr = u64;

/// Key type for local-context hashing (`tc.rs::ctx_addr_for_lbr`) and
/// other places that still need a collision-resistant digest over
/// variable-length content. Per-node expression identity uses [`Addr`].
pub type CtxAddr = blake3::Hash;

/// Shallow structural key of an expression node: the variant tag plus the
/// uids of its children and its semantic payload. Mirrors EXACTLY what the
/// historical per-node content hash covered — display names, binder info,
/// and mdata are excluded — so interning semantics are unchanged. Children
/// are identified by uid: within one table, equal keys ⇔ structurally
/// equal nodes (children canonical by induction).
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum ExprKey {
  Var(u64),
  FVar(u64),
  Sort(Addr),
  Const(Address, Box<[Addr]>),
  App(Addr, Addr),
  Lam(Addr, Addr),
  All(Addr, Addr),
  Let(Addr, Addr, Addr, bool),
  Prj(Address, u64, Addr),
  Nat(Address),
  Str(Address),
}

/// Shallow structural key of a universe node. `Param` display names are
/// excluded, mirroring the historical hash semantics.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum UnivKey {
  Zero,
  Succ(Addr),
  Max(Addr, Addr),
  IMax(Addr, Addr),
  Param(u64),
}

/// Hash-consing intern table for expressions and universes.
///
/// Single-threaded and owned by one `KEnv`. Guarantees uid/pointer
/// uniqueness per shallow structural key within that environment:
/// `ptr(a) == ptr(b)` iff `key(a) == key(b)` for interned values.
///
/// Also owns reusable scratch buffers used by `subst`, `simul_subst`, and
/// `lift` to memoize content-addressed sub-traversals within a single
/// call. Allocating these as `FxHashMap::default()` per call shows up in
/// profiles for big mathlib blocks where beta/zeta reductions fire
/// millions of times; threading the scratch through the `&mut InternTable`
/// already passed for hash-consing eliminates the malloc/free churn while
/// keeping the per-call invariant (caches are cleared on entry).
pub struct InternTable<M: KernelMode> {
  pub(crate) univs: FxHashMap<UnivKey, KUniv<M>>,
  pub(crate) exprs: FxHashMap<ExprKey, KExpr<M>>,
  /// Uids of canonical (interned) nodes. `intern_expr`/`intern_univ`
  /// short-circuit on members, and use it to detect non-canonical
  /// children that must be canonicalized before the shallow key is
  /// meaningful.
  pub(crate) canon_exprs: FxHashSet<Addr>,
  pub(crate) canon_univs: FxHashSet<Addr>,
  /// Scratch buffer for `subst` / `simul_subst` per-call memoization,
  /// keyed by `(addr, depth)`. Cleared on entry. Owned here so the
  /// allocation persists across calls.
  pub(crate) subst_scratch: FxHashMap<(Addr, u64), KExpr<M>>,
  /// Scratch buffer for `lift` per-call memoization, keyed by
  /// `(addr, cutoff)`. Cleared on entry. Separate from `subst_scratch`
  /// because `lift` is invoked from inside `subst_cached`, and the two
  /// caches have different semantics, so they must not share entries.
  pub(crate) lift_scratch: FxHashMap<(Addr, u64), KExpr<M>>,
  /// Pool of scratch maps for `clo_subst` per-call memoization, keyed by
  /// `(addr, depth)`. A pool rather than a single buffer because
  /// `clo_subst` re-enters itself through `clo_readback` of environment
  /// entries (each readback substitutes under a *different* environment,
  /// so the memo must not be shared between the nesting levels). Maps are
  /// cleared and returned to the pool on exit, so allocations persist
  /// across calls like the other scratches.
  pub(crate) clo_scratch_pool: Vec<FxHashMap<(Addr, u64), KExpr<M>>>,
}

impl<M: KernelMode> Default for InternTable<M> {
  fn default() -> Self {
    Self::new()
  }
}

/// Shallow structural key of an expression whose children are canonical.
pub fn expr_key<M: KernelMode>(e: &KExpr<M>) -> ExprKey {
  use super::expr::ExprData;
  match e.data() {
    ExprData::Var(i, _, _) => ExprKey::Var(*i),
    ExprData::FVar(id, _, _) => ExprKey::FVar(id.0),
    ExprData::Sort(u, _) => ExprKey::Sort(*u.addr()),
    ExprData::Const(id, us, _) => ExprKey::Const(
      id.addr.clone(),
      us.iter().map(|u| *u.addr()).collect(),
    ),
    ExprData::App(f, a, _) => ExprKey::App(*f.addr(), *a.addr()),
    ExprData::Lam(_, _, t, b, _) => ExprKey::Lam(*t.addr(), *b.addr()),
    ExprData::All(_, _, t, b, _) => ExprKey::All(*t.addr(), *b.addr()),
    ExprData::Let(_, t, v, b, nd, _) => {
      ExprKey::Let(*t.addr(), *v.addr(), *b.addr(), *nd)
    },
    ExprData::Prj(id, f, v, _) => {
      ExprKey::Prj(id.addr.clone(), *f, *v.addr())
    },
    ExprData::Nat(_, ba, _) => ExprKey::Nat(ba.clone()),
    ExprData::Str(_, ba, _) => ExprKey::Str(ba.clone()),
  }
}

/// Shallow structural key of a universe whose children are canonical.
pub fn univ_key<M: KernelMode>(u: &KUniv<M>) -> UnivKey {
  use super::level::UnivData;
  match u.data() {
    UnivData::Zero(_) => UnivKey::Zero,
    UnivData::Succ(inner, _) => UnivKey::Succ(*inner.addr()),
    UnivData::Max(a, b, _) => UnivKey::Max(*a.addr(), *b.addr()),
    UnivData::IMax(a, b, _) => UnivKey::IMax(*a.addr(), *b.addr()),
    UnivData::Param(idx, _, _) => UnivKey::Param(*idx),
  }
}

impl<M: KernelMode> InternTable<M> {
  pub fn new() -> Self {
    InternTable {
      univs: FxHashMap::default(),
      exprs: FxHashMap::default(),
      canon_exprs: FxHashSet::default(),
      canon_univs: FxHashSet::default(),
      subst_scratch: FxHashMap::default(),
      lift_scratch: FxHashMap::default(),
      clo_scratch_pool: Vec::new(),
    }
  }

  /// Read-only fast path: return the canonical interned universe for
  /// `key` if already present. The key must be built from CANONICAL
  /// children (their uids). Plain callers should use `intern_univ`.
  #[inline]
  pub fn try_get_univ(&self, key: &UnivKey) -> Option<KUniv<M>> {
    self.univs.get(key).cloned()
  }

  /// Read-only fast path counterpart of `try_get_univ` for expressions.
  #[inline]
  pub fn try_get_expr(&self, key: &ExprKey) -> Option<KExpr<M>> {
    self.exprs.get(key).cloned()
  }

  /// Intern a universe: returns the canonical value for its structural
  /// identity, recursively canonicalizing children as needed so the
  /// shallow key is meaningful.
  pub fn intern_univ(&mut self, u: KUniv<M>) -> KUniv<M> {
    use super::level::UnivData;
    if self.canon_univs.contains(u.addr()) {
      return u;
    }
    // Canonicalize children first; rebuild only if any child changed.
    let u = match u.data() {
      UnivData::Succ(inner, _) => {
        let ci = self.intern_univ(inner.clone());
        if ci.ptr_eq(inner) { u } else { KUniv::new(UnivData::Succ(ci, super::expr::fresh_uid())) }
      },
      UnivData::Max(a, b, _) => {
        let ca = self.intern_univ(a.clone());
        let cb = self.intern_univ(b.clone());
        if ca.ptr_eq(a) && cb.ptr_eq(b) {
          u
        } else {
          KUniv::new(UnivData::Max(ca, cb, super::expr::fresh_uid()))
        }
      },
      UnivData::IMax(a, b, _) => {
        let ca = self.intern_univ(a.clone());
        let cb = self.intern_univ(b.clone());
        if ca.ptr_eq(a) && cb.ptr_eq(b) {
          u
        } else {
          KUniv::new(UnivData::IMax(ca, cb, super::expr::fresh_uid()))
        }
      },
      UnivData::Zero(_) | UnivData::Param(..) => u,
    };
    let key = univ_key(&u);
    if let Some(existing) = self.univs.get(&key) {
      return existing.clone();
    }
    self.canon_univs.insert(*u.addr());
    self.univs.insert(key, u.clone());
    u
  }

  /// Intern an expression: returns the canonical value for its structural
  /// identity. Children are canonicalized recursively when needed (a node
  /// built outside the table has non-canonical children whose uids would
  /// make the shallow key meaningless), preserving the historical
  /// content-hash interning semantics.
  pub fn intern_expr(&mut self, e: KExpr<M>) -> KExpr<M> {
    use super::expr::ExprData;
    if self.canon_exprs.contains(e.addr()) {
      return e;
    }
    let e = match e.data() {
      ExprData::Sort(un, _) => {
        let cu = self.intern_univ(un.clone());
        if cu.ptr_eq(un) {
          e
        } else {
          KExpr::sort_mdata(cu, e.mdata().clone())
        }
      },
      ExprData::Const(id, us, _) => {
        let cus: Box<[KUniv<M>]> =
          us.iter().map(|un| self.intern_univ(un.clone())).collect();
        if cus.iter().zip(us.iter()).all(|(a, b)| a.ptr_eq(b)) {
          e
        } else {
          KExpr::cnst_mdata(id.clone(), cus, e.mdata().clone())
        }
      },
      ExprData::App(f, a, _) => {
        let cf = self.intern_expr(f.clone());
        let ca = self.intern_expr(a.clone());
        if cf.ptr_eq(f) && ca.ptr_eq(a) {
          e
        } else {
          KExpr::app_mdata(cf, ca, e.mdata().clone())
        }
      },
      ExprData::Lam(n, bi, t, b, _) => {
        let ct = self.intern_expr(t.clone());
        let cb = self.intern_expr(b.clone());
        if ct.ptr_eq(t) && cb.ptr_eq(b) {
          e
        } else {
          KExpr::lam_mdata(n.clone(), bi.clone(), ct, cb, e.mdata().clone())
        }
      },
      ExprData::All(n, bi, t, b, _) => {
        let ct = self.intern_expr(t.clone());
        let cb = self.intern_expr(b.clone());
        if ct.ptr_eq(t) && cb.ptr_eq(b) {
          e
        } else {
          KExpr::all_mdata(n.clone(), bi.clone(), ct, cb, e.mdata().clone())
        }
      },
      ExprData::Let(n, t, v, b, nd, _) => {
        let ct = self.intern_expr(t.clone());
        let cv = self.intern_expr(v.clone());
        let cb = self.intern_expr(b.clone());
        if ct.ptr_eq(t) && cv.ptr_eq(v) && cb.ptr_eq(b) {
          e
        } else {
          KExpr::let_mdata(n.clone(), ct, cv, cb, *nd, e.mdata().clone())
        }
      },
      ExprData::Prj(id, f, v, _) => {
        let cv = self.intern_expr(v.clone());
        if cv.ptr_eq(v) {
          e
        } else {
          KExpr::prj_mdata(id.clone(), *f, cv, e.mdata().clone())
        }
      },
      ExprData::Var(..)
      | ExprData::FVar(..)
      | ExprData::Nat(..)
      | ExprData::Str(..) => e,
    };
    let key = expr_key(&e);
    if let Some(existing) = self.exprs.get(&key) {
      // The shallow key (exact structural Eq over variant tag + child
      // uids + payload — never a truncated or content-hashed key) plus
      // canonical children make this hit structurally exact. Checked in
      // debug builds; a violation here would be an interning bug, not
      // an input an adversary can craft (uids are assigned, not hashed).
      debug_assert!(existing == &e, "intern hit is not structurally equal");
      return existing.clone();
    }
    self.canon_exprs.insert(*e.addr());
    self.exprs.insert(key, e.clone());
    e
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
  pub whnf_no_delta_cheap: usize,
  pub whnf_core: usize,
  pub whnf_core_cheap: usize,
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
      self.whnf_no_delta_cheap,
      self.whnf_core,
      self.whnf_core_cheap,
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
      "consts={} intern_exprs={} intern_univs={} whnf={}/{}/{}/{}/{} infer={}/{} def_eq={}/{}/{} unfold={} ingress={} is_prop={}",
      self.consts,
      self.intern_exprs,
      self.intern_univs,
      self.whnf,
      self.whnf_no_delta,
      self.whnf_no_delta_cheap,
      self.whnf_core,
      self.whnf_core_cheap,
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
  pub whnf_cache: FxHashMap<(Addr, CtxAddr), KExpr<M>>,
  /// WHNF cache (no delta): (expr_hash, ctx_hash)-keyed.
  pub whnf_no_delta_cache: FxHashMap<(Addr, CtxAddr), KExpr<M>>,
  /// Cheap-mode WHNF cache (no delta, DEF_EQ_CORE flags): same key shape as
  /// `whnf_no_delta_cache`, but populated by cheap-projection callers in the
  /// def-eq lazy-delta loop. Cheap output is NOT shared with full callers
  /// because cheap projections leave projection-of-non-ctor terms stuck where
  /// FULL would unfold the underlying definition. Reads and writes here are
  /// gated to cheap-mode callers only — mirrors the `def_eq_cheap_cache`
  /// pattern. Without this, every iteration of the lazy-delta loop redoes
  /// `whnf_no_delta_for_def_eq` from scratch (mathlib hot path).
  pub whnf_no_delta_cheap_cache: FxHashMap<(Addr, CtxAddr), KExpr<M>>,
  /// WHNF core cache: structural-only reduction (beta/iota/zeta/proj),
  /// no native primitives, no delta. Mirrors lean4lean's `whnfCoreCache`
  /// (refs/lean4lean/Lean4Lean/TypeChecker.lean:19) and lean4 C++'s
  /// `m_whnf_core`. Populated only when flags are FULL — cheap-projection
  /// results are not safe to share with full callers.
  pub whnf_core_cache: FxHashMap<(Addr, CtxAddr), KExpr<M>>,
  /// Cheap-mode WHNF core cache: same key shape as `whnf_core_cache`, but
  /// populated by cheap-projection callers (DEF_EQ_CORE flags) inside the
  /// def-eq lazy-delta loop. Same soundness reasoning as
  /// `whnf_no_delta_cheap_cache` — cheap output stays in its own pool so
  /// full callers always see a properly-reduced result.
  pub whnf_core_cheap_cache: FxHashMap<(Addr, CtxAddr), KExpr<M>>,
  /// Infer cache: keyed by (expr_hash, ctx_hash). Context-dependent.
  /// Populated only from full-mode `infer` (i.e. not from `with_infer_only`),
  /// so every cached result has passed the validation `infer_only` skips.
  /// Both modes read from this same cache — an `infer_only` lookup happily
  /// consumes a full-mode result since it's strictly stronger.
  pub infer_cache: FxHashMap<(Addr, CtxAddr), KExpr<M>>,
  /// Infer-only cache: keyed like `infer_cache`, but populated only by
  /// `with_infer_only` synthesis and read only while infer-only is active.
  /// This keeps unchecked results out of the validated full-mode cache while
  /// still sharing repeated proof-irrelevance/projection probes.
  pub infer_only_cache: FxHashMap<(Addr, CtxAddr), KExpr<M>>,
  /// Full def-eq cache: keyed by (expr_hash, expr_hash, ctx_hash).
  /// Context-dependent. Entries in this cache are valid for both full and
  /// cheap def-eq callers.
  pub def_eq_cache: FxHashMap<(Addr, Addr, CtxAddr), bool>,
  /// Cheap def-eq cache: same key as `def_eq_cache`, but only for comparisons
  /// performed inside cheap projection reductions. Cheap `false` can be a
  /// full-mode false negative, so those entries must not be visible to full
  /// callers.
  pub def_eq_cheap_cache: FxHashMap<(Addr, Addr, CtxAddr), bool>,
  /// Failed def-eq pairs in lazy delta: canonical ordering by hash.
  pub def_eq_failure: FxHashSet<(Addr, Addr, CtxAddr)>,
  /// Constant-instantiation cache: caches the result of
  /// `instantiate_univ_params(val, us)` for each `Const(id, us)` head encountered
  /// during delta unfolding. Keyed by the head expression's content hash, which
  /// already content-addresses `(id, us)` (the head's address derives from id +
  /// universe args). Mirrors lean4 C++ `m_unfold` cache. Cross-call sharing of
  /// universe-substituted bodies eliminates O(body) walks on every unfold.
  pub unfold_cache: FxHashMap<Addr, KExpr<M>>,
  /// Memo of `try_reduce_nat_succ_iter` STUCK outcomes: succ-chain args
  /// whose base never collapses to a literal. Keyed like `whnf_cache`
  /// ((expr_hash, ctx_hash)). The succ-collapse loop runs its inner WHNF
  /// in `NatSuccMode::Stuck`, which bypasses the WHNF caches, so without
  /// this memo a stuck `Nat.succ^k(x)` chain is re-peeled from every
  /// depth it is encountered at — O(k²) fuel for symbolic-plus-literal
  /// Nat arithmetic (e.g. `x + 0xC0` in the UTF-8 codec proofs).
  pub nat_succ_stuck: FxHashSet<(Addr, CtxAddr)>,
  /// Ingress cache: LeanExpr → KExpr conversion results.
  /// Keyed by (expr_hash, param_names_hash) to account for different
  /// level param bindings producing different KExprs from the same LeanExpr.
  pub ingress_cache: FxHashMap<(CtxAddr, CtxAddr), KExpr<M>>,
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
  pub is_prop_cache: FxHashMap<(Addr, CtxAddr), bool>,
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

  /// Primitive-reducer family per head-constant address (see
  /// `whnf.rs::PrimFamily`). Pure function of the address; memoized so
  /// the WHNF loops classify each head with one map probe instead of a
  /// ~30-address compare gauntlet across five recognizers.
  pub prim_family_cache: FxHashMap<Address, super::whnf::PrimFamily>,

  /// Next free-variable id for checker-local binder openings.
  ///
  /// Type-checking caches live on `KEnv`, not on one `TypeChecker`, so FVar
  /// ids must also be allocated from the shared environment. Otherwise two
  /// checker instances could both mint `fv$0` and reuse an `infer(fv$0)` cache
  /// entry under different local contexts.
  next_fvar_id: u64,

  // -- Performance counters (audit §10) --
  /// Cache hit/miss and fuel-consumption counters, gated by
  /// `IX_PERF_COUNTERS=1`. When the env var is unset the counters are
  /// no-ops; when set, the totals are dumped from the `Drop` impl below.
  pub perf: PerfCounters,

  /// Out-of-circuit profile recorder for sharding (see `plans/sharding.md`).
  /// `Some` enables per-constant heartbeat + delta-unfold recording on this
  /// worker; `None` (the default) has zero overhead. Deliberately preserved
  /// across `clear`/`clear_releasing_memory` so recording survives scheduled
  /// block boundaries within a run.
  pub profile_sink: Option<crate::profile::ProfileSink>,
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
        log::info!("{summary}");
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
      whnf_no_delta_cheap_cache: FxHashMap::default(),
      whnf_core_cache: FxHashMap::default(),
      whnf_core_cheap_cache: FxHashMap::default(),
      infer_cache: FxHashMap::default(),
      infer_only_cache: FxHashMap::default(),
      def_eq_cache: FxHashMap::default(),
      def_eq_cheap_cache: FxHashMap::default(),
      def_eq_failure: FxHashSet::default(),
      unfold_cache: FxHashMap::default(),
      nat_succ_stuck: FxHashSet::default(),
      ingress_cache: FxHashMap::default(),
      is_prop_cache: FxHashMap::default(),
      recursor_cache: FxHashMap::default(),
      recursor_aux_order,
      rec_majors_cache: FxHashMap::default(),
      block_peer_agreement_cache: FxHashSet::default(),
      block_check_results: FxHashMap::default(),
      prim_family_cache: FxHashMap::default(),
      next_fvar_id: 0,
      perf: PerfCounters::default(),
      profile_sink: None,
    }
  }

  pub fn fresh_fvar_id(&mut self) -> FVarId {
    let id = self.next_fvar_id;
    self.next_fvar_id = self.next_fvar_id.checked_add(1).expect(
      "KEnv::fresh_fvar_id: u64 counter overflow (more than 2^64 fvars in one environment)",
    );
    FVarId(id)
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
    self.intern.canon_exprs.clear();
    self.intern.canon_univs.clear();
    // Scratch buffers retain entries from the most recent subst/lift call;
    // emptying them releases the KExpr Arc references they hold so the
    // intern.exprs cleanup above can actually drop ExprData allocations.
    self.intern.subst_scratch.clear();
    self.intern.lift_scratch.clear();
    self.intern.clo_scratch_pool.clear();
    let _ = self.prims.take();
    self.whnf_cache.clear();
    self.whnf_no_delta_cache.clear();
    self.whnf_no_delta_cheap_cache.clear();
    self.whnf_core_cache.clear();
    self.whnf_core_cheap_cache.clear();
    self.infer_cache.clear();
    self.infer_only_cache.clear();
    self.def_eq_cache.clear();
    self.def_eq_cheap_cache.clear();
    self.def_eq_failure.clear();
    self.unfold_cache.clear();
    self.nat_succ_stuck.clear();
    self.ingress_cache.clear();
    self.is_prop_cache.clear();
    self.recursor_cache.clear();
    self.rec_majors_cache.clear();
    self.block_peer_agreement_cache.clear();
    self.block_check_results.clear();
    self.prim_family_cache.clear();
    self.next_fvar_id = 0;
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
      whnf_no_delta_cheap: self.whnf_no_delta_cheap_cache.len(),
      whnf_core: self.whnf_core_cache.len(),
      whnf_core_cheap: self.whnf_core_cheap_cache.len(),
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
    self.whnf_no_delta_cheap_cache = FxHashMap::default();
    self.whnf_core_cache = FxHashMap::default();
    self.whnf_core_cheap_cache = FxHashMap::default();
    self.infer_cache = FxHashMap::default();
    self.infer_only_cache = FxHashMap::default();
    self.def_eq_cache = FxHashMap::default();
    self.def_eq_cheap_cache = FxHashMap::default();
    self.def_eq_failure = FxHashSet::default();
    self.unfold_cache = FxHashMap::default();
    self.nat_succ_stuck = FxHashSet::default();
    self.ingress_cache = FxHashMap::default();
    self.is_prop_cache = FxHashMap::default();
    self.recursor_cache = FxHashMap::default();
    self.rec_majors_cache = FxHashMap::default();
    self.block_peer_agreement_cache = FxHashSet::default();
    self.block_check_results = FxHashMap::default();
    self.prim_family_cache = FxHashMap::default();
    self.next_fvar_id = 0;
  }

  /// Clear only the reduction-memo caches (whnf / infer / def-eq / unfold /
  /// is-prop). Structural caches (`consts`, `blocks`, `intern`, recursor
  /// caches, `block_check_results`) and the profile sink are preserved.
  ///
  /// Used by the profile recorder's per-constant isolation mode: clearing the
  /// cross-constant memo between constants forces every delta-unfold to
  /// re-execute (sound delta recording) and makes recorded heartbeats reflect
  /// the in-circuit cost, which has no cross-constant memoization. Clearing a
  /// pure memo never affects correctness — only performance.
  pub fn clear_reduction_caches(&mut self) {
    self.whnf_cache.clear();
    self.whnf_no_delta_cache.clear();
    self.whnf_no_delta_cheap_cache.clear();
    self.whnf_core_cache.clear();
    self.whnf_core_cheap_cache.clear();
    self.infer_cache.clear();
    self.infer_only_cache.clear();
    self.def_eq_cache.clear();
    self.def_eq_cheap_cache.clear();
    self.def_eq_failure.clear();
    self.unfold_cache.clear();
    self.nat_succ_stuck.clear();
    self.is_prop_cache.clear();
  }
}

#[cfg(test)]
mod tests {
  use super::super::mode::Anon;
  use super::super::primitive::PrimAddrs;
  use super::*;
  use ix_common::address::Address;

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
