//! Ingress: convert Ixon environment to zero kernel types.
//!
//! Converts Ixon `Constant`/`ConstantInfo`/`Expr`/`Univ` (alpha-invariant,
//! content-addressed) to `KExpr`/`KUniv`/`KConst` (kernel types with positional
//! universe params and optional metadata). Uses iterative stack-based traversal
//! to avoid stack overflow on deeply nested expressions.

use std::cell::Cell;
use std::hash::{BuildHasher, Hash};
use std::sync::Arc;
use std::time::{Duration, Instant};

use rayon::iter::{
  IntoParallelIterator, IntoParallelRefIterator, ParallelIterator,
};
use rustc_hash::{FxHashMap, FxHashSet};

use dashmap::DashMap;

use crate::ix::address::Address;
use crate::ix::env::{
  BinderInfo, ConstantInfo as LeanCI, DefinitionSafety, Env as LeanEnv, Name,
  ReducibilityHints,
};
use crate::ix::ixon::constant::{
  Constant, ConstantInfo as IxonCI, DefKind, MutConst as IxonMutConst,
};
use crate::ix::ixon::env::Env as IxonEnv;
use crate::ix::ixon::expr::Expr as IxonExpr;
use crate::ix::ixon::metadata::{
  ConstantMeta, ConstantMetaInfo, ExprMeta, ExprMetaData, resolve_kvmap,
};
use crate::ix::ixon::univ::Univ as IxonUniv;
use crate::ix::kernel::env::Addr;
use lean_ffi::nat::Nat;

use super::constant::{KConst, RecRule};
use super::env::{InternTable, KEnv, intern_addr};
use super::expr::{KExpr, MData};
use super::id::KId;
use super::level::KUniv;
use super::mode::{KernelMode, Meta};
use super::primitive::reserved_marker_name;

// ============================================================================
// Lookup tables
// ============================================================================

/// Read-only context for converting a single Ixon constant's expressions.
struct Ctx<'a, M: KernelMode> {
  sharing: &'a [Arc<IxonExpr>],
  refs: &'a [Address],
  univs: &'a [Arc<IxonUniv>],
  /// ZIds of mutual block members (for resolving `Expr::Rec`).
  mut_ctx: Vec<KId<M>>,
  arena: &'a ExprMeta,
  names: &'a FxHashMap<Address, Name>,
  lvls: Vec<Name>,
  /// Canonical intern table (shared across all ingress calls).
  intern: &'a InternTable<M>,
  /// Counter for generating synthetic unique names when metadata is missing.
  synth_counter: Cell<u64>,
}

/// Expression conversion cache, keyed on (expr pointer, arena_idx).
type ExprCache<M> = FxHashMap<(usize, u64), KExpr<M>>;
/// Universe conversion cache, scoped to one level-parameter context.
type UnivCache<M> = FxHashMap<usize, KUniv<M>>;

#[derive(Clone, Default)]
struct ConvertStats {
  enabled: bool,
  expr_roots: u64,
  expr_process: u64,
  expr_cache_hits: u64,
  expr_cache_misses: u64,
  expr_cache_inserts: u64,
  expr_cache_peak: u64,
  expr_cache_clears: u64,
  expr_cache_entries_cleared: u64,
  share_expansions: u64,
  mdata_nodes: u64,
  mdata_kv_maps: u64,
  callsites: u64,
  callsite_args: u64,
  univ_roots: u64,
  univ_cache_hits: u64,
  univ_cache_misses: u64,
  univ_cache_inserts: u64,
  univ_cache_peak: u64,
  univ_process: u64,
  univ_interns: u64,
  sort_nodes: u64,
  var_nodes: u64,
  ref_nodes: u64,
  rec_nodes: u64,
  app_nodes: u64,
  lam_nodes: u64,
  all_nodes: u64,
  let_nodes: u64,
  prj_nodes: u64,
  str_nodes: u64,
  nat_nodes: u64,
  // ---- Phase-1 timing breakdown (ns), gated by IX_INGRESS_CONVERT_STATS ----
  /// Time spent in the `for kvm in mdata { resolve_kvmap(...) }` loop in
  /// `ingress_expr`. Aggregates blob fetches, name lookups, and (for
  /// OfSyntax) recursive `deser_syntax` work.
  resolve_kvmap_ns: u64,
  /// Number of `resolve_kvmap` calls (bumped by `mdata.len()` per Mdata
  /// arena node, matching `mdata_kv_maps`).
  resolve_kvmap_calls: u64,
  /// Time spent walking the `ExprMetaData::Mdata` arena chain (the whole
  /// `while let Some(Mdata)` loop including `resolve_kvmap`).
  arena_walk_ns: u64,
  /// Time spent inside `intern_expr` (sum of fast-path get + slow-path
  /// entry).
  intern_expr_ns: u64,
  /// Number of `intern_expr` calls.
  intern_expr_calls: u64,
  /// Of those calls, how many were satisfied by the read-locked fast path
  /// (vs. falling through to the write-locked entry path).
  intern_expr_get_hits: u64,
  /// Time spent inside `intern_univ`.
  intern_univ_ns: u64,
  /// Number of `intern_univ` calls.
  intern_univ_calls: u64,
  /// Of those, fast-path hits.
  intern_univ_get_hits: u64,
  /// Time spent on `cache.get(&cache_key)` lookups in `ingress_expr`.
  expr_cache_lookup_ns: u64,
  /// Time spent on `cache.insert(...)` for `ExprFrame::Cache`.
  expr_cache_insert_ns: u64,
  /// Time spent in `ixon_env.get_blob` calls from the `Str`/`Nat` arms of
  /// `ingress_expr` (does NOT include `resolve_kvmap`'s blob fetches —
  /// those live inside `resolve_kvmap_ns`).
  get_blob_ns: u64,
  /// Number of those `get_blob` calls.
  get_blob_calls: u64,
  /// Total time spent inside the `ExprFrame::Process` arm body — covers
  /// share expansion, cache check, arena walk, `resolve_kvmap`, the
  /// per-variant match arms (KExpr constructor calls, stack pushes for
  /// continuations), and `intern_expr` invocations from this arm.
  /// Subtracting the inner timed sub-stages from this gives the cost of
  /// "everything else": KExpr construction, match dispatch, frame
  /// allocation, Arc clones, and minor lookups.
  process_arm_ns: u64,
  /// Total time spent inside continuation arms (`AppDone`, `LamDone`,
  /// `AllDone`, `LetDone`, `PrjDone`, `LetVal`, `BinderPush`, `BinderPop`,
  /// `AppArg`, `LamBody`, `AllBody`, `LetBody`, `Cache`). These build a
  /// new KExpr from already-converted children and then call
  /// `intern_expr`. Subtracting `intern_expr_ns` (continuation share) and
  /// `expr_cache_insert_ns` (Cache arm) from this gives the cost of the
  /// continuation-side KExpr construction + frame manipulation.
  continuation_arms_ns: u64,
  /// Time spent constructing KExprs at all 13 call sites in
  /// `ingress_expr` — covers blake3 hashing, `intern_addr`, and the outer
  /// `Arc<ExprData>` allocation. Excludes the subsequent `intern_expr`
  /// call (separately timed). Bumped by every `KExpr::*_mdata` /
  /// `KExpr::*` constructor we wrap.
  kexpr_construct_ns: u64,
  /// Number of timed KExpr constructor calls.
  kexpr_construct_calls: u64,
}

impl ConvertStats {
  fn new(enabled: bool) -> Self {
    ConvertStats { enabled, ..ConvertStats::default() }
  }

  fn merge(mut self, other: Self) -> Self {
    self.enabled |= other.enabled;
    self.expr_roots += other.expr_roots;
    self.expr_process += other.expr_process;
    self.expr_cache_hits += other.expr_cache_hits;
    self.expr_cache_misses += other.expr_cache_misses;
    self.expr_cache_inserts += other.expr_cache_inserts;
    self.expr_cache_peak = self.expr_cache_peak.max(other.expr_cache_peak);
    self.expr_cache_clears += other.expr_cache_clears;
    self.expr_cache_entries_cleared += other.expr_cache_entries_cleared;
    self.share_expansions += other.share_expansions;
    self.mdata_nodes += other.mdata_nodes;
    self.mdata_kv_maps += other.mdata_kv_maps;
    self.callsites += other.callsites;
    self.callsite_args += other.callsite_args;
    self.univ_roots += other.univ_roots;
    self.univ_cache_hits += other.univ_cache_hits;
    self.univ_cache_misses += other.univ_cache_misses;
    self.univ_cache_inserts += other.univ_cache_inserts;
    self.univ_cache_peak = self.univ_cache_peak.max(other.univ_cache_peak);
    self.univ_process += other.univ_process;
    self.univ_interns += other.univ_interns;
    self.sort_nodes += other.sort_nodes;
    self.var_nodes += other.var_nodes;
    self.ref_nodes += other.ref_nodes;
    self.rec_nodes += other.rec_nodes;
    self.app_nodes += other.app_nodes;
    self.lam_nodes += other.lam_nodes;
    self.all_nodes += other.all_nodes;
    self.let_nodes += other.let_nodes;
    self.prj_nodes += other.prj_nodes;
    self.str_nodes += other.str_nodes;
    self.nat_nodes += other.nat_nodes;
    self.resolve_kvmap_ns += other.resolve_kvmap_ns;
    self.resolve_kvmap_calls += other.resolve_kvmap_calls;
    self.arena_walk_ns += other.arena_walk_ns;
    self.intern_expr_ns += other.intern_expr_ns;
    self.intern_expr_calls += other.intern_expr_calls;
    self.intern_expr_get_hits += other.intern_expr_get_hits;
    self.intern_univ_ns += other.intern_univ_ns;
    self.intern_univ_calls += other.intern_univ_calls;
    self.intern_univ_get_hits += other.intern_univ_get_hits;
    self.expr_cache_lookup_ns += other.expr_cache_lookup_ns;
    self.expr_cache_insert_ns += other.expr_cache_insert_ns;
    self.get_blob_ns += other.get_blob_ns;
    self.get_blob_calls += other.get_blob_calls;
    self.process_arm_ns += other.process_arm_ns;
    self.continuation_arms_ns += other.continuation_arms_ns;
    self.kexpr_construct_ns += other.kexpr_construct_ns;
    self.kexpr_construct_calls += other.kexpr_construct_calls;
    self
  }

  fn record_cache_clear<M: KernelMode>(&mut self, cache: &ExprCache<M>) {
    if self.enabled {
      self.expr_cache_clears += 1;
      self.expr_cache_entries_cleared += cache.len() as u64;
    }
  }
}

macro_rules! bump_convert_stat {
  ($stats:expr, $field:ident) => {
    if ($stats).enabled {
      ($stats).$field += 1;
    }
  };
  ($stats:expr, $field:ident, $amount:expr) => {
    if ($stats).enabled {
      ($stats).$field += $amount as u64;
    }
  };
}

/// Universe counterpart of [`timed_intern_or_build`].
#[inline]
fn timed_intern_univ<M: KernelMode>(
  intern: &InternTable<M>,
  u: KUniv<M>,
  stats: &mut ConvertStats,
) -> KUniv<M> {
  if !stats.enabled {
    return intern.intern_univ(u);
  }
  let t0 = Instant::now();
  let key = **u.addr();
  let result = if let Some(existing) = intern.try_get_univ(&key) {
    stats.intern_univ_get_hits += 1;
    existing
  } else {
    intern.intern_univ(u)
  };
  stats.intern_univ_calls += 1;
  stats.intern_univ_ns += t0.elapsed().as_nanos() as u64;
  result
}

/// Hash-first interning. Precomputes the content hash, asks the intern
/// table for an existing canonical KExpr; only on a miss does it call
/// `build(addr)` to allocate a new KExpr.
///
/// Why this exists: profiling on Mathlib shows `kexpr_construct` (the
/// blake3 hash + `intern_addr` + `Arc<ExprData>` allocation triple)
/// is ~45% of `convert` worker-sum, of which ~62% is wasted because the
/// intern table already has the same canonical value. By computing just
/// the hash up front and skipping construction entirely on a hit, we
/// avoid the allocation + the duplicate `intern_addr` work for the
/// majority case.
///
/// The `build` closure receives the canonical `Addr` (the result of
/// `intern_addr(hash)`) and is expected to call one of the
/// `KExpr::*_mdata_with_addr` constructors so it can plug the
/// pre-interned `Addr` into `ExprInfo` without re-hashing or
/// re-traversing `ADDR_INTERN`.
///
/// Stats accounting (when enabled): the hit path bumps
/// `intern_expr_get_hits`. The miss path also bumps `kexpr_construct_*`
/// for the cost of the closure body. `intern_expr_ns` covers the
/// surrounding DashMap traffic on both paths but excludes the
/// closure-internal time.
#[inline]
fn timed_intern_or_build<M: KernelMode>(
  intern: &InternTable<M>,
  hash: blake3::Hash,
  build: impl FnOnce(Addr) -> KExpr<M>,
  stats: &mut ConvertStats,
) -> KExpr<M> {
  if !stats.enabled {
    if let Some(existing) = intern.try_get_expr(&hash) {
      return existing;
    }
    let addr = intern_addr(hash);
    return intern.intern_expr(build(addr));
  }
  let t0 = Instant::now();
  if let Some(existing) = intern.try_get_expr(&hash) {
    stats.intern_expr_get_hits += 1;
    stats.intern_expr_calls += 1;
    stats.intern_expr_ns += t0.elapsed().as_nanos() as u64;
    return existing;
  }
  let addr = intern_addr(hash);
  let kc_t0 = Instant::now();
  let new = build(addr);
  let kc_elapsed = kc_t0.elapsed().as_nanos() as u64;
  stats.kexpr_construct_ns += kc_elapsed;
  stats.kexpr_construct_calls += 1;
  let interned = intern.intern_expr(new);
  let total = t0.elapsed().as_nanos() as u64;
  // Account for the DashMap traffic only — the closure body's time is
  // already in `kexpr_construct_ns`.
  stats.intern_expr_ns += total.saturating_sub(kc_elapsed);
  stats.intern_expr_calls += 1;
  interned
}

fn resolve_name(addr: &Address, names: &FxHashMap<Address, Name>) -> Name {
  names.get(addr).cloned().unwrap_or_else(Name::anon)
}

impl<M: KernelMode> Ctx<'_, M> {
  /// Generate a unique synthetic name like `_s0`, `_s1`, etc.
  fn synth_name(&self) -> Name {
    let n = self.synth_counter.get();
    self.synth_counter.set(n + 1);
    Name::str(Name::anon(), format!("_s{n}"))
  }
}

fn resolve_level_params(
  lvl_addrs: &[Address],
  names: &FxHashMap<Address, Name>,
) -> Vec<Name> {
  lvl_addrs.iter().map(|a| resolve_name(a, names)).collect()
}

/// Resolve a list of **Lean-name-hash** addresses to `KId<M>` pairs whose
/// `addr` is the **projection-content address** under which the corresponding
/// KConst is actually stored in `KEnv`.
///
/// The callers (`build_mut_ctx`, `ingress_muts_inductive`'s `ctor_ids`, and
/// `lean_all` reconstruction in `ingress_defn` / `ingress_recursor` /
/// `ingress_muts_inductive`) pull addresses out of `ConstantMetaInfo::*::{all,
/// ctx, ctors}`. Those fields store **name-hash** addresses (they were written
/// by compile via `compile_name`), but each KConst is stored in `KEnv` under
/// its **projection** address (the content hash of the `IPrj` / `CPrj` / `RPrj`
/// / `DPrj` struct, or `block_addr` for singleton Muts classes). The two
/// address spaces are different, so we have to round-trip through the Lean
/// name to recover the projection address:
///
///   name-hash-addr → Lean Name → `ixon_env.named[name].addr` → projection
///
/// If the `name_to_addr` lookup misses, that means the Named entry we expected
/// the compile pipeline to register is missing — bailing with an error is far
/// better than guessing (the prior behavior synthesized a name-hash address as
/// a fallback, which produced **ghost KConsts**: KIds referring to addresses
/// that no KConst was ever stored at, causing obscure downstream lookup
/// failures and alpha-collapse confusion).
fn resolve_all<M: KernelMode>(
  all_addrs: &[Address],
  names: &FxHashMap<Address, Name>,
  name_to_addr: &FxHashMap<Name, Address>,
) -> Result<Vec<KId<M>>, String> {
  all_addrs
    .iter()
    .map(|name_addr| {
      let name = resolve_name(name_addr, names);
      let addr = name_to_addr.get(&name).cloned().ok_or_else(|| {
        format!(
          "resolve_all: Named entry for '{name}' missing in ixon_env.named \
           (expected projection or block address for the compiled constant)"
        )
      })?;
      Ok(KId::new(addr, M::meta_field(name)))
    })
    .collect()
}

fn get_ctx_addrs(meta: &ConstantMeta) -> &[Address] {
  match &meta.info {
    ConstantMetaInfo::Def { ctx, .. }
    | ConstantMetaInfo::Indc { ctx, .. }
    | ConstantMetaInfo::Rec { ctx, .. } => ctx,
    _ => &[],
  }
}

fn build_mut_ctx<M: KernelMode>(
  meta: &ConstantMeta,
  names: &FxHashMap<Address, Name>,
  name_to_addr: &FxHashMap<Name, Address>,
) -> Result<Vec<KId<M>>, String> {
  resolve_all(get_ctx_addrs(meta), names, name_to_addr)
}

// ============================================================================
// Universe ingress (iterative)
// ============================================================================

enum UnivFrame {
  Process(Arc<IxonUniv>),
  Succ,
  MaxLeft(Arc<IxonUniv>),
  Max,
  IMaxLeft(Arc<IxonUniv>),
  IMax,
}

fn ingress_univ<M: KernelMode>(
  root: &Arc<IxonUniv>,
  ctx: &Ctx<'_, M>,
  intern: &InternTable<M>,
  cache: &mut UnivCache<M>,
  stats: &mut ConvertStats,
) -> KUniv<M> {
  bump_convert_stat!(stats, univ_roots);
  let cache_key = Arc::as_ptr(root) as usize;
  if let Some(cached) = cache.get(&cache_key) {
    bump_convert_stat!(stats, univ_cache_hits);
    return cached.clone();
  }
  bump_convert_stat!(stats, univ_cache_misses);

  let mut stack: Vec<UnivFrame> = vec![UnivFrame::Process(root.clone())];
  let mut values: Vec<KUniv<M>> = Vec::new();

  while let Some(frame) = stack.pop() {
    match frame {
      UnivFrame::Process(u) => match u.as_ref() {
        IxonUniv::Zero => {
          bump_convert_stat!(stats, univ_process);
          bump_convert_stat!(stats, univ_interns);
          values.push(timed_intern_univ(intern, KUniv::zero(), stats));
        },
        IxonUniv::Succ(inner) => {
          bump_convert_stat!(stats, univ_process);
          stack.push(UnivFrame::Succ);
          stack.push(UnivFrame::Process(inner.clone()));
        },
        IxonUniv::Max(a, b) => {
          bump_convert_stat!(stats, univ_process);
          stack.push(UnivFrame::Max);
          stack.push(UnivFrame::Process(b.clone()));
          stack.push(UnivFrame::MaxLeft(a.clone()));
        },
        IxonUniv::IMax(a, b) => {
          bump_convert_stat!(stats, univ_process);
          stack.push(UnivFrame::IMax);
          stack.push(UnivFrame::Process(b.clone()));
          stack.push(UnivFrame::IMaxLeft(a.clone()));
        },
        IxonUniv::Var(idx) => {
          bump_convert_stat!(stats, univ_process);
          let pos =
            usize::try_from(*idx).expect("univ var index exceeds usize");
          let name = ctx.lvls.get(pos).cloned().unwrap_or_else(Name::anon);
          bump_convert_stat!(stats, univ_interns);
          values.push(timed_intern_univ(
            intern,
            KUniv::param(*idx, M::meta_field(name)),
            stats,
          ));
        },
      },
      UnivFrame::Succ => {
        let inner = values.pop().unwrap();
        bump_convert_stat!(stats, univ_interns);
        values.push(timed_intern_univ(intern, KUniv::succ(inner), stats));
      },
      UnivFrame::MaxLeft(a) | UnivFrame::IMaxLeft(a) => {
        stack.push(UnivFrame::Process(a));
      },
      UnivFrame::Max => {
        let b = values.pop().unwrap();
        let a = values.pop().unwrap();
        bump_convert_stat!(stats, univ_interns);
        values.push(timed_intern_univ(intern, KUniv::max(a, b), stats));
      },
      UnivFrame::IMax => {
        let b = values.pop().unwrap();
        let a = values.pop().unwrap();
        bump_convert_stat!(stats, univ_interns);
        values.push(timed_intern_univ(intern, KUniv::imax(a, b), stats));
      },
    }
  }

  bump_convert_stat!(stats, univ_interns);
  let result = timed_intern_univ(intern, values.pop().unwrap(), stats);
  cache.insert(cache_key, result.clone());
  if stats.enabled {
    stats.univ_cache_inserts += 1;
    stats.univ_cache_peak = stats.univ_cache_peak.max(cache.len() as u64);
  }
  result
}

fn ingress_univ_args<M: KernelMode>(
  univ_idxs: &[u64],
  ctx: &Ctx<'_, M>,
  intern: &InternTable<M>,
  cache: &mut UnivCache<M>,
  stats: &mut ConvertStats,
) -> Result<Box<[KUniv<M>]>, String> {
  let mut result = Vec::with_capacity(univ_idxs.len());
  for &idx in univ_idxs {
    let i = usize::try_from(idx)
      .map_err(|_e| format!("universe index {idx} exceeds usize"))?;
    let u = ctx.univs.get(i).ok_or_else(|| {
      format!("universe index {i} out of bounds (len {})", ctx.univs.len())
    })?;
    result.push(ingress_univ(u, ctx, intern, cache, stats));
  }
  Ok(result.into_boxed_slice())
}

// ============================================================================
// Expression ingress (iterative)
// ============================================================================

enum ExprFrame<M: KernelMode> {
  Process {
    expr: Arc<IxonExpr>,
    arena_idx: u64,
  },
  AppArg {
    arg: Arc<IxonExpr>,
    arg_arena: u64,
  },
  AppDone {
    mdata: M::MField<Vec<MData>>,
  },
  LamBody {
    body: Arc<IxonExpr>,
    body_arena: u64,
  },
  LamDone {
    name: M::MField<Name>,
    bi: M::MField<BinderInfo>,
    mdata: M::MField<Vec<MData>>,
  },
  AllBody {
    body: Arc<IxonExpr>,
    body_arena: u64,
  },
  AllDone {
    name: M::MField<Name>,
    bi: M::MField<BinderInfo>,
    mdata: M::MField<Vec<MData>>,
  },
  LetVal {
    val: Arc<IxonExpr>,
    val_arena: u64,
    body: Arc<IxonExpr>,
    body_arena: u64,
    binder_name: Name,
  },
  LetBody {
    body: Arc<IxonExpr>,
    body_arena: u64,
  },
  LetDone {
    name: M::MField<Name>,
    nd: bool,
    mdata: M::MField<Vec<MData>>,
  },
  PrjDone {
    type_id: KId<M>,
    field_idx: u64,
    mdata: M::MField<Vec<MData>>,
  },
  Cache {
    key: (usize, u64),
  },
  /// Push a binder name before processing a body (for BVar name resolution).
  BinderPush {
    name: Name,
  },
  /// Pop a binder name after processing a body.
  BinderPop,
}

/// Default empty arena for constants without metadata.
static DEFAULT_ARENA: ExprMeta = ExprMeta { nodes: Vec::new() };

fn ingress_expr<M: KernelMode>(
  root_expr: &Arc<IxonExpr>,
  root_arena: u64,
  ctx: &Ctx<'_, M>,
  ixon_env: &IxonEnv,
  cache: &mut ExprCache<M>,
  univ_cache: &mut UnivCache<M>,
  stats: &mut ConvertStats,
) -> Result<KExpr<M>, String> {
  bump_convert_stat!(stats, expr_roots);
  let mut stack: Vec<ExprFrame<M>> =
    vec![ExprFrame::Process { expr: root_expr.clone(), arena_idx: root_arena }];
  let mut values: Vec<KExpr<M>> = Vec::new();
  // Binder name context for resolving BVar names via de Bruijn index.
  // Pushed when entering a binder body, popped when leaving.
  let mut binder_names: Vec<Name> = Vec::new();

  while let Some(frame) = stack.pop() {
    match frame {
      ExprFrame::Process { mut expr, arena_idx } => {
        bump_convert_stat!(stats, expr_process);
        let process_t0 =
          if stats.enabled { Some(Instant::now()) } else { None };

        // `Share` is transparent and keeps the same arena root. Expand it
        // before cache/mdata work; the old path walked metadata for the Share
        // frame, discarded it, then reprocessed the shared expression.
        while let IxonExpr::Share(share_idx) = expr.as_ref() {
          bump_convert_stat!(stats, share_expansions);
          expr =
            ctx
              .sharing
              .get(usize::try_from(*share_idx).map_err(|_e| {
                format!("Share index {share_idx} exceeds usize")
              })?)
              .ok_or_else(|| format!("invalid Share index {share_idx}"))?
              .clone();
        }

        let is_var = matches!(expr.as_ref(), IxonExpr::Var(_));

        // Check cache before walking mdata. The key includes the original arena
        // root, so a hit already includes the resolved metadata layers.
        let cache_key = (Arc::as_ptr(&expr) as usize, arena_idx);
        if !is_var {
          let lookup_t0 = if stats.enabled {
            Some(Instant::now())
          } else {
            None
          };
          let cached = cache.get(&cache_key);
          if let Some(t0) = lookup_t0 {
            stats.expr_cache_lookup_ns += t0.elapsed().as_nanos() as u64;
          }
          if let Some(cached) = cached {
            bump_convert_stat!(stats, expr_cache_hits);
            values.push(cached.clone());
            if let Some(t0) = process_t0 {
              stats.process_arm_ns += t0.elapsed().as_nanos() as u64;
            }
            continue;
          }
          bump_convert_stat!(stats, expr_cache_misses);
        }

        // Walk mdata chain in arena
        let arena_t0 = if stats.enabled { Some(Instant::now()) } else { None };
        let mut current_idx = arena_idx;
        let mut mdata_layers: Vec<MData> = Vec::new();
        while let Some(ExprMetaData::Mdata { mdata, child }) =
          ctx.arena.nodes.get(
            usize::try_from(current_idx).map_err(|_e| {
              format!("arena index {current_idx} exceeds usize")
            })?,
          )
        {
          bump_convert_stat!(stats, mdata_nodes);
          bump_convert_stat!(stats, mdata_kv_maps, mdata.len());
          let kv_t0 = if stats.enabled { Some(Instant::now()) } else { None };
          for kvm in mdata {
            mdata_layers.push(resolve_kvmap(kvm, ixon_env));
          }
          if let Some(t0) = kv_t0 {
            stats.resolve_kvmap_ns += t0.elapsed().as_nanos() as u64;
            stats.resolve_kvmap_calls += mdata.len() as u64;
          }
          current_idx = *child;
        }
        if let Some(t0) = arena_t0 {
          stats.arena_walk_ns += t0.elapsed().as_nanos() as u64;
        }

        //loop {
        //  match ctx.arena.nodes.get(current_idx as usize) {
        //    Some(ExprMetaData::Mdata { mdata, child }) => {
        //      for kvm in mdata {
        //        mdata_layers.push(resolve_kvmap(kvm, ixon_env));
        //      }
        //      current_idx = *child;
        //    },
        //    _ => break,
        //  }
        //}

        // BVar early return (no caching needed for leaves)
        if let IxonExpr::Var(idx) = expr.as_ref() {
          bump_convert_stat!(stats, var_nodes);
          // Resolve name from the binder context using de Bruijn index.
          let idx_usize = usize::try_from(*idx)
            .map_err(|_e| format!("BVar index {idx} exceeds usize"))?;
          let name = binder_names
            .len()
            .checked_sub(1 + idx_usize)
            .and_then(|i| binder_names.get(i))
            .cloned()
            .unwrap_or_else(Name::anon);
          if mdata_layers.is_empty() {
            let name_field = M::meta_field(name);
            let mdata_field: M::MField<Vec<MData>> = M::meta_field(vec![]);
            let hash = KExpr::<M>::var_hash(*idx, &name_field, &mdata_field);
            values.push(timed_intern_or_build(
              ctx.intern,
              hash,
              |addr| {
                KExpr::var_mdata_with_addr(
                  *idx, name_field, mdata_field, addr,
                )
              },
              stats,
            ));
          } else {
            let name_field = M::meta_field(name);
            let mdata_field = M::meta_field(mdata_layers);
            let hash = KExpr::<M>::var_hash(*idx, &name_field, &mdata_field);
            values.push(timed_intern_or_build(
              ctx.intern,
              hash,
              |addr| {
                KExpr::var_mdata_with_addr(
                  *idx, name_field, mdata_field, addr,
                )
              },
              stats,
            ));
          }
          if let Some(t0) = process_t0 {
            stats.process_arm_ns += t0.elapsed().as_nanos() as u64;
          }
          continue;
        }

        let node =
          ctx
            .arena
            .nodes
            .get(usize::try_from(current_idx).map_err(|_e| {
              format!("arena index {current_idx} exceeds usize")
            })?)
            .unwrap_or(&ExprMetaData::Leaf);

        stack.push(ExprFrame::Cache { key: cache_key });
        let mdata = M::meta_field(mdata_layers);

        match expr.as_ref() {
          IxonExpr::Sort(idx) => {
            bump_convert_stat!(stats, sort_nodes);
            let u =
              ctx
                .univs
                .get(usize::try_from(*idx).map_err(|_e| {
                  format!("Sort univ index {idx} exceeds usize")
                })?)
                .ok_or_else(|| format!("invalid Sort univ index {idx}"))?;
            let zu = ingress_univ(u, ctx, ctx.intern, univ_cache, stats);
            let hash = KExpr::<M>::sort_hash(&zu, &mdata);
            values.push(timed_intern_or_build(
              ctx.intern,
              hash,
              |addr| KExpr::sort_mdata_with_addr(zu, mdata, addr),
              stats,
            ));
          },

          IxonExpr::Var(_) | IxonExpr::Share(_) => unreachable!(),

          IxonExpr::Ref(ref_idx, univ_idxs) => {
            bump_convert_stat!(stats, ref_nodes);
            let addr = ctx
              .refs
              .get(
                usize::try_from(*ref_idx)
                  .map_err(|_e| format!("Ref index {ref_idx} exceeds usize"))?,
              )
              .ok_or_else(|| format!("invalid Ref index {ref_idx}"))?
              .clone();
            let name = match node {
              ExprMetaData::Ref { name: name_addr } => {
                resolve_name(name_addr, ctx.names)
              },
              _ => {
                return Err(format!(
                  "Ref at index {ref_idx} (addr {}) has no metadata name (node={node:?})",
                  &addr.hex()[..8]
                ));
              },
            };
            let univs =
              ingress_univ_args(univ_idxs, ctx, ctx.intern, univ_cache, stats)?;
            let id = KId::new(addr, M::meta_field(name));
            let hash = KExpr::<M>::cnst_hash(&id, &univs, &mdata);
            values.push(timed_intern_or_build(
              ctx.intern,
              hash,
              |a| KExpr::cnst_mdata_with_addr(id, univs, mdata, a),
              stats,
            ));
          },

          IxonExpr::Rec(rec_idx, univ_idxs) => {
            bump_convert_stat!(stats, rec_nodes);
            let mid = ctx
              .mut_ctx
              .get(
                usize::try_from(*rec_idx)
                  .map_err(|_e| format!("Rec index {rec_idx} exceeds usize"))?,
              )
              .ok_or_else(|| format!("invalid Rec index {rec_idx}"))?
              .clone();
            let univs =
              ingress_univ_args(univ_idxs, ctx, ctx.intern, univ_cache, stats)?;
            let hash = KExpr::<M>::cnst_hash(&mid, &univs, &mdata);
            values.push(timed_intern_or_build(
              ctx.intern,
              hash,
              |a| KExpr::cnst_mdata_with_addr(mid, univs, mdata, a),
              stats,
            ));
          },

          IxonExpr::App(f, a) => {
            bump_convert_stat!(stats, app_nodes);
            // CallSite at the outermost App of a surgery spine. The
            // arena replaces the spine's N+1 App/Ref nodes with one
            // flat node whose `canon_meta` carries per-canonical-arg
            // arena indices and whose `name` holds the head's Ref name.
            // Walk the IXON App telescope here and distribute each
            // canonical arg's arena index from `canon_meta`; a plain App
            // descent (`_` arm below) would propagate the CallSite arena
            // down every child, losing per-arg binder names and failing
            // the head's Ref metadata lookup (see
            // `ingress_expr` Ref arm — no `CallSite` matching branch).
            //
            // The head is `IxonExpr::Ref | IxonExpr::Rec`. We build its
            // KExpr here using `cs_name` so the normal Ref arm's
            // `(_, Expr::Ref) => Err(...)` fallback never fires. The
            // compile side's `BuildCallSite` drops the head's own
            // arena root on the floor (the comment there reads
            // "head's Ref metadata is subsumed by CallSite.name"), so
            // there is no other source of truth for the head name.
            if let ExprMetaData::CallSite {
              name: cs_name,
              entries: _,
              canon_meta,
            } = node
            {
              // Flatten the canonical App telescope. `a_i` is the arg
              // applied at spine position `i` (0 = innermost, N-1 =
              // outermost); `head` is the innermost function.
              let mut canonical_args: Vec<Arc<IxonExpr>> = Vec::new();
              let mut cur = expr.clone();
              loop {
                while let IxonExpr::Share(share_idx) = cur.as_ref() {
                  cur = ctx
                    .sharing
                    .get(usize::try_from(*share_idx).map_err(|_e| {
                      format!("Share index {share_idx} exceeds usize")
                    })?)
                    .ok_or_else(|| format!("invalid Share index {share_idx}"))?
                    .clone();
                }
                match cur.as_ref() {
                  IxonExpr::App(f2, a2) => {
                    canonical_args.push(a2.clone());
                    cur = f2.clone();
                  },
                  _ => break,
                }
              }
              canonical_args.reverse();
              let mut head_ixon = cur;
              while let IxonExpr::Share(share_idx) = head_ixon.as_ref() {
                head_ixon = ctx
                  .sharing
                  .get(usize::try_from(*share_idx).map_err(|_e| {
                    format!("Share index {share_idx} exceeds usize")
                  })?)
                  .ok_or_else(|| format!("invalid Share index {share_idx}"))?
                  .clone();
              }
              let n_args = canonical_args.len();
              bump_convert_stat!(stats, callsites);
              bump_convert_stat!(stats, callsite_args, n_args);

              if canon_meta.len() != n_args {
                let head_name = resolve_name(cs_name, ctx.names);
                return Err(format!(
                  "CallSite for '{}' has {} canonical metadata entries but \
                   canonical telescope has {} args",
                  head_name.pretty(),
                  canon_meta.len(),
                  n_args
                ));
              }
              let arg_arenas = canon_meta.clone();

              // Build the head KExpr inline. `cs_name` is the name
              // address stored in the CallSite (e.g. the address of
              // `Code.rec`'s Lean name); resolving it gives the same
              // `Name` the normal Ref arm would produce.
              let head_kexpr: KExpr<M> = match head_ixon.as_ref() {
                IxonExpr::Ref(ref_idx, univ_idxs) => {
                  let addr = ctx
                    .refs
                    .get(usize::try_from(*ref_idx).map_err(|_e| {
                      format!("Ref index {ref_idx} exceeds usize")
                    })?)
                    .ok_or_else(|| {
                      format!("CallSite head: invalid Ref index {ref_idx}")
                    })?
                    .clone();
                  let name = resolve_name(cs_name, ctx.names);
                  let univs = ingress_univ_args(
                    univ_idxs, ctx, ctx.intern, univ_cache, stats,
                  )?;
                  let id = KId::new(addr, M::meta_field(name));
                  let mdata_field: M::MField<Vec<MData>> =
                    M::meta_field(vec![]);
                  let hash =
                    KExpr::<M>::cnst_hash(&id, &univs, &mdata_field);
                  timed_intern_or_build(
                    ctx.intern,
                    hash,
                    |a| {
                      KExpr::cnst_mdata_with_addr(id, univs, mdata_field, a)
                    },
                    stats,
                  )
                },
                IxonExpr::Rec(rec_idx, univ_idxs) => {
                  // Rec heads refer to the enclosing mutual block; the
                  // KId already carries the member's name from
                  // `mut_ctx`, so `cs_name` is redundant here. Kept
                  // the shape parallel to the Ref arm for symmetry.
                  let mid = ctx
                    .mut_ctx
                    .get(usize::try_from(*rec_idx).map_err(|_e| {
                      format!("Rec index {rec_idx} exceeds usize")
                    })?)
                    .ok_or_else(|| {
                      format!("CallSite head: invalid Rec index {rec_idx}")
                    })?
                    .clone();
                  let univs = ingress_univ_args(
                    univ_idxs, ctx, ctx.intern, univ_cache, stats,
                  )?;
                  let mdata_field: M::MField<Vec<MData>> =
                    M::meta_field(vec![]);
                  let hash =
                    KExpr::<M>::cnst_hash(&mid, &univs, &mdata_field);
                  timed_intern_or_build(
                    ctx.intern,
                    hash,
                    |a| {
                      KExpr::cnst_mdata_with_addr(mid, univs, mdata_field, a)
                    },
                    stats,
                  )
                },
                _ => {
                  return Err(format!(
                    "CallSite head is not Ref/Rec: {:?}",
                    head_ixon
                  ));
                },
              };

              // Emit the canonical App spine via AppArg/AppDone pairs.
              // Push order — LIFO, so last pushed is first processed:
              //
              //   push AppDone_outer (carries `mdata`)
              //   push AppArg(a_{N-1})
              //   push AppDone for each middle/inner App (no mdata)
              //   push AppArg(a_i) for i from N-2 down to 0
              //   push head_kexpr onto `values` (processed "first")
              //
              // Execution then pops AppArg(a_0), Process(a_0), runs
              // the innermost AppDone to wrap (head, a_0), pops
              // AppArg(a_1), runs the next AppDone, …, ending with
              // AppDone_outer applying `mdata` to the full spine.
              // Inner AppDones use an empty mdata because the IXON
              // Mdata variant lives outside the App chain — only the
              // outermost App carries the wrapper.
              let no_mdata_inner: M::MField<Vec<MData>> = M::meta_field(vec![]);

              if n_args == 0 {
                // Defensive: we only arrive here from IxonExpr::App,
                // so n_args >= 1. Fall through safely anyway.
                values.push(head_kexpr);
              } else {
                // Outermost AppDone (with mdata) + AppArg for the
                // outermost arg.
                stack.push(ExprFrame::AppDone { mdata });
                stack.push(ExprFrame::AppArg {
                  arg: canonical_args[n_args - 1].clone(),
                  arg_arena: arg_arenas[n_args - 1],
                });
                // Middle + inner AppDones (no mdata) + AppArgs for
                // args n_args-2 down to 0. Iterating in reverse keeps
                // each (AppDone, AppArg) pair in the correct LIFO
                // position.
                for i in (0..n_args - 1).rev() {
                  stack
                    .push(ExprFrame::AppDone { mdata: no_mdata_inner.clone() });
                  stack.push(ExprFrame::AppArg {
                    arg: canonical_args[i].clone(),
                    arg_arena: arg_arenas[i],
                  });
                }
                // Seed `values` with the head so the first AppDone
                // popped sees (head, a_0) and produces App(head, a_0).
                values.push(head_kexpr);
              }
            } else {
              let (f_arena, a_arena) = match node {
                ExprMetaData::App { children } => (children[0], children[1]),
                _ => (current_idx, current_idx),
              };
              stack.push(ExprFrame::AppDone { mdata });
              stack
                .push(ExprFrame::AppArg { arg: a.clone(), arg_arena: a_arena });
              stack.push(ExprFrame::Process {
                expr: f.clone(),
                arena_idx: f_arena,
              });
            }
          },

          IxonExpr::Lam(ty, body) => {
            bump_convert_stat!(stats, lam_nodes);
            let (name, bi, ty_arena, body_arena) = match node {
              ExprMetaData::Binder { name: addr, info, children } => (
                resolve_name(addr, ctx.names),
                info.clone(),
                children[0],
                children[1],
              ),
              _ => (
                ctx.synth_name(),
                BinderInfo::Default,
                current_idx,
                current_idx,
              ),
            };
            stack.push(ExprFrame::LamDone {
              name: M::meta_field(name.clone()),
              bi: M::meta_field(bi),
              mdata,
            });
            stack.push(ExprFrame::BinderPop);
            stack.push(ExprFrame::LamBody { body: body.clone(), body_arena });
            stack.push(ExprFrame::BinderPush { name });
            stack.push(ExprFrame::Process {
              expr: ty.clone(),
              arena_idx: ty_arena,
            });
          },

          IxonExpr::All(ty, body) => {
            bump_convert_stat!(stats, all_nodes);
            let (name, bi, ty_arena, body_arena) = match node {
              ExprMetaData::Binder { name: addr, info, children } => (
                resolve_name(addr, ctx.names),
                info.clone(),
                children[0],
                children[1],
              ),
              _ => (
                ctx.synth_name(),
                BinderInfo::Default,
                current_idx,
                current_idx,
              ),
            };
            stack.push(ExprFrame::AllDone {
              name: M::meta_field(name.clone()),
              bi: M::meta_field(bi),
              mdata,
            });
            stack.push(ExprFrame::BinderPop);
            stack.push(ExprFrame::AllBody { body: body.clone(), body_arena });
            stack.push(ExprFrame::BinderPush { name });
            stack.push(ExprFrame::Process {
              expr: ty.clone(),
              arena_idx: ty_arena,
            });
          },

          IxonExpr::Let(nd, ty, val, body) => {
            bump_convert_stat!(stats, let_nodes);
            let (name, ty_arena, val_arena, body_arena) = match node {
              ExprMetaData::LetBinder { name: addr, children } => (
                resolve_name(addr, ctx.names),
                children[0],
                children[1],
                children[2],
              ),
              _ => (ctx.synth_name(), current_idx, current_idx, current_idx),
            };
            stack.push(ExprFrame::LetDone {
              name: M::meta_field(name.clone()),
              nd: *nd,
              mdata,
            });
            stack.push(ExprFrame::BinderPop);
            stack.push(ExprFrame::LetVal {
              val: val.clone(),
              val_arena,
              body: body.clone(),
              body_arena,
              binder_name: name,
            });
            stack.push(ExprFrame::Process {
              expr: ty.clone(),
              arena_idx: ty_arena,
            });
          },

          IxonExpr::Prj(type_ref_idx, field_idx, s) => {
            bump_convert_stat!(stats, prj_nodes);
            let type_addr = ctx
              .refs
              .get(usize::try_from(*type_ref_idx).map_err(|_e| {
                format!("Prj type ref index {type_ref_idx} exceeds usize")
              })?)
              .ok_or_else(|| {
                format!("invalid Prj type ref index {type_ref_idx}")
              })?
              .clone();
            let (struct_name, child_arena) = match node {
              ExprMetaData::Prj { struct_name: addr, child } => {
                (resolve_name(addr, ctx.names), *child)
              },
              _ => {
                return Err(format!(
                  "Prj at ref index {type_ref_idx} (addr {}) has no metadata name (node={node:?})",
                  &type_addr.hex()[..8]
                ));
              },
            };
            stack.push(ExprFrame::PrjDone {
              type_id: KId::new(type_addr, M::meta_field(struct_name)),
              field_idx: *field_idx,
              mdata,
            });
            stack.push(ExprFrame::Process {
              expr: s.clone(),
              arena_idx: child_arena,
            });
          },

          IxonExpr::Str(ref_idx) => {
            bump_convert_stat!(stats, str_nodes);
            let addr = ctx
              .refs
              .get(usize::try_from(*ref_idx).map_err(|_e| {
                format!("Str ref index {ref_idx} exceeds usize")
              })?)
              .ok_or_else(|| format!("invalid Str ref index {ref_idx}"))?;
            let gb_t0 = if stats.enabled { Some(Instant::now()) } else { None };
            let blob = ixon_env.get_blob(addr).ok_or_else(|| {
              format!("missing Str blob at addr {}", addr.hex())
            })?;
            if let Some(t0) = gb_t0 {
              stats.get_blob_ns += t0.elapsed().as_nanos() as u64;
              stats.get_blob_calls += 1;
            }
            let s = String::from_utf8(blob).map_err(|e| {
              format!("invalid UTF-8 in Str blob at addr {}: {e}", addr.hex())
            })?;
            let blob_addr = addr.clone();
            let hash = KExpr::<M>::str_hash(&blob_addr, &mdata);
            values.push(timed_intern_or_build(
              ctx.intern,
              hash,
              |a| KExpr::str_mdata_with_addr(s, blob_addr, mdata, a),
              stats,
            ));
          },

          IxonExpr::Nat(ref_idx) => {
            bump_convert_stat!(stats, nat_nodes);
            let addr = ctx
              .refs
              .get(usize::try_from(*ref_idx).map_err(|_e| {
                format!("Nat ref index {ref_idx} exceeds usize")
              })?)
              .ok_or_else(|| format!("invalid Nat ref index {ref_idx}"))?;
            let gb_t0 = if stats.enabled { Some(Instant::now()) } else { None };
            let blob = ixon_env.get_blob(addr).ok_or_else(|| {
              format!("missing Nat blob at addr {}", addr.hex())
            })?;
            if let Some(t0) = gb_t0 {
              stats.get_blob_ns += t0.elapsed().as_nanos() as u64;
              stats.get_blob_calls += 1;
            }
            let n = Nat::from_le_bytes(&blob);
            let blob_addr = addr.clone();
            let hash = KExpr::<M>::nat_hash(&blob_addr, &mdata);
            values.push(timed_intern_or_build(
              ctx.intern,
              hash,
              |a| KExpr::nat_mdata_with_addr(n, blob_addr, mdata, a),
              stats,
            ));
          },
        }
        if let Some(t0) = process_t0 {
          stats.process_arm_ns += t0.elapsed().as_nanos() as u64;
        }
      },

      // Continuation frames
      ExprFrame::AppArg { arg, arg_arena } => {
        let cont_t0 =
          if stats.enabled { Some(Instant::now()) } else { None };
        stack.push(ExprFrame::Process { expr: arg, arena_idx: arg_arena });
        if let Some(t0) = cont_t0 {
          stats.continuation_arms_ns += t0.elapsed().as_nanos() as u64;
        }
      },
      ExprFrame::AppDone { mdata } => {
        let cont_t0 =
          if stats.enabled { Some(Instant::now()) } else { None };
        let a = values.pop().unwrap();
        let f = values.pop().unwrap();
        let hash = KExpr::<M>::app_hash(&f, &a, &mdata);
        values.push(timed_intern_or_build(
          ctx.intern,
          hash,
          |addr| KExpr::app_mdata_with_addr(f, a, mdata, addr),
          stats,
        ));
        if let Some(t0) = cont_t0 {
          stats.continuation_arms_ns += t0.elapsed().as_nanos() as u64;
        }
      },
      ExprFrame::LamBody { body, body_arena } => {
        let cont_t0 =
          if stats.enabled { Some(Instant::now()) } else { None };
        // The binder name was already pushed by BinderPush before this frame
        stack.push(ExprFrame::Process { expr: body, arena_idx: body_arena });
        if let Some(t0) = cont_t0 {
          stats.continuation_arms_ns += t0.elapsed().as_nanos() as u64;
        }
      },
      ExprFrame::LamDone { name, bi, mdata } => {
        let cont_t0 =
          if stats.enabled { Some(Instant::now()) } else { None };
        let body = values.pop().unwrap();
        let ty = values.pop().unwrap();
        let hash = KExpr::<M>::lam_hash(&name, &bi, &ty, &body, &mdata);
        values.push(timed_intern_or_build(
          ctx.intern,
          hash,
          |addr| KExpr::lam_mdata_with_addr(name, bi, ty, body, mdata, addr),
          stats,
        ));
        if let Some(t0) = cont_t0 {
          stats.continuation_arms_ns += t0.elapsed().as_nanos() as u64;
        }
      },
      ExprFrame::AllBody { body, body_arena }
      | ExprFrame::LetBody { body, body_arena } => {
        let cont_t0 =
          if stats.enabled { Some(Instant::now()) } else { None };
        stack.push(ExprFrame::Process { expr: body, arena_idx: body_arena });
        if let Some(t0) = cont_t0 {
          stats.continuation_arms_ns += t0.elapsed().as_nanos() as u64;
        }
      },
      ExprFrame::AllDone { name, bi, mdata } => {
        let cont_t0 =
          if stats.enabled { Some(Instant::now()) } else { None };
        let body = values.pop().unwrap();
        let ty = values.pop().unwrap();
        let hash = KExpr::<M>::all_hash(&name, &bi, &ty, &body, &mdata);
        values.push(timed_intern_or_build(
          ctx.intern,
          hash,
          |addr| KExpr::all_mdata_with_addr(name, bi, ty, body, mdata, addr),
          stats,
        ));
        if let Some(t0) = cont_t0 {
          stats.continuation_arms_ns += t0.elapsed().as_nanos() as u64;
        }
      },
      ExprFrame::LetVal { val, val_arena, body, body_arena, binder_name } => {
        let cont_t0 =
          if stats.enabled { Some(Instant::now()) } else { None };
        stack.push(ExprFrame::LetBody { body, body_arena });
        stack.push(ExprFrame::BinderPush { name: binder_name });
        stack.push(ExprFrame::Process { expr: val, arena_idx: val_arena });
        if let Some(t0) = cont_t0 {
          stats.continuation_arms_ns += t0.elapsed().as_nanos() as u64;
        }
      },
      ExprFrame::LetDone { name, nd, mdata } => {
        let cont_t0 =
          if stats.enabled { Some(Instant::now()) } else { None };
        let body = values.pop().unwrap();
        let val = values.pop().unwrap();
        let ty = values.pop().unwrap();
        let hash = KExpr::<M>::let_hash(&name, &ty, &val, &body, nd, &mdata);
        values.push(timed_intern_or_build(
          ctx.intern,
          hash,
          |addr| {
            KExpr::let_mdata_with_addr(name, ty, val, body, nd, mdata, addr)
          },
          stats,
        ));
        if let Some(t0) = cont_t0 {
          stats.continuation_arms_ns += t0.elapsed().as_nanos() as u64;
        }
      },
      ExprFrame::BinderPush { name } => {
        let cont_t0 =
          if stats.enabled { Some(Instant::now()) } else { None };
        binder_names.push(name);
        if let Some(t0) = cont_t0 {
          stats.continuation_arms_ns += t0.elapsed().as_nanos() as u64;
        }
      },
      ExprFrame::BinderPop => {
        let cont_t0 =
          if stats.enabled { Some(Instant::now()) } else { None };
        binder_names.pop();
        if let Some(t0) = cont_t0 {
          stats.continuation_arms_ns += t0.elapsed().as_nanos() as u64;
        }
      },
      ExprFrame::PrjDone { type_id, field_idx, mdata } => {
        let cont_t0 =
          if stats.enabled { Some(Instant::now()) } else { None };
        let s = values.pop().unwrap();
        let hash = KExpr::<M>::prj_hash(&type_id, field_idx, &s, &mdata);
        values.push(timed_intern_or_build(
          ctx.intern,
          hash,
          |addr| {
            KExpr::prj_mdata_with_addr(type_id, field_idx, s, mdata, addr)
          },
          stats,
        ));
        if let Some(t0) = cont_t0 {
          stats.continuation_arms_ns += t0.elapsed().as_nanos() as u64;
        }
      },
      ExprFrame::Cache { key } => {
        let cont_t0 =
          if stats.enabled { Some(Instant::now()) } else { None };
        let result = values.last().unwrap().clone();
        let ins_t0 = if stats.enabled { Some(Instant::now()) } else { None };
        cache.insert(key, result);
        if let Some(t0) = ins_t0 {
          stats.expr_cache_insert_ns += t0.elapsed().as_nanos() as u64;
          stats.expr_cache_inserts += 1;
          stats.expr_cache_peak = stats.expr_cache_peak.max(cache.len() as u64);
        }
        if let Some(t0) = cont_t0 {
          stats.continuation_arms_ns += t0.elapsed().as_nanos() as u64;
        }
      },
    }
  }

  values.pop().ok_or_else(|| "ingress_expr: empty value stack".to_string())
}

// ============================================================================
// Constant ingress
// ============================================================================

#[allow(clippy::too_many_arguments)]
fn ingress_defn<M: KernelMode>(
  def: &crate::ix::ixon::constant::Definition,
  self_id: KId<M>,
  meta: &ConstantMeta,
  ixon_env: &IxonEnv,
  names: &FxHashMap<Address, Name>,
  name_to_addr: &FxHashMap<Name, Address>,
  sharing: &[Arc<IxonExpr>],
  refs: &[Address],
  univs: &[Arc<IxonUniv>],
  block: KId<M>,
  intern: &InternTable<M>,
  stats: &mut ConvertStats,
) -> Result<Vec<(KId<M>, KConst<M>)>, String> {
  let mut cache: ExprCache<M> = FxHashMap::default();
  let mut univ_cache: UnivCache<M> = FxHashMap::default();
  let (level_params, arena, type_root, value_root, hints, safety, all_addrs) =
    match &meta.info {
      ConstantMetaInfo::Def {
        lvls,
        arena,
        type_root,
        value_root,
        hints,
        all,
        ..
      } => (
        resolve_level_params(lvls, names),
        arena,
        *type_root,
        *value_root,
        *hints,
        def.safety,
        all.clone(),
      ),
      _ => (
        vec![],
        &DEFAULT_ARENA,
        0,
        0,
        ReducibilityHints::Regular(0),
        def.safety,
        vec![],
      ),
    };

  let ctx = Ctx {
    sharing,
    refs,
    univs,
    mut_ctx: build_mut_ctx(meta, names, name_to_addr)?,
    arena,
    names,
    lvls: level_params.clone(),
    intern,
    synth_counter: Cell::new(0),
  };

  let typ = ingress_expr(
    &def.typ,
    type_root,
    &ctx,
    ixon_env,
    &mut cache,
    &mut univ_cache,
    stats,
  )?;
  let value = ingress_expr(
    &def.value,
    value_root,
    &ctx,
    ixon_env,
    &mut cache,
    &mut univ_cache,
    stats,
  )?;
  let lean_all = resolve_all(&all_addrs, names, name_to_addr)?;

  let name = resolve_name(
    match &meta.info {
      ConstantMetaInfo::Def { name, .. } => name,
      _ => &self_id.addr,
    },
    names,
  );

  Ok(vec![(
    self_id,
    KConst::Defn {
      name: M::meta_field(name),
      level_params: M::meta_field(level_params),
      kind: def.kind,
      safety,
      hints,
      lvls: def.lvls,
      ty: typ,
      val: value,
      lean_all: M::meta_field(lean_all),
      block,
    },
  )])
}

#[allow(clippy::too_many_arguments)]
fn ingress_recursor<M: KernelMode>(
  rec: &crate::ix::ixon::constant::Recursor,
  self_id: KId<M>,
  meta: &ConstantMeta,
  ixon_env: &IxonEnv,
  names: &FxHashMap<Address, Name>,
  name_to_addr: &FxHashMap<Name, Address>,
  sharing: &[Arc<IxonExpr>],
  refs: &[Address],
  univs: &[Arc<IxonUniv>],
  block: KId<M>,
  intern: &InternTable<M>,
  stats: &mut ConvertStats,
) -> Result<Vec<(KId<M>, KConst<M>)>, String> {
  let mut cache: ExprCache<M> = FxHashMap::default();
  let mut univ_cache: UnivCache<M> = FxHashMap::default();
  let (level_params, arena, type_root, rule_roots, rule_ctor_addrs, all_addrs) =
    match &meta.info {
      ConstantMetaInfo::Rec {
        lvls,
        arena,
        type_root,
        rule_roots,
        rules,
        all,
        ..
      } => (
        resolve_level_params(lvls, names),
        arena,
        *type_root,
        rule_roots.clone(),
        rules.clone(),
        all.clone(),
      ),
      _ => (vec![], &DEFAULT_ARENA, 0, vec![], vec![], vec![]),
    };

  let ctx = Ctx {
    sharing,
    refs,
    univs,
    mut_ctx: build_mut_ctx(meta, names, name_to_addr)?,
    arena,
    names,
    lvls: level_params.clone(),
    intern,
    synth_counter: Cell::new(0),
  };

  let typ = ingress_expr(
    &rec.typ,
    type_root,
    &ctx,
    ixon_env,
    &mut cache,
    &mut univ_cache,
    stats,
  )?;
  let rules: Result<Vec<RecRule<M>>, String> = rec
    .rules
    .iter()
    .enumerate()
    .map(|(i, rule)| {
      // If the meta arm above matched `Rec`, we have one `rule_root` per
      // Ixon rule (compile emits them in lockstep). The `DEFAULT_ARENA`
      // fallback arm supplies an empty `rule_roots` vec, in which case
      // falling back to root 0 is fine because the arena is empty — every
      // arena index then misses and degrades to `ExprMetaData::Leaf`.
      let rhs_root = rule_roots.get(i).copied().unwrap_or(0);
      let rhs = ingress_expr(
        &rule.rhs,
        rhs_root,
        &ctx,
        ixon_env,
        &mut cache,
        &mut univ_cache,
        stats,
      )?;
      // `ConstantMetaInfo::Rec::rules[i]` is the name-hash address of the
      // i-th rule's ctor. Resolve it through the names map; fall back to
      // anonymous when metadata is absent (recursor compiled without
      // meta, e.g. synthetic kernel tests).
      let ctor_name = rule_ctor_addrs
        .get(i)
        .map_or_else(Name::anon, |a| resolve_name(a, names));
      Ok(RecRule { ctor: M::meta_field(ctor_name), fields: rule.fields, rhs })
    })
    .collect();
  let lean_all = resolve_all(&all_addrs, names, name_to_addr)?;

  let name = resolve_name(
    match &meta.info {
      ConstantMetaInfo::Rec { name, .. } => name,
      _ => &self_id.addr,
    },
    names,
  );

  Ok(vec![(
    self_id,
    KConst::Recr {
      name: M::meta_field(name),
      level_params: M::meta_field(level_params),
      k: rec.k,
      is_unsafe: rec.is_unsafe,
      lvls: rec.lvls,
      params: rec.params,
      indices: rec.indices,
      motives: rec.motives,
      minors: rec.minors,
      block,
      member_idx: 0, // filled in by caller for muts blocks
      ty: typ,
      rules: rules?,
      lean_all: M::meta_field(lean_all),
    },
  )])
}

#[allow(clippy::too_many_arguments)]
fn ingress_standalone<M: KernelMode>(
  const_name: &Name,
  addr: &Address,
  constant: &Constant,
  meta: &ConstantMeta,
  ixon_env: &IxonEnv,
  names: &FxHashMap<Address, Name>,
  name_to_addr: &FxHashMap<Name, Address>,
  intern: &InternTable<M>,
  stats: &mut ConvertStats,
) -> Result<Vec<(KId<M>, KConst<M>)>, String> {
  let self_id: KId<M> =
    KId::new(addr.clone(), M::meta_field(const_name.clone()));

  match &constant.info {
    IxonCI::Defn(def) => ingress_defn(
      def,
      self_id.clone(),
      meta,
      ixon_env,
      names,
      name_to_addr,
      &constant.sharing,
      &constant.refs,
      &constant.univs,
      self_id,
      intern,
      stats,
    ),

    IxonCI::Axio(ax) => {
      let mut cache: ExprCache<M> = FxHashMap::default();
      let mut univ_cache: UnivCache<M> = FxHashMap::default();
      let (level_params, arena, type_root) = match &meta.info {
        ConstantMetaInfo::Axio { lvls, arena, type_root, .. } => {
          (resolve_level_params(lvls, names), arena, *type_root)
        },
        _ => (vec![], &DEFAULT_ARENA, 0),
      };
      let ctx = Ctx {
        sharing: &constant.sharing,
        refs: &constant.refs,
        univs: &constant.univs,
        mut_ctx: vec![],
        arena,
        names,
        lvls: level_params.clone(),
        intern,
        synth_counter: Cell::new(0),
      };
      let typ = ingress_expr(
        &ax.typ,
        type_root,
        &ctx,
        ixon_env,
        &mut cache,
        &mut univ_cache,
        stats,
      )?;
      let name = resolve_name(
        match &meta.info {
          ConstantMetaInfo::Axio { name, .. } => name,
          _ => addr,
        },
        names,
      );
      Ok(vec![(
        self_id,
        KConst::Axio {
          name: M::meta_field(name),
          level_params: M::meta_field(level_params),
          is_unsafe: ax.is_unsafe,
          lvls: ax.lvls,
          ty: typ,
        },
      )])
    },

    IxonCI::Quot(q) => {
      let mut cache: ExprCache<M> = FxHashMap::default();
      let mut univ_cache: UnivCache<M> = FxHashMap::default();
      let (level_params, arena, type_root) = match &meta.info {
        ConstantMetaInfo::Quot { lvls, arena, type_root, .. } => {
          (resolve_level_params(lvls, names), arena, *type_root)
        },
        _ => (vec![], &DEFAULT_ARENA, 0),
      };
      let ctx = Ctx {
        sharing: &constant.sharing,
        refs: &constant.refs,
        univs: &constant.univs,
        mut_ctx: vec![],
        arena,
        names,
        lvls: level_params.clone(),
        intern,
        synth_counter: Cell::new(0),
      };
      let typ = ingress_expr(
        &q.typ,
        type_root,
        &ctx,
        ixon_env,
        &mut cache,
        &mut univ_cache,
        stats,
      )?;
      let name = resolve_name(
        match &meta.info {
          ConstantMetaInfo::Quot { name, .. } => name,
          _ => addr,
        },
        names,
      );
      Ok(vec![(
        self_id,
        KConst::Quot {
          name: M::meta_field(name),
          level_params: M::meta_field(level_params),
          kind: q.kind,
          lvls: q.lvls,
          ty: typ,
        },
      )])
    },

    IxonCI::Recr(rec) => ingress_recursor(
      rec,
      self_id.clone(),
      meta,
      ixon_env,
      names,
      name_to_addr,
      &constant.sharing,
      &constant.refs,
      &constant.univs,
      self_id,
      intern,
      stats,
    ),

    // Projections and Muts are handled in ingress_muts_block
    IxonCI::IPrj(_)
    | IxonCI::CPrj(_)
    | IxonCI::RPrj(_)
    | IxonCI::DPrj(_)
    | IxonCI::Muts(_) => Ok(vec![]),
  }
}

// ============================================================================
// Muts block ingress
// ============================================================================

#[allow(clippy::too_many_arguments)]
fn ingress_muts_inductive<M: KernelMode>(
  ind: &crate::ix::ixon::constant::Inductive,
  self_id: &KId<M>,
  meta: &ConstantMeta,
  ixon_env: &IxonEnv,
  names: &FxHashMap<Address, Name>,
  name_to_addr: &FxHashMap<Name, Address>,
  block_constant: &Constant,
  block_id: KId<M>,
  member_idx: u64,
  intern: &InternTable<M>,
  stats: &mut ConvertStats,
) -> Result<Vec<(KId<M>, KConst<M>)>, String> {
  let (level_params, arena, type_root, all_addrs, ctor_addrs) = match &meta.info
  {
    ConstantMetaInfo::Indc { lvls, arena, type_root, all, ctors, .. } => (
      resolve_level_params(lvls, names),
      arena,
      *type_root,
      all.clone(),
      ctors.clone(),
    ),
    _ => (vec![], &DEFAULT_ARENA, 0, vec![], vec![]),
  };

  let mut cache: ExprCache<M> = FxHashMap::default();
  let mut univ_cache: UnivCache<M> = FxHashMap::default();
  let mut_ctx = build_mut_ctx(meta, names, name_to_addr)?;
  let ctx = Ctx {
    sharing: &block_constant.sharing,
    refs: &block_constant.refs,
    univs: &block_constant.univs,
    mut_ctx,
    arena,
    names,
    lvls: level_params.clone(),
    intern,
    synth_counter: Cell::new(0),
  };

  let typ = ingress_expr(
    &ind.typ,
    type_root,
    &ctx,
    ixon_env,
    &mut cache,
    &mut univ_cache,
    stats,
  )?;
  let lean_all = resolve_all(&all_addrs, names, name_to_addr)?;
  // Constructor KIds: `ctor_addrs` holds the **name-hash** addresses the
  // compile pass stored in `ConstantMetaInfo::Indc::ctors`, but each Ctor
  // `KConst` is registered in the kernel env under its **projection**
  // address (`CPrj` content hash). We must therefore round-trip through
  // the Lean name to look up the projection address — see `resolve_all`
  // for the rationale. Calling `resolve_all` directly reuses that error
  // handling (error on missing Named instead of guessing a name-hash).
  let ctor_ids: Vec<KId<M>> = resolve_all(&ctor_addrs, names, name_to_addr)?;

  let name = resolve_name(
    match &meta.info {
      ConstantMetaInfo::Indc { name, .. } => name,
      _ => &self_id.addr,
    },
    names,
  );

  let mut results = vec![(
    self_id.clone(),
    KConst::Indc {
      name: M::meta_field(name),
      level_params: M::meta_field(level_params.clone()),
      lvls: ind.lvls,
      params: ind.params,
      indices: ind.indices,
      is_rec: ind.recr,
      is_refl: ind.refl,
      is_unsafe: ind.is_unsafe,
      nested: ind.nested,
      block: block_id,
      member_idx,
      ty: typ,
      ctors: ctor_ids.clone(),
      lean_all: M::meta_field(lean_all),
    },
  )];

  // Emit constructors. For each position `cidx`, `ctor_addrs[cidx]` is the
  // name-hash address of the ctor's Lean name; from that we resolve the name
  // and then look up its per-ctor ConstantMeta (holding the ctor's own arena
  // and type_root). These must be present — the parent inductive's meta
  // doesn't carry ctor-specific expression metadata inline, so if the Named
  // entry is missing we'd be roundtripping with no arena and synthesize junk
  // binder names. Error loudly instead of silently falling back.
  for (cidx, ctor) in ind.ctors.iter().enumerate() {
    stats.record_cache_clear(&cache);
    cache.clear();
    let ctor_id = ctor_ids
      .get(cidx)
      .cloned()
      .ok_or_else(|| format!("missing ctor_id for constructor index {cidx}"))?;
    let ctor_name_addr = ctor_addrs.get(cidx).ok_or_else(|| {
      format!("missing ctor_addrs entry for constructor index {cidx}")
    })?;
    let ctor_name = resolve_name(ctor_name_addr, names);
    let ctor_named = ixon_env.lookup_name(&ctor_name).ok_or_else(|| {
      format!(
        "missing Named entry for ctor '{ctor_name}' (cidx={cidx}) — \
         per-ctor metadata (arena, type_root, lvls) must be registered \
         for every constructor of this inductive block"
      )
    })?;

    let (ctor_lvl_params, ctor_arena, ctor_type_root) =
      match &ctor_named.meta.info {
        ConstantMetaInfo::Ctor { lvls, arena, type_root, .. } => {
          (resolve_level_params(lvls, names), arena, *type_root)
        },
        other => {
          return Err(format!(
            "ctor '{ctor_name}' has unexpected meta kind '{}' (expected Ctor)",
            other.kind_name()
          ));
        },
      };

    let ctor_ctx = Ctx {
      sharing: &block_constant.sharing,
      refs: &block_constant.refs,
      univs: &block_constant.univs,
      mut_ctx: ctx.mut_ctx.clone(),
      arena: ctor_arena,
      names,
      lvls: ctor_lvl_params.clone(),
      intern,
      synth_counter: Cell::new(0),
    };
    let mut ctor_univ_cache: UnivCache<M> = FxHashMap::default();

    let ctor_typ = ingress_expr(
      &ctor.typ,
      ctor_type_root,
      &ctor_ctx,
      ixon_env,
      &mut cache,
      &mut ctor_univ_cache,
      stats,
    )?;

    results.push((
      ctor_id,
      KConst::Ctor {
        name: M::meta_field(ctor_name),
        level_params: M::meta_field(ctor_lvl_params),
        is_unsafe: ctor.is_unsafe,
        lvls: ctor.lvls,
        induct: self_id.clone(),
        cidx: ctor.cidx,
        params: ctor.params,
        fields: ctor.fields,
        ty: ctor_typ,
      },
    ));
  }

  Ok(results)
}

#[allow(clippy::too_many_arguments)]
fn ingress_muts_block<M: KernelMode>(
  entry_name: &Name,
  entry_addr: &Address,
  all: &[Vec<Address>],
  ixon_env: &IxonEnv,
  names: &FxHashMap<Address, Name>,
  name_to_addr: &FxHashMap<Name, Address>,
  intern: &InternTable<M>,
  stats: &mut ConvertStats,
) -> Result<Vec<(KId<M>, KConst<M>)>, String> {
  let block_id: KId<M> =
    KId::new(entry_addr.clone(), M::meta_field(entry_name.clone()));

  let block_constant = ixon_env.get_const(entry_addr).ok_or_else(|| {
    format!("missing Muts block constant {}", entry_addr.hex())
  })?;
  let members = match &block_constant.info {
    IxonCI::Muts(m) => m,
    _ => return Err(format!("constant at {} is not Muts", entry_addr.hex())),
  };

  let mut results: Vec<(KId<M>, KConst<M>)> = Vec::new();

  for (i, member) in members.iter().enumerate() {
    // `all[i][0]` is the name-hash address of this member's canonical Lean
    // name; we read the per-member metadata (arena, type_root, etc.) from
    // that Named entry. Note the address distinction: `primary_name_addr`
    // is a *name-content* hash (Blake3 of the Lean name components),
    // whereas `member_named.addr` is the *projection-constant* content
    // hash (address of the IPrj/CPrj/RPrj/DPrj struct that projects this
    // member out of the enclosing Muts block). We want the projection
    // address for the `KId`, because that's the address under which every
    // `Expr::Ref` to this member in the rest of the env was registered.
    //
    // Error loudly if the Named entry is missing — the Muts-registration
    // pass in `compile/mutual.rs` is supposed to emit one per member, and
    // a missing entry means the compile phase dropped work we need here.
    let primary_name_addr = all
      .get(i)
      .and_then(|cls| cls.first())
      .ok_or_else(|| format!("Muts block member {i} has no name in all"))?;
    let member_name = resolve_name(primary_name_addr, names);

    let member_named = ixon_env.lookup_name(&member_name).ok_or_else(|| {
      format!("Muts member '{member_name}' not found in named entries")
    })?;
    let member_addr = &member_named.addr;
    let member_meta = &member_named.meta;

    let self_id: KId<M> =
      KId::new(member_addr.clone(), M::meta_field(member_name.clone()));

    match member {
      IxonMutConst::Indc(ind) => {
        results.extend(ingress_muts_inductive(
          ind,
          &self_id,
          member_meta,
          ixon_env,
          names,
          name_to_addr,
          &block_constant,
          block_id.clone(),
          i as u64,
          intern,
          stats,
        )?);
      },
      IxonMutConst::Recr(rec) => {
        results.extend(ingress_recursor(
          rec,
          self_id,
          member_meta,
          ixon_env,
          names,
          name_to_addr,
          &block_constant.sharing,
          &block_constant.refs,
          &block_constant.univs,
          block_id.clone(),
          intern,
          stats,
        )?);
      },
      IxonMutConst::Defn(def) => {
        results.extend(ingress_defn(
          def,
          self_id,
          member_meta,
          ixon_env,
          names,
          name_to_addr,
          &block_constant.sharing,
          &block_constant.refs,
          &block_constant.univs,
          block_id.clone(),
          intern,
          stats,
        )?);
      },
    }
  }

  // Canonicity validation for Indc-only blocks.
  //
  // Per `docs/ix_canonicity.md` §6.0, the inductive block's primary
  // members ship in `sort_consts` canonical order. Take that ordering
  // as the alleged partition (each member ↔ class index = its position)
  // and reject any adjacent pair that doesn't satisfy strict `Less`.
  //
  // Skip Recr blocks (they contain primary + aux recursors, with the
  // aux portion in kernel-computed canonical order, not stored
  // sort_consts) and Defn blocks (the plan focuses on Indc; defn-block
  // ordering can be added later if needed).
  //
  // Returns `TcError::NonCanonicalBlock` on failure, propagated as the
  // string error variant `ingress_muts_block` already returns.
  let mut indcs: Vec<(KId<M>, &KConst<M>)> = Vec::new();
  for (id, c) in &results {
    if matches!(c, KConst::Indc { .. }) {
      indcs.push((id.clone(), c));
    }
  }
  let all_primary_indc = !indcs.is_empty()
    && indcs.len()
      == members.iter().filter(|m| matches!(m, IxonMutConst::Indc(_))).count();
  if all_primary_indc
    && members.iter().all(|m| matches!(m, IxonMutConst::Indc(_)))
  {
    // Resolve a ctor by id by scanning the ingested results — simpler
    // than threading the env, since the comparator only needs Ctor
    // payloads for Indc ctors.
    let results_ref: &Vec<(KId<M>, KConst<M>)> = &results;
    let resolve_ctor = |cid: &KId<M>| -> Option<KConst<M>> {
      results_ref.iter().find(|(rid, _)| rid == cid).map(|(_, c)| c.clone())
    };
    crate::ix::kernel::canonical_check::validate_canonical_block_single_pass::<
      M,
    >(entry_addr, &indcs, &resolve_ctor)
    .map_err(|e| format!("{e}"))?;
  }

  Ok(results)
}

// ============================================================================
// Lightweight LeanExpr → KExpr ingress (compile-side)
// ============================================================================

use crate::ix::env::{
  Expr as LeanExpr, ExprData as LeanExprData, Level, LevelData,
};

/// Convert a Lean Level to KUniv<Meta>, mapping named params to positional indices.
pub fn lean_level_to_kuniv(lvl: &Level, param_names: &[Name]) -> KUniv<Meta> {
  match lvl.as_data() {
    LevelData::Succ(l, _) => KUniv::succ(lean_level_to_kuniv(l, param_names)),
    LevelData::Max(a, b, _) => KUniv::max(
      lean_level_to_kuniv(a, param_names),
      lean_level_to_kuniv(b, param_names),
    ),
    LevelData::Imax(a, b, _) => KUniv::imax(
      lean_level_to_kuniv(a, param_names),
      lean_level_to_kuniv(b, param_names),
    ),
    LevelData::Param(name, _) => {
      let idx =
        param_names.iter().position(|n| n == name).unwrap_or_else(|| {
          panic!(
            "unknown level param `{}` not found in param_names {:?}",
            name.pretty(),
            param_names.iter().map(|n| n.pretty()).collect::<Vec<_>>()
          )
        }) as u64;
      KUniv::param(idx, name.clone())
    },
    LevelData::Zero(_) => KUniv::zero(),
    LevelData::Mvar(name, _) => {
      panic!(
        "unexpected level metavariable `{}` in elaborated kernel term",
        name.pretty()
      );
    },
  }
}

/// Resolve a Lean Name to an Address, using real Ixon address if available.
///
/// Checks `name_to_ixon_addr` first (real compiled address), falls back to
/// `Address::from_blake3_hash(*name.get_hash())` for constants not yet compiled.
pub fn resolve_lean_name_addr(
  name: &Name,
  name_to_ixon_addr: Option<&DashMap<Name, Address>>,
  aux_n2a: Option<&DashMap<Name, Address>>,
) -> Address {
  if let Some(map) = name_to_ixon_addr
    && let Some(entry) = map.get(name)
  {
    return entry.value().clone();
  }
  if let Some(map) = aux_n2a
    && let Some(entry) = map.get(name)
  {
    return entry.value().clone();
  }
  Address::from_blake3_hash(*name.get_hash())
}

/// Convert a LeanExpr to KExpr<Meta>.
///
/// `param_names` provides the positional mapping for universe level params.
/// `name_to_ixon_addr` maps Lean names to real Ixon addresses for already-compiled
/// constants. Falls back to name hash for constants not yet compiled.
/// Compute a stable hash for a `param_names` slice, used as part of the
/// ingress cache key. Two calls with the same param names (in the same
/// order) produce the same hash.
pub fn param_names_hash(param_names: &[Name]) -> Addr {
  let mut hasher = blake3::Hasher::new();
  hasher.update(&(param_names.len() as u64).to_le_bytes());
  for n in param_names {
    hasher.update(n.get_hash().as_bytes());
  }
  intern_addr(hasher.finalize())
}

pub fn lean_expr_to_zexpr(
  expr: &LeanExpr,
  param_names: &[Name],
  intern: &InternTable<Meta>,
  name_to_ixon_addr: Option<&DashMap<Name, Address>>,
  aux_n2a: Option<&DashMap<Name, Address>>,
) -> KExpr<Meta> {
  // Uncached path — only for callers without KEnv access. Top-level
  // expressions start with an empty binder stack.
  let mut binder_names: Vec<Name> = Vec::new();
  let e = lean_expr_to_zexpr_raw(
    expr,
    param_names,
    &mut binder_names,
    intern,
    name_to_ixon_addr,
    aux_n2a,
    None,
    None,
  );
  intern.intern_expr(e)
}

/// Cached variant that takes a full `KEnv` reference instead of just `InternTable`.
/// Uses the KEnv's `ingress_cache` to avoid re-converting shared LeanExpr subtrees.
pub fn lean_expr_to_zexpr_with_kenv(
  expr: &LeanExpr,
  param_names: &[Name],
  kenv: &KEnv<Meta>,
  n2a: Option<&DashMap<Name, Address>>,
  aux_n2a: Option<&DashMap<Name, Address>>,
) -> KExpr<Meta> {
  let pn_h = param_names_hash(param_names);
  let mut binder_names: Vec<Name> = Vec::new();
  lean_expr_to_zexpr_cached(
    expr,
    param_names,
    &mut binder_names,
    &kenv.intern,
    n2a,
    aux_n2a,
    Some(&kenv.ingress_cache),
    Some(&pn_h),
  )
}

/// Cached variant: uses `ingress_cache` (if provided) to avoid re-converting
/// shared LeanExpr subtrees. The cache is keyed by `(expr_hash, pn_hash)` to
/// account for different level param bindings producing different KExprs.
///
/// `binder_names` is the stack of enclosing binder names (outermost first),
/// pushed/popped around each Lam/All/Let body recursion. It's used to
/// populate `ExprData::Var`'s `name` metadata by de Bruijn lookup — a
/// cosmetic field for pretty-printing that doesn't affect type-checking.
/// Top-level callers pass an empty `Vec`. Mirrors the `binder_names` stack
/// used by the iterative Ixon-side `ingress_expr`.
///
/// Note: the cache key does not include `binder_names`, so a cache hit
/// returns a `KExpr` whose Var names reflect the FIRST context the subtree
/// was traversed under. The kernel itself never consults Var names (they're
/// erased in Anon mode, ignored in Meta mode by type checking), and egress
/// drops them on the way back to Lean's (nameless) Bvar, so this staleness
/// is benign. Matches the behavior of `ixon_ingress`'s iterative cache.
#[allow(clippy::too_many_arguments)]
pub fn lean_expr_to_zexpr_cached(
  expr: &LeanExpr,
  param_names: &[Name],
  binder_names: &mut Vec<Name>,
  intern: &InternTable<Meta>,
  n2a: Option<&DashMap<Name, Address>>,
  aux_n2a: Option<&DashMap<Name, Address>>,
  cache: Option<&DashMap<(Addr, Addr), KExpr<Meta>>>,
  pn_hash: Option<&Addr>,
) -> KExpr<Meta> {
  // Check cache
  if let (Some(cache), Some(pn_hash)) = (cache, pn_hash) {
    let expr_key = Arc::new(*expr.get_hash());
    let key = (expr_key, pn_hash.clone());
    if let Some(hit) = cache.get(&key) {
      return hit.value().clone();
    }
  }

  let e = lean_expr_to_zexpr_raw(
    expr,
    param_names,
    binder_names,
    intern,
    n2a,
    aux_n2a,
    cache,
    pn_hash,
  );
  let result = intern.intern_expr(e);

  // Store in cache
  if let (Some(cache), Some(pn_hash)) = (cache, pn_hash) {
    let expr_key = Arc::new(*expr.get_hash());
    cache.insert((expr_key, pn_hash.clone()), result.clone());
  }

  result
}

#[allow(clippy::too_many_arguments)]
fn lean_expr_to_zexpr_raw(
  expr: &LeanExpr,
  pn: &[Name],
  binder_names: &mut Vec<Name>,
  intern: &InternTable<Meta>,
  n2a: Option<&DashMap<Name, Address>>,
  aux_n2a: Option<&DashMap<Name, Address>>,
  cache: Option<&DashMap<(Addr, Addr), KExpr<Meta>>>,
  pn_hash: Option<&Addr>,
) -> KExpr<Meta> {
  // Walk through any consecutive `Mdata` wrappers first, accumulating them
  // as kernel-side `MData` layers. Lean represents `Mdata(a, Mdata(b, e))`
  // as two separate AST nodes; the kernel stores the layers in a single
  // `Vec<MData>` attached to the innermost node via the `_mdata` constructors.
  //
  // The accumulation is **essential for roundtrip fidelity** — earlier
  // versions discarded the kv-map here, which silently lost every Lean
  // mdata annotation (`_recApp`, `_inaccessible`, `noImplicitLambda`,
  // `borrowed`, `sunfoldMatch`, `save_info`, etc.). The `kernel-lean-
  // roundtrip` test guards against regressing that.
  let mut mdata_layers: Vec<MData> = Vec::new();
  let mut cur = expr;
  while let LeanExprData::Mdata(kv, inner, _) = cur.as_data() {
    mdata_layers.push(kv.clone());
    cur = inner;
  }

  // Emit the `_mdata` variant of the appropriate constructor. An empty
  // `mdata_layers` hashes identically to the non-`_mdata` constructor (both
  // go through `no_mdata::<Meta>()` which is just `Vec::new()`), so we
  // don't need a separate empty-case branch.
  //
  // For subtree recursion into a fresh binder context, we push the binder
  // name onto `binder_names`, recurse, then pop — mirroring the Ixon side
  // of ingress.
  match cur.as_data() {
    LeanExprData::Bvar(idx, _) => {
      let idx_u64 = idx.to_u64().unwrap_or(0);
      // Resolve the bound variable's display name by de Bruijn lookup
      // into the current binder stack. Missing entries (ill-scoped
      // expressions, or traversals from a non-empty starting stack)
      // fall back to anonymous; the idx itself is always correct.
      let idx_usize = usize::try_from(idx_u64).unwrap_or(usize::MAX);
      let name = binder_names
        .len()
        .checked_sub(1 + idx_usize)
        .and_then(|i| binder_names.get(i))
        .cloned()
        .unwrap_or_else(Name::anon);
      KExpr::var_mdata(idx_u64, name, mdata_layers)
    },
    LeanExprData::Sort(lvl, _) => {
      KExpr::sort_mdata(lean_level_to_kuniv(lvl, pn), mdata_layers)
    },
    LeanExprData::Const(name, us, _) => {
      let addr = resolve_lean_name_addr(name, n2a, aux_n2a);
      let zid = KId::new(addr, name.clone());
      let zus: Box<[KUniv<Meta>]> =
        us.iter().map(|u| lean_level_to_kuniv(u, pn)).collect();
      KExpr::cnst_mdata(zid, zus, mdata_layers)
    },
    LeanExprData::App(f, a, _) => {
      let f_k = lean_expr_to_zexpr_cached(
        f,
        pn,
        binder_names,
        intern,
        n2a,
        aux_n2a,
        cache,
        pn_hash,
      );
      let a_k = lean_expr_to_zexpr_cached(
        a,
        pn,
        binder_names,
        intern,
        n2a,
        aux_n2a,
        cache,
        pn_hash,
      );
      KExpr::app_mdata(f_k, a_k, mdata_layers)
    },
    LeanExprData::ForallE(binder_name, dom, body, bi, _) => {
      let dom_k = lean_expr_to_zexpr_cached(
        dom,
        pn,
        binder_names,
        intern,
        n2a,
        aux_n2a,
        cache,
        pn_hash,
      );
      binder_names.push(binder_name.clone());
      let body_k = lean_expr_to_zexpr_cached(
        body,
        pn,
        binder_names,
        intern,
        n2a,
        aux_n2a,
        cache,
        pn_hash,
      );
      binder_names.pop();
      KExpr::all_mdata(
        binder_name.clone(),
        bi.clone(),
        dom_k,
        body_k,
        mdata_layers,
      )
    },
    LeanExprData::Lam(binder_name, dom, body, bi, _) => {
      let dom_k = lean_expr_to_zexpr_cached(
        dom,
        pn,
        binder_names,
        intern,
        n2a,
        aux_n2a,
        cache,
        pn_hash,
      );
      binder_names.push(binder_name.clone());
      let body_k = lean_expr_to_zexpr_cached(
        body,
        pn,
        binder_names,
        intern,
        n2a,
        aux_n2a,
        cache,
        pn_hash,
      );
      binder_names.pop();
      KExpr::lam_mdata(
        binder_name.clone(),
        bi.clone(),
        dom_k,
        body_k,
        mdata_layers,
      )
    },
    LeanExprData::LetE(binder_name, ty, val, body, nd, _) => {
      let ty_k = lean_expr_to_zexpr_cached(
        ty,
        pn,
        binder_names,
        intern,
        n2a,
        aux_n2a,
        cache,
        pn_hash,
      );
      let val_k = lean_expr_to_zexpr_cached(
        val,
        pn,
        binder_names,
        intern,
        n2a,
        aux_n2a,
        cache,
        pn_hash,
      );
      binder_names.push(binder_name.clone());
      let body_k = lean_expr_to_zexpr_cached(
        body,
        pn,
        binder_names,
        intern,
        n2a,
        aux_n2a,
        cache,
        pn_hash,
      );
      binder_names.pop();
      KExpr::let_mdata(
        binder_name.clone(),
        ty_k,
        val_k,
        body_k,
        *nd,
        mdata_layers,
      )
    },
    LeanExprData::Proj(name, idx, e, _) => {
      let addr = resolve_lean_name_addr(name, n2a, aux_n2a);
      let zid = KId::new(addr, name.clone());
      let e_k = lean_expr_to_zexpr_cached(
        e,
        pn,
        binder_names,
        intern,
        n2a,
        aux_n2a,
        cache,
        pn_hash,
      );
      KExpr::prj_mdata(zid, idx.to_u64().unwrap_or(0), e_k, mdata_layers)
    },
    LeanExprData::Lit(lit, _) => {
      use crate::ix::env::Literal;
      match lit {
        Literal::NatVal(n) => {
          // Address must match the Ixon-side blob address for this Nat,
          // which is `Address::hash(&blob_bytes)` where `blob_bytes =
          // n.to_le_bytes()` (see `store_nat` / `store_blob`). Hashing
          // `to_u64()` instead truncates any value ≥ 2^64 to 0, causing
          // distinct Nats to hash-cons to the same KExpr.
          let addr = Address::hash(&n.to_le_bytes());
          KExpr::nat_mdata(n.clone(), addr, mdata_layers)
        },
        Literal::StrVal(s) => {
          let addr = Address::hash(s.as_bytes());
          KExpr::str_mdata(s.clone(), addr, mdata_layers)
        },
      }
    },
    LeanExprData::Mdata(..) => {
      // Unreachable — the while-loop above peeled off every `Mdata` layer.
      unreachable!("Mdata should have been peeled off into mdata_layers");
    },
    LeanExprData::Fvar(name, _) => {
      panic!(
        "unexpected FVar({}) in elaborated kernel term during ingress",
        name.pretty()
      );
    },
    LeanExprData::Mvar(name, _) => {
      panic!(
        "unexpected MVar({}) in elaborated kernel term during ingress",
        name.pretty()
      );
    },
  }
}

/// Name → Address for KId construction from Lean Names.
pub fn lean_name_to_addr(name: &Name) -> Address {
  Address::from_blake3_hash(*name.get_hash())
}

/// Incrementally ingress a set of just-compiled constants into a KEnv.
///
/// Called after each block compiles in the topological compilation loop.
/// `names` are the Lean names of constants in the block. For each name,
/// we look up its Ixon address and constant, convert to KConst, and insert.
/// Build the address → name + name → address lookup tables for
/// `ingress_compiled_names`. Call once at compile start, then pass to each
/// incremental ingress call.
///
/// Two maps:
/// - `name_map`: `ixon_env.names` inverted — address of a `Lean.Name` →
///   the name itself. Used in Meta mode to recover names from arena
///   metadata.
/// - `addr_map`: `ixon_env.named` — each registered Lean name → the
///   content address at which its compiled `Constant` is stored
///   (projection address for Muts members, or direct block address for
///   singletons). This is the kernel-addressing map: `KId`s for sibling
///   references inside Muts blocks MUST use these addresses (the raw
///   name-hash address is insufficient because an alpha-collapsed block
///   is stored at its content address, not any individual member's name
///   hash).
pub fn build_ingress_lookups(
  ixon_env: &IxonEnv,
) -> (FxHashMap<Address, Name>, FxHashMap<Name, Address>) {
  let mut name_map: FxHashMap<Address, Name> = FxHashMap::default();
  for entry in ixon_env.names.iter() {
    name_map.insert(entry.key().clone(), entry.value().clone());
  }
  let mut addr_map: FxHashMap<Name, Address> = FxHashMap::default();
  for entry in ixon_env.named.iter() {
    addr_map.insert(entry.key().clone(), entry.value().addr.clone());
  }
  (name_map, addr_map)
}

pub fn ingress_compiled_names(
  names: &[Name],
  ixon_env: &IxonEnv,
  zenv: &KEnv<Meta>,
  intern: &InternTable<Meta>,
  name_map: &FxHashMap<Address, Name>,
  addr_map: &FxHashMap<Name, Address>,
) {
  for name in names {
    let named = match ixon_env.named.get(name) {
      Some(entry) => entry.value().clone(),
      None => continue,
    };
    let constant = match ixon_env.get_const(&named.addr) {
      Some(c) => c,
      None => continue,
    };
    let mut stats = ConvertStats::default();

    // Check if this is a Muts entry (mutual block) — handle differently
    if matches!(&named.meta.info, ConstantMetaInfo::Muts { .. }) {
      if let ConstantMetaInfo::Muts { all, .. } = &named.meta.info
        && let Ok(entries) = ingress_muts_block(
          name,
          &named.addr,
          all,
          ixon_env,
          name_map,
          addr_map,
          intern,
          &mut stats,
        )
      {
        let block_id = entries.first().and_then(|(_, zc)| match zc {
          KConst::Defn { block, .. }
          | KConst::Recr { block, .. }
          | KConst::Indc { block, .. } => Some(block.clone()),
          _ => None,
        });
        let member_ids: Vec<KId<Meta>> =
          entries.iter().map(|(id, _)| id.clone()).collect();
        if let Some(bid) = block_id {
          zenv.blocks.insert(bid, member_ids);
        }
        for (id, zc) in entries {
          zenv.insert(id, zc);
        }
      }
      continue;
    }

    // Standalone constant (or member of a mutual block handled via Muts)
    // Skip projection wrappers — they're handled by the Muts path
    match &constant.info {
      IxonCI::IPrj(_) | IxonCI::CPrj(_) | IxonCI::RPrj(_) | IxonCI::DPrj(_) => {
        continue;
      },
      _ => {},
    }

    if let Ok(entries) = ingress_standalone(
      name,
      &named.addr,
      &constant,
      &named.meta,
      ixon_env,
      name_map,
      addr_map,
      intern,
      &mut stats,
    ) {
      for (id, zc) in entries {
        zenv.insert(id, zc);
      }
    }
  }
}

// ============================================================================
// Direct Lean env → kernel env (bypasses Ixon)
// ============================================================================
//
// This path is used by the `kernel-lean-roundtrip` diagnostic
// test (`src/ffi/kernel.rs::rs_kernel_roundtrip_no_compile`) to isolate
// ingress bugs from compile/Ixon bugs. It produces a `KEnv<M>` directly
// from the decoded Lean `Env`, using:
//
//   * `lean_name_to_addr` for `KId.addr`s — the same name-hash scheme that
//     `resolve_lean_name_addr` falls back to when both maps are `None`, so
//     `Const`-reference addresses inside expressions match constant keys.
//   * `lean_expr_to_zexpr_with_kenv` for expression ingress — the very same
//     helper aux_gen already uses after regeneration, so any binder-name /
//     const-ref semantics are shared between the two paths.
//   * `kenv.intern` is populated in-place (no separate `InternTable` to
//     swap in the way `ixon_ingress` requires).

/// Extract the `all` (mutual siblings) list from a Lean `ConstantInfo`.
/// Returns `None` for variants without a mutual block (Axio, Quot, Ctor, Rec).
/// Ctors/Recs have their own `induct`/`all` but the block identity comes
/// from the inductive, which is what's on the map anyway.
fn lean_constant_all(ci: &LeanCI) -> Option<&Vec<Name>> {
  match ci {
    LeanCI::DefnInfo(v) => Some(&v.all),
    LeanCI::ThmInfo(v) => Some(&v.all),
    LeanCI::OpaqueInfo(v) => Some(&v.all),
    LeanCI::InductInfo(v) => Some(&v.all),
    LeanCI::RecInfo(v) => Some(&v.all),
    LeanCI::AxiomInfo(_) | LeanCI::QuotInfo(_) | LeanCI::CtorInfo(_) => None,
  }
}

/// Look up position of `name` in its mutual `all` list, returning 0 for
/// non-mutuals or constants not found in their own `all`.
fn lean_member_idx(name: &Name, all: Option<&Vec<Name>>) -> u64 {
  all.and_then(|a| a.iter().position(|n| n == name)).map_or(0, |i| i as u64)
}

/// Build a `Name → LEON content-hash` map for every constant in the Lean env.
///
/// The LEON hash is `ConstantInfo::get_hash()` in `src/ix/env.rs` — a Blake3
/// digest over the serialized original `ConstantInfo`
/// (name, level params, type expression, variant-specific fields).
/// Two constants with the same Lean name but different content get distinct
/// addresses, so a rogue environment can't shadow a primitive just by naming
/// its own declaration `Nat`.
///
/// The resulting map is the addressing authority for `lean_ingress`: every
/// `KId.addr` in `orig_kenv` and every `Const`-reference address inside
/// `orig_kenv` expressions is drawn from it. Names absent from the env
/// (dangling refs, partial envs) fall through to `lean_name_to_addr` as a
/// best-effort — those cases produce mismatched addresses and will surface
/// as `UnknownConst` in the type checker rather than silently succeeding.
pub fn build_leon_addr_map(lean_env: &LeanEnv) -> DashMap<Name, Address> {
  // Build in parallel. Each shard's write lock is contended only when
  // distinct names happen to hash into the same shard — with 64 default
  // shards and ~199k names, contention is low. Pre-sizing `with_capacity`
  // keeps the shards from growing during construction.
  //
  // The map type stays `DashMap` (rather than `FxHashMap`) because
  // downstream signatures (`lean_expr_to_zexpr_cached`,
  // `resolve_lean_name_addr`) share the `n2a` parameter slot with
  // `aux_n2a`, which is concurrently *written* during the scheduler
  // phase from `src/ix/compile/aux_gen.rs:823`. Splitting the two into
  // different types would propagate a signature change through ~5
  // functions with no matching perf win.
  let entries: Vec<(&Name, &LeanCI)> = lean_env.iter().collect();
  let map = DashMap::with_capacity(lean_env.len());
  entries.par_iter().for_each(|(name, ci)| {
    map.insert((*name).clone(), Address::from_blake3_hash(ci.get_hash()));
  });
  map
}

/// Resolve a Lean name to its LEON content-hash address, falling back to
/// the name-hash when the name isn't present in `n2a`.
///
/// The fallback exists for robustness against dangling references — a
/// well-formed Lean env should never trigger it. Callers that need
/// strict resolution (e.g. "does this name exist?") should check
/// `n2a.contains_key` directly.
fn leon_addr_of(name: &Name, n2a: &DashMap<Name, Address>) -> Address {
  n2a.get(name).map_or_else(|| lean_name_to_addr(name), |e| e.value().clone())
}

/// Build the `block` KId for a constant's mutual block. For singletons
/// (no `all` or `all` length 1), the block id is the constant's own KId.
/// For mutuals, it's the representative (first name in `all`).
fn lean_block_id(
  self_name: &Name,
  all: Option<&Vec<Name>>,
  n2a: &DashMap<Name, Address>,
) -> KId<Meta> {
  let rep = all.and_then(|a| a.first()).unwrap_or(self_name);
  KId::new(leon_addr_of(rep, n2a), rep.clone())
}

/// Build the `lean_all` KId list in Meta mode.
fn lean_all_ids(all: &[Name], n2a: &DashMap<Name, Address>) -> Vec<KId<Meta>> {
  all.iter().map(|n| KId::new(leon_addr_of(n, n2a), n.clone())).collect()
}

/// Convert one Lean `ConstantInfo` to a `KConst<Meta>`. Expressions go through
/// `lean_expr_to_zexpr_with_kenv` with the `n2a` map so inner `Const`
/// references resolve to LEON addresses (same scheme used for the KId
/// addresses in this constant's own fields).
fn lean_const_to_kconst(
  self_name: &Name,
  ci: &LeanCI,
  kenv: &KEnv<Meta>,
  n2a: &DashMap<Name, Address>,
) -> KConst<Meta> {
  // Helper: shorthand for expression ingress. `n2a` carries the env-wide
  // LEON addressing so `Const` refs inside expressions resolve to the same
  // addresses we're using for KId keys — any KId we construct here and any
  // Const-ref we ingress agree on where they point.
  let expr_to_k = |e: &crate::ix::env::Expr, pn: &[Name]| -> KExpr<Meta> {
    lean_expr_to_zexpr_with_kenv(e, pn, kenv, Some(n2a), None)
  };

  match ci {
    LeanCI::AxiomInfo(v) => {
      let pn = &v.cnst.level_params;
      KConst::Axio {
        name: self_name.clone(),
        level_params: pn.clone(),
        is_unsafe: v.is_unsafe,
        lvls: pn.len() as u64,
        ty: expr_to_k(&v.cnst.typ, pn),
      }
    },
    LeanCI::DefnInfo(v) => {
      let pn = &v.cnst.level_params;
      let all = Some(&v.all);
      KConst::Defn {
        name: self_name.clone(),
        level_params: pn.clone(),
        kind: DefKind::Definition,
        safety: v.safety,
        hints: v.hints,
        lvls: pn.len() as u64,
        ty: expr_to_k(&v.cnst.typ, pn),
        val: expr_to_k(&v.value, pn),
        lean_all: lean_all_ids(&v.all, n2a),
        block: lean_block_id(self_name, all, n2a),
      }
    },
    LeanCI::ThmInfo(v) => {
      let pn = &v.cnst.level_params;
      let all = Some(&v.all);
      KConst::Defn {
        name: self_name.clone(),
        level_params: pn.clone(),
        kind: DefKind::Theorem,
        safety: DefinitionSafety::Safe,
        hints: ReducibilityHints::Opaque,
        lvls: pn.len() as u64,
        ty: expr_to_k(&v.cnst.typ, pn),
        val: expr_to_k(&v.value, pn),
        lean_all: lean_all_ids(&v.all, n2a),
        block: lean_block_id(self_name, all, n2a),
      }
    },
    LeanCI::OpaqueInfo(v) => {
      let pn = &v.cnst.level_params;
      let all = Some(&v.all);
      KConst::Defn {
        name: self_name.clone(),
        level_params: pn.clone(),
        kind: DefKind::Opaque,
        safety: if v.is_unsafe {
          DefinitionSafety::Unsafe
        } else {
          DefinitionSafety::Safe
        },
        hints: ReducibilityHints::Opaque,
        lvls: pn.len() as u64,
        ty: expr_to_k(&v.cnst.typ, pn),
        val: expr_to_k(&v.value, pn),
        lean_all: lean_all_ids(&v.all, n2a),
        block: lean_block_id(self_name, all, n2a),
      }
    },
    LeanCI::QuotInfo(v) => {
      let pn = &v.cnst.level_params;
      KConst::Quot {
        name: self_name.clone(),
        level_params: pn.clone(),
        kind: v.kind,
        lvls: pn.len() as u64,
        ty: expr_to_k(&v.cnst.typ, pn),
      }
    },
    LeanCI::InductInfo(v) => {
      let pn = &v.cnst.level_params;
      let all = Some(&v.all);
      let ctors = v
        .ctors
        .iter()
        .map(|n| KId::new(leon_addr_of(n, n2a), n.clone()))
        .collect();
      KConst::Indc {
        name: self_name.clone(),
        level_params: pn.clone(),
        lvls: pn.len() as u64,
        params: v.num_params.to_u64().unwrap_or(0),
        indices: v.num_indices.to_u64().unwrap_or(0),
        is_rec: v.is_rec,
        is_refl: v.is_reflexive,
        is_unsafe: v.is_unsafe,
        nested: v.num_nested.to_u64().unwrap_or(0),
        block: lean_block_id(self_name, all, n2a),
        member_idx: lean_member_idx(self_name, all),
        ty: expr_to_k(&v.cnst.typ, pn),
        ctors,
        lean_all: lean_all_ids(&v.all, n2a),
      }
    },
    LeanCI::CtorInfo(v) => {
      let pn = &v.cnst.level_params;
      KConst::Ctor {
        name: self_name.clone(),
        level_params: pn.clone(),
        is_unsafe: v.is_unsafe,
        lvls: pn.len() as u64,
        induct: KId::new(leon_addr_of(&v.induct, n2a), v.induct.clone()),
        cidx: v.cidx.to_u64().unwrap_or(0),
        params: v.num_params.to_u64().unwrap_or(0),
        fields: v.num_fields.to_u64().unwrap_or(0),
        ty: expr_to_k(&v.cnst.typ, pn),
      }
    },
    LeanCI::RecInfo(v) => {
      let pn = &v.cnst.level_params;
      let all = Some(&v.all);
      let rules = v
        .rules
        .iter()
        .map(|r| RecRule {
          ctor: r.ctor.clone(),
          fields: r.n_fields.to_u64().unwrap_or(0),
          rhs: expr_to_k(&r.rhs, pn),
        })
        .collect();
      KConst::Recr {
        name: self_name.clone(),
        level_params: pn.clone(),
        k: v.k,
        is_unsafe: v.is_unsafe,
        lvls: pn.len() as u64,
        params: v.num_params.to_u64().unwrap_or(0),
        indices: v.num_indices.to_u64().unwrap_or(0),
        motives: v.num_motives.to_u64().unwrap_or(0),
        minors: v.num_minors.to_u64().unwrap_or(0),
        block: lean_block_id(self_name, all, n2a),
        member_idx: lean_member_idx(self_name, all),
        ty: expr_to_k(&v.cnst.typ, pn),
        rules,
        lean_all: lean_all_ids(&v.all, n2a),
      }
    },
  }
}

/// Direct ingress: build a `KEnv<Meta>` from a Lean `Env` without going
/// through Ixon compilation. Used by the `kernel-lean-roundtrip`
/// diagnostic test and by `compile_env` to produce the `orig_kenv`
/// used for original-constant verification (see `src/ix/compile.rs::
/// KernelCtx::orig_kenv`).
///
/// # Addressing
///
/// All `KId.addr`s are derived via `ConstantInfo::get_hash()` — the LEON
/// content hash, Blake3 over the serialized original `ConstantInfo`
/// (name + level params + type + variant-specific fields). `Const`
/// references inside expressions resolve against the same map so
/// constant keys and reference targets line up automatically.
///
/// LEON addressing has two properties that name-hash addressing lacked:
///
/// - **Content-distinguishing**: two constants with the same name but
///   different content hash to different addresses, so a rogue env
///   can't silently shadow a primitive by naming its own declaration
///   `Nat`.
/// - **Compatible with `PrimOrigAddrs`**: the hardcoded original-addr
///   table in `src/ix/kernel/primitive.rs` holds LEON hashes, so
///   address-keyed primitive lookup against `orig_kenv` succeeds
///   without a synthetic `@<hex>` fallback.
///
/// # Block entries
///
/// `kenv.blocks` is populated for every constant: each `KId` is pushed
/// under its block's representative (first name in `all`, or the
/// constant itself for singletons). Constructors follow their parent
/// inductive's block.
///
/// **Meta-only**: the existing `lean_expr_to_zexpr_*` family is Meta-mode
/// only, so this helper is Meta-mode only by extension. Generalizing to
/// `Anon` would require generalizing `lean_expr_to_zexpr_raw` too.
pub fn lean_ingress(lean_env: &LeanEnv) -> KEnv<Meta> {
  use std::time::Instant;
  let quiet = std::env::var("IX_QUIET").is_ok();
  let kenv = KEnv::<Meta>::new_with_recursor_aux_order(
    super::env::RecursorAuxOrder::Source,
  );

  // Build the env-wide name → LEON-addr map once. Threaded through every
  // KId construction below so all addresses in orig_kenv — whether
  // stored as the KEnv key, or referenced from within a KExpr via
  // `Const`, or captured in structural fields like `block`, `ctors`,
  // `induct`, `lean_all` — come from the same authoritative source.
  let t = Instant::now();
  let n2a = build_leon_addr_map(lean_env);
  if !quiet {
    eprintln!(
      "[lean_ingress]   build_leon_addr_map: {:.2}s ({} names)",
      t.elapsed().as_secs_f32(),
      n2a.len()
    );
  }

  // Pass 1: ingress every constant — parallelized via rayon.
  //
  // Every function called from the worker body is thread-safe:
  //   - `leon_addr_of` reads from `n2a` (a DashMap).
  //   - `lean_const_to_kconst` reads `ci`/`n2a` and builds fresh `KConst`
  //     values; any expression interning it triggers goes through
  //     `kenv.intern` (DashMap) and `kenv.ingress_cache` (DashMap), both
  //     documented thread-safe. It does not read `kenv.consts` or
  //     `kenv.blocks`, so parallel inserts here are partition-safe.
  //   - `kenv.insert` writes the freshly-built `KConst` into
  //     `kenv.consts` (DashMap). KIds are derived from LEON content
  //     hashes, so no two workers produce the same key, so no shard
  //     contention on the write.
  //
  // `lean_env` is an `FxHashMap`, so we collect a `Vec<_>` of references
  // and hand that to rayon; the `std::collections::HashMap` par_iter
  // impl requires the default hasher, which `FxHashMap` isn't.
  let t = Instant::now();
  let entries: Vec<(&Name, &LeanCI)> = lean_env.iter().collect();
  entries.into_par_iter().for_each(|(name, ci)| {
    let kid = KId::new(leon_addr_of(name, &n2a), name.clone());
    let kc = lean_const_to_kconst(name, ci, &kenv, &n2a);
    kenv.insert(kid, kc);
  });
  if !quiet {
    eprintln!(
      "[lean_ingress]   pass 1 (parallel ingress): {:.2}s",
      t.elapsed().as_secs_f32()
    );
  }

  // Pass 2: populate `kenv.blocks`.
  //
  // Each inductive block's entry under `blocks[rep_kid]` must hold
  // *every* KId that the kernel's block-traversal paths need:
  //
  // - The inductives themselves (discovered by
  //   `discover_block_inductives` during `check_inductive`'s A1–A4
  //   pass and during `compute_is_rec`).
  // - Their constructors (needed for ctor lookups keyed on the block).
  // - Their recursors (needed by `find_peer_recursors` during
  //   `generate_block_recursors`'s rule generation — without recs in
  //   the block, rule RHS construction returns None and the stored
  //   rules can't be verified).
  //
  // **Order matters for inductives.** `discover_block_inductives`
  // filters the block's member list down to `KConst::Indc` entries
  // and the resulting order drives `build_flat_block` → `build_rec_type`
  // → motive-binder emission in `generate_block_recursors`. That
  // order must match whatever order the *stored* recursor was
  // generated against.
  //
  // For `orig_kenv` (what this function builds), the stored recursor
  // is Lean's own — generated against the **declaration order** given
  // by each constant's `all` list (the source order the user wrote
  // the mutual block in). If `discover_block_inductives` returns
  // members in any other order, the generated motive prefix permutes
  // relative to Lean's, yielding spurious `check_recursor: type
  // mismatch` on every mutual-block recursor (we saw this on
  // `Lean.Xml.Content.rec`, `Lean.Compiler.LCNF.Code.rec`, every
  // `Grind.Arith.*.*Cnstr*.rec`, etc.).
  //
  // Declaration order is *not* the canonical structural order that
  // `sort_consts` produces during compilation — that second order
  // only shows up in the compiled `kctx.kenv`, not here. Iterating
  // `lean_env` directly to push each constant's `self_kid` gave
  // random (FxHashMap iteration) order; we now seed each block with
  // its `all` list the first time any member is observed, then
  // append ctors and recursors in a second pass. Ctors/recursors
  // land at the tail — the block's inductive-prefix carries the
  // declaration order that `discover_block_inductives` consumes.
  //
  // `ixon_ingress` builds an analogous list for `kctx.kenv`, but
  // there the ordering comes from `sort_consts`' equivalence-class
  // output (structural, not declarational). The two paths diverge on
  // purpose: `orig_kenv` carries Lean's source-order recursor
  // expectations, `kctx.kenv` carries the canonical-compile recursor
  // expectations.
  //
  // For singleton inductives, the block is keyed at `self_kid`; for
  // multi-member mutuals, at the representative (first name in `all`).
  let block_rep = |name: &Name, ci: &LeanCI| -> KId<Meta> {
    let all = lean_constant_all(ci);
    let rep =
      all.and_then(|a| a.first()).cloned().unwrap_or_else(|| name.clone());
    KId::new(leon_addr_of(&rep, &n2a), rep)
  };

  // Phase A: seed each block's initial member list from the constant's
  // `all` list (canonical order), exactly once per block. Constants
  // without `all` (axioms, quotients, ctors) seed a singleton block
  // under their own KId.
  let t = Instant::now();
  let mut seeded: FxHashSet<KId<Meta>> = FxHashSet::default();
  for (name, ci) in lean_env.iter() {
    let block_id = block_rep(name, ci);
    if !seeded.insert(block_id.clone()) {
      continue;
    }
    let all =
      lean_constant_all(ci).cloned().unwrap_or_else(|| vec![name.clone()]);
    let members: Vec<KId<Meta>> =
      all.iter().map(|n| KId::new(leon_addr_of(n, &n2a), n.clone())).collect();
    kenv.blocks.insert(block_id, members);
  }
  if !quiet {
    eprintln!(
      "[lean_ingress]   phase A (block seed): {:.2}s",
      t.elapsed().as_secs_f32()
    );
  }

  // Phase B: append constructors (for each inductive in the block) and
  // recursors (which aren't in `all` — `all` lists inductives even for
  // RecInfo). Order within ctors/recs doesn't affect kernel correctness
  // because consumer lookups go by KId (ctors) or major-inductive match
  // (`find_peer_recursors` for recs).
  let t = Instant::now();
  for (name, ci) in lean_env.iter() {
    match ci {
      LeanCI::InductInfo(v) => {
        let block_id = block_rep(name, ci);
        for ctor_name in &v.ctors {
          let ctor_kid: KId<Meta> =
            KId::new(leon_addr_of(ctor_name, &n2a), ctor_name.clone());
          kenv.blocks.entry(block_id.clone()).or_default().push(ctor_kid);
        }
      },
      LeanCI::RecInfo(_) => {
        let block_id = block_rep(name, ci);
        let self_kid = KId::new(leon_addr_of(name, &n2a), name.clone());
        kenv.blocks.entry(block_id).or_default().push(self_kid);
      },
      // Inductives and Defns/Thms/Opaques are already in the Phase-A
      // seed via their `all` list; axioms, quotients, and ctors are
      // placed as singletons (the latter also get appended above).
      _ => {},
    }
  }
  if !quiet {
    eprintln!(
      "[lean_ingress]   phase B (ctor/rec append): {:.2}s",
      t.elapsed().as_secs_f32()
    );
  }

  // Pre-cache primitives against the LEON-addressed scheme so
  // `TypeChecker::new(orig_kenv)` and any caller of `kenv.prims()`
  // resolve primitives through `PrimAddrs::new_orig` (matching KIds in
  // this env) instead of the canonical table (which would always miss
  // here and produce synthetic `@<hex>` KIds).
  //
  // Returns `Err` only if `prims()` has already been called on this
  // KEnv — fresh `KEnv::new()` above guarantees that hasn't happened,
  // so we ignore the Result.
  let _ = kenv
    .set_prims(crate::ix::kernel::primitive::Primitives::from_env_orig(&kenv));

  kenv
}

// ============================================================================
// Top-level entry point
// ============================================================================

enum IngressWorkItem {
  Standalone(Name),
  Muts(Name),
}

#[derive(Default)]
struct IngressInsertTiming {
  blocks_ns: u64,
  consts_ns: u64,
}

#[derive(Default)]
struct IngressStreamTimingSnapshot {
  standalone_items: u64,
  muts_items: u64,
  output_consts: u64,
  missing_consts: u64,
  lookup_ns: u64,
  const_get_ns: u64,
  convert_ns: u64,
  insert_ns: u64,
  insert_blocks_ns: u64,
  insert_consts_ns: u64,
  convert_stats: ConvertStats,
}

impl IngressStreamTimingSnapshot {
  fn merge(mut self, other: Self) -> Self {
    self.standalone_items += other.standalone_items;
    self.muts_items += other.muts_items;
    self.output_consts += other.output_consts;
    self.missing_consts += other.missing_consts;
    self.lookup_ns += other.lookup_ns;
    self.const_get_ns += other.const_get_ns;
    self.convert_ns += other.convert_ns;
    self.insert_ns += other.insert_ns;
    self.insert_blocks_ns += other.insert_blocks_ns;
    self.insert_consts_ns += other.insert_consts_ns;
    self.convert_stats = self.convert_stats.merge(other.convert_stats);
    self
  }
}

#[derive(Default)]
struct IxonDropTiming {
  consts_ns: u64,
  named_ns: u64,
  names_ns: u64,
  blobs_ns: u64,
  comms_ns: u64,
}

struct LookupDropTiming {
  names_ns: u64,
  name_to_addr_ns: u64,
}

fn duration_ns(d: Duration) -> u64 {
  d.as_nanos().min(u128::from(u64::MAX)) as u64
}

fn elapsed_ns(start: Instant) -> u64 {
  duration_ns(start.elapsed())
}

fn seconds(ns: u64) -> f64 {
  ns as f64 / 1_000_000_000.0
}

fn percent(part: u64, total: u64) -> f64 {
  if total == 0 { 0.0 } else { (part as f64 * 100.0) / total as f64 }
}

fn timed_drop_ns<T>(value: T) -> u64 {
  let start = Instant::now();
  drop(value);
  elapsed_ns(start)
}

/// Drop a `DashMap` in parallel across its shards.
///
/// DashMap's `IntoParallelIterator` impl yields owned `(K, V)` pairs by
/// processing shards as the parallel unit (one rayon task per shard,
/// sequential within a shard). Default shard count is `4 * num_cpus()`, which
/// gives rayon's work-stealing plenty to distribute.
///
/// Used by `drop_ixon_env` to tear down the five `DashMap`s holding the
/// post-ingress IxonEnv. Concurrent `Arc::drop` is safe by construction
/// (atomic refcount; the last decrementer destroys exactly once), and none
/// of the value types have custom `Drop` impls — so this is a pure
/// parallelisation of the existing teardown.
fn timed_drop_dashmap_par<K, V, S>(map: DashMap<K, V, S>) -> u64
where
  K: Eq + Hash + Send,
  V: Send,
  S: BuildHasher + Clone + Send,
{
  let start = Instant::now();
  map.into_par_iter().for_each(drop);
  elapsed_ns(start)
}

/// Drop an `FxHashMap` (= `std::HashMap` with FxHasher) in parallel.
///
/// `std::HashMap` only exposes a sequential `into_iter()`, so we drain into
/// a `Vec<(K, V)>` first (a cheap O(n) sequential pass that just moves owned
/// pairs) and then `into_par_iter().for_each(drop)` on the Vec, letting
/// rayon distribute the actual destructor work.
fn timed_drop_fxmap_par<K: Send, V: Send>(map: FxHashMap<K, V>) -> u64 {
  let start = Instant::now();
  let entries: Vec<(K, V)> = map.into_iter().collect();
  entries.into_par_iter().for_each(drop);
  elapsed_ns(start)
}

/// Opt-out for the parallel drop path: set `IX_SEQ_IXON_DROP=1` to fall back
/// to single-threaded `drop` for measurement comparisons.
fn seq_ixon_drop_enabled() -> bool {
  std::env::var_os("IX_SEQ_IXON_DROP").is_some()
}

fn ingress_convert_stats_enabled() -> bool {
  std::env::var_os("IX_INGRESS_CONVERT_STATS").is_some()
}

fn drop_ingress_lookups(
  names: FxHashMap<Address, Name>,
  name_to_addr: FxHashMap<Name, Address>,
  quiet: bool,
) {
  let total_start = Instant::now();
  let names_len = names.len();
  let name_to_addr_len = name_to_addr.len();
  let sequential = seq_ixon_drop_enabled();

  // Drop the two lookup tables in series; each one fully utilises the rayon
  // pool internally via `timed_drop_fxmap_par`. Running them in parallel via
  // `rayon::scope` would just fight for the same global thread pool and
  // entangle per-map timings.
  let timing = if sequential {
    LookupDropTiming {
      names_ns: timed_drop_ns(names),
      name_to_addr_ns: timed_drop_ns(name_to_addr),
    }
  } else {
    LookupDropTiming {
      names_ns: timed_drop_fxmap_par(names),
      name_to_addr_ns: timed_drop_fxmap_par(name_to_addr),
    }
  };

  let total_ns = elapsed_ns(total_start);
  if !quiet {
    eprintln!(
      "[ixon_ingress] drop lookups: {:.2}s {} threads={} \
       (names {:.2}s/{} name_to_addr {:.2}s/{})",
      seconds(total_ns),
      if sequential { "sequential" } else { "parallel" },
      rayon::current_num_threads(),
      seconds(timing.names_ns),
      names_len,
      seconds(timing.name_to_addr_ns),
      name_to_addr_len
    );
  }
}

fn insert_standalone_entries<M: KernelMode>(
  zenv: &KEnv<M>,
  entries: Vec<(KId<M>, KConst<M>)>,
) -> IngressInsertTiming {
  let mut timing = IngressInsertTiming::default();

  let phase_start = Instant::now();
  for (id, _) in &entries {
    zenv.blocks.entry(id.clone()).or_default().push(id.clone());
  }
  timing.blocks_ns = elapsed_ns(phase_start);

  let phase_start = Instant::now();
  for (id, zc) in entries {
    zenv.insert(id, zc);
  }
  timing.consts_ns = elapsed_ns(phase_start);

  timing
}

fn insert_muts_entries<M: KernelMode>(
  zenv: &KEnv<M>,
  entries: Vec<(KId<M>, KConst<M>)>,
) -> IngressInsertTiming {
  let mut timing = IngressInsertTiming::default();

  let phase_start = Instant::now();
  let block_id = entries.first().and_then(|(_, zc)| match zc {
    KConst::Defn { block, .. }
    | KConst::Recr { block, .. }
    | KConst::Indc { block, .. } => Some(block.clone()),
    _ => None,
  });
  let member_ids: Vec<KId<M>> =
    entries.iter().map(|(id, _)| id.clone()).collect();
  if let Some(bid) = block_id {
    zenv.blocks.insert(bid, member_ids);
  }
  timing.blocks_ns = elapsed_ns(phase_start);

  let phase_start = Instant::now();
  for (id, zc) in entries {
    zenv.insert(id, zc);
  }
  timing.consts_ns = elapsed_ns(phase_start);

  timing
}

/// Convert an Ixon environment to a zero kernel environment.
pub fn ixon_ingress<M: KernelMode>(
  ixon_env: &IxonEnv,
) -> Result<(KEnv<M>, InternTable<M>), String> {
  ixon_ingress_inner(ixon_env)
}

/// Convert an owned Ixon environment to a zero kernel environment.
///
/// This is the production path for callers that do not need the compiled Ixon
/// environment after ingress. Taking ownership ensures the Ixon side is dropped
/// before the kernel check loop starts.
pub fn ixon_ingress_owned<M: KernelMode>(
  ixon_env: IxonEnv,
) -> Result<(KEnv<M>, InternTable<M>), String> {
  let quiet = std::env::var_os("IX_QUIET").is_some();
  let result = ixon_ingress_inner(&ixon_env);
  drop_ixon_env(ixon_env, quiet);
  result
}

fn drop_ixon_env(ixon_env: IxonEnv, quiet: bool) {
  let total_start = Instant::now();
  let IxonEnv { consts, named, blobs, names, comms } = ixon_env;
  let consts_len = consts.len();
  let named_len = named.len();
  let names_len = names.len();
  let blobs_len = blobs.len();
  let comms_len = comms.len();

  // Drop each map sequentially, but parallelise across each map's shards via
  // `timed_drop_dashmap_par`. The previous `rayon::scope` 5-task fan-out only
  // achieved map-level parallelism — wall-clock was bounded by `consts`,
  // which is single-threaded internally and dominates the total. Doing one
  // map at a time, fully parallel within, gives clean per-map timing and
  // saturates the rayon pool on the work that actually matters.
  let sequential = seq_ixon_drop_enabled();
  let timing = if sequential {
    IxonDropTiming {
      consts_ns: timed_drop_ns(consts),
      named_ns: timed_drop_ns(named),
      names_ns: timed_drop_ns(names),
      blobs_ns: timed_drop_ns(blobs),
      comms_ns: timed_drop_ns(comms),
    }
  } else {
    IxonDropTiming {
      consts_ns: timed_drop_dashmap_par(consts),
      named_ns: timed_drop_dashmap_par(named),
      names_ns: timed_drop_dashmap_par(names),
      blobs_ns: timed_drop_dashmap_par(blobs),
      comms_ns: timed_drop_dashmap_par(comms),
    }
  };

  let total_ns = elapsed_ns(total_start);
  if !quiet {
    eprintln!(
      "[ixon_ingress] drop ixon_env: {:.2}s {} threads={} \
       (consts {:.2}s/{} named {:.2}s/{} names {:.2}s/{} blobs {:.2}s/{} comms {:.2}s/{})",
      seconds(total_ns),
      if sequential { "sequential" } else { "parallel" },
      rayon::current_num_threads(),
      seconds(timing.consts_ns),
      consts_len,
      seconds(timing.named_ns),
      named_len,
      seconds(timing.names_ns),
      names_len,
      seconds(timing.blobs_ns),
      blobs_len,
      seconds(timing.comms_ns),
      comms_len
    );
  }
}

fn ixon_ingress_inner<M: KernelMode>(
  ixon_env: &IxonEnv,
) -> Result<(KEnv<M>, InternTable<M>), String> {
  let quiet = std::env::var_os("IX_QUIET").is_some();
  let total_start = Instant::now();

  let phase_start = Instant::now();
  validate_no_reserved_marker_addresses(ixon_env)?;
  if !quiet {
    eprintln!(
      "[ixon_ingress] validate_reserved: {:.2}s",
      phase_start.elapsed().as_secs_f32()
    );
  }

  let intern = InternTable::new();

  // Build the address → Lean-name lookup and the Lean-name → projection-
  // address lookup. See `build_ingress_lookups` for the role each plays.
  let phase_start = Instant::now();
  let mut names: FxHashMap<Address, Name> = FxHashMap::default();
  for entry in ixon_env.names.iter() {
    names.insert(entry.key().clone(), entry.value().clone());
  }
  let mut name_to_addr: FxHashMap<Name, Address> = FxHashMap::default();
  for entry in ixon_env.named.iter() {
    name_to_addr.insert(entry.key().clone(), entry.value().addr.clone());
  }
  if !quiet {
    eprintln!(
      "[ixon_ingress] build lookups: {:.2}s ({} names, {} named)",
      phase_start.elapsed().as_secs_f32(),
      names.len(),
      name_to_addr.len()
    );
  }

  // Partition named entries into work items without cloning the `Named`
  // metadata payloads. Each worker resolves its current Named entry just
  // before conversion.
  let phase_start = Instant::now();
  let mut work_items: Vec<IngressWorkItem> = Vec::new();
  let mut standalone_count = 0usize;
  let mut muts_count = 0usize;

  for entry in ixon_env.named.iter() {
    let const_name = entry.key().clone();
    let named = entry.value();
    match &named.meta.info {
      ConstantMetaInfo::Muts { .. } => {
        muts_count += 1;
        work_items.push(IngressWorkItem::Muts(const_name));
      },
      ConstantMetaInfo::Indc { .. }
      | ConstantMetaInfo::Ctor { .. }
      | ConstantMetaInfo::Rec { .. } => {
        if let Some(c) = ixon_env.consts.get(&named.addr) {
          match &c.info {
            IxonCI::IPrj(_)
            | IxonCI::CPrj(_)
            | IxonCI::RPrj(_)
            | IxonCI::DPrj(_) => {},
            _ => {
              standalone_count += 1;
              work_items.push(IngressWorkItem::Standalone(const_name));
            },
          }
        }
      },
      ConstantMetaInfo::Def { .. } => {
        if let Some(c) = ixon_env.consts.get(&named.addr) {
          match &c.info {
            IxonCI::DPrj(_) => {},
            _ => {
              standalone_count += 1;
              work_items.push(IngressWorkItem::Standalone(const_name));
            },
          }
        }
      },
      _ => {
        standalone_count += 1;
        work_items.push(IngressWorkItem::Standalone(const_name));
      },
    }
  }
  if !quiet {
    eprintln!(
      "[ixon_ingress] partition work: {:.2}s ({} standalone, {} muts)",
      phase_start.elapsed().as_secs_f32(),
      standalone_count,
      muts_count
    );
  }

  // Convert each standalone constant or Muts block in parallel, then insert
  // the completed block directly into the DashMap-backed KEnv. This keeps peak
  // memory bounded by in-flight worker outputs instead of materializing every
  // converted constant before assembly.
  let phase_start = Instant::now();
  let convert_stats_enabled = ingress_convert_stats_enabled();
  let zenv: KEnv<M> = KEnv::new();
  let stream = work_items
    .into_par_iter()
    .map(|work_item| -> Result<IngressStreamTimingSnapshot, String> {
      let mut timing = IngressStreamTimingSnapshot::default();
      let mut convert_stats = ConvertStats::new(convert_stats_enabled);
      match work_item {
        IngressWorkItem::Standalone(const_name) => {
          timing.standalone_items += 1;
          let lookup_start = Instant::now();
          let named = ixon_env
            .lookup_name(&const_name)
            .ok_or_else(|| format!("{const_name}: missing Named entry"))?;
          timing.lookup_ns += elapsed_ns(lookup_start);

          let const_start = Instant::now();
          let constant = match ixon_env.get_const(&named.addr) {
            Some(c) => {
              timing.const_get_ns += elapsed_ns(const_start);
              c
            },
            None => {
              timing.const_get_ns += elapsed_ns(const_start);
              timing.missing_consts += 1;
              return Ok(timing);
            },
          };
          let convert_start = Instant::now();
          let entries = ingress_standalone(
            &const_name,
            &named.addr,
            &constant,
            &named.meta,
            ixon_env,
            &names,
            &name_to_addr,
            &intern,
            &mut convert_stats,
          )
          .map_err(|e| format!("{const_name}: {e}"))?;
          timing.convert_ns += elapsed_ns(convert_start);
          timing.output_consts += entries.len() as u64;

          let insert_start = Instant::now();
          let insert_timing = insert_standalone_entries(&zenv, entries);
          timing.insert_ns += elapsed_ns(insert_start);
          timing.insert_blocks_ns += insert_timing.blocks_ns;
          timing.insert_consts_ns += insert_timing.consts_ns;
        },
        IngressWorkItem::Muts(entry_name) => {
          timing.muts_items += 1;
          let lookup_start = Instant::now();
          let named = ixon_env
            .lookup_name(&entry_name)
            .ok_or_else(|| format!("{entry_name}: missing Named entry"))?;
          timing.lookup_ns += elapsed_ns(lookup_start);

          let all = match &named.meta.info {
            ConstantMetaInfo::Muts { all, .. } => all,
            _ => return Ok(timing),
          };
          let convert_start = Instant::now();
          let entries = ingress_muts_block(
            &entry_name,
            &named.addr,
            all,
            ixon_env,
            &names,
            &name_to_addr,
            &intern,
            &mut convert_stats,
          )
          .map_err(|e| format!("{entry_name}: {e}"))?;
          timing.convert_ns += elapsed_ns(convert_start);
          timing.output_consts += entries.len() as u64;

          let insert_start = Instant::now();
          let insert_timing = insert_muts_entries(&zenv, entries);
          timing.insert_ns += elapsed_ns(insert_start);
          timing.insert_blocks_ns += insert_timing.blocks_ns;
          timing.insert_consts_ns += insert_timing.consts_ns;
        },
      }
      timing.convert_stats = convert_stats;
      Ok(timing)
    })
    .try_reduce(IngressStreamTimingSnapshot::default, |a, b| Ok(a.merge(b)))?;
  if !quiet {
    eprintln!(
      "[ixon_ingress] stream ingress+insert: {:.2}s",
      phase_start.elapsed().as_secs_f32()
    );
    eprintln!(
      "[ixon_ingress]   stream detail (worker-sum): lookup {:.2}s, const_get {:.2}s, convert {:.2}s, insert {:.2}s (blocks {:.2}s, consts {:.2}s), work {} standalone/{} muts, output {} consts, missing {}",
      seconds(stream.lookup_ns),
      seconds(stream.const_get_ns),
      seconds(stream.convert_ns),
      seconds(stream.insert_ns),
      seconds(stream.insert_blocks_ns),
      seconds(stream.insert_consts_ns),
      stream.standalone_items,
      stream.muts_items,
      stream.output_consts,
      stream.missing_consts
    );
    let cs = &stream.convert_stats;
    if cs.enabled {
      let cache_lookups = cs.expr_cache_hits + cs.expr_cache_misses;
      eprintln!(
        "[ixon_ingress]   convert cache: roots {} process {} hits {} misses {} hit {:.1}% inserts {} peak {} clears {} cleared {} shares {}",
        cs.expr_roots,
        cs.expr_process,
        cs.expr_cache_hits,
        cs.expr_cache_misses,
        percent(cs.expr_cache_hits, cache_lookups),
        cs.expr_cache_inserts,
        cs.expr_cache_peak,
        cs.expr_cache_clears,
        cs.expr_cache_entries_cleared,
        cs.share_expansions
      );
      eprintln!(
        "[ixon_ingress]   convert nodes: sort {} var {} ref {} rec {} app {} lam {} all {} let {} prj {} str {} nat {} callsites {} args {}",
        cs.sort_nodes,
        cs.var_nodes,
        cs.ref_nodes,
        cs.rec_nodes,
        cs.app_nodes,
        cs.lam_nodes,
        cs.all_nodes,
        cs.let_nodes,
        cs.prj_nodes,
        cs.str_nodes,
        cs.nat_nodes,
        cs.callsites,
        cs.callsite_args
      );
      eprintln!(
        "[ixon_ingress]   convert metadata/univ: mdata_nodes {} mdata_kv_maps {} univ_roots {} univ_cache_hits {} univ_cache_misses {} univ_hit {:.1}% univ_cache_peak {} univ_process {} univ_interns {}",
        cs.mdata_nodes,
        cs.mdata_kv_maps,
        cs.univ_roots,
        cs.univ_cache_hits,
        cs.univ_cache_misses,
        percent(cs.univ_cache_hits, cs.univ_cache_hits + cs.univ_cache_misses),
        cs.univ_cache_peak,
        cs.univ_process,
        cs.univ_interns
      );
      let ie_lookups = cs.intern_expr_calls;
      let iu_lookups = cs.intern_univ_calls;
      eprintln!(
        "[ixon_ingress]   convert timing (worker-sum): \
         resolve_kvmap {:.2}s/{} arena_walk {:.2}s \
         intern_expr {:.2}s/{} (get_hits {:.1}%) \
         intern_univ {:.2}s/{} (get_hits {:.1}%) \
         expr_cache lookup {:.2}s / insert {:.2}s \
         get_blob {:.2}s/{} \
         kexpr_construct {:.2}s/{} \
         process_arm {:.2}s continuation_arms {:.2}s",
        seconds(cs.resolve_kvmap_ns),
        cs.resolve_kvmap_calls,
        seconds(cs.arena_walk_ns),
        seconds(cs.intern_expr_ns),
        cs.intern_expr_calls,
        percent(cs.intern_expr_get_hits, ie_lookups),
        seconds(cs.intern_univ_ns),
        cs.intern_univ_calls,
        percent(cs.intern_univ_get_hits, iu_lookups),
        seconds(cs.expr_cache_lookup_ns),
        seconds(cs.expr_cache_insert_ns),
        seconds(cs.get_blob_ns),
        cs.get_blob_calls,
        seconds(cs.kexpr_construct_ns),
        cs.kexpr_construct_calls,
        seconds(cs.process_arm_ns),
        seconds(cs.continuation_arms_ns)
      );
    }
    eprintln!(
      "[ixon_ingress] complete: {:.2}s ({} consts, {} blocks)",
      total_start.elapsed().as_secs_f32(),
      zenv.len(),
      zenv.blocks.len()
    );
  }

  drop_ingress_lookups(names, name_to_addr, quiet);

  Ok((zenv, intern))
}

fn validate_no_reserved_marker_addresses(
  ixon_env: &IxonEnv,
) -> Result<(), String> {
  for entry in ixon_env.consts.iter() {
    if let Some(marker) = reserved_marker_name(entry.key()) {
      return Err(format!(
        "reserved kernel marker address {marker} ({}) used as an Ixon constant key",
        entry.key().hex()
      ));
    }
    for (idx, addr) in entry.value().refs.iter().enumerate() {
      if let Some(marker) = reserved_marker_name(addr) {
        return Err(format!(
          "reserved kernel marker address {marker} ({}) used in refs[{idx}] of Ixon constant {}",
          addr.hex(),
          entry.key().hex()
        ));
      }
    }
  }

  for entry in ixon_env.named.iter() {
    if let Some(marker) = reserved_marker_name(&entry.value().addr) {
      return Err(format!(
        "reserved kernel marker address {marker} ({}) used as the named address for {}",
        entry.value().addr.hex(),
        entry.key().pretty()
      ));
    }
  }

  Ok(())
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::ix::env::{self, BinderInfo};
  use crate::ix::ixon::metadata::CallSiteEntry;
  use crate::ix::kernel::expr::ExprData;
  use crate::ix::kernel::level::UnivData;

  fn mk_name(s: &str) -> Name {
    let mut n = Name::anon();
    for part in s.split('.') {
      n = Name::str(n, part.to_string());
    }
    n
  }

  fn n_lit(x: u64) -> Nat {
    Nat::from(x)
  }

  // ---- lean_level_to_kuniv ----

  #[test]
  fn lean_level_zero_to_kuniv() {
    let u = lean_level_to_kuniv(&Level::zero(), &[]);
    assert!(matches!(u.data(), UnivData::Zero(_)));
  }

  #[test]
  fn lean_level_succ_to_kuniv() {
    let u = lean_level_to_kuniv(&Level::succ(Level::zero()), &[]);
    match u.data() {
      UnivData::Succ(inner, _) => {
        assert!(matches!(inner.data(), UnivData::Zero(_)))
      },
      other => panic!("expected Succ, got {other:?}"),
    }
  }

  #[test]
  fn lean_level_param_by_index() {
    let u_name = mk_name("u");
    let v_name = mk_name("v");
    let params = vec![u_name.clone(), v_name.clone()];
    let u = lean_level_to_kuniv(&Level::param(v_name), &params);
    match u.data() {
      UnivData::Param(i, _, _) => assert_eq!(*i, 1),
      other => panic!("expected Param, got {other:?}"),
    }
  }

  #[test]
  fn lean_level_max_to_kuniv() {
    let u_name = mk_name("u");
    let v_name = mk_name("v");
    let params = vec![u_name.clone(), v_name.clone()];
    let ll = Level::max(Level::param(u_name), Level::param(v_name));
    let u = lean_level_to_kuniv(&ll, &params);
    assert!(matches!(u.data(), UnivData::Max(..)));
  }

  #[test]
  #[should_panic(expected = "unknown level param")]
  fn lean_level_param_unknown_panics() {
    let _ = lean_level_to_kuniv(&Level::param(mk_name("zzz")), &[mk_name("u")]);
  }

  #[test]
  #[should_panic(expected = "unexpected level metavariable")]
  fn lean_level_mvar_panics() {
    let _ = lean_level_to_kuniv(&Level::mvar(mk_name("m")), &[]);
  }

  // ---- lean_name_to_addr ----

  #[test]
  fn lean_name_to_addr_is_deterministic() {
    let a1 = lean_name_to_addr(&mk_name("Nat"));
    let a2 = lean_name_to_addr(&mk_name("Nat"));
    assert_eq!(a1, a2);
  }

  #[test]
  fn lean_name_to_addr_different_names_differ() {
    let a1 = lean_name_to_addr(&mk_name("Nat"));
    let a2 = lean_name_to_addr(&mk_name("Bool"));
    assert_ne!(a1, a2);
  }

  #[test]
  fn lean_name_to_addr_respects_dot_segments() {
    let a1 = lean_name_to_addr(&mk_name("Nat.zero"));
    let a2 = lean_name_to_addr(&mk_name("Nat.succ"));
    assert_ne!(a1, a2);
  }

  // ---- param_names_hash ----

  #[test]
  fn param_names_hash_determinism() {
    let ps = [mk_name("u"), mk_name("v")];
    let h1 = param_names_hash(&ps);
    let h2 = param_names_hash(&ps);
    assert_eq!(h1, h2);
  }

  #[test]
  fn param_names_hash_order_sensitive() {
    let h1 = param_names_hash(&[mk_name("u"), mk_name("v")]);
    let h2 = param_names_hash(&[mk_name("v"), mk_name("u")]);
    assert_ne!(h1, h2);
  }

  #[test]
  fn param_names_hash_length_sensitive() {
    let h1 = param_names_hash(&[mk_name("u")]);
    let h2 = param_names_hash(&[mk_name("u"), mk_name("u")]);
    assert_ne!(h1, h2);
  }

  #[test]
  fn param_names_hash_empty_is_stable() {
    let h1 = param_names_hash(&[]);
    let h2 = param_names_hash(&[]);
    assert_eq!(h1, h2);
  }

  // ---- resolve_lean_name_addr ----

  #[test]
  fn resolve_lean_name_addr_fallback_uses_name_hash() {
    let name = mk_name("Unknown");
    let expected = lean_name_to_addr(&name);
    let a = resolve_lean_name_addr(&name, None, None);
    assert_eq!(a, expected);
  }

  #[test]
  fn resolve_lean_name_addr_uses_primary_map() {
    let map: DashMap<Name, Address> = DashMap::new();
    let name = mk_name("Foo");
    let real = Address::hash(b"custom");
    map.insert(name.clone(), real.clone());
    let got = resolve_lean_name_addr(&name, Some(&map), None);
    assert_eq!(got, real);
  }

  #[test]
  fn resolve_lean_name_addr_falls_through_to_aux() {
    let primary: DashMap<Name, Address> = DashMap::new();
    let aux: DashMap<Name, Address> = DashMap::new();
    let name = mk_name("Aux.name");
    let real = Address::hash(b"aux");
    aux.insert(name.clone(), real.clone());
    let got = resolve_lean_name_addr(&name, Some(&primary), Some(&aux));
    assert_eq!(got, real);
  }

  #[test]
  fn ixon_ingress_rejects_reserved_marker_named_addr() {
    let env = IxonEnv::new();
    let marker = crate::ix::kernel::primitive::PrimAddrs::new().eager_reduce;
    env.register_name(
      mk_name("Evil.marker"),
      crate::ix::ixon::env::Named::with_addr(marker),
    );

    let err = match ixon_ingress::<Meta>(&env) {
      Ok(_) => panic!("expected reserved marker rejection"),
      Err(err) => err,
    };
    assert!(err.contains("eager_reduce"), "{err}");
    assert!(err.contains("named address"), "{err}");
  }

  #[test]
  fn ixon_ingress_rejects_reserved_marker_refs() {
    let env = IxonEnv::new();
    let marker = crate::ix::kernel::primitive::PrimAddrs::new().eager_reduce;
    let constant = Constant::with_tables(
      crate::ix::ixon::constant::ConstantInfo::Axio(
        crate::ix::ixon::constant::Axiom {
          is_unsafe: false,
          lvls: 0,
          typ: IxonExpr::sort(0),
        },
      ),
      vec![],
      vec![marker],
      vec![],
    );
    env.store_const(Address::hash(b"evil-const"), constant);

    let err = match ixon_ingress::<Meta>(&env) {
      Ok(_) => panic!("expected reserved marker rejection"),
      Err(err) => err,
    };
    assert!(err.contains("eager_reduce"), "{err}");
    assert!(err.contains("refs[0]"), "{err}");
  }

  // ---- lean_expr_to_zexpr: variant coverage ----

  fn do_ingress(e: &LeanExpr, pn: &[Name]) -> KExpr<Meta> {
    let intern = InternTable::<Meta>::new();
    lean_expr_to_zexpr(e, pn, &intern, None, None)
  }

  #[test]
  fn ingress_bvar() {
    let e = LeanExpr::bvar(n_lit(5));
    let k = do_ingress(&e, &[]);
    match k.data() {
      ExprData::Var(i, _, _) => assert_eq!(*i, 5),
      other => panic!("expected Var, got {other:?}"),
    }
  }

  #[test]
  fn ingress_sort_zero() {
    let e = LeanExpr::sort(Level::zero());
    let k = do_ingress(&e, &[]);
    assert!(matches!(k.data(), ExprData::Sort(..)));
  }

  #[test]
  fn ingress_const_without_universe_args() {
    let e = LeanExpr::cnst(mk_name("Unit"), vec![]);
    let k = do_ingress(&e, &[]);
    match k.data() {
      ExprData::Const(id, univs, _) => {
        assert_eq!(univs.len(), 0);
        assert_eq!(id.addr, lean_name_to_addr(&mk_name("Unit")));
      },
      other => panic!("expected Const, got {other:?}"),
    }
  }

  #[test]
  fn ingress_const_with_universe_args() {
    let u_name = mk_name("u");
    let e = LeanExpr::cnst(mk_name("List"), vec![Level::param(u_name.clone())]);
    let k = do_ingress(&e, &[u_name]);
    match k.data() {
      ExprData::Const(_id, univs, _) => {
        assert_eq!(univs.len(), 1);
        assert!(matches!(univs[0].data(), UnivData::Param(0, _, _)));
      },
      other => panic!("expected Const, got {other:?}"),
    }
  }

  #[test]
  fn ingress_app() {
    let e =
      LeanExpr::app(LeanExpr::sort(Level::zero()), LeanExpr::bvar(n_lit(0)));
    let k = do_ingress(&e, &[]);
    assert!(matches!(k.data(), ExprData::App(..)));
  }

  #[test]
  fn ingress_lambda() {
    let e = LeanExpr::lam(
      mk_name("x"),
      LeanExpr::sort(Level::zero()),
      LeanExpr::bvar(n_lit(0)),
      BinderInfo::Default,
    );
    let k = do_ingress(&e, &[]);
    assert!(matches!(k.data(), ExprData::Lam(..)));
  }

  #[test]
  fn ingress_forall() {
    let e = LeanExpr::all(
      mk_name("x"),
      LeanExpr::sort(Level::zero()),
      LeanExpr::sort(Level::zero()),
      BinderInfo::Default,
    );
    let k = do_ingress(&e, &[]);
    assert!(matches!(k.data(), ExprData::All(..)));
  }

  #[test]
  fn ingress_let() {
    let e = LeanExpr::letE(
      mk_name("x"),
      LeanExpr::sort(Level::zero()),
      LeanExpr::bvar(n_lit(0)),
      LeanExpr::bvar(n_lit(0)),
      false,
    );
    let k = do_ingress(&e, &[]);
    assert!(matches!(k.data(), ExprData::Let(..)));
  }

  #[test]
  fn ingress_nat_literal() {
    let e = LeanExpr::lit(env::Literal::NatVal(n_lit(42)));
    let k = do_ingress(&e, &[]);
    assert!(matches!(k.data(), ExprData::Nat(..)));
  }

  #[test]
  fn ingress_str_literal() {
    let e = LeanExpr::lit(env::Literal::StrVal("hi".into()));
    let k = do_ingress(&e, &[]);
    assert!(matches!(k.data(), ExprData::Str(..)));
  }

  #[test]
  fn ingress_proj() {
    let e = LeanExpr::proj(mk_name("Prod"), n_lit(0), LeanExpr::bvar(n_lit(0)));
    let k = do_ingress(&e, &[]);
    match k.data() {
      ExprData::Prj(id, field, _, _) => {
        assert_eq!(id.addr, lean_name_to_addr(&mk_name("Prod")));
        assert_eq!(*field, 0);
      },
      other => panic!("expected Prj, got {other:?}"),
    }
  }

  #[test]
  fn ingress_mdata_passes_through_inner_shape() {
    // Mdata is metadata; the shape of the outer expression mirrors the inner.
    let inner = LeanExpr::sort(Level::zero());
    let e = LeanExpr::mdata(vec![], inner);
    let k = do_ingress(&e, &[]);
    assert!(matches!(k.data(), ExprData::Sort(..)));
  }

  // ---- Deep nesting: exercises the iterative stack ----

  /// Drop a left-deep `Arc<ExprData::App>` spine iteratively so test
  /// teardown doesn't recurse once per level. Without this, dropping a
  /// chain of N `Expr`s recurses N times regardless of whether ingress
  /// itself is iterative (the recursion is in `Arc<ExprData>::drop`).
  fn drop_app_spine_iteratively(mut e: LeanExpr) {
    while let env::ExprData::App(f, _, _) = e.as_data() {
      let next = f.clone();
      drop(e);
      e = next;
    }
    drop(e);
  }

  /// Same pattern for forall / lambda body chains.
  fn drop_binder_chain_iteratively(mut e: LeanExpr) {
    while let env::ExprData::ForallE(_, _, body, _, _)
    | env::ExprData::Lam(_, _, body, _, _) = e.as_data()
    {
      let next = body.clone();
      drop(e);
      e = next;
    }
    drop(e);
  }

  #[test]
  fn ingress_deep_app_nesting_does_not_overflow() {
    // Build a left-deep app spine and verify ingress completes without
    // stack overflow. Depth is chosen to exercise the iterative stack
    // without tipping the Arc<ExprData> drop chain over thread-stack
    // limits (the recursive drop of a deeply nested `LeanExpr` is the
    // dominant hazard here — ingress proper is iterative).
    let depth = 500;
    let mut e = LeanExpr::sort(Level::zero());
    for _ in 0..depth {
      e = LeanExpr::app(e, LeanExpr::bvar(n_lit(0)));
    }
    let _k = do_ingress(&e, &[]);
    // Manual teardown: avoid `e`'s recursive Drop.
    drop_app_spine_iteratively(e);
  }

  #[test]
  fn ingress_deep_forall_nesting_does_not_overflow() {
    // Body under deeply nested foralls. Binder-name stack must not
    // overflow during ingress.
    let depth = 500;
    let mut e = LeanExpr::bvar(n_lit(0));
    for _ in 0..depth {
      e = LeanExpr::all(
        mk_name("x"),
        LeanExpr::sort(Level::zero()),
        e,
        BinderInfo::Default,
      );
    }
    let _k = do_ingress(&e, &[]);
    drop_binder_chain_iteratively(e);
  }

  #[test]
  fn ingress_deep_max_univ_does_not_overflow() {
    // Deeply nested Max chain. Level drop is also recursive; keep depth
    // conservative.
    let mut l = Level::zero();
    for _ in 0..300 {
      l = Level::max(l, Level::zero());
    }
    let _u = lean_level_to_kuniv(&l, &[]);
  }

  // ---- Panic-on-invalid-input regression guards ----

  #[test]
  #[should_panic(expected = "FVar")]
  fn ingress_fvar_panics() {
    let e = LeanExpr::fvar(mk_name("x"));
    let _ = do_ingress(&e, &[]);
  }

  #[test]
  #[should_panic(expected = "MVar")]
  fn ingress_mvar_panics() {
    let e = LeanExpr::mvar(mk_name("m"));
    let _ = do_ingress(&e, &[]);
  }

  // ---- Caching ----

  #[test]
  fn ingress_cached_hits_cache_on_second_call() {
    let env = KEnv::<Meta>::new();
    let e = LeanExpr::app(
      LeanExpr::sort(Level::zero()),
      LeanExpr::sort(Level::zero()),
    );
    let k1 = lean_expr_to_zexpr_with_kenv(&e, &[], &env, None, None);
    let k2 = lean_expr_to_zexpr_with_kenv(&e, &[], &env, None, None);
    // Cache hit → same interned result.
    assert!(k1.ptr_eq(&k2));
  }

  #[test]
  fn callsite_ingress_uses_canon_meta_for_collapsed_canonical_arg() {
    let head_name = mk_name("Head.rec");
    let arg_name = mk_name("GoodArg");
    let bad_name = mk_name("BadArg");
    let head_name_addr = lean_name_to_addr(&head_name);
    let arg_name_addr = lean_name_to_addr(&arg_name);
    let bad_name_addr = lean_name_to_addr(&bad_name);
    let head_ref_addr = Address::hash(b"head-content");
    let arg_ref_addr = Address::hash(b"arg-content");

    let mut names = FxHashMap::default();
    names.insert(head_name_addr.clone(), head_name.clone());
    names.insert(arg_name_addr.clone(), arg_name.clone());
    names.insert(bad_name_addr.clone(), bad_name);

    let mut arena = ExprMeta::default();
    let bad_entry_meta = arena.alloc(ExprMetaData::Ref { name: bad_name_addr });
    let arg_canon_meta = arena.alloc(ExprMetaData::Ref { name: arg_name_addr });
    let root = arena.alloc(ExprMetaData::CallSite {
      name: head_name_addr,
      entries: vec![CallSiteEntry::Collapsed {
        sharing_idx: 0,
        meta: bad_entry_meta,
      }],
      canon_meta: vec![arg_canon_meta],
    });

    let ixon = IxonExpr::app(
      IxonExpr::reference(0, vec![]),
      IxonExpr::reference(1, vec![]),
    );
    let sharing: Vec<Arc<IxonExpr>> = vec![];
    let refs = vec![head_ref_addr.clone(), arg_ref_addr.clone()];
    let univs: Vec<Arc<IxonUniv>> = vec![];
    let intern = InternTable::<Meta>::new();
    let ctx = Ctx {
      sharing: &sharing,
      refs: &refs,
      univs: &univs,
      mut_ctx: vec![],
      arena: &arena,
      names: &names,
      lvls: vec![],
      intern: &intern,
      synth_counter: Cell::new(0),
    };
    let ixon_env = IxonEnv::new();
    let mut cache = ExprCache::<Meta>::default();
    let mut univ_cache = UnivCache::<Meta>::default();

    let mut stats = ConvertStats::default();
    let k = ingress_expr(
      &ixon,
      root,
      &ctx,
      &ixon_env,
      &mut cache,
      &mut univ_cache,
      &mut stats,
    )
    .unwrap();
    let ExprData::App(f, a, _) = k.data() else {
      panic!("expected App, got {:?}", k.data());
    };
    let ExprData::Const(head_id, _, _) = f.data() else {
      panic!("expected CallSite head Const, got {:?}", f.data());
    };
    let ExprData::Const(arg_id, _, _) = a.data() else {
      panic!("expected canonical arg Const, got {:?}", a.data());
    };
    assert_eq!(head_id.addr, head_ref_addr);
    assert_eq!(head_id.name, head_name);
    assert_eq!(arg_id.addr, arg_ref_addr);
    assert_eq!(arg_id.name, arg_name);
  }

  #[test]
  fn ingress_cache_differentiates_by_param_names() {
    let env = KEnv::<Meta>::new();
    // Same Lean expression, but different param names should produce
    // different cache keys and (for Param-containing exprs) different
    // KExprs.
    let u_name = mk_name("u");
    let v_name = mk_name("v");
    let e = LeanExpr::sort(Level::param(u_name.clone()));
    let k1 = lean_expr_to_zexpr_with_kenv(
      &e,
      std::slice::from_ref(&u_name),
      &env,
      None,
      None,
    );
    let k2 = lean_expr_to_zexpr_with_kenv(
      &e,
      &[v_name, u_name.clone()],
      &env,
      None,
      None,
    );
    // In the first, Param(u) has index 0; in the second, Param(u) has index 1.
    let i1 = match k1.data() {
      ExprData::Sort(u, _) => match u.data() {
        UnivData::Param(i, _, _) => *i,
        _ => panic!(),
      },
      _ => panic!(),
    };
    let i2 = match k2.data() {
      ExprData::Sort(u, _) => match u.data() {
        UnivData::Param(i, _, _) => *i,
        _ => panic!(),
      },
      _ => panic!(),
    };
    assert_eq!(i1, 0);
    assert_eq!(i2, 1);
  }

  // ---- build_ingress_lookups ----

  #[test]
  fn build_ingress_lookups_on_empty_env() {
    let ie = IxonEnv::new();
    let (name_map, addr_map) = build_ingress_lookups(&ie);
    assert!(name_map.is_empty());
    assert!(addr_map.is_empty());
  }

  #[test]
  fn build_ingress_lookups_inverts_name_table() {
    let ie = IxonEnv::new();
    let nat_name = mk_name("Nat");
    let nat_addr = lean_name_to_addr(&nat_name);
    ie.names.insert(nat_addr.clone(), nat_name.clone());

    let list_name = mk_name("List");
    let list_addr = Address::hash(b"arbitrary");
    ie.named.insert(
      list_name.clone(),
      crate::ix::ixon::env::Named::with_addr(list_addr.clone()),
    );

    let (name_map, addr_map) = build_ingress_lookups(&ie);
    assert_eq!(name_map.get(&nat_addr), Some(&nat_name));
    assert_eq!(addr_map.get(&list_name), Some(&list_addr));
  }
}
