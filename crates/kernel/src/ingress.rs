//! Ingress: convert Ixon environment to zero kernel types.
//!
//! Converts Ixon `Constant`/`ConstantInfo`/`Expr`/`Univ` (alpha-invariant,
//! content-addressed) to `KExpr`/`KUniv`/`KConst` (kernel types with positional
//! universe params and optional metadata). Uses iterative stack-based traversal
//! to avoid stack overflow on deeply nested expressions.

use std::cell::{Cell, RefCell};
#[cfg(not(target_arch = "riscv64"))]
use std::hash::{BuildHasher, Hash};
use std::sync::Arc;
use std::time::{Duration, Instant};

#[cfg(not(target_arch = "riscv64"))]
use rayon::iter::{
  IntoParallelIterator, IntoParallelRefIterator, ParallelIterator,
};
use rustc_hash::{FxHashMap, FxHashSet};

use dashmap::DashMap;

use bignat::Nat;
use ix_common::address::Address;
#[cfg(not(target_arch = "riscv64"))]
use ix_common::env::ConstantInfo as LeanCI;
use ix_common::env::DefinitionSafety;
#[cfg(not(target_arch = "riscv64"))]
use ix_common::env::Env as LeanEnv;
use ix_common::env::{BinderInfo, Name, ReducibilityHints};
#[cfg(not(target_arch = "riscv64"))]
use ixon::constant::DefKind;
use ixon::constant::{
  Constant, ConstantInfo as IxonCI, MutConst as IxonMutConst,
};
use ixon::contract::{BinderContract, LetContract, ValueContract, source};
use ixon::env::Env as IxonEnv;
use ixon::expr::Expr as IxonExpr;
use ixon::metadata::{ConstantMeta, ConstantMetaInfo, ExprMeta, ExprMetaData};
use ixon::univ::Univ as IxonUniv;

use super::constant::{KConst, RecRule};
use super::env::{CtxAddr, InternTable, KEnv};
use super::expr::{KExpr, MData, UnivDecor};
use super::id::KId;
use super::level::{KUniv, UnivData};
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
  /// Rec edges for the definition currently being admitted.
  local_refs: Option<&'a RefCell<FxHashSet<Address>>>,
  arena: &'a ExprMeta,
  names: &'a FxHashMap<Address, Name>,
  lvls: Vec<Name>,
  /// Level-spelling patches of this constant, keyed by metadata arena
  /// index — the stage-2 decoration source (canonicity §10.6). Values
  /// are the patch's univ indices in the VIRTUAL index space
  /// `univs ++ meta_univs`. Empty for anon ingress and for constants
  /// without patches.
  univ_patches: FxHashMap<u64, &'a [u64]>,
  /// Extension univ table: original (pre-canonicalization) spellings
  /// referenced by `univ_patches` (canonicity §10.6).
  meta_univs: &'a [Arc<IxonUniv>],
  /// Counter for generating synthetic unique names when metadata is missing.
  synth_counter: Cell<u64>,
}

impl<'a, M: KernelMode> Ctx<'a, M> {
  /// The level-spelling patch covering the occurrence whose (post-mdata)
  /// arena index is `arena_idx`, if any.
  fn univ_patch(&self, arena_idx: u64) -> Option<&'a [u64]> {
    self.univ_patches.get(&arena_idx).copied()
  }

  /// Resolve a univ index in the VIRTUAL space `univs ++ meta_univs` —
  /// the index space `univ_patches` entries are written in
  /// (canonicity §10.6).
  fn univ_at_virtual(&self, idx: u64) -> Result<&'a Arc<IxonUniv>, String> {
    let i = usize::try_from(idx)
      .map_err(|_e| format!("virtual univ index {idx} exceeds usize"))?;
    self
      .univs
      .get(i)
      .or_else(|| self.meta_univs.get(i - self.univs.len()))
      .ok_or_else(|| {
        format!(
          "virtual univ index {i} out of bounds (univs {} + meta_univs {})",
          self.univs.len(),
          self.meta_univs.len()
        )
      })
  }
}

/// Build the arena-index → patch lookup for a constant's
/// `ConstantMeta.univ_patches` (canonicity §10.6).
fn univ_patch_map(meta: &ConstantMeta) -> FxHashMap<u64, &[u64]> {
  meta
    .univ_patches
    .iter()
    .map(|p| (p.arena_idx, p.univ_idxs.as_slice()))
    .collect()
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

  fn merge(mut self, other: &Self) -> Self {
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
  intern: &mut InternTable<M>,
  u: KUniv<M>,
  stats: &mut ConvertStats,
) -> KUniv<M> {
  if !stats.enabled {
    return intern.intern_univ(u);
  }
  let t0 = Instant::now();
  let key = super::env::univ_key(&u);
  let result = if let Some(existing) = intern.try_get_univ(&key) {
    stats.intern_univ_get_hits += 1;
    existing
  } else {
    intern.intern_univ(u)
  };
  stats.intern_univ_calls += 1;
  stats.intern_univ_ns += elapsed_ns(t0);
  result
}

/// Key-first interning. Builds the shallow structural key from already
/// canonical children, asks the intern table for an existing canonical
/// KExpr; only on a miss does it call `build()` to allocate a new KExpr
/// (which takes a fresh uid).
///
/// Why this exists: profiling on Mathlib showed the construction +
/// interning pair dominates `convert` worker-sum, and most constructed
/// values are immediately discarded for an existing canonical Arc. By
/// probing with just the shallow key we skip construction entirely on a
/// hit. (Historically the probe key was a precomputed blake3 content
/// hash; the shallow key preserves the skip while removing the hash.)
#[inline]
fn timed_intern_or_build<M: KernelMode>(
  intern: &mut InternTable<M>,
  key: &super::env::ExprKey,
  build: impl FnOnce() -> KExpr<M>,
  stats: &mut ConvertStats,
) -> KExpr<M> {
  if !stats.enabled {
    if let Some(existing) = intern.try_get_expr(key) {
      return existing;
    }
    return intern.intern_expr(build());
  }
  let t0 = Instant::now();
  if let Some(existing) = intern.try_get_expr(key) {
    stats.intern_expr_get_hits += 1;
    stats.intern_expr_calls += 1;
    stats.intern_expr_ns += elapsed_ns(t0);
    return existing;
  }
  let kc_t0 = Instant::now();
  let new = build();
  let kc_elapsed = elapsed_ns(kc_t0);
  stats.kexpr_construct_ns += kc_elapsed;
  stats.kexpr_construct_calls += 1;
  let interned = intern.intern_expr(new);
  let total = elapsed_ns(t0);
  // Account for the map traffic only — the closure body's time is
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
/// The callers (`ingress_muts_inductive`'s `ctor_ids`, and
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
  intern: &mut InternTable<M>,
  cache: &mut UnivCache<M>,
  stats: &mut ConvertStats,
) -> Result<KUniv<M>, String> {
  bump_convert_stat!(stats, univ_roots);
  let cache_key = Arc::as_ptr(root) as usize;
  if let Some(cached) = cache.get(&cache_key) {
    bump_convert_stat!(stats, univ_cache_hits);
    return Ok(cached.clone());
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
          let pos = usize::try_from(*idx)
            .map_err(|_e| format!("univ var index {idx} exceeds usize"))?;
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
  Ok(result)
}

fn ingress_univ_args<M: KernelMode>(
  univ_idxs: &[u64],
  ctx: &Ctx<'_, M>,
  intern: &mut InternTable<M>,
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
    result.push(ingress_univ(u, ctx, intern, cache, stats)?);
  }
  Ok(result.into_boxed_slice())
}

/// Does this stored Ixon universe tree match the (`mk*`-reduced) kernel
/// universe node-for-node? `false` means the smart constructors changed
/// it during ingress — the occurrence gets a level-spelling decoration
/// (canonicity §10.6, stage-1 rule).
fn ixon_matches_kuniv<M: KernelMode>(u: &IxonUniv, k: &KUniv<M>) -> bool {
  match (u, k.data()) {
    (IxonUniv::Zero, UnivData::Zero(_)) => true,
    (IxonUniv::Succ(a), UnivData::Succ(b, _)) => ixon_matches_kuniv(a, b),
    (IxonUniv::Max(a1, b1), UnivData::Max(a2, b2, _))
    | (IxonUniv::IMax(a1, b1), UnivData::IMax(a2, b2, _)) => {
      ixon_matches_kuniv(a1, a2) && ixon_matches_kuniv(b1, b2)
    },
    (IxonUniv::Var(i), UnivData::Param(j, _, _)) => i == j,
    _ => false,
  }
}

/// Level-spelling decoration for a `Const` occurrence: `Some` of the
/// FULL stored level-arg spelling list when any referenced table entry's
/// `mk*` rebuild differs from its stored tree (already-normal entries
/// ride along unchanged so egress replays the whole list positionally),
/// `None` when every entry is normal. Meta mode only — call inside
/// `M::meta_field_with`; indices were validated by `ingress_univ_args`.
fn univ_args_decor<M: KernelMode>(
  univ_idxs: &[u64],
  ctx: &Ctx<'_, M>,
  ingressed: &[KUniv<M>],
) -> Option<UnivDecor> {
  let stored_at = |idx: u64| -> &Arc<IxonUniv> {
    usize::try_from(idx)
      .ok()
      .and_then(|i| ctx.univs.get(i))
      .expect("univ index validated by ingress_univ_args")
  };
  let changed = univ_idxs
    .iter()
    .zip(ingressed.iter())
    .any(|(&idx, k)| !ixon_matches_kuniv(stored_at(idx), k));
  if !changed {
    return None;
  }
  let spellings: Box<[Arc<IxonUniv>]> =
    univ_idxs.iter().map(|&idx| stored_at(idx).clone()).collect();
  Some(UnivDecor::Const(spellings))
}

/// Stage-2 decoration source for a `Const`-shaped occurrence
/// (canonicity §10.6): a `univ_patches` entry keyed by the occurrence's
/// (post-mdata) arena index carries the FULL original spelling list in
/// the virtual index space — decorate from it. Without a patch, fall
/// back to the stage-1 mk*-rebuild test against the stored primary
/// entries; on canonical tables the fallback never fires (P3), but it
/// keeps hand-built raw-table fixtures exercised. Meta mode only — call
/// inside `M::meta_field_try`.
fn univ_args_decor_at<M: KernelMode>(
  arena_idx: u64,
  univ_idxs: &[u64],
  ctx: &Ctx<'_, M>,
  ingressed: &[KUniv<M>],
) -> Result<Option<UnivDecor>, String> {
  let Some(patch_idxs) = ctx.univ_patch(arena_idx) else {
    return Ok(univ_args_decor(univ_idxs, ctx, ingressed));
  };
  if patch_idxs.len() != ingressed.len() {
    return Err(format!(
      "univ patch at arena index {arena_idx} has {} entries but the \
       occurrence has {} level args",
      patch_idxs.len(),
      ingressed.len()
    ));
  }
  let mut spellings = Vec::with_capacity(patch_idxs.len());
  for &vidx in patch_idxs {
    spellings.push(ctx.univ_at_virtual(vidx)?.clone());
  }
  let changed = spellings
    .iter()
    .zip(ingressed.iter())
    .any(|(s, k)| !ixon_matches_kuniv(s, k));
  Ok(if changed {
    Some(UnivDecor::Const(spellings.into_boxed_slice()))
  } else {
    None
  })
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
    contract: BinderContract,
    mdata: M::MField<Vec<MData>>,
  },
  AllBody {
    body: Arc<IxonExpr>,
    body_arena: u64,
  },
  AllDone {
    name: M::MField<Name>,
    bi: M::MField<BinderInfo>,
    contract: BinderContract,
    result: ValueContract,
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
    contract: LetContract,
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
  intern: &mut InternTable<M>,
  ixon_env: crate::input::Input<'_>,
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
          let lookup_t0 =
            if stats.enabled { Some(Instant::now()) } else { None };
          let cached = cache.get(&cache_key);
          if let Some(t0) = lookup_t0 {
            stats.expr_cache_lookup_ns += elapsed_ns(t0);
          }
          if let Some(cached) = cached {
            bump_convert_stat!(stats, expr_cache_hits);
            values.push(cached.clone());
            if let Some(t0) = process_t0 {
              stats.process_arm_ns += elapsed_ns(t0);
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
            let data = ixon_env.mdata(kvm)?;
            if M::HAS_META && source::has_metadata(&data) {
              return Err(
                "semantic contracts cannot come from optional metadata".into(),
              );
            }
            mdata_layers.push(data);
          }
          if let Some(t0) = kv_t0 {
            stats.resolve_kvmap_ns += elapsed_ns(t0);
            stats.resolve_kvmap_calls += mdata.len() as u64;
          }
          current_idx = *child;
        }
        if let Some(t0) = arena_t0 {
          stats.arena_walk_ns += elapsed_ns(t0);
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
            .checked_sub(1)
            .and_then(|top| top.checked_sub(idx_usize))
            .and_then(|i| binder_names.get(i))
            .cloned()
            .unwrap_or_else(Name::anon);
          if mdata_layers.is_empty() {
            let name_field = M::meta_field(name);
            let mdata_field: M::MField<Vec<MData>> = M::meta_field(vec![]);
            let key = super::env::ExprKey::Var(*idx);
            values.push(timed_intern_or_build(
              intern,
              &key,
              || KExpr::var_mdata(*idx, name_field, mdata_field),
              stats,
            ));
          } else {
            let name_field = M::meta_field(name);
            let mdata_field = M::meta_field(mdata_layers);
            let key = super::env::ExprKey::Var(*idx);
            values.push(timed_intern_or_build(
              intern,
              &key,
              || KExpr::var_mdata(*idx, name_field, mdata_field),
              stats,
            ));
          }
          if let Some(t0) = process_t0 {
            stats.process_arm_ns += elapsed_ns(t0);
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
            let zu = ingress_univ(u, ctx, intern, univ_cache, stats)?;
            // Spelling decoration (canonicity §10.6): the occurrence's
            // `univ_patches` entry (stage 2) is the primary source of
            // the original spelling; without one, fall back to the
            // stage-1 rule (stored tree vs mk* rebuild — never fires on
            // canonical tables, P3). Anon mode skips the closure.
            let decor: M::MField<Option<UnivDecor>> =
              M::meta_field_try::<Option<UnivDecor>, _, String>(|| {
                let spelling = match ctx.univ_patch(current_idx) {
                  Some(idxs) => {
                    let vidx = *idxs.first().ok_or_else(|| {
                      format!("empty univ patch at arena index {current_idx}")
                    })?;
                    ctx.univ_at_virtual(vidx)?
                  },
                  None => u,
                };
                Ok(if ixon_matches_kuniv(spelling, &zu) {
                  None
                } else {
                  Some(UnivDecor::Sort(spelling.clone()))
                })
              })?;
            let key = super::env::ExprKey::Sort(
              *zu.addr(),
              M::meta_get(&decor).cloned().flatten(),
            );
            values.push(timed_intern_or_build(
              intern,
              &key,
              || KExpr::sort_full(zu, mdata, decor),
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
            ixon_env.require_reference(&addr)?;
            // Meta mode: walk the arena to find the Ref's Lean name.
            // Anon mode: the closure is never invoked — no arena walk,
            // no name construction, no resolve_name call.
            let name_field: M::MField<Name> = M::meta_field_try::<
              Name,
              _,
              String,
            >(|| match node {
              ExprMetaData::Ref { name: name_addr } => {
                Ok(resolve_name(name_addr, ctx.names))
              },
              _ => Err(format!(
                "Ref at index {ref_idx} (addr {}) has no metadata name (node={node:?})",
                &addr.hex()[..8]
              )),
            })?;
            let univs =
              ingress_univ_args(univ_idxs, ctx, intern, univ_cache, stats)?;
            let id = KId::new(addr, name_field);
            let decor: M::MField<Option<UnivDecor>> =
              M::meta_field_try::<Option<UnivDecor>, _, String>(|| {
                univ_args_decor_at(current_idx, univ_idxs, ctx, &univs)
              })?;
            let key = super::env::ExprKey::Const(
              id.addr.clone(),
              univs.iter().map(|u| *u.addr()).collect(),
              M::meta_get(&decor).cloned().flatten(),
            );
            values.push(timed_intern_or_build(
              intern,
              &key,
              || KExpr::cnst_full(id, univs, mdata, decor),
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
            if let Some(refs) = ctx.local_refs {
              refs.borrow_mut().insert(mid.addr.clone());
            }
            let univs =
              ingress_univ_args(univ_idxs, ctx, intern, univ_cache, stats)?;
            let decor: M::MField<Option<UnivDecor>> =
              M::meta_field_try::<Option<UnivDecor>, _, String>(|| {
                univ_args_decor_at(current_idx, univ_idxs, ctx, &univs)
              })?;
            let key = super::env::ExprKey::Const(
              mid.addr.clone(),
              univs.iter().map(|u| *u.addr()).collect(),
              M::meta_get(&decor).cloned().flatten(),
            );
            values.push(timed_intern_or_build(
              intern,
              &key,
              || KExpr::cnst_full(mid, univs, mdata, decor),
              stats,
            ));
          },

          IxonExpr::App(f, a) => {
            bump_convert_stat!(stats, app_nodes);
            let (f_arena, a_arena) = match node {
              ExprMetaData::App { children } => (children[0], children[1]),
              _ => (current_idx, current_idx),
            };
            stack.push(ExprFrame::AppDone { mdata });
            stack
              .push(ExprFrame::AppArg { arg: a.clone(), arg_arena: a_arena });
            stack
              .push(ExprFrame::Process { expr: f.clone(), arena_idx: f_arena });
          },

          // Input contracts participate in conversion. Resource validity still
          // requires the separate addressed validator in `crate::resource`.
          IxonExpr::Lam(contract, ty, body) => {
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
              contract: *contract,
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

          IxonExpr::All(contract, result, ty, body) => {
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
              contract: *contract,
              result: *result,
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

          IxonExpr::Let(contract, ty, val, body) => {
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
              contract: *contract,
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
            ixon_env.require_reference(&type_addr)?;
            // The arena holds both the struct name and the child arena
            // pointer (needed for the projected value's metadata walk).
            // Meta mode reads both; Anon mode skips the entire arena
            // touch — no name, no child-arena indexing.
            let mut child_arena: u64 = 0;
            let struct_name_field: M::MField<Name> = M::meta_field_try::<
              Name,
              _,
              String,
            >(
              || match node
            {
              ExprMetaData::Prj { struct_name: addr, child } => {
                child_arena = *child;
                Ok(resolve_name(addr, ctx.names))
              },
              _ => Err(format!(
                "Prj at ref index {type_ref_idx} (addr {}) has no metadata name (node={node:?})",
                &type_addr.hex()[..8]
              )),
            }
            )?;
            stack.push(ExprFrame::PrjDone {
              type_id: KId::new(type_addr, struct_name_field),
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
            let blob = ixon_env.blob(addr)?.ok_or_else(|| {
              format!("missing Str blob at addr {}", addr.hex())
            })?;
            if let Some(t0) = gb_t0 {
              stats.get_blob_ns += elapsed_ns(t0);
              stats.get_blob_calls += 1;
            }
            let s = String::from_utf8(blob).map_err(|e| {
              format!("invalid UTF-8 in Str blob at addr {}: {e}", addr.hex())
            })?;
            let blob_addr = addr.clone();
            let key = super::env::ExprKey::Str(blob_addr.clone());
            values.push(timed_intern_or_build(
              intern,
              &key,
              || KExpr::str_mdata(s, blob_addr, mdata),
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
            let blob = ixon_env.blob(addr)?.ok_or_else(|| {
              format!("missing Nat blob at addr {}", addr.hex())
            })?;
            if let Some(t0) = gb_t0 {
              stats.get_blob_ns += elapsed_ns(t0);
              stats.get_blob_calls += 1;
            }
            let n = Nat::from_le_bytes(&blob);
            let blob_addr = addr.clone();
            let key = super::env::ExprKey::Nat(blob_addr.clone());
            values.push(timed_intern_or_build(
              intern,
              &key,
              || KExpr::nat_mdata(n, blob_addr, mdata),
              stats,
            ));
          },
        }
        if let Some(t0) = process_t0 {
          stats.process_arm_ns += elapsed_ns(t0);
        }
      },

      // Continuation frames
      ExprFrame::AppArg { arg, arg_arena } => {
        let cont_t0 = if stats.enabled { Some(Instant::now()) } else { None };
        stack.push(ExprFrame::Process { expr: arg, arena_idx: arg_arena });
        if let Some(t0) = cont_t0 {
          stats.continuation_arms_ns += elapsed_ns(t0);
        }
      },
      ExprFrame::AppDone { mdata } => {
        let cont_t0 = if stats.enabled { Some(Instant::now()) } else { None };
        let a = values.pop().unwrap();
        let f = values.pop().unwrap();
        let key = super::env::ExprKey::App(*f.addr(), *a.addr());
        values.push(timed_intern_or_build(
          intern,
          &key,
          || KExpr::app_mdata(f, a, mdata),
          stats,
        ));
        if let Some(t0) = cont_t0 {
          stats.continuation_arms_ns += elapsed_ns(t0);
        }
      },
      ExprFrame::LamBody { body, body_arena } => {
        let cont_t0 = if stats.enabled { Some(Instant::now()) } else { None };
        // The binder name was already pushed by BinderPush before this frame
        stack.push(ExprFrame::Process { expr: body, arena_idx: body_arena });
        if let Some(t0) = cont_t0 {
          stats.continuation_arms_ns += elapsed_ns(t0);
        }
      },
      ExprFrame::LamDone { name, bi, contract, mdata } => {
        let cont_t0 = if stats.enabled { Some(Instant::now()) } else { None };
        let body = values.pop().unwrap();
        let ty = values.pop().unwrap();
        let key = super::env::ExprKey::Lam(contract, *ty.addr(), *body.addr());
        values.push(timed_intern_or_build(
          intern,
          &key,
          || KExpr::lam_contract_mdata(name, bi, contract, ty, body, mdata),
          stats,
        ));
        if let Some(t0) = cont_t0 {
          stats.continuation_arms_ns += elapsed_ns(t0);
        }
      },
      ExprFrame::AllBody { body, body_arena }
      | ExprFrame::LetBody { body, body_arena } => {
        let cont_t0 = if stats.enabled { Some(Instant::now()) } else { None };
        stack.push(ExprFrame::Process { expr: body, arena_idx: body_arena });
        if let Some(t0) = cont_t0 {
          stats.continuation_arms_ns += elapsed_ns(t0);
        }
      },
      ExprFrame::AllDone { name, bi, contract, result, mdata } => {
        let cont_t0 = if stats.enabled { Some(Instant::now()) } else { None };
        let body = values.pop().unwrap();
        let ty = values.pop().unwrap();
        let key =
          super::env::ExprKey::All(contract, result, *ty.addr(), *body.addr());
        values.push(timed_intern_or_build(
          intern,
          &key,
          || {
            KExpr::all_contract_mdata(
              name, bi, contract, result, ty, body, mdata,
            )
          },
          stats,
        ));
        if let Some(t0) = cont_t0 {
          stats.continuation_arms_ns += elapsed_ns(t0);
        }
      },
      ExprFrame::LetVal { val, val_arena, body, body_arena, binder_name } => {
        let cont_t0 = if stats.enabled { Some(Instant::now()) } else { None };
        stack.push(ExprFrame::LetBody { body, body_arena });
        stack.push(ExprFrame::BinderPush { name: binder_name });
        stack.push(ExprFrame::Process { expr: val, arena_idx: val_arena });
        if let Some(t0) = cont_t0 {
          stats.continuation_arms_ns += elapsed_ns(t0);
        }
      },
      ExprFrame::LetDone { name, contract, mdata } => {
        let cont_t0 = if stats.enabled { Some(Instant::now()) } else { None };
        let body = values.pop().unwrap();
        let val = values.pop().unwrap();
        let ty = values.pop().unwrap();
        let key = super::env::ExprKey::Let(
          contract,
          *ty.addr(),
          *val.addr(),
          *body.addr(),
        );
        values.push(timed_intern_or_build(
          intern,
          &key,
          || KExpr::let_contract_mdata(name, contract, ty, val, body, mdata),
          stats,
        ));
        if let Some(t0) = cont_t0 {
          stats.continuation_arms_ns += elapsed_ns(t0);
        }
      },
      ExprFrame::BinderPush { name } => {
        let cont_t0 = if stats.enabled { Some(Instant::now()) } else { None };
        binder_names.push(name);
        if let Some(t0) = cont_t0 {
          stats.continuation_arms_ns += elapsed_ns(t0);
        }
      },
      ExprFrame::BinderPop => {
        let cont_t0 = if stats.enabled { Some(Instant::now()) } else { None };
        binder_names.pop();
        if let Some(t0) = cont_t0 {
          stats.continuation_arms_ns += elapsed_ns(t0);
        }
      },
      ExprFrame::PrjDone { type_id, field_idx, mdata } => {
        let cont_t0 = if stats.enabled { Some(Instant::now()) } else { None };
        let s = values.pop().unwrap();
        let key =
          super::env::ExprKey::Prj(type_id.addr.clone(), field_idx, *s.addr());
        values.push(timed_intern_or_build(
          intern,
          &key,
          || KExpr::prj_mdata(type_id, field_idx, s, mdata),
          stats,
        ));
        if let Some(t0) = cont_t0 {
          stats.continuation_arms_ns += elapsed_ns(t0);
        }
      },
      ExprFrame::Cache { key } => {
        let cont_t0 = if stats.enabled { Some(Instant::now()) } else { None };
        let result = values.last().unwrap().clone();
        let ins_t0 = if stats.enabled { Some(Instant::now()) } else { None };
        cache.insert(key, result);
        if let Some(t0) = ins_t0 {
          stats.expr_cache_insert_ns += elapsed_ns(t0);
          stats.expr_cache_inserts += 1;
          stats.expr_cache_peak = stats.expr_cache_peak.max(cache.len() as u64);
        }
        if let Some(t0) = cont_t0 {
          stats.continuation_arms_ns += elapsed_ns(t0);
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
  def: &ixon::constant::Definition,
  self_id: KId<M>,
  meta: &ConstantMeta,
  ixon_env: crate::input::Input<'_>,
  names: &FxHashMap<Address, Name>,
  name_to_addr: &FxHashMap<Name, Address>,
  sharing: &[Arc<IxonExpr>],
  refs: &[Address],
  univs: &[Arc<IxonUniv>],
  block: KId<M>,
  intern: &mut InternTable<M>,
  stats: &mut ConvertStats,
  // The semantic targets of `Expr::Rec`: the serialized owner's members
  // (see `owner_mut_ctx`), or `[self_id]` for a standalone. Metadata
  // never selects them.
  mut_ctx: Vec<KId<M>>,
  local_dependencies: Option<&mut LocalDefnDependencies>,
) -> Result<Vec<(KId<M>, KConst<M>)>, String> {
  let mut cache: ExprCache<M> = FxHashMap::default();
  let mut univ_cache: UnivCache<M> = FxHashMap::default();
  // Hints live only in `Env::anon_hints`, keyed by the constant's own
  // address, in both anon and meta modes. Without an entry the kernel
  // falls back to `Regular(0)` — always correct, just more def-eq work.
  let hints =
    ixon_env.hint(&self_id.addr).unwrap_or(ReducibilityHints::Regular(0));
  let safety = def.safety;
  let local_refs = RefCell::new(FxHashSet::default());
  let (level_params, arena, type_root, value_root, all_addrs) = match &meta.info
  {
    ConstantMetaInfo::Def {
      lvls, arena, type_root, value_root, all, ..
    } => (
      resolve_level_params(lvls, names),
      arena,
      *type_root,
      *value_root,
      all.clone(),
    ),
    _ => (vec![], &DEFAULT_ARENA, 0, 0, vec![]),
  };

  let ctx = Ctx {
    sharing,
    refs,
    univs,
    mut_ctx,
    arena,
    names,
    lvls: level_params.clone(),
    univ_patches: univ_patch_map(meta),
    meta_univs: &meta.meta_univs,
    local_refs: local_dependencies.as_ref().map(|_| &local_refs),
    synth_counter: Cell::new(0),
  };

  let typ = ingress_expr(
    &def.typ,
    type_root,
    &ctx,
    intern,
    ixon_env,
    &mut cache,
    &mut univ_cache,
    stats,
  )?;
  let value = ingress_expr(
    &def.value,
    value_root,
    &ctx,
    intern,
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

  if let Some(dependencies) = local_dependencies {
    dependencies.insert(&self_id.addr, def.safety, local_refs.into_inner());
  }

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
  rec: &ixon::constant::Recursor,
  self_id: KId<M>,
  meta: &ConstantMeta,
  ixon_env: crate::input::Input<'_>,
  names: &FxHashMap<Address, Name>,
  name_to_addr: &FxHashMap<Name, Address>,
  sharing: &[Arc<IxonExpr>],
  refs: &[Address],
  univs: &[Arc<IxonUniv>],
  block: KId<M>,
  intern: &mut InternTable<M>,
  stats: &mut ConvertStats,
  // The semantic targets of `Expr::Rec`, as for `ingress_defn`.
  mut_ctx: Vec<KId<M>>,
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
    mut_ctx,
    arena,
    names,
    lvls: level_params.clone(),
    univ_patches: univ_patch_map(meta),
    meta_univs: &meta.meta_univs,
    local_refs: None,
    synth_counter: Cell::new(0),
  };

  let typ = ingress_expr(
    &rec.typ,
    type_root,
    &ctx,
    intern,
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
        intern,
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
  ixon_env: crate::input::Input<'_>,
  names: &FxHashMap<Address, Name>,
  name_to_addr: &FxHashMap<Name, Address>,
  intern: &mut InternTable<M>,
  stats: &mut ConvertStats,
) -> Result<Vec<(KId<M>, KConst<M>)>, String> {
  let self_id: KId<M> =
    KId::new(addr.clone(), M::meta_field(const_name.clone()));

  match &constant.info {
    IxonCI::Defn(def) => {
      let mut local_dependencies = LocalDefnDependencies::default();
      let entries = ingress_defn(
        def,
        self_id.clone(),
        meta,
        ixon_env,
        names,
        name_to_addr,
        &constant.sharing,
        &constant.refs,
        &constant.univs,
        self_id.clone(),
        intern,
        stats,
        // A standalone is a singleton unit: `Rec(0)` is itself.
        vec![self_id],
        Some(&mut local_dependencies),
      )?;
      local_dependencies.validate()?;
      Ok(entries)
    },

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
        univ_patches: univ_patch_map(meta),
        meta_univs: &meta.meta_univs,
        local_refs: None,
        synth_counter: Cell::new(0),
      };
      let typ = ingress_expr(
        &ax.typ,
        type_root,
        &ctx,
        intern,
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
        univ_patches: univ_patch_map(meta),
        meta_univs: &meta.meta_univs,
        local_refs: None,
        synth_counter: Cell::new(0),
      };
      let typ = ingress_expr(
        &q.typ,
        type_root,
        &ctx,
        intern,
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
      self_id.clone(),
      intern,
      stats,
      vec![self_id],
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
  ind: &ixon::constant::Inductive,
  self_id: &KId<M>,
  meta: &ConstantMeta,
  ixon_env: crate::input::Input<'_>,
  names: &FxHashMap<Address, Name>,
  name_to_addr: &FxHashMap<Name, Address>,
  block_constant: &Constant,
  block_id: KId<M>,
  member_idx: u64,
  // The owner's members, the semantic targets of `Expr::Rec`.
  mut_ctx: Vec<KId<M>>,
  intern: &mut InternTable<M>,
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
  let ctx = Ctx {
    sharing: &block_constant.sharing,
    refs: &block_constant.refs,
    univs: &block_constant.univs,
    mut_ctx,
    arena,
    names,
    lvls: level_params.clone(),
    univ_patches: univ_patch_map(meta),
    meta_univs: &meta.meta_univs,
    local_refs: None,
    synth_counter: Cell::new(0),
  };

  let typ = ingress_expr(
    &ind.typ,
    type_root,
    &ctx,
    intern,
    ixon_env,
    &mut cache,
    &mut univ_cache,
    stats,
  )?;
  let lean_all = resolve_all(&all_addrs, names, name_to_addr)?;
  // Metadata selects presentation names; the owner and constructor position
  // determine semantic identity. Validate that each named address agrees
  // before any payload can be installed under that address.
  let ctor_ids: Vec<KId<M>> = resolve_all(&ctor_addrs, names, name_to_addr)?;
  if ctor_ids.len() != ind.ctors.len() {
    return Err("constructor metadata count differs from its owner".into());
  }
  for (index, id) in ctor_ids.iter().enumerate() {
    let index = u64::try_from(index).map_err(|error| error.to_string())?;
    if id.addr != anon_ctor_proj_addr(&block_id.addr, member_idx, index) {
      return Err(format!(
        "constructor metadata address differs from owner/index ({member_idx}, {index})"
      ));
    }
  }

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
      is_unsafe: ind.is_unsafe,
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
    let ctor_named = ixon_env.named(&ctor_name).ok_or_else(|| {
      format!(
        "missing Named entry for ctor '{ctor_name}' (cidx={cidx}) — \
         per-ctor metadata (arena, type_root, lvls) must be registered \
         for every constructor of this inductive block"
      )
    })?;
    if ctor_named.addr != ctor_id.addr {
      return Err(format!("ctor '{ctor_name}' metadata address changed"));
    }

    let ctor_named_meta = ctor_named.meta();
    let (ctor_lvl_params, ctor_arena, ctor_type_root) =
      match &ctor_named_meta.info {
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
      // Constructor patches are scoped to the ctor's own meta — its
      // virtual indices extend the BLOCK primary table with the ctor's
      // own `meta_univs` (canonicity §10.6).
      univ_patches: univ_patch_map(&ctor_named_meta),
      meta_univs: &ctor_named_meta.meta_univs,
      local_refs: None,
      synth_counter: Cell::new(0),
    };
    let mut ctor_univ_cache: UnivCache<M> = FxHashMap::default();

    let ctor_typ = ingress_expr(
      &ctor.typ,
      ctor_type_root,
      &ctor_ctx,
      intern,
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

/// Serialized mutual units follow the certified reader's shape policy:
/// definitions form their own block; inductives and recursors may share a
/// family block. Direct Lean source grouping has a separate contract.
pub(crate) fn validate_serialized_muts(
  members: &[IxonMutConst],
) -> Result<(), String> {
  if members.is_empty() {
    return Err("empty serialized mutual block".into());
  }
  let definitions =
    members.iter().filter(|m| matches!(m, IxonMutConst::Defn(_))).count();
  if definitions != 0 && definitions != members.len() {
    return Err("unsupported serialized mutual block: definitions mixed with an inductive/recursor family".into());
  }
  Ok(())
}

#[allow(clippy::too_many_arguments)]
fn ingress_muts_block<M: KernelMode>(
  entry_name: &Name,
  entry_addr: &Address,
  all: &[Vec<Address>],
  ixon_env: crate::input::Input<'_>,
  names: &FxHashMap<Address, Name>,
  name_to_addr: &FxHashMap<Name, Address>,
  intern: &mut InternTable<M>,
  stats: &mut ConvertStats,
) -> Result<Vec<(KId<M>, KConst<M>)>, String> {
  let block_id: KId<M> =
    KId::new(entry_addr.clone(), M::meta_field(entry_name.clone()));

  let block_constant = ixon_env.constant(entry_addr)?.ok_or_else(|| {
    format!("missing Muts block constant {}", entry_addr.hex())
  })?;
  let members = match &block_constant.info {
    IxonCI::Muts(m) => m,
    _ => return Err(format!("constant at {} is not Muts", entry_addr.hex())),
  };
  validate_serialized_muts(members)?;

  // The serialized owner defines its members: member `i`'s address is its
  // projection from this owner, and `Expr::Rec(i)` denotes it. Metadata only
  // names them: `all[i][0]` is the name-hash address of member `i`'s
  // canonical Lean name, whose Named entry carries the member's own metadata
  // (arena, type root, ...) and must agree with the owner-derived address.
  // Error loudly if the Named entry is missing — the Muts-registration pass
  // in `compile_mutual` is supposed to emit one per member.
  let mut member_ids: Vec<KId<M>> = Vec::with_capacity(members.len());
  let mut member_metas: Vec<Arc<ConstantMeta>> =
    Vec::with_capacity(members.len());
  for (i, member) in members.iter().enumerate() {
    let primary_name_addr = all
      .get(i)
      .and_then(|cls| cls.first())
      .ok_or_else(|| format!("Muts block member {i} has no name in all"))?;
    let member_name = resolve_name(primary_name_addr, names);

    let member_named = ixon_env.named(&member_name).ok_or_else(|| {
      format!("Muts member '{member_name}' not found in named entries")
    })?;
    let index = u64::try_from(i).map_err(|error| error.to_string())?;
    let (kind, member_addr) = match member {
      IxonMutConst::Defn(_) => ("DPrj", anon_defn_proj_addr(entry_addr, index)),
      IxonMutConst::Indc(_) => ("IPrj", anon_indc_proj_addr(entry_addr, index)),
      IxonMutConst::Recr(_) => ("RPrj", anon_recr_proj_addr(entry_addr, index)),
    };
    if member_named.addr != member_addr {
      return Err(format!(
        "Muts member '{member_name}' metadata address differs from owner/index {index}"
      ));
    }
    // A carried projection record must be this member's, as in anonymous
    // ingress; installing the owner's members must not shadow a corrupted
    // one that a later reference would otherwise reach.
    verify_proj_addr_in_env(
      kind,
      &member_addr,
      entry_addr,
      index,
      None,
      ixon_env,
    )?;
    if let IxonMutConst::Indc(ind) = member {
      for (cidx, ctor_addr) in
        anon_ctor_addrs(entry_addr, index, ind).iter().enumerate()
      {
        verify_proj_addr_in_env(
          "CPrj",
          ctor_addr,
          entry_addr,
          index,
          Some(cidx as u64),
          ixon_env,
        )?;
      }
    }
    member_metas.push(member_named.meta());
    member_ids.push(KId::new(member_addr, M::meta_field(member_name)));
  }
  let mut_ctx = member_ids.clone();

  let mut results: Vec<(KId<M>, KConst<M>)> = Vec::new();
  let mut local_dependencies = LocalDefnDependencies::default();

  for (i, member) in members.iter().enumerate() {
    let self_id = member_ids[i].clone();
    let member_meta = &member_metas[i];

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
          mut_ctx.clone(),
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
          mut_ctx.clone(),
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
          mut_ctx.clone(),
          Some(&mut local_dependencies),
        )?);
      },
    }
  }
  local_dependencies.validate()?;

  // No member-order check: an inductive block is stored in its source's
  // order, which shapes its recursors (as constructor order does), so any
  // member order is admissible. The recursor block is checked against the
  // stored order position by position.

  Ok(results)
}

// ============================================================================
// Lightweight LeanExpr → KExpr ingress (compile-side)
// ============================================================================

use ix_common::env::{
  Expr as LeanExpr, ExprData as LeanExprData, Level, LevelData,
};

/// Convert a Lean Level to KUniv<Meta>, mapping named params to positional indices.
///
/// An unknown universe parameter or a level metavariable is an error naming
/// it, never a panic (the texts are those of the panics it replaces).
pub fn lean_level_to_kuniv(
  lvl: &Level,
  param_names: &[Name],
) -> Result<KUniv<Meta>, String> {
  Ok(match lvl.as_data() {
    LevelData::Succ(l, _) => KUniv::succ(lean_level_to_kuniv(l, param_names)?),
    LevelData::Max(a, b, _) => KUniv::max(
      lean_level_to_kuniv(a, param_names)?,
      lean_level_to_kuniv(b, param_names)?,
    ),
    LevelData::Imax(a, b, _) => KUniv::imax(
      lean_level_to_kuniv(a, param_names)?,
      lean_level_to_kuniv(b, param_names)?,
    ),
    LevelData::Param(name, _) => {
      let idx = param_names.iter().position(|n| n == name).ok_or_else(|| {
        format!(
          "unknown level param `{}` not found in param_names {:?}",
          name.pretty(),
          param_names.iter().map(|n| n.pretty()).collect::<Vec<_>>()
        )
      })? as u64;
      KUniv::param(idx, name.clone())
    },
    LevelData::Zero(_) => KUniv::zero(),
    LevelData::Mvar(name, _) => {
      return Err(format!(
        "unexpected level metavariable `{}` in elaborated kernel term",
        name.pretty()
      ));
    },
  })
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
pub fn param_names_hash(param_names: &[Name]) -> CtxAddr {
  let mut hasher = blake3::Hasher::new();
  hasher.update(&(param_names.len() as u64).to_le_bytes());
  for n in param_names {
    hasher.update(n.get_hash().as_bytes());
  }
  hasher.finalize()
}

pub fn lean_expr_to_zexpr(
  expr: &LeanExpr,
  param_names: &[Name],
  intern: &mut InternTable<Meta>,
  name_to_ixon_addr: Option<&DashMap<Name, Address>>,
  aux_n2a: Option<&DashMap<Name, Address>>,
) -> Result<KExpr<Meta>, String> {
  // Uncached path — only for callers without KEnv access. Top-level
  // expressions start with an empty binder stack.
  let mut binder_names: Vec<Name> = Vec::new();
  lean_expr_to_zexpr_cached(
    expr,
    param_names,
    &mut binder_names,
    intern,
    name_to_ixon_addr,
    aux_n2a,
    None,
    None,
  )
}

/// Cached variant that takes a full `KEnv` reference instead of just `InternTable`.
/// Uses the KEnv's `ingress_cache` to avoid re-converting shared LeanExpr subtrees.
pub fn lean_expr_to_zexpr_with_kenv(
  expr: &LeanExpr,
  param_names: &[Name],
  kenv: &mut KEnv<Meta>,
  n2a: Option<&DashMap<Name, Address>>,
  aux_n2a: Option<&DashMap<Name, Address>>,
) -> Result<KExpr<Meta>, String> {
  let pn_h = param_names_hash(param_names);
  let mut binder_names: Vec<Name> = Vec::new();
  lean_expr_to_zexpr_cached(
    expr,
    param_names,
    &mut binder_names,
    &mut kenv.intern,
    n2a,
    aux_n2a,
    Some(&mut kenv.ingress_cache),
    Some(&pn_h),
  )
}

enum LeanExprFrame<'a> {
  Visit(&'a LeanExpr),
  Finish {
    node: &'a LeanExprData,
    mdata: Vec<MData>,
    source_contract: Option<source::Contract>,
    key: Option<(CtxAddr, CtxAddr)>,
    projection_id: Option<KId<Meta>>,
  },
  PushBinder(&'a Name),
  PopBinder,
}

/// Cached variant: uses `ingress_cache` (if provided) to avoid re-converting
/// shared LeanExpr subtrees. The cache is keyed by `(expr_hash, pn_hash)` to
/// account for different level param bindings producing different KExprs.
///
/// `binder_names` is the stack of enclosing binder names (outermost first),
/// pushed/popped around each Lam/All/Let body. It's used to
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
///
/// # Errors
///
/// The whole `lean_expr_to_zexpr*` family returns an error, never a panic or
/// a substituted value, on an unknown universe parameter, a level
/// metavariable, a free variable, an expression metavariable, or a bound
/// variable or projection index that does not fit a `u64`. Only successful
/// conversions enter the cache. The caller's binder stack is restored on
/// both success and error; completed child cache entries survive an error.
#[allow(clippy::too_many_arguments)]
pub fn lean_expr_to_zexpr_cached(
  expr: &LeanExpr,
  param_names: &[Name],
  binder_names: &mut Vec<Name>,
  intern: &mut InternTable<Meta>,
  n2a: Option<&DashMap<Name, Address>>,
  aux_n2a: Option<&DashMap<Name, Address>>,
  mut cache: Option<&mut FxHashMap<(CtxAddr, CtxAddr), KExpr<Meta>>>,
  pn_hash: Option<&CtxAddr>,
) -> Result<KExpr<Meta>, String> {
  let entry_depth = binder_names.len();
  let result = (|| {
    let mut stack = vec![LeanExprFrame::Visit(expr)];
    let mut values: Vec<KExpr<Meta>> = Vec::new();
    while let Some(frame) = stack.pop() {
      match frame {
        LeanExprFrame::Visit(expr) => {
          let key = pn_hash.map(|h| (*expr.get_hash(), *h));
          if let (Some(cache), Some(key)) = (cache.as_ref(), key)
            && let Some(hit) = cache.get(&key)
          {
            values.push(hit.clone());
            continue;
          }
          // Preserve the original cache key and outer-to-inner Mdata order.
          // Peeled intermediate wrappers are not separate cache entries.
          let mut mdata = Vec::new();
          let mut cur = expr;
          while let LeanExprData::Mdata(kv, inner, _) = cur.as_data() {
            mdata.push(kv.clone());
            cur = inner;
          }
          let node = cur.as_data();
          let source_contract =
            source::source_layers(cur, &mdata).map_err(|e| e.to_string())?;
          // Projection address resolution precedes its operand conversion;
          // field-index validation remains after that conversion.
          let projection_id = match node {
            LeanExprData::Proj(name, ..) => Some(KId::new(
              resolve_lean_name_addr(name, n2a, aux_n2a),
              name.clone(),
            )),
            _ => None,
          };
          stack.push(LeanExprFrame::Finish {
            node,
            mdata,
            source_contract,
            key,
            projection_id,
          });
          match node {
            LeanExprData::App(f, a, _) => {
              stack.push(LeanExprFrame::Visit(a));
              stack.push(LeanExprFrame::Visit(f));
            },
            LeanExprData::Lam(name, dom, body, _, _)
            | LeanExprData::ForallE(name, dom, body, _, _) => {
              stack.push(LeanExprFrame::PopBinder);
              stack.push(LeanExprFrame::Visit(body));
              stack.push(LeanExprFrame::PushBinder(name));
              stack.push(LeanExprFrame::Visit(dom));
            },
            LeanExprData::LetE(name, ty, val, body, _, _) => {
              stack.push(LeanExprFrame::PopBinder);
              stack.push(LeanExprFrame::Visit(body));
              stack.push(LeanExprFrame::PushBinder(name));
              stack.push(LeanExprFrame::Visit(val));
              stack.push(LeanExprFrame::Visit(ty));
            },
            LeanExprData::Proj(_, _, value, _) => {
              stack.push(LeanExprFrame::Visit(value));
            },
            _ => {},
          }
        },
        LeanExprFrame::PushBinder(name) => binder_names.push(name.clone()),
        LeanExprFrame::PopBinder => {
          binder_names.pop();
        },
        LeanExprFrame::Finish {
          node,
          mdata,
          source_contract,
          key,
          projection_id,
        } => {
          let e = match node {
            LeanExprData::Bvar(idx, _) => {
              let idx_u64 = idx.to_u64().ok_or_else(|| {
                format!("bound variable index {idx} exceeds u64")
              })?;
              let idx_usize = usize::try_from(idx_u64).unwrap_or(usize::MAX);
              let name = binder_names
                .len()
                .checked_sub(1)
                .and_then(|top| top.checked_sub(idx_usize))
                .and_then(|i| binder_names.get(i))
                .cloned()
                .unwrap_or_else(Name::anon);
              KExpr::var_mdata(idx_u64, name, mdata)
            },
            LeanExprData::Sort(lvl, _) => {
              KExpr::sort_mdata(lean_level_to_kuniv(lvl, param_names)?, mdata)
            },
            LeanExprData::Const(name, us, _) => {
              let id = KId::new(
                resolve_lean_name_addr(name, n2a, aux_n2a),
                name.clone(),
              );
              let us = us
                .iter()
                .map(|u| lean_level_to_kuniv(u, param_names))
                .collect::<Result<Box<[_]>, _>>()?;
              KExpr::cnst_mdata(id, us, mdata)
            },
            LeanExprData::App(..) => {
              let a = values.pop().unwrap();
              let f = values.pop().unwrap();
              KExpr::app_mdata(f, a, mdata)
            },
            LeanExprData::Lam(name, _, _, bi, _) => {
              let body = values.pop().unwrap();
              let dom = values.pop().unwrap();
              KExpr::lam_contract_mdata(
                name.clone(),
                bi.clone(),
                source_contract
                  .map_or_else(BinderContract::default, |c| c.binder),
                dom,
                body,
                mdata,
              )
            },
            LeanExprData::ForallE(name, _, _, bi, _) => {
              let body = values.pop().unwrap();
              let dom = values.pop().unwrap();
              KExpr::all_contract_mdata(
                name.clone(),
                bi.clone(),
                source_contract
                  .map_or_else(BinderContract::default, |c| c.binder),
                source_contract
                  .map_or_else(ValueContract::shared, |c| c.result),
                dom,
                body,
                mdata,
              )
            },
            LeanExprData::LetE(name, _, _, _, nd, _) => {
              let body = values.pop().unwrap();
              let val = values.pop().unwrap();
              let ty = values.pop().unwrap();
              let contract = source_contract.map_or_else(
                || LetContract::plain(*nd),
                |c| LetContract {
                  non_dep: *nd,
                  kind: c.let_kind,
                  binder: c.binder,
                },
              );
              KExpr::let_contract_mdata(
                name.clone(),
                contract,
                ty,
                val,
                body,
                mdata,
              )
            },
            LeanExprData::Proj(name, idx, _, _) => {
              let value = values.pop().unwrap();
              let idx_u64 = idx.to_u64().ok_or_else(|| {
                format!(
                  "projection index {idx} of {} exceeds u64",
                  name.pretty()
                )
              })?;
              KExpr::prj_mdata(projection_id.unwrap(), idx_u64, value, mdata)
            },
            LeanExprData::Lit(lit, _) => match lit {
              ix_common::env::Literal::NatVal(n) => KExpr::nat_mdata(
                n.clone(),
                Address::hash(&n.to_le_bytes()),
                mdata,
              ),
              ix_common::env::Literal::StrVal(s) => {
                KExpr::str_mdata(s.clone(), Address::hash(s.as_bytes()), mdata)
              },
            },
            LeanExprData::Fvar(name, _) => {
              return Err(format!(
                "unexpected FVar({}) in elaborated kernel term during ingress",
                name.pretty()
              ));
            },
            LeanExprData::Mvar(name, _) => {
              return Err(format!(
                "unexpected MVar({}) in elaborated kernel term during ingress",
                name.pretty()
              ));
            },
            LeanExprData::Mdata(..) => {
              unreachable!("Mdata was peeled on entry")
            },
          };
          // Construct and intern in the old postorder, including on intern
          // hits, so allocation/first-occurrence metadata behavior is stable.
          let e = intern.intern_expr(e);
          if let (Some(cache), Some(key)) = (cache.as_deref_mut(), key) {
            cache.insert(key, e.clone());
          }
          values.push(e);
        },
      }
    }
    Ok(values.pop().unwrap())
  })();
  // A failed body must not leak a pushed binder into its caller. Successful
  // child cache/interner writes are retained, exactly as on the old path.
  binder_names.truncate(entry_depth);
  result
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
  zenv: &mut KEnv<Meta>,
  intern: &mut InternTable<Meta>,
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
    let named_meta = named.meta();
    if matches!(&named_meta.info, ConstantMetaInfo::Muts { .. }) {
      if let ConstantMetaInfo::Muts { all, .. } = &named_meta.info
        && let Ok(entries) = ingress_muts_block(
          name,
          &named.addr,
          all,
          ixon_env.into(),
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
      &named_meta,
      ixon_env.into(),
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
//   * `lean_expr_to_zexpr_with_kenv` for expression ingress.
//   * `kenv.intern` is populated in-place (no separate `InternTable` to
//     swap in the way `ixon_ingress` requires).

/// Extract the `all` (mutual siblings) list from a Lean `ConstantInfo`.
/// Returns `None` for variants without a mutual block (Axio, Quot, Ctor, Rec).
/// Ctors/Recs have their own `induct`/`all` but the block identity comes
/// from the inductive, which is what's on the map anyway.
#[cfg(not(target_arch = "riscv64"))]
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
#[cfg(not(target_arch = "riscv64"))]
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
#[cfg(not(target_arch = "riscv64"))]
pub fn build_leon_addr_map(lean_env: &LeanEnv) -> DashMap<Name, Address> {
  // Build in parallel. Each shard's write lock is contended only when
  // distinct names happen to hash into the same shard — with 64 default
  // shards and ~199k names, contention is low. Pre-sizing `with_capacity`
  // keeps the shards from growing during construction.
  //
  // The map type stays `DashMap` (rather than `FxHashMap`) because
  // downstream signatures (`lean_expr_to_zexpr_cached`,
  // `resolve_lean_name_addr`) take their `n2a` and `aux_n2a` name maps as
  // `DashMap`s.
  let entries: Vec<_> = lean_env.iter().collect();
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
#[cfg(not(target_arch = "riscv64"))]
fn leon_addr_of(name: &Name, n2a: &DashMap<Name, Address>) -> Address {
  n2a.get(name).map_or_else(|| lean_name_to_addr(name), |e| e.value().clone())
}

/// Build the `block` KId for a constant's mutual block. For singletons
/// (no `all` or `all` length 1), the block id is the constant's own KId.
/// For mutuals, it's the representative (first name in `all`).
#[cfg(not(target_arch = "riscv64"))]
fn lean_block_id(
  self_name: &Name,
  all: Option<&Vec<Name>>,
  n2a: &DashMap<Name, Address>,
) -> KId<Meta> {
  let rep = all.and_then(|a| a.first()).unwrap_or(self_name);
  KId::new(leon_addr_of(rep, n2a), rep.clone())
}

/// Build the `lean_all` KId list in Meta mode.
#[cfg(not(target_arch = "riscv64"))]
fn lean_all_ids(all: &[Name], n2a: &DashMap<Name, Address>) -> Vec<KId<Meta>> {
  all.iter().map(|n| KId::new(leon_addr_of(n, n2a), n.clone())).collect()
}

/// Convert one Lean `ConstantInfo` to a `KConst<Meta>`. Expressions go through
/// `lean_expr_to_zexpr_with_kenv` with the `n2a` map so inner `Const`
/// references resolve to LEON addresses (same scheme used for the KId
/// addresses in this constant's own fields).
///
/// Every error names the constant (`"{self_name}: ..."`): an expression the
/// expression ingress refuses, or a `Nat` count or index field that does
/// not fit a `u64` (such a field used to become 0).
#[cfg(not(target_arch = "riscv64"))]
fn lean_const_to_kconst(
  self_name: &Name,
  ci: &LeanCI,
  kenv: &mut KEnv<Meta>,
  n2a: &DashMap<Name, Address>,
) -> Result<KConst<Meta>, String> {
  // Helper: shorthand for expression ingress. `n2a` carries the env-wide
  // LEON addressing so `Const` refs inside expressions resolve to the same
  // addresses we're using for KId keys — any KId we construct here and any
  // Const-ref we ingress agree on where they point.
  let mut expr_to_k =
    |e: &ix_common::env::Expr, pn: &[Name]| -> Result<KExpr<Meta>, String> {
      lean_expr_to_zexpr_with_kenv(e, pn, kenv, Some(n2a), None)
        .map_err(|e| format!("{}: {e}", self_name.pretty()))
    };
  // Helper: a `Nat` count or index field as a `u64`, refused when it does
  // not fit.
  let nat_field = |n: &Nat, field: &str| -> Result<u64, String> {
    n.to_u64()
      .ok_or_else(|| format!("{}: {field} {n} exceeds u64", self_name.pretty()))
  };

  Ok(match ci {
    LeanCI::AxiomInfo(v) => {
      let pn = &v.cnst.level_params;
      KConst::Axio {
        name: self_name.clone(),
        level_params: pn.clone(),
        is_unsafe: v.is_unsafe,
        lvls: pn.len() as u64,
        ty: expr_to_k(&v.cnst.typ, pn)?,
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
        ty: expr_to_k(&v.cnst.typ, pn)?,
        val: expr_to_k(&v.value, pn)?,
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
        ty: expr_to_k(&v.cnst.typ, pn)?,
        val: expr_to_k(&v.value, pn)?,
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
        ty: expr_to_k(&v.cnst.typ, pn)?,
        val: expr_to_k(&v.value, pn)?,
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
        ty: expr_to_k(&v.cnst.typ, pn)?,
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
        params: nat_field(&v.num_params, "num_params")?,
        indices: nat_field(&v.num_indices, "num_indices")?,
        is_unsafe: v.is_unsafe,
        block: lean_block_id(self_name, all, n2a),
        member_idx: lean_member_idx(self_name, all),
        ty: expr_to_k(&v.cnst.typ, pn)?,
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
        cidx: nat_field(&v.cidx, "cidx")?,
        params: nat_field(&v.num_params, "num_params")?,
        fields: nat_field(&v.num_fields, "num_fields")?,
        ty: expr_to_k(&v.cnst.typ, pn)?,
      }
    },
    LeanCI::RecInfo(v) => {
      let pn = &v.cnst.level_params;
      let all = Some(&v.all);
      let rules = v
        .rules
        .iter()
        .map(|r| -> Result<RecRule<Meta>, String> {
          let fields = r.n_fields.to_u64().ok_or_else(|| {
            format!(
              "{}: n_fields {} of the rule for {} exceeds u64",
              self_name.pretty(),
              r.n_fields,
              r.ctor.pretty()
            )
          })?;
          Ok(RecRule {
            ctor: r.ctor.clone(),
            fields,
            rhs: expr_to_k(&r.rhs, pn)?,
          })
        })
        .collect::<Result<_, _>>()?;
      KConst::Recr {
        name: self_name.clone(),
        level_params: pn.clone(),
        k: v.k,
        is_unsafe: v.is_unsafe,
        lvls: pn.len() as u64,
        params: nat_field(&v.num_params, "num_params")?,
        indices: nat_field(&v.num_indices, "num_indices")?,
        motives: nat_field(&v.num_motives, "num_motives")?,
        minors: nat_field(&v.num_minors, "num_minors")?,
        block: lean_block_id(self_name, all, n2a),
        member_idx: lean_member_idx(self_name, all),
        ty: expr_to_k(&v.cnst.typ, pn)?,
        rules,
        lean_all: lean_all_ids(&v.all, n2a),
      }
    },
  })
}

/// Lean emits original recursors in `.all` declaration order, followed by
/// nested auxiliaries named `<all[0]>.rec_N` in numeric source-walk order.
/// This is loader layout metadata, not evidence that a recursor is valid:
/// the kernel still checks every peer's full header, type, and rules.
#[cfg(not(target_arch = "riscv64"))]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum LeanRecursorOrder {
  Original(usize),
  Nested(usize),
  Unrecognized,
}

#[cfg(not(target_arch = "riscv64"))]
fn lean_recursor_order(
  name: &Name,
  block_name: &Name,
  original_positions: &FxHashMap<Name, usize>,
) -> LeanRecursorOrder {
  use ix_common::env::NameData;

  let NameData::Str(parent, suffix, _) = name.as_data() else {
    return LeanRecursorOrder::Unrecognized;
  };
  if suffix == "rec" {
    return original_positions
      .get(parent)
      .map_or(LeanRecursorOrder::Unrecognized, |&i| {
        LeanRecursorOrder::Original(i)
      });
  }
  if parent == block_name
    && let Some(index) = suffix.strip_prefix("rec_")
    && !index.starts_with('0')
    && index.bytes().all(|b| b.is_ascii_digit())
    && let Ok(index) = index.parse::<usize>()
  {
    return LeanRecursorOrder::Nested(index);
  }
  LeanRecursorOrder::Unrecognized
}

/// Direct ingress: build a `KEnv<Meta>` from a Lean `Env` without going
/// through Ixon compilation. Used by the `kernel-lean-roundtrip`
/// diagnostic test.
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
/// # Errors
///
/// A constant whose conversion is refused (see
/// [`lean_expr_to_zexpr_cached`], and a `Nat` count or index field that does
/// not fit a `u64`) makes the whole ingress fail with an error naming that
/// constant.
///
/// **Meta-only**: the existing `lean_expr_to_zexpr_*` family is Meta-mode
/// only, so this helper is Meta-mode only by extension. Generalizing to
/// `Anon` would require generalizing `lean_expr_to_zexpr_cached` too.
#[cfg(not(target_arch = "riscv64"))]
pub fn lean_ingress(lean_env: &LeanEnv) -> Result<KEnv<Meta>, String> {
  use std::time::Instant;
  let quiet = crate::env_var("IX_VERBOSE").is_err();
  let mut kenv = KEnv::<Meta>::new_with_recursor_aux_order(
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
    log::info!(
      "[lean_ingress]   build_leon_addr_map: {:.2}s ({} names)",
      t.elapsed().as_secs_f32(),
      n2a.len()
    );
  }

  // Pass 1: ingress every constant sequentially into this worker-local env.
  let t = Instant::now();
  for (name, ci) in lean_env.iter() {
    let kid = KId::new(leon_addr_of(name, &n2a), name.clone());
    // The error already names the constant.
    let kc = lean_const_to_kconst(name, &ci, &mut kenv, &n2a)?;
    kenv.insert(kid, kc);
  }
  if !quiet {
    log::info!(
      "[lean_ingress]   pass 1 (serial ingress): {:.2}s",
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
  // **Order matters for inductives and recursors.** `discover_block_inductives`
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
  // The compiler stores each block in this same declaration order.
  // Iterating `lean_env` directly to push each constant's `self_kid` gave
  // random (FxHashMap iteration) order; we now seed each block with
  // its `all` list the first time any member is observed, then
  // append ctors and source-ordered recursors in a second pass. The
  // inductive and recursor subsequences must align positionally with the
  // flat block (original `.all` members, then source-walk nested auxes).
  //
  // `ixon_ingress` builds an analogous list from each block's stored
  // `Muts` entry, in stored member order. The two kenvs differ in how
  // recursor generation opens a nested occurrence of an external
  // inductive (`RecursorAuxOrder`): this one opens the head alone, an
  // Ixon-ingressed one the head's whole stored block.
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
  // `all` list (source order), exactly once per block. Constants
  // without `all` (axioms, quotients, ctors) seed a singleton block
  // under their own KId.
  let t = Instant::now();
  let mut seeded: FxHashSet<KId<Meta>> = FxHashSet::default();
  for (name, ci) in lean_env.iter() {
    let block_id = block_rep(name, &ci);
    if !seeded.insert(block_id.clone()) {
      continue;
    }
    let all =
      lean_constant_all(&ci).cloned().unwrap_or_else(|| vec![name.clone()]);
    let members: Vec<KId<Meta>> =
      all.iter().map(|n| KId::new(leon_addr_of(n, &n2a), n.clone())).collect();
    kenv.blocks.insert(block_id, members);
  }
  if !quiet {
    log::info!(
      "[lean_ingress]   phase A (block seed): {:.2}s",
      t.elapsed().as_secs_f32()
    );
  }

  // Phase B: append constructors and collect recursors separately. `.all`
  // lists inductives even for RecInfo; environment iteration is not the
  // recursor order required by positional peer matching in the kernel.
  let t = Instant::now();
  let mut recursors: FxHashMap<KId<Meta>, Vec<KId<Meta>>> =
    FxHashMap::default();
  for (name, ci) in lean_env.iter() {
    match &*ci {
      LeanCI::InductInfo(v) => {
        let block_id = block_rep(name, &ci);
        for ctor_name in &v.ctors {
          let ctor_kid: KId<Meta> =
            KId::new(leon_addr_of(ctor_name, &n2a), ctor_name.clone());
          kenv.blocks.entry(block_id.clone()).or_default().push(ctor_kid);
        }
      },
      LeanCI::RecInfo(_) => {
        let block_id = block_rep(name, &ci);
        let self_kid = KId::new(leon_addr_of(name, &n2a), name.clone());
        recursors.entry(block_id).or_default().push(self_kid);
      },
      // Inductives and Defns/Thms/Opaques are already in the Phase-A
      // seed via their `all` list; axioms, quotients, and ctors are
      // placed as singletons (the latter also get appended above).
      _ => {},
    }
  }
  for (block_id, mut peers) in recursors {
    let members = kenv.blocks.entry(block_id.clone()).or_default();
    let original_positions: FxHashMap<Name, usize> = members
      .iter()
      .filter(|id| matches!(kenv.consts.get(id), Some(KConst::Indc { .. })))
      .enumerate()
      .map(|(i, id)| (id.name.clone(), i))
      .collect();
    peers.sort_by_cached_key(|id| {
      lean_recursor_order(&id.name, &block_id.name, &original_positions)
    });
    // Keep unrecognized names too. Dropping malformed/extra peers here
    // could hide a recursor-count or type mismatch from kernel validation.
    members.extend(peers);
  }
  if !quiet {
    log::info!(
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
  let _ = kenv.set_prims(crate::primitive::Primitives::from_env_orig(&kenv));

  Ok(kenv)
}

// ============================================================================
// Top-level entry point
// ============================================================================

enum IngressWorkItem {
  Standalone(Name),
  Muts(Name),
}

#[derive(Clone, Debug, Default)]
pub struct IxonIngressLookups {
  names: FxHashMap<Address, Name>,
  name_to_addr: FxHashMap<Name, Address>,
  addr_to_name: FxHashMap<Address, Name>,
  names_by_addr: FxHashMap<Address, Vec<Name>>,
  muts_by_addr: FxHashMap<Address, Vec<(Name, Vec<Vec<Address>>)>>,
}

impl IxonIngressLookups {
  pub fn name_for_addr(&self, addr: &Address) -> Option<&Name> {
    self.addr_to_name.get(addr)
  }

  fn names_for_addr(&self, addr: &Address) -> Option<&[Name]> {
    self.names_by_addr.get(addr).map(Vec::as_slice)
  }
}

pub fn build_ixon_ingress_lookups(ixon_env: &IxonEnv) -> IxonIngressLookups {
  let mut lookups = IxonIngressLookups::default();
  for entry in ixon_env.names.iter() {
    lookups.names.insert(entry.key().clone(), entry.value().clone());
  }
  for entry in ixon_env.named.iter() {
    let name = entry.key().clone();
    let named = entry.value();
    lookups.name_to_addr.insert(name.clone(), named.addr.clone());
    lookups
      .names_by_addr
      .entry(named.addr.clone())
      .or_default()
      .push(name.clone());
    lookups
      .addr_to_name
      .entry(named.addr.clone())
      .or_insert_with(|| name.clone());
    if let ConstantMetaInfo::Muts { all, .. } = &named.meta().info {
      lookups
        .muts_by_addr
        .entry(named.addr.clone())
        .or_default()
        .push((name, all.clone()));
    }
  }
  lookups
}

fn projection_block(info: &IxonCI) -> Option<&Address> {
  match info {
    IxonCI::IPrj(p) => Some(&p.block),
    IxonCI::CPrj(p) => Some(&p.block),
    IxonCI::RPrj(p) => Some(&p.block),
    IxonCI::DPrj(p) => Some(&p.block),
    _ => None,
  }
}

enum IngressNeed {
  Addr(Address),
  ProjectionAliases(Address),
}

fn insert_addr_aliases<M: KernelMode>(
  kenv: &mut KEnv<M>,
  lookups: &IxonIngressLookups,
  addr: &Address,
) {
  let Some(names) = lookups.names_for_addr(addr) else {
    return;
  };
  let Some(template) = kenv
    .consts
    .iter()
    .find_map(|(id, c)| if &id.addr == addr { Some(c.clone()) } else { None })
  else {
    return;
  };
  for name in names {
    let id = KId::new(addr.clone(), M::meta_field(name.clone()));
    if !kenv.contains_key(&id) {
      kenv.insert(id, template.clone());
    }
  }
}

pub fn ingress_const_into_kenv<M: KernelMode>(
  kenv: &mut KEnv<M>,
  ixon_env: &IxonEnv,
  name: &Name,
) -> Result<KId<M>, String> {
  let lookups = build_ixon_ingress_lookups(ixon_env);
  ingress_const_into_kenv_with_lookups(kenv, ixon_env, &lookups, name)
}

pub fn ingress_const_into_kenv_with_lookups<M: KernelMode>(
  kenv: &mut KEnv<M>,
  ixon_env: &IxonEnv,
  lookups: &IxonIngressLookups,
  name: &Name,
) -> Result<KId<M>, String> {
  ingress_const_into_kenv_with_lookups_impl(
    kenv,
    ixon_env.into(),
    lookups,
    name,
    true,
  )
}

pub fn ingress_const_shallow_into_kenv_with_lookups<M: KernelMode>(
  kenv: &mut KEnv<M>,
  ixon_env: &IxonEnv,
  lookups: &IxonIngressLookups,
  name: &Name,
) -> Result<KId<M>, String> {
  ingress_const_into_kenv_with_lookups_impl(
    kenv,
    ixon_env.into(),
    lookups,
    name,
    false,
  )
}

pub fn ingress_addr_shallow_into_kenv_with_lookups<M: KernelMode>(
  kenv: &mut KEnv<M>,
  ixon_env: &IxonEnv,
  lookups: &IxonIngressLookups,
  addr: &Address,
) -> Result<bool, String> {
  ingress_addr_set_into_kenv(kenv, ixon_env.into(), lookups, addr, false)
}

pub(crate) fn ingress_addr_with_input<M: KernelMode>(
  kenv: &mut KEnv<M>,
  input: crate::input::Input<'_>,
  lookups: &IxonIngressLookups,
  addr: &Address,
) -> Result<bool, String> {
  ingress_addr_set_into_kenv(kenv, input, lookups, addr, false)
}

pub(crate) fn ingress_name_with_input<M: KernelMode>(
  kenv: &mut KEnv<M>,
  input: crate::input::Input<'_>,
  lookups: &IxonIngressLookups,
  name: &Name,
) -> Result<KId<M>, String> {
  ingress_const_into_kenv_with_lookups_impl(kenv, input, lookups, name, false)
}

fn ingress_const_into_kenv_with_lookups_impl<M: KernelMode>(
  kenv: &mut KEnv<M>,
  ixon_env: crate::input::Input<'_>,
  lookups: &IxonIngressLookups,
  name: &Name,
  follow_refs: bool,
) -> Result<KId<M>, String> {
  let requested = ixon_env
    .named(name)
    .ok_or_else(|| format!("{}: missing Named entry", name.pretty()))?;
  let requested_id =
    KId::new(requested.addr.clone(), M::meta_field(name.clone()));

  ingress_addr_set_into_kenv(
    kenv,
    ixon_env,
    lookups,
    &requested.addr,
    follow_refs,
  )?;

  if !kenv.contains_key(&requested_id) {
    return Err(format!("{}: no ingressed kernel constant", name.pretty()));
  }
  Ok(requested_id)
}

fn ingress_addr_set_into_kenv<M: KernelMode>(
  kenv: &mut KEnv<M>,
  ixon_env: crate::input::Input<'_>,
  lookups: &IxonIngressLookups,
  seed_addr: &Address,
  follow_refs: bool,
) -> Result<bool, String> {
  let mut seen: FxHashSet<Address> = FxHashSet::default();
  let mut found_seed = false;
  let mut worklist = vec![IngressNeed::Addr(seed_addr.clone())];
  let convert_stats_enabled = ingress_convert_stats_enabled();

  while let Some(need) = worklist.pop() {
    let addr = match need {
      IngressNeed::Addr(addr) => addr,
      IngressNeed::ProjectionAliases(addr) => {
        insert_addr_aliases(kenv, lookups, &addr);
        continue;
      },
    };

    if !seen.insert(addr.clone()) {
      continue;
    }

    let Some(constant) = ixon_env.constant(&addr)? else {
      // `Constant.refs` also contains blob addresses for string/nat payloads.
      continue;
    };
    if &addr == seed_addr {
      found_seed = true;
    }

    if let Some(block_addr) = projection_block(&constant.info) {
      worklist.push(IngressNeed::ProjectionAliases(addr));
      worklist.push(IngressNeed::Addr(block_addr.clone()));
      continue;
    }

    if follow_refs {
      for dep in &constant.refs {
        if ixon_env.contains(dep) {
          worklist.push(IngressNeed::Addr(dep.clone()));
        }
      }
    }

    match &constant.info {
      IxonCI::Muts(_) => {
        let Some(block_entries) = lookups.muts_by_addr.get(&addr) else {
          return Err(format!("Muts block {} has no named entry", addr.hex()));
        };
        for (entry_name, all) in block_entries {
          let block_id =
            KId::new(addr.clone(), M::meta_field(entry_name.clone()));
          if kenv.blocks.contains_key(&block_id) {
            continue;
          }
          let mut convert_stats = ConvertStats::new(convert_stats_enabled);
          let entries = ingress_muts_block(
            entry_name,
            &addr,
            all,
            ixon_env,
            &lookups.names,
            &lookups.name_to_addr,
            &mut kenv.intern,
            &mut convert_stats,
          )
          .map_err(|e| format!("{entry_name}: {e}"))?;
          insert_muts_entries(kenv, entries);
        }
      },
      _ => {
        let Some(const_names) = lookups.names_for_addr(&addr) else {
          return Err(format!("constant {} has no named entry", addr.hex()));
        };
        for const_name in const_names {
          let kid = KId::new(addr.clone(), M::meta_field(const_name.clone()));
          if kenv.contains_key(&kid) {
            continue;
          }
          let named = ixon_env
            .named(const_name)
            .ok_or_else(|| format!("{const_name}: missing Named entry"))?;
          let mut convert_stats = ConvertStats::new(convert_stats_enabled);
          let entries = ingress_standalone(
            const_name,
            &addr,
            &constant,
            &named.meta(),
            ixon_env,
            &lookups.names,
            &lookups.name_to_addr,
            &mut kenv.intern,
            &mut convert_stats,
          )
          .map_err(|e| format!("{const_name}: {e}"))?;
          insert_standalone_entries(kenv, entries);
        }
      },
    }
  }

  Ok(found_seed)
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
  fn merge(mut self, other: &Self) -> Self {
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
    self.convert_stats = self.convert_stats.merge(&other.convert_stats);
    self
  }
}

#[cfg(not(target_arch = "riscv64"))]
#[derive(Default)]
struct IxonDropTiming {
  consts_ns: u64,
  named_ns: u64,
  names_ns: u64,
  blobs_ns: u64,
  comms_ns: u64,
}

#[cfg(not(target_arch = "riscv64"))]
struct LookupDropTiming {
  names_ns: u64,
  name_to_addr_ns: u64,
}

fn duration_ns(d: Duration) -> u64 {
  u64::try_from(d.as_nanos()).unwrap_or(u64::MAX)
}

fn elapsed_ns(start: Instant) -> u64 {
  duration_ns(start.elapsed())
}

#[cfg(not(target_arch = "riscv64"))]
#[allow(clippy::cast_precision_loss)]
fn seconds(ns: u64) -> f64 {
  ns as f64 / 1_000_000_000.0
}

#[cfg(not(target_arch = "riscv64"))]
#[allow(clippy::cast_precision_loss)]
fn percent(part: u64, total: u64) -> f64 {
  if total == 0 { 0.0 } else { (part as f64 * 100.0) / total as f64 }
}

#[cfg(not(target_arch = "riscv64"))]
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
#[cfg(not(target_arch = "riscv64"))]
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
#[cfg(not(target_arch = "riscv64"))]
fn timed_drop_fxmap_par<K: Send, V: Send>(map: FxHashMap<K, V>) -> u64 {
  let start = Instant::now();
  let entries: Vec<(K, V)> = map.into_iter().collect();
  entries.into_par_iter().for_each(drop);
  elapsed_ns(start)
}

/// Opt-out for the parallel drop path: set `IX_SEQ_IXON_DROP=1` to fall back
/// to single-threaded `drop` for measurement comparisons.
#[cfg(not(target_arch = "riscv64"))]
fn seq_ixon_drop_enabled() -> bool {
  crate::env_var_os("IX_SEQ_IXON_DROP").is_some()
}

#[cfg(not(target_arch = "riscv64"))]
fn ingress_convert_stats_enabled() -> bool {
  crate::env_var_os("IX_INGRESS_CONVERT_STATS").is_some()
}
#[cfg(target_arch = "riscv64")]
fn ingress_convert_stats_enabled() -> bool {
  false
}

#[cfg(target_arch = "riscv64")]
fn drop_ingress_lookups(
  _names: FxHashMap<Address, Name>,
  _name_to_addr: FxHashMap<Name, Address>,
  _quiet: bool,
) {
  // Auto-dropped at end of scope.
}

#[cfg(not(target_arch = "riscv64"))]
fn drop_ingress_lookups(
  names: FxHashMap<Address, Name>,
  name_to_addr: FxHashMap<Name, Address>,
  quiet: bool,
) {
  let total_start = Instant::now();
  let names_len = names.len();
  let name_to_addr_len = name_to_addr.len();
  #[cfg(not(target_arch = "riscv64"))]
  let sequential = seq_ixon_drop_enabled();
  #[cfg(target_arch = "riscv64")]
  let sequential = true;

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
    #[cfg(not(target_arch = "riscv64"))]
    {
      LookupDropTiming {
        names_ns: timed_drop_fxmap_par(names),
        name_to_addr_ns: timed_drop_fxmap_par(name_to_addr),
      }
    }
    #[cfg(target_arch = "riscv64")]
    unreachable!()
  };

  let total_ns = elapsed_ns(total_start);
  if !quiet {
    #[cfg(not(target_arch = "riscv64"))]
    let threads = rayon::current_num_threads();
    #[cfg(target_arch = "riscv64")]
    let threads = 1;
    log::info!(
      "[ixon_ingress] drop lookups: {:.2}s {} threads={} \
       (names {:.2}s/{} name_to_addr {:.2}s/{})",
      seconds(total_ns),
      if sequential { "sequential" } else { "parallel" },
      threads,
      seconds(timing.names_ns),
      names_len,
      seconds(timing.name_to_addr_ns),
      name_to_addr_len
    );
  }
}

fn insert_standalone_entries<M: KernelMode>(
  zenv: &mut KEnv<M>,
  entries: Vec<(KId<M>, KConst<M>)>,
) -> IngressInsertTiming {
  #[cfg(not(target_arch = "riscv64"))]
  let mut timing = IngressInsertTiming::default();
  #[cfg(target_arch = "riscv64")]
  let timing = IngressInsertTiming::default();

  #[cfg(not(target_arch = "riscv64"))]
  let phase_start = Instant::now();
  for (id, _) in &entries {
    zenv.blocks.entry(id.clone()).or_default().push(id.clone());
  }
  #[cfg(not(target_arch = "riscv64"))]
  {
    timing.blocks_ns = elapsed_ns(phase_start);
  }

  #[cfg(not(target_arch = "riscv64"))]
  let phase_start = Instant::now();
  for (id, zc) in entries {
    zenv.insert(id, zc);
  }
  #[cfg(not(target_arch = "riscv64"))]
  {
    timing.consts_ns = elapsed_ns(phase_start);
  }

  timing
}

fn insert_muts_entries<M: KernelMode>(
  zenv: &mut KEnv<M>,
  entries: Vec<(KId<M>, KConst<M>)>,
) -> IngressInsertTiming {
  #[cfg(not(target_arch = "riscv64"))]
  let mut timing = IngressInsertTiming::default();
  #[cfg(target_arch = "riscv64")]
  let timing = IngressInsertTiming::default();

  #[cfg(not(target_arch = "riscv64"))]
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
  #[cfg(not(target_arch = "riscv64"))]
  {
    timing.blocks_ns = elapsed_ns(phase_start);
  }

  #[cfg(not(target_arch = "riscv64"))]
  let phase_start = Instant::now();
  for (id, zc) in entries {
    zenv.insert(id, zc);
  }
  #[cfg(not(target_arch = "riscv64"))]
  {
    timing.consts_ns = elapsed_ns(phase_start);
  }

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
  let quiet = crate::env_var_os("IX_VERBOSE").is_none();
  let result = ixon_ingress_inner(&ixon_env);
  drop_ixon_env(ixon_env, quiet);
  result
}

#[cfg(target_arch = "riscv64")]
fn drop_ixon_env(_ixon_env: IxonEnv, _quiet: bool) {
  // Auto-dropped at end of scope.
}

#[cfg(not(target_arch = "riscv64"))]
fn drop_ixon_env(ixon_env: IxonEnv, quiet: bool) {
  let total_start = Instant::now();
  // `anon_hints` is small (one entry per Def from the .ixe's hints
  // section); `main`/`assumptions` are a single address and a small
  // set. Dropping them inline alongside the bookkeeping below is
  // negligible compared to the DashMap dropdance.
  // `..` covers the env's private fields.
  let IxonEnv { consts, named, blobs, names, comms, .. } = ixon_env;
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
  #[cfg(not(target_arch = "riscv64"))]
  let sequential = seq_ixon_drop_enabled();
  #[cfg(target_arch = "riscv64")]
  let sequential = true;
  let timing = if sequential {
    IxonDropTiming {
      consts_ns: timed_drop_ns(consts),
      named_ns: timed_drop_ns(named),
      names_ns: timed_drop_ns(names),
      blobs_ns: timed_drop_ns(blobs),
      comms_ns: timed_drop_ns(comms),
    }
  } else {
    #[cfg(not(target_arch = "riscv64"))]
    {
      IxonDropTiming {
        consts_ns: timed_drop_dashmap_par(consts),
        named_ns: timed_drop_dashmap_par(named),
        names_ns: timed_drop_dashmap_par(names),
        blobs_ns: timed_drop_dashmap_par(blobs),
        comms_ns: timed_drop_dashmap_par(comms),
      }
    }
    #[cfg(target_arch = "riscv64")]
    unreachable!()
  };

  let total_ns = elapsed_ns(total_start);
  if !quiet {
    #[cfg(not(target_arch = "riscv64"))]
    let threads = rayon::current_num_threads();
    #[cfg(target_arch = "riscv64")]
    let threads = 1;
    log::info!(
      "[ixon_ingress] drop ixon_env: {:.2}s {} threads={} \
       (consts {:.2}s/{} named {:.2}s/{} names {:.2}s/{} blobs {:.2}s/{} comms {:.2}s/{})",
      seconds(total_ns),
      if sequential { "sequential" } else { "parallel" },
      threads,
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
  #[cfg(not(target_arch = "riscv64"))]
  let total_start = Instant::now();

  #[cfg(not(target_arch = "riscv64"))]
  let phase_start = Instant::now();
  validate_no_reserved_marker_addresses(ixon_env)?;
  #[cfg(not(target_arch = "riscv64"))]
  log::info!(
    "[ixon_ingress] validate_reserved: {:.2}s",
    phase_start.elapsed().as_secs_f32()
  );

  let mut intern = InternTable::new();

  // Build the address → Lean-name lookup and the Lean-name → projection-
  // address lookup. See `build_ingress_lookups` for the role each plays.
  #[cfg(not(target_arch = "riscv64"))]
  let phase_start = Instant::now();
  let mut names: FxHashMap<Address, Name> = FxHashMap::default();
  for entry in ixon_env.names.iter() {
    names.insert(entry.key().clone(), entry.value().clone());
  }
  let mut name_to_addr: FxHashMap<Name, Address> = FxHashMap::default();
  for entry in ixon_env.named.iter() {
    name_to_addr.insert(entry.key().clone(), entry.value().addr.clone());
  }
  #[cfg(not(target_arch = "riscv64"))]
  log::info!(
    "[ixon_ingress] build lookups: {:.2}s ({} names, {} named)",
    phase_start.elapsed().as_secs_f32(),
    names.len(),
    name_to_addr.len()
  );

  // Partition named entries into work items without cloning the `Named`
  // metadata payloads. Each worker resolves its current Named entry just
  // before conversion.
  #[cfg(not(target_arch = "riscv64"))]
  let phase_start = Instant::now();
  let mut work_items: Vec<IngressWorkItem> = Vec::new();

  for entry in ixon_env.named.iter() {
    let const_name = entry.key().clone();
    let named = entry.value();
    match &named.meta().info {
      ConstantMetaInfo::Muts { .. } => {
        work_items.push(IngressWorkItem::Muts(const_name));
      },
      ConstantMetaInfo::Indc { .. }
      | ConstantMetaInfo::Ctor { .. }
      | ConstantMetaInfo::Rec { .. } => {
        if let Some(c) = ixon_env.get_const(&named.addr) {
          match &c.info {
            IxonCI::IPrj(_)
            | IxonCI::CPrj(_)
            | IxonCI::RPrj(_)
            | IxonCI::DPrj(_) => {},
            _ => {
              work_items.push(IngressWorkItem::Standalone(const_name));
            },
          }
        }
      },
      ConstantMetaInfo::Def { .. } => {
        if let Some(c) = ixon_env.get_const(&named.addr) {
          match &c.info {
            IxonCI::DPrj(_) => {},
            _ => {
              work_items.push(IngressWorkItem::Standalone(const_name));
            },
          }
        }
      },
      _ => {
        work_items.push(IngressWorkItem::Standalone(const_name));
      },
    }
  }
  #[cfg(not(target_arch = "riscv64"))]
  {
    let muts_count = work_items
      .iter()
      .filter(|w| matches!(w, IngressWorkItem::Muts(_)))
      .count();
    log::info!(
      "[ixon_ingress] partition work: {:.2}s ({} standalone, {} muts)",
      phase_start.elapsed().as_secs_f32(),
      work_items.len() - muts_count,
      muts_count
    );
  }

  // Convert each standalone constant or Muts block sequentially into the
  // single-threaded KEnv.
  #[cfg(not(target_arch = "riscv64"))]
  let phase_start = Instant::now();
  let convert_stats_enabled = ingress_convert_stats_enabled();
  let mut zenv: KEnv<M> = KEnv::new();
  let mut stream = IngressStreamTimingSnapshot::default();
  for work_item in work_items {
    let mut timing = IngressStreamTimingSnapshot::default();
    let mut convert_stats = ConvertStats::new(convert_stats_enabled);
    match work_item {
      IngressWorkItem::Standalone(const_name) => {
        timing.standalone_items += 1;
        #[cfg(not(target_arch = "riscv64"))]
        let lookup_start = Instant::now();
        let named = ixon_env
          .lookup_name(&const_name)
          .ok_or_else(|| format!("{const_name}: missing Named entry"))?;
        #[cfg(not(target_arch = "riscv64"))]
        {
          timing.lookup_ns += elapsed_ns(lookup_start);
        }

        #[cfg(not(target_arch = "riscv64"))]
        let const_start = Instant::now();
        let constant = match ixon_env.get_const(&named.addr) {
          Some(c) => {
            #[cfg(not(target_arch = "riscv64"))]
            {
              timing.const_get_ns += elapsed_ns(const_start);
            }
            c
          },
          None => {
            #[cfg(not(target_arch = "riscv64"))]
            {
              timing.const_get_ns += elapsed_ns(const_start);
            }
            timing.missing_consts += 1;
            timing.convert_stats = convert_stats;
            stream = stream.merge(&timing);
            continue;
          },
        };
        #[cfg(not(target_arch = "riscv64"))]
        let convert_start = Instant::now();
        let entries = ingress_standalone(
          &const_name,
          &named.addr,
          &constant,
          &named.meta(),
          ixon_env.into(),
          &names,
          &name_to_addr,
          &mut intern,
          &mut convert_stats,
        )
        .map_err(|e| format!("{const_name}: {e}"))?;
        #[cfg(not(target_arch = "riscv64"))]
        {
          timing.convert_ns += elapsed_ns(convert_start);
        }
        timing.output_consts += entries.len() as u64;

        #[cfg(not(target_arch = "riscv64"))]
        let insert_start = Instant::now();
        let insert_timing = insert_standalone_entries(&mut zenv, entries);
        #[cfg(not(target_arch = "riscv64"))]
        {
          timing.insert_ns += elapsed_ns(insert_start);
        }
        timing.insert_blocks_ns += insert_timing.blocks_ns;
        timing.insert_consts_ns += insert_timing.consts_ns;
      },
      IngressWorkItem::Muts(entry_name) => {
        timing.muts_items += 1;
        #[cfg(not(target_arch = "riscv64"))]
        let lookup_start = Instant::now();
        let named = ixon_env
          .lookup_name(&entry_name)
          .ok_or_else(|| format!("{entry_name}: missing Named entry"))?;
        #[cfg(not(target_arch = "riscv64"))]
        {
          timing.lookup_ns += elapsed_ns(lookup_start);
        }

        let named_meta = named.meta();
        let all = match &named_meta.info {
          ConstantMetaInfo::Muts { all, .. } => all,
          _ => {
            timing.convert_stats = convert_stats;
            stream = stream.merge(&timing);
            continue;
          },
        };
        #[cfg(not(target_arch = "riscv64"))]
        let convert_start = Instant::now();
        let entries = ingress_muts_block(
          &entry_name,
          &named.addr,
          all,
          ixon_env.into(),
          &names,
          &name_to_addr,
          &mut intern,
          &mut convert_stats,
        )
        .map_err(|e| format!("{entry_name}: {e}"))?;
        #[cfg(not(target_arch = "riscv64"))]
        {
          timing.convert_ns += elapsed_ns(convert_start);
        }
        timing.output_consts += entries.len() as u64;

        #[cfg(not(target_arch = "riscv64"))]
        let insert_start = Instant::now();
        let insert_timing = insert_muts_entries(&mut zenv, entries);
        #[cfg(not(target_arch = "riscv64"))]
        {
          timing.insert_ns += elapsed_ns(insert_start);
        }
        timing.insert_blocks_ns += insert_timing.blocks_ns;
        timing.insert_consts_ns += insert_timing.consts_ns;
      },
    }
    timing.convert_stats = convert_stats;
    stream = stream.merge(&timing);
  }
  #[cfg(not(target_arch = "riscv64"))]
  log::info!(
    "[ixon_ingress] stream ingress+insert: {:.2}s",
    phase_start.elapsed().as_secs_f32()
  );
  #[cfg(not(target_arch = "riscv64"))]
  log::info!(
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
  #[cfg(not(target_arch = "riscv64"))]
  let cs = &stream.convert_stats;
  #[cfg(not(target_arch = "riscv64"))]
  if cs.enabled {
    let cache_lookups = cs.expr_cache_hits + cs.expr_cache_misses;
    log::info!(
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
    log::info!(
      "[ixon_ingress]   convert nodes: sort {} var {} ref {} rec {} app {} lam {} all {} let {} prj {} str {} nat {}",
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
      cs.nat_nodes
    );
    log::info!(
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
    log::info!(
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
  #[cfg(not(target_arch = "riscv64"))]
  log::info!(
    "[ixon_ingress] complete: {:.2}s ({} consts, {} blocks)",
    total_start.elapsed().as_secs_f32(),
    zenv.len(),
    zenv.blocks.len()
  );

  drop_ingress_lookups(names, name_to_addr, false);

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
    let constant = entry.value().get().map_err(|e| {
      format!(
        "validate_no_reserved_marker_addresses: cannot materialize {}: {e}",
        entry.key().hex()
      )
    })?;
    for (idx, addr) in constant.refs.iter().enumerate() {
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

// ============================================================================
// Anonymous-mode ingress
// ============================================================================
//
// Companion to the Meta-mode ingress above. Uses only `Constant` data —
// never reads `ConstantMeta`, `Env::named`, `Env::names`, or any other
// metadata. Projection addresses are reconstructed deterministically from
// `(block, idx, [cidx])` via `Constant::commit`, which agrees with the
// addresses stored in `env.consts` (the compiler produces these same
// projection constants).
//
// Intended for use with environments loaded via `Env::get_anon`, which
// discards `named`/`names`/`comms` sections. The helpers below do not
// depend on those sections being empty — they simply never consult them.

use crate::mode::Anon;

/// Fetch a constant with an explicit binding to its map key, including sources
/// assembled in memory rather than loaded with deferred address verification.
fn anon_constant(
  env: crate::input::Input<'_>,
  addr: &Address,
) -> Result<Option<Arc<Constant>>, String> {
  env.constant(addr)
}

/// A content-addressed file cannot encode a cycle between distinct blocks
/// without a hash preimage. Rec slots are the only local back edges. Gather
/// them during conversion and check the block before publishing any members.
#[derive(Default)]
struct LocalDefnDependencies {
  edges: FxHashMap<Address, FxHashSet<Address>>,
  safe: Vec<Address>,
}

impl LocalDefnDependencies {
  fn insert(
    &mut self,
    addr: &Address,
    safety: DefinitionSafety,
    refs: FxHashSet<Address>,
  ) {
    // Most declarations have no Rec nodes: keep their admission allocation-free.
    if refs.is_empty() {
      return;
    }
    if safety == DefinitionSafety::Safe {
      self.safe.push(addr.clone());
    }
    self.edges.insert(addr.clone(), refs);
  }

  fn validate(&self) -> Result<(), String> {
    let mut finished = FxHashSet::default();
    let mut active = FxHashSet::default();
    for root in &self.safe {
      let mut pending = vec![(root, false)];
      while let Some((addr, exit)) = pending.pop() {
        if exit {
          active.remove(addr);
          finished.insert(addr);
          continue;
        }
        if finished.contains(addr) {
          continue;
        }
        let Some(refs) = self.edges.get(addr) else {
          continue;
        };
        if !active.insert(addr) {
          return Err(format!(
            "cyclic definition dependency at {}",
            addr.hex()
          ));
        }
        pending.push((addr, true));
        pending.extend(refs.iter().map(|dependency| (dependency, false)));
      }
    }
    Ok(())
  }
}

/// Verify that a projection address computed from a block's structure
/// is actually present in the env's consts. Wrapped here so the four
/// dispatch arms in `ingress_anon_block` (DPrj/RPrj/IPrj/CPrj) all
/// produce the same error format.
fn verify_proj_addr_in_env(
  kind: &'static str,
  proj_addr: &Address,
  block_addr: &Address,
  member_idx: u64,
  ctor_idx: Option<u64>,
  anon_env: crate::input::Input<'_>,
) -> Result<(), String> {
  if let Some(actual) = anon_env.constant(proj_addr)? {
    let expected = match kind {
      "DPrj" => {
        ixon::constant::defn_proj_constant(member_idx, block_addr.clone())
      },
      "RPrj" => {
        ixon::constant::recr_proj_constant(member_idx, block_addr.clone())
      },
      "IPrj" => {
        ixon::constant::indc_proj_constant(member_idx, block_addr.clone())
      },
      "CPrj" => ixon::constant::ctor_proj_constant(
        member_idx,
        ctor_idx.ok_or("constructor projection has no constructor index")?,
        block_addr.clone(),
      ),
      _ => return Err("unknown projection kind".into()),
    };
    if actual.as_ref() != &expected {
      return Err(format!(
        "carried {kind} {} differs from its owner/index",
        proj_addr.hex()
      ));
    }
    return Ok(());
  }
  #[cfg(not(target_arch = "riscv64"))]
  if matches!(anon_env, crate::input::Input::Artifact(_)) {
    // The authenticated owner defines these semantic members. Absence does
    // not fabricate a raw record or authorize lookup of a missing reference.
    return Ok(());
  }
  match ctor_idx {
    None => Err(format!(
      "ingress_anon_block: computed {kind} address {} not present in env (block {} idx {})",
      proj_addr.hex(),
      block_addr.hex(),
      member_idx
    )),
    Some(cidx) => Err(format!(
      "ingress_anon_block: computed {kind} address {} not present in env (block {} idx {} cidx {})",
      proj_addr.hex(),
      block_addr.hex(),
      member_idx,
      cidx
    )),
  }
}

/// Deterministic IPrj content address for member `idx` of `block`.
///
/// Thin re-export of `ixon::constant::indc_proj_address` —
/// the canonical projection-address helper used by both compile and
/// ingress paths. Keep the `anon_` alias so existing call sites read
/// naturally in the anon-mode pipeline.
pub fn anon_indc_proj_addr(block: &Address, idx: u64) -> Address {
  ixon::constant::indc_proj_address(idx, block)
}

/// Deterministic DPrj content address for member `idx` of `block`.
pub fn anon_defn_proj_addr(block: &Address, idx: u64) -> Address {
  ixon::constant::defn_proj_address(idx, block)
}

/// Deterministic RPrj content address for member `idx` of `block`.
pub fn anon_recr_proj_addr(block: &Address, idx: u64) -> Address {
  ixon::constant::recr_proj_address(idx, block)
}

/// Deterministic CPrj content address for ctor `(idx, cidx)` of `block`.
pub fn anon_ctor_proj_addr(block: &Address, idx: u64, cidx: u64) -> Address {
  ixon::constant::ctor_proj_address(idx, cidx, block)
}

/// Compute deterministic ctor projection addresses for every constructor of
/// an inductive member at position `indc_idx` in a block at `block_addr`.
fn anon_ctor_addrs(
  block_addr: &Address,
  indc_idx: u64,
  ind: &ixon::constant::Inductive,
) -> Vec<Address> {
  (0..ind.ctors.len() as u64)
    .map(|cidx| anon_ctor_proj_addr(block_addr, indc_idx, cidx))
    .collect()
}

/// Anon ingress for a single standalone (non-mutual) constant.
///
/// For `Defn` and `Recr` the mutual context is the singleton `[self_id]`,
/// so self-recursive standalones can use `Expr::Rec(0, univs)` to refer to
/// themselves. (Singleton-unwrapped self-recursive defs are emitted by the
/// compiler as standalones, with their self-reference encoded as `Rec(0)` —
/// same as a one-member mutual block would have used.) Named ingress uses
/// the same singleton.
///
/// `Axio` and `Quot` cannot have `Rec`-references so we route them through
/// `ingress_standalone` unchanged. Projections / `Muts` belong to a block
/// and are not valid as standalone entries.
fn ingress_anon_standalone(
  kenv: &mut KEnv<Anon>,
  anon_env: crate::input::Input<'_>,
  addr: &Address,
  constant: &Constant,
) -> Result<KId<Anon>, String> {
  let empty_meta = ConstantMeta::default();
  let empty_names: FxHashMap<Address, Name> = FxHashMap::default();
  let empty_n2a: FxHashMap<Name, Address> = FxHashMap::default();
  let mut convert_stats = ConvertStats::new(false);
  let self_id: KId<Anon> = KId::new(addr.clone(), ());

  let mut local_dependencies = LocalDefnDependencies::default();
  let entries = match &constant.info {
    IxonCI::Defn(def) => ingress_defn::<Anon>(
      def,
      self_id.clone(),
      &empty_meta,
      anon_env,
      &empty_names,
      &empty_n2a,
      &constant.sharing,
      &constant.refs,
      &constant.univs,
      self_id.clone(),
      &mut kenv.intern,
      &mut convert_stats,
      vec![self_id.clone()],
      Some(&mut local_dependencies),
    )?,
    IxonCI::Recr(rec) => ingress_recursor::<Anon>(
      rec,
      self_id.clone(),
      &empty_meta,
      anon_env,
      &empty_names,
      &empty_n2a,
      &constant.sharing,
      &constant.refs,
      &constant.univs,
      self_id.clone(),
      &mut kenv.intern,
      &mut convert_stats,
      vec![self_id.clone()],
    )?,
    _ => ingress_standalone::<Anon>(
      &Name::anon(),
      addr,
      constant,
      &empty_meta,
      anon_env,
      &empty_names,
      &empty_n2a,
      &mut kenv.intern,
      &mut convert_stats,
    )?,
  };
  local_dependencies.validate()?;
  insert_standalone_entries(kenv, entries);
  Ok(self_id)
}

/// Anon ingress for a mutual inductive member. Parallel to
/// `ingress_muts_inductive` but takes ctor projection addresses **directly**
/// (caller computes via `anon_ctor_addrs`) and a pre-computed `mut_ctx`
/// (sibling KIds for `Expr::Rec` resolution) instead of going through
/// metadata. Uses `DEFAULT_ARENA` + `type_root=0` + empty level-params
/// for the inductive and every ctor.
#[allow(clippy::too_many_arguments)]
fn ingress_anon_inductive(
  ind: &ixon::constant::Inductive,
  self_id: &KId<Anon>,
  anon_env: crate::input::Input<'_>,
  block_constant: &Constant,
  block_id: KId<Anon>,
  member_idx: u64,
  ctor_addrs: &[Address],
  mut_ctx: &[KId<Anon>],
  intern: &mut InternTable<Anon>,
  stats: &mut ConvertStats,
) -> Result<Vec<(KId<Anon>, KConst<Anon>)>, String> {
  if ctor_addrs.len() != ind.ctors.len() {
    return Err(format!(
      "ingress_anon_inductive: ctor_addrs.len()={} but ind.ctors.len()={}",
      ctor_addrs.len(),
      ind.ctors.len()
    ));
  }

  let empty_names: FxHashMap<Address, Name> = FxHashMap::default();
  let level_params: Vec<Name> = Vec::new();
  let mut cache: ExprCache<Anon> = FxHashMap::default();
  let mut univ_cache: UnivCache<Anon> = FxHashMap::default();
  let ctx = Ctx::<Anon> {
    sharing: &block_constant.sharing,
    refs: &block_constant.refs,
    univs: &block_constant.univs,
    mut_ctx: mut_ctx.to_vec(),
    arena: &DEFAULT_ARENA,
    names: &empty_names,
    lvls: level_params.clone(),
    // Anon ingress never reads decorations (§5.5: anon stays
    // metadata-blind), so no patches are threaded here.
    univ_patches: FxHashMap::default(),
    meta_univs: &[],
    local_refs: None,
    synth_counter: Cell::new(0),
  };

  let typ = ingress_expr(
    &ind.typ,
    0,
    &ctx,
    intern,
    anon_env,
    &mut cache,
    &mut univ_cache,
    stats,
  )?;

  let ctor_ids: Vec<KId<Anon>> =
    ctor_addrs.iter().map(|a| KId::<Anon>::new(a.clone(), ())).collect();

  let mut results = vec![(
    self_id.clone(),
    KConst::Indc {
      name: (),
      level_params: (),
      lvls: ind.lvls,
      params: ind.params,
      indices: ind.indices,
      is_unsafe: ind.is_unsafe,
      block: block_id,
      member_idx,
      ty: typ,
      ctors: ctor_ids.clone(),
      lean_all: (),
    },
  )];

  for (cidx, ctor) in ind.ctors.iter().enumerate() {
    stats.record_cache_clear(&cache);
    cache.clear();
    let ctor_id = ctor_ids[cidx].clone();
    let ctor_ctx = Ctx::<Anon> {
      sharing: &block_constant.sharing,
      refs: &block_constant.refs,
      univs: &block_constant.univs,
      mut_ctx: mut_ctx.to_vec(),
      arena: &DEFAULT_ARENA,
      names: &empty_names,
      lvls: Vec::new(),
      univ_patches: FxHashMap::default(),
      meta_univs: &[],
      local_refs: None,
      synth_counter: Cell::new(0),
    };
    let mut ctor_univ_cache: UnivCache<Anon> = FxHashMap::default();

    let ctor_typ = ingress_expr(
      &ctor.typ,
      0,
      &ctor_ctx,
      intern,
      anon_env,
      &mut cache,
      &mut ctor_univ_cache,
      stats,
    )?;

    results.push((
      ctor_id,
      KConst::Ctor {
        name: (),
        level_params: (),
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

/// Anon ingress for an entire Muts block: ingresses every member (and
/// every constructor of every inductive member) under its deterministic
/// projection address. Verifies that each computed address exists in
/// `anon_env.consts` — missing → error (corrupted .ixe).
///
/// Returns the KIds in member order. The first KId is the block's
/// "primary" — `check_ixon_const` checks the complete serialized unit,
/// including both phases of an inductive/recursor family.
pub fn ingress_anon_block(
  kenv: &mut KEnv<Anon>,
  anon_env: &IxonEnv,
  block_constant: &Constant,
  block_addr: &Address,
) -> Result<Vec<KId<Anon>>, String> {
  ingress_anon_block_input(kenv, anon_env.into(), block_constant, block_addr)
}

pub(crate) fn ingress_anon_block_input(
  kenv: &mut KEnv<Anon>,
  anon_env: crate::input::Input<'_>,
  block_constant: &Constant,
  block_addr: &Address,
) -> Result<Vec<KId<Anon>>, String> {
  let IxonCI::Muts(members) = &block_constant.info else {
    return Err(format!(
      "ingress_anon_block: addr {} is not a Muts block (got variant {:?})",
      block_addr.hex(),
      block_constant.info.variant()
    ));
  };
  validate_serialized_muts(members)?;

  convert_anon_muts(kenv, anon_env, block_constant, block_addr, members)
}

fn convert_anon_muts(
  kenv: &mut KEnv<Anon>,
  anon_env: crate::input::Input<'_>,
  block_constant: &Constant,
  block_addr: &Address,
  members: &[IxonMutConst],
) -> Result<Vec<KId<Anon>>, String> {
  let block_id = KId::<Anon>::new(block_addr.clone(), ());
  let mut convert_stats = ConvertStats::new(false);
  let empty_meta = ConstantMeta::default();
  let empty_names: FxHashMap<Address, Name> = FxHashMap::default();
  let empty_n2a: FxHashMap<Name, Address> = FxHashMap::default();

  // Compute mut_ctx for the entire block: one KId per member, addressed
  // by its projection variant. Threaded through every member's ingress
  // so `Expr::Rec(idx)` resolves to a sibling correctly.
  let mut_ctx: Vec<KId<Anon>> = members
    .iter()
    .enumerate()
    .map(|(i, m)| {
      let i = i as u64;
      let addr = match m {
        IxonMutConst::Defn(_) => anon_defn_proj_addr(block_addr, i),
        IxonMutConst::Indc(_) => anon_indc_proj_addr(block_addr, i),
        IxonMutConst::Recr(_) => anon_recr_proj_addr(block_addr, i),
      };
      KId::<Anon>::new(addr, ())
    })
    .collect();

  let mut local_dependencies = LocalDefnDependencies::default();
  let mut all_entries: Vec<(KId<Anon>, KConst<Anon>)> = Vec::new();
  let mut member_kids: Vec<KId<Anon>> = Vec::with_capacity(members.len());

  for (i, member) in members.iter().enumerate() {
    let idx = i as u64;
    match member {
      IxonMutConst::Defn(def) => {
        let proj_addr = anon_defn_proj_addr(block_addr, idx);
        verify_proj_addr_in_env(
          "DPrj", &proj_addr, block_addr, idx, None, anon_env,
        )?;
        let self_id = KId::<Anon>::new(proj_addr.clone(), ());
        member_kids.push(self_id.clone());

        let entries = ingress_defn::<Anon>(
          def,
          self_id,
          &empty_meta,
          anon_env,
          &empty_names,
          &empty_n2a,
          &block_constant.sharing,
          &block_constant.refs,
          &block_constant.univs,
          block_id.clone(),
          &mut kenv.intern,
          &mut convert_stats,
          mut_ctx.clone(),
          Some(&mut local_dependencies),
        )?;
        all_entries.extend(entries);
      },
      IxonMutConst::Recr(rec) => {
        let proj_addr = anon_recr_proj_addr(block_addr, idx);
        verify_proj_addr_in_env(
          "RPrj", &proj_addr, block_addr, idx, None, anon_env,
        )?;
        let self_id = KId::<Anon>::new(proj_addr.clone(), ());
        member_kids.push(self_id.clone());

        let entries = ingress_recursor::<Anon>(
          rec,
          self_id,
          &empty_meta,
          anon_env,
          &empty_names,
          &empty_n2a,
          &block_constant.sharing,
          &block_constant.refs,
          &block_constant.univs,
          block_id.clone(),
          &mut kenv.intern,
          &mut convert_stats,
          mut_ctx.clone(),
        )?;
        all_entries.extend(entries);
      },
      IxonMutConst::Indc(ind) => {
        let proj_addr = anon_indc_proj_addr(block_addr, idx);
        verify_proj_addr_in_env(
          "IPrj", &proj_addr, block_addr, idx, None, anon_env,
        )?;
        let self_id = KId::<Anon>::new(proj_addr.clone(), ());
        member_kids.push(self_id.clone());

        let ctor_addrs = anon_ctor_addrs(block_addr, idx, ind);
        // Verify ctor addresses too — catches corruption early.
        for (cidx, c_addr) in ctor_addrs.iter().enumerate() {
          verify_proj_addr_in_env(
            "CPrj",
            c_addr,
            block_addr,
            idx,
            Some(cidx as u64),
            anon_env,
          )?;
        }

        let entries = ingress_anon_inductive(
          ind,
          &self_id,
          anon_env,
          block_constant,
          block_id.clone(),
          idx,
          &ctor_addrs,
          &mut_ctx,
          &mut kenv.intern,
          &mut convert_stats,
        )?;
        all_entries.extend(entries);
      },
    }
  }

  local_dependencies.validate()?;
  insert_muts_entries(kenv, all_entries);
  Ok(member_kids)
}

/// Anon shallow ingress for a single address — used by the lazy fault
/// path in `TypeChecker` (`LazyAnonIngress`). For projections, fetches
/// the parent block and ingresses the relevant member (or the full
/// inductive when a constructor is requested). For standalones, ingresses
/// directly. Errors if asked about a Muts block address (not a valid
/// kernel KId target) or an absent address.
pub fn ingress_anon_addr_shallow(
  kenv: &mut KEnv<Anon>,
  anon_env: &IxonEnv,
  addr: &Address,
) -> Result<bool, String> {
  ingress_anon_addr_shallow_input(kenv, anon_env.into(), addr)
}

pub(crate) fn ingress_anon_addr_shallow_input(
  kenv: &mut KEnv<Anon>,
  anon_env: crate::input::Input<'_>,
  addr: &Address,
) -> Result<bool, String> {
  let Some(constant) = anon_constant(anon_env, addr)? else {
    return Ok(false);
  };

  // Extract the parent block address if this is a projection. The
  // kernel sometimes asks for the block's KId directly (block
  // coordination during mutual recursion) — in that case we ingress
  // the block at its own address.
  let block_addr: Option<Address> = match &constant.info {
    IxonCI::DPrj(p) => Some(p.block.clone()),
    IxonCI::IPrj(p) => Some(p.block.clone()),
    IxonCI::RPrj(p) => Some(p.block.clone()),
    IxonCI::CPrj(p) => Some(p.block.clone()),
    IxonCI::Muts(_) => Some(addr.clone()),
    _ => None,
  };

  if let Some(block_addr) = block_addr {
    // Block dedup: `insert_muts_entries` always stores the block under
    // `KId<Anon>(block_addr, ())` in `kenv.blocks`. A prior fault on any
    // projection of this block populated all members in `kenv.consts`;
    // re-ingressing would be wasted work and leaves heap-allocator
    // fragmentation that doesn't return to the OS. The
    // `LazyAnonIngress::faulted_addrs` set in `tc.rs` only dedupes at the
    // projection-address level, so distinct sibling projections of the
    // same block each fault separately and reach here.
    let block_kid = KId::<Anon>::new(block_addr.clone(), ());
    if kenv.blocks.contains_key(&block_kid) {
      return Ok(true);
    }
    let block_const =
      anon_constant(anon_env, &block_addr)?.ok_or_else(|| {
        format!(
          "ingress_anon_addr_shallow: block {} (parent of {}) absent",
          block_addr.hex(),
          addr.hex()
        )
      })?;
    ingress_anon_block_input(kenv, anon_env, &block_const, &block_addr)?;
    return Ok(true);
  }

  // Standalone (Defn/Recr/Axio/Quot).
  ingress_anon_standalone(kenv, anon_env, addr, &constant)?;
  Ok(true)
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::expr::ExprData;
  use crate::level::UnivData;
  use ix_common::env::{self, BinderInfo};

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

  #[cfg(not(target_arch = "riscv64"))]
  #[test]
  fn lean_recursor_layout_uses_source_then_numeric_order() {
    // Layout-only test: the source mutual may split into structural SCCs,
    // but direct ingress must keep all three originals in `.all` order.
    let head = mk_name("Z");
    let positions = FxHashMap::from_iter([
      (head.clone(), 0),
      (mk_name("A"), 1),
      (mk_name("C"), 2),
    ]);
    let mut peers =
      ["Z.rec_10", "A.rec", "Z.rec_2", "C.rec", "Z.rec_1", "Z.rec"]
        .map(mk_name);
    peers
      .sort_by_cached_key(|name| lean_recursor_order(name, &head, &positions));
    assert_eq!(
      peers.map(|name| name.pretty()),
      ["Z.rec", "A.rec", "C.rec", "Z.rec_1", "Z.rec_2", "Z.rec_10"],
    );
  }

  #[cfg(not(target_arch = "riscv64"))]
  #[test]
  fn lean_recursor_layout_does_not_recognize_foreign_or_malformed_names() {
    let head = mk_name("Z");
    let positions =
      FxHashMap::from_iter([(head.clone(), 0), (mk_name("A"), 1)]);
    for name in [
      "Foreign.rec",
      "Foreign.rec_1",
      "A.rec_1",
      "Z.rec_0",
      "Z.rec_01",
      "Z.rec_",
      "Z.rec_+1",
      "Z.rec_-1",
      "Z.rec_١",
      "Z.rec_9999999999999999999999999999999999999999",
    ] {
      assert_eq!(
        lean_recursor_order(&mk_name(name), &head, &positions),
        LeanRecursorOrder::Unrecognized,
        "{name} must not claim a valid source slot",
      );
    }
    assert_eq!(
      lean_recursor_order(
        &Name::num(head.clone(), n_lit(1)),
        &head,
        &positions
      ),
      LeanRecursorOrder::Unrecognized,
    );
  }

  // ---- lean_level_to_kuniv ----

  #[test]
  fn lean_level_zero_to_kuniv() {
    let u = lean_level_to_kuniv(&Level::zero(), &[]).unwrap();
    assert!(matches!(u.data(), UnivData::Zero(_)));
  }

  #[test]
  fn lean_level_succ_to_kuniv() {
    let u = lean_level_to_kuniv(&Level::succ(Level::zero()), &[]).unwrap();
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
    let u = lean_level_to_kuniv(&Level::param(v_name), &params).unwrap();
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
    let u = lean_level_to_kuniv(&ll, &params).unwrap();
    assert!(matches!(u.data(), UnivData::Max(..)));
  }

  #[test]
  fn lean_level_param_unknown_is_an_error() {
    let err =
      lean_level_to_kuniv(&Level::param(mk_name("zzz")), &[mk_name("u")])
        .unwrap_err();
    assert!(err.contains("unknown level param `zzz`"), "{err}");
    // Valid neighbour: the declared parameter converts.
    assert!(
      lean_level_to_kuniv(&Level::param(mk_name("u")), &[mk_name("u")]).is_ok()
    );
    // Nested under succ/max the refusal still propagates.
    let nested =
      Level::max(Level::zero(), Level::succ(Level::param(mk_name("zzz"))));
    assert!(lean_level_to_kuniv(&nested, &[mk_name("u")]).is_err());
  }

  #[test]
  fn lean_level_mvar_is_an_error() {
    let err = lean_level_to_kuniv(&Level::mvar(mk_name("m")), &[]).unwrap_err();
    assert!(err.contains("unexpected level metavariable `m`"), "{err}");
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
    let marker = crate::primitive::PrimAddrs::new().eager_reduce;
    env.register_name(
      mk_name("Evil.marker"),
      ixon::env::Named::with_addr(marker),
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
    let marker = crate::primitive::PrimAddrs::new().eager_reduce;
    let constant = Constant::with_tables(
      ixon::constant::ConstantInfo::Axio(ixon::constant::Axiom {
        is_unsafe: false,
        lvls: 0,
        typ: IxonExpr::sort(0),
      }),
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

  /// Meta-mode ingress must reject a local definition cycle before any member
  /// is published: `TypeChecker::new_with_lazy_ixon` relies on that admission
  /// check instead of walking definition dependencies on every check.
  #[test]
  fn ixon_ingress_meta_rejects_local_definition_cycles() {
    use ix_common::env::DefinitionSafety;
    use ixon::constant::{
      Constant, ConstantInfo, DefKind, Definition, MutConst, defn_proj_constant,
    };
    use ixon::env::Named;
    use ixon::metadata::{ConstantMeta, ConstantMetaInfo, ExprMeta};
    use ixon::univ::Univ;
    let definition = |value: IxonExpr| Definition {
      kind: DefKind::Definition,
      safety: DefinitionSafety::Safe,
      lvls: 0,
      typ: Arc::new(IxonExpr::Sort(1)),
      value: Arc::new(value),
    };
    for cyclic in [false, true] {
      let env = IxonEnv::new();
      let mut block = Constant::new(ConstantInfo::Muts(vec![
        MutConst::Defn(definition(IxonExpr::Rec(1, vec![]))),
        MutConst::Defn(definition(if cyclic {
          IxonExpr::Rec(0, vec![])
        } else {
          IxonExpr::Sort(0)
        })),
      ]));
      block.univs = vec![Univ::zero(), Univ::succ(Univ::zero())];
      let block_addr = block.commit().0;
      env.store_const(block_addr.clone(), block);
      let member_names = [mk_name("Cycle.f"), mk_name("Cycle.g")];
      let name_addrs: Vec<Address> = member_names
        .iter()
        .map(|n| Address::hash(n.pretty().as_bytes()))
        .collect();
      let mut names: FxHashMap<Address, Name> = FxHashMap::default();
      let mut name_to_addr: FxHashMap<Name, Address> = FxHashMap::default();
      for (i, name) in member_names.iter().enumerate() {
        let proj = defn_proj_constant(i as u64, block_addr.clone());
        let proj_addr = proj.commit().0;
        env.store_const(proj_addr.clone(), proj);
        let meta = ConstantMeta::new(ConstantMetaInfo::Def {
          name: name_addrs[i].clone(),
          lvls: vec![],
          all: name_addrs.clone(),
          ctx: name_addrs.clone(),
          arena: ExprMeta::default(),
          type_root: 0,
          value_root: 0,
        });
        env.register_name(name.clone(), Named::new(proj_addr.clone(), meta));
        names.insert(name_addrs[i].clone(), name.clone());
        name_to_addr.insert(name.clone(), proj_addr);
      }
      let all: Vec<Vec<Address>> =
        name_addrs.iter().map(|a| vec![a.clone()]).collect();
      let mut intern = InternTable::<Meta>::new();
      let mut stats = ConvertStats::new(false);
      let result = ingress_muts_block::<Meta>(
        &mk_name("Cycle"),
        &block_addr,
        &all,
        (&env).into(),
        &names,
        &name_to_addr,
        &mut intern,
        &mut stats,
      );
      if cyclic {
        let err = result.unwrap_err();
        assert!(err.contains("cyclic definition dependency"), "{err}");
      } else {
        assert!(!result.unwrap().is_empty());
      }
    }
  }

  // ---- lean_expr_to_zexpr: variant coverage ----

  fn do_ingress(e: &LeanExpr, pn: &[Name]) -> KExpr<Meta> {
    let mut intern = InternTable::<Meta>::new();
    lean_expr_to_zexpr(e, pn, &mut intern, None, None).unwrap()
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
  fn ingress_bvar_display_names_with_nonempty_context() {
    let prefix = vec![mk_name("outer"), mk_name("inner")];
    let mut binders = prefix.clone();
    for (idx, expected) in [
      (0, mk_name("inner")),
      (1, mk_name("outer")),
      (2, Name::anon()),
      (u64::MAX, Name::anon()),
    ] {
      let k = lean_expr_to_zexpr_cached(
        &LeanExpr::bvar(Nat::from(idx)),
        &[],
        &mut binders,
        &mut InternTable::new(),
        None,
        None,
        None,
        None,
      )
      .unwrap();
      assert!(
        matches!(k.data(), ExprData::Var(i, n, _) if *i == idx && n == &expected)
      );
      assert_eq!(binders, prefix);
    }
  }

  #[test]
  fn ixon_bvar_largest_usize_has_anonymous_name() {
    let ctx = Ctx::<Meta> {
      sharing: &[],
      refs: &[],
      univs: &[],
      mut_ctx: vec![],
      local_refs: None,
      arena: &ExprMeta::default(),
      names: &FxHashMap::default(),
      lvls: vec![],
      univ_patches: FxHashMap::default(),
      meta_univs: &[],
      synth_counter: Cell::new(0),
    };
    let idx = usize::MAX as u64;
    let k = ingress_expr(
      &Arc::new(IxonExpr::Var(idx)),
      0,
      &ctx,
      &mut InternTable::new(),
      (&IxonEnv::new()).into(),
      &mut ExprCache::default(),
      &mut UnivCache::default(),
      &mut ConvertStats::default(),
    )
    .unwrap();
    assert!(
      matches!(k.data(), ExprData::Var(i, n, _) if *i == idx && n == &Name::anon())
    );
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
    let _u = lean_level_to_kuniv(&l, &[]).unwrap();
  }

  // ---- Invalid-input refusals (errors, not panics) ----

  fn try_ingress(e: &LeanExpr, pn: &[Name]) -> Result<KExpr<Meta>, String> {
    let mut intern = InternTable::<Meta>::new();
    lean_expr_to_zexpr(e, pn, &mut intern, None, None)
  }

  #[test]
  fn ingress_fvar_is_an_error() {
    let e = LeanExpr::fvar(mk_name("x"));
    let err = try_ingress(&e, &[]).unwrap_err();
    assert!(err.contains("unexpected FVar(x)"), "{err}");
  }

  #[test]
  fn ingress_mvar_is_an_error() {
    let e = LeanExpr::mvar(mk_name("m"));
    let err = try_ingress(&e, &[]).unwrap_err();
    assert!(err.contains("unexpected MVar(m)"), "{err}");
  }

  #[test]
  fn ingress_unknown_level_param_under_app_is_an_error() {
    // The refusal propagates from a level nested inside an application;
    // the valid neighbour with the parameter declared ingresses.
    let u = mk_name("u");
    let e = LeanExpr::app(
      LeanExpr::cnst(mk_name("f"), vec![Level::param(u.clone())]),
      LeanExpr::sort(Level::succ(Level::param(u.clone()))),
    );
    let err = try_ingress(&e, &[mk_name("v")]).unwrap_err();
    assert!(err.contains("unknown level param `u`"), "{err}");
    assert!(try_ingress(&e, std::slice::from_ref(&u)).is_ok());
  }

  #[test]
  fn ingress_level_mvar_under_sort_is_an_error() {
    let e = LeanExpr::sort(Level::succ(Level::mvar(mk_name("m"))));
    let err = try_ingress(&e, &[]).unwrap_err();
    assert!(err.contains("unexpected level metavariable `m`"), "{err}");
  }

  /// 2^64, the least `Nat` that does not fit a `u64`.
  fn past_u64() -> Nat {
    Nat::from_le_bytes(&[0, 0, 0, 0, 0, 0, 0, 0, 1])
  }

  #[test]
  fn ingress_bvar_index_past_u64_is_an_error() {
    // It used to become `bvar 0`.
    let err = try_ingress(&LeanExpr::bvar(past_u64()), &[]).unwrap_err();
    assert!(
      err.contains("bound variable index 18446744073709551616 exceeds u64"),
      "{err}"
    );
    // Under a binder the refusal still propagates.
    let lam = LeanExpr::lam(
      mk_name("x"),
      LeanExpr::sort(Level::zero()),
      LeanExpr::bvar(past_u64()),
      BinderInfo::Default,
    );
    assert!(try_ingress(&lam, &[]).unwrap_err().contains("exceeds u64"));
    // Valid neighbour: the largest index that fits is kept as it is.
    let k = try_ingress(&LeanExpr::bvar(Nat::from(u64::MAX)), &[]).unwrap();
    assert!(matches!(k.data(), ExprData::Var(i, ..) if *i == u64::MAX));
  }

  #[test]
  fn ingress_proj_index_past_u64_is_an_error() {
    // It used to become field 0.
    let s = LeanExpr::sort(Level::zero());
    let e = LeanExpr::proj(mk_name("Prod"), past_u64(), s.clone());
    let err = try_ingress(&e, &[]).unwrap_err();
    assert!(
      err.contains("projection index 18446744073709551616 of Prod exceeds u64"),
      "{err}"
    );
    // Valid neighbour: the largest index that fits is kept as it is.
    let ok = LeanExpr::proj(mk_name("Prod"), Nat::from(u64::MAX), s);
    let k = try_ingress(&ok, &[]).unwrap();
    assert!(matches!(k.data(), ExprData::Prj(_, i, ..) if *i == u64::MAX));
  }

  // ---- lean_ingress: refusals name the constant ----

  /// `T : Type`, `T.mk : T` and `T.rec` with one rule, each Nat field as
  /// `edit` leaves it (all fit by default). Ingress does not type-check, so
  /// the expressions only need to be well-formed.
  #[cfg(not(target_arch = "riscv64"))]
  fn unit_like_env(
    edit: impl FnOnce(
      &mut env::InductiveVal,
      &mut env::ConstructorVal,
      &mut env::RecursorVal,
    ),
  ) -> LeanEnv {
    let (t, mk, rec) = (mk_name("T"), mk_name("T.mk"), mk_name("T.rec"));
    let cv = |name: &Name, typ: LeanExpr| env::ConstantVal {
      name: name.clone(),
      level_params: vec![],
      typ,
    };
    let type0 = LeanExpr::sort(Level::succ(Level::zero()));
    let mut ind = env::InductiveVal {
      cnst: cv(&t, type0.clone()),
      num_params: n_lit(0),
      num_indices: n_lit(0),
      all: vec![t.clone()],
      ctors: vec![mk.clone()],
      num_nested: n_lit(0),
      is_rec: false,
      is_unsafe: false,
      is_reflexive: false,
    };
    let mut ctor = env::ConstructorVal {
      cnst: cv(&mk, LeanExpr::cnst(t.clone(), vec![])),
      induct: t.clone(),
      cidx: n_lit(0),
      num_params: n_lit(0),
      num_fields: n_lit(0),
      is_unsafe: false,
    };
    let mut recr = env::RecursorVal {
      cnst: cv(&rec, type0.clone()),
      all: vec![t.clone()],
      num_params: n_lit(0),
      num_indices: n_lit(0),
      num_motives: n_lit(1),
      num_minors: n_lit(1),
      rules: vec![env::RecursorRule {
        ctor: mk.clone(),
        n_fields: n_lit(0),
        rhs: LeanExpr::lam(
          mk_name("motive"),
          type0,
          LeanExpr::bvar(n_lit(0)),
          BinderInfo::Default,
        ),
      }],
      k: false,
      is_unsafe: false,
    };
    edit(&mut ind, &mut ctor, &mut recr);
    let mut lean_env = LeanEnv::default();
    lean_env.insert(t, LeanCI::InductInfo(ind));
    lean_env.insert(mk, LeanCI::CtorInfo(ctor));
    lean_env.insert(rec, LeanCI::RecInfo(recr));
    lean_env
  }

  #[cfg(not(target_arch = "riscv64"))]
  fn assert_lean_ingress_refuses(lean_env: &LeanEnv, text: &str) {
    match lean_ingress(lean_env) {
      Err(err) => assert!(err.contains(text), "{err:?} lacks {text:?}"),
      Ok(_) => panic!("expected lean_ingress to refuse with {text:?}"),
    }
  }

  #[cfg(not(target_arch = "riscv64"))]
  #[test]
  fn direct_lean_family_retains_member_checking() {
    let source = unit_like_env(|_, _, rec| {
      let u = mk_name("u");
      let typ = LeanExpr::cnst(mk_name("T"), vec![]);
      let ctor = LeanExpr::cnst(mk_name("T.mk"), vec![]);
      let var = |i| LeanExpr::bvar(n_lit(i));
      let motive = LeanExpr::all(
        mk_name("x"),
        typ.clone(),
        LeanExpr::sort(Level::param(u.clone())),
        BinderInfo::Default,
      );
      let minor = LeanExpr::app(var(0), ctor);
      rec.cnst.level_params = vec![u];
      rec.cnst.typ = LeanExpr::all(
        mk_name("motive"),
        motive.clone(),
        LeanExpr::all(
          mk_name("minor"),
          minor.clone(),
          LeanExpr::all(
            mk_name("major"),
            typ,
            LeanExpr::app(var(2), var(0)),
            BinderInfo::Default,
          ),
          BinderInfo::Default,
        ),
        BinderInfo::Default,
      );
      rec.rules[0].rhs = LeanExpr::lam(
        mk_name("motive"),
        motive,
        LeanExpr::lam(mk_name("minor"), minor, var(0), BinderInfo::Default),
        BinderInfo::Default,
      );
    });
    let mut kernel = lean_ingress(&source).unwrap();
    let ids: Vec<_> = ["T", "T.mk", "T.rec"]
      .into_iter()
      .map(|name| {
        kernel
          .consts
          .keys()
          .find(|id| id.name == mk_name(name))
          .unwrap()
          .clone()
      })
      .collect();
    let mut checker = crate::tc::TypeChecker::new(&mut kernel);
    assert!(
      checker.coordinated_check_block_for_const(&ids[0]).unwrap().is_none()
    );
    for id in ids {
      checker.check_const(&id).unwrap();
    }
  }

  #[cfg(not(target_arch = "riscv64"))]
  #[test]
  fn lean_ingress_names_the_constant_of_an_expression_refusal() {
    let mut lean_env = unit_like_env(|_, _, _| {});
    let ax = mk_name("Ax");
    lean_env.insert(
      ax.clone(),
      LeanCI::AxiomInfo(env::AxiomVal {
        cnst: env::ConstantVal {
          name: ax,
          level_params: vec![],
          typ: LeanExpr::sort(Level::param(mk_name("u"))),
        },
        is_unsafe: false,
      }),
    );
    assert_lean_ingress_refuses(&lean_env, "Ax: unknown level param `u`");
    let fvar_rhs = unit_like_env(|_, _, r| {
      r.rules[0].rhs = LeanExpr::fvar(mk_name("x"));
    });
    assert_lean_ingress_refuses(&fvar_rhs, "T.rec: unexpected FVar(x)");
    let mvar_ty = unit_like_env(|_, c, _| {
      c.cnst.typ = LeanExpr::mvar(mk_name("m"));
    });
    assert_lean_ingress_refuses(&mvar_ty, "T.mk: unexpected MVar(m)");
    // Valid neighbour.
    assert!(lean_ingress(&unit_like_env(|_, _, _| {})).is_ok());
  }

  #[cfg(not(target_arch = "riscv64"))]
  #[test]
  fn lean_ingress_refuses_inductive_counts_past_u64() {
    let params = unit_like_env(|i, _, _| i.num_params = past_u64());
    assert_lean_ingress_refuses(
      &params,
      "T: num_params 18446744073709551616 exceeds u64",
    );
    let indices = unit_like_env(|i, _, _| i.num_indices = past_u64());
    assert_lean_ingress_refuses(
      &indices,
      "T: num_indices 18446744073709551616 exceeds u64",
    );
  }

  #[cfg(not(target_arch = "riscv64"))]
  #[test]
  fn lean_ingress_refuses_constructor_fields_past_u64() {
    let cidx = unit_like_env(|_, c, _| c.cidx = past_u64());
    assert_lean_ingress_refuses(
      &cidx,
      "T.mk: cidx 18446744073709551616 exceeds u64",
    );
    let params = unit_like_env(|_, c, _| c.num_params = past_u64());
    assert_lean_ingress_refuses(
      &params,
      "T.mk: num_params 18446744073709551616 exceeds u64",
    );
    let fields = unit_like_env(|_, c, _| c.num_fields = past_u64());
    assert_lean_ingress_refuses(
      &fields,
      "T.mk: num_fields 18446744073709551616 exceeds u64",
    );
  }

  #[cfg(not(target_arch = "riscv64"))]
  #[test]
  fn lean_ingress_refuses_recursor_counts_past_u64() {
    type Edit = fn(&mut env::RecursorVal);
    let cases: [(&str, Edit); 4] = [
      ("num_params", |r| r.num_params = past_u64()),
      ("num_indices", |r| r.num_indices = past_u64()),
      ("num_motives", |r| r.num_motives = past_u64()),
      ("num_minors", |r| r.num_minors = past_u64()),
    ];
    for (field, edit) in cases {
      assert_lean_ingress_refuses(
        &unit_like_env(|_, _, r| edit(r)),
        &format!("T.rec: {field} 18446744073709551616 exceeds u64"),
      );
    }
    let rule = unit_like_env(|_, _, r| r.rules[0].n_fields = past_u64());
    assert_lean_ingress_refuses(
      &rule,
      "T.rec: n_fields 18446744073709551616 of the rule for T.mk exceeds u64",
    );
  }

  /// Valid neighbour of the count refusals: every field at `u64::MAX` is
  /// kept as it is (not 0), and the default fields convert unchanged.
  #[cfg(not(target_arch = "riscv64"))]
  #[test]
  fn lean_ingress_keeps_count_fields_that_fit() {
    let id_of = |kenv: &KEnv<Meta>, n: &str| {
      kenv.consts.keys().find(|id| id.name == mk_name(n)).unwrap().clone()
    };
    let kenv = lean_ingress(&unit_like_env(|_, _, _| {})).unwrap();
    match &kenv.consts[&id_of(&kenv, "T.rec")] {
      KConst::Recr { params, indices, motives, minors, rules, .. } => {
        assert_eq!((*params, *indices, *motives, *minors), (0, 0, 1, 1));
        assert_eq!(rules[0].fields, 0);
      },
      other => panic!("expected a recursor, got {other:?}"),
    }
    let max = Nat::from(u64::MAX);
    let kenv = lean_ingress(&unit_like_env(|i, c, r| {
      i.num_params = max.clone();
      i.num_indices = max.clone();
      c.cidx = max.clone();
      c.num_params = max.clone();
      c.num_fields = max.clone();
      r.num_params = max.clone();
      r.num_indices = max.clone();
      r.num_motives = max.clone();
      r.num_minors = max.clone();
      r.rules[0].n_fields = max.clone();
    }))
    .unwrap();
    match &kenv.consts[&id_of(&kenv, "T")] {
      KConst::Indc { params, indices, .. } => {
        assert_eq!((*params, *indices), (u64::MAX, u64::MAX));
      },
      other => panic!("expected an inductive, got {other:?}"),
    }
    match &kenv.consts[&id_of(&kenv, "T.mk")] {
      KConst::Ctor { cidx, params, fields, .. } => {
        assert_eq!((*cidx, *params, *fields), (u64::MAX, u64::MAX, u64::MAX));
      },
      other => panic!("expected a constructor, got {other:?}"),
    }
    match &kenv.consts[&id_of(&kenv, "T.rec")] {
      KConst::Recr { params, indices, motives, minors, rules, .. } => {
        assert_eq!(
          (*params, *indices, *motives, *minors, rules[0].fields),
          (u64::MAX, u64::MAX, u64::MAX, u64::MAX, u64::MAX)
        );
      },
      other => panic!("expected a recursor, got {other:?}"),
    }
  }

  // ---- Caching ----

  #[test]
  fn ingress_cached_hits_cache_on_second_call() {
    let mut env = KEnv::<Meta>::new();
    let e = LeanExpr::app(
      LeanExpr::sort(Level::zero()),
      LeanExpr::sort(Level::zero()),
    );
    let k1 =
      lean_expr_to_zexpr_with_kenv(&e, &[], &mut env, None, None).unwrap();
    let k2 =
      lean_expr_to_zexpr_with_kenv(&e, &[], &mut env, None, None).unwrap();
    // Cache hit → same interned result.
    assert!(k1.ptr_eq(&k2));
  }

  /// Canonicity §10.6 stage 2: a `univ_patches` entry keyed by the
  /// occurrence's arena index decorates the occurrence with the
  /// ORIGINAL spelling (resolved through the virtual index space
  /// `univs ++ meta_univs`), while the kernel-held level stays the
  /// canonical table entry.
  #[test]
  fn patch_sourced_sort_decoration() {
    let canon = IxonUniv::max(
      IxonUniv::succ(IxonUniv::var(0)),
      IxonUniv::succ(IxonUniv::var(1)),
    );
    let orig =
      IxonUniv::succ(IxonUniv::max(IxonUniv::var(0), IxonUniv::var(1)));
    let univs = vec![canon.clone()];
    let meta_univs = vec![orig.clone()];
    let mut arena = ExprMeta::default();
    let root = arena.alloc(ExprMetaData::Leaf);
    // Virtual index 1 = univs.len() (1) + extension slot 0.
    let patch_idxs: Vec<u64> = vec![1];
    let mut univ_patches: FxHashMap<u64, &[u64]> = FxHashMap::default();
    univ_patches.insert(root, patch_idxs.as_slice());
    let names: FxHashMap<Address, Name> = FxHashMap::default();
    let ctx = Ctx::<Meta> {
      sharing: &[],
      refs: &[],
      univs: &univs,
      mut_ctx: vec![],
      arena: &arena,
      names: &names,
      lvls: vec![mk_name("u"), mk_name("v")],
      univ_patches,
      meta_univs: &meta_univs,
      local_refs: None,
      synth_counter: Cell::new(0),
    };
    let mut intern = InternTable::<Meta>::new();
    let ixon_env = IxonEnv::new();
    let mut cache = ExprCache::<Meta>::default();
    let mut univ_cache = UnivCache::<Meta>::default();
    let mut stats = ConvertStats::default();
    let k = ingress_expr(
      &IxonExpr::sort(0),
      root,
      &ctx,
      &mut intern,
      (&ixon_env).into(),
      &mut cache,
      &mut univ_cache,
      &mut stats,
    )
    .unwrap();
    let decor = Meta::meta_get(k.univ_decor()).cloned().flatten();
    assert_eq!(decor, Some(UnivDecor::Sort(orig.clone())));
    // The kernel-held level is the canonical entry, node-for-node.
    let ExprData::Sort(zu, _) = k.data() else {
      panic!("expected Sort, got {:?}", k.data());
    };
    assert!(ixon_matches_kuniv(&canon, zu));
  }

  /// P3 at the kernel boundary: `canon_univ`-fixed table entries ingress
  /// as identity — the mk* smart constructors change nothing, so no
  /// stage-1 fallback decoration fires without a patch.
  #[test]
  fn canonical_table_ingress_identity_no_decoration() {
    use ixon::canon_univ::canon_univ;
    let spellings = [
      IxonUniv::zero(),
      IxonUniv::succ(IxonUniv::max(IxonUniv::var(0), IxonUniv::var(1))),
      IxonUniv::imax(IxonUniv::var(0), IxonUniv::succ(IxonUniv::var(1))),
      IxonUniv::max(IxonUniv::var(1), IxonUniv::var(0)),
      IxonUniv::imax(
        IxonUniv::succ(IxonUniv::var(0)),
        IxonUniv::imax(IxonUniv::var(0), IxonUniv::var(1)),
      ),
    ];
    for spelling in spellings {
      let canon = canon_univ(&spelling);
      let univs = vec![canon.clone()];
      let mut arena = ExprMeta::default();
      let root = arena.alloc(ExprMetaData::Leaf);
      let names: FxHashMap<Address, Name> = FxHashMap::default();
      let ctx = Ctx::<Meta> {
        sharing: &[],
        refs: &[],
        univs: &univs,
        mut_ctx: vec![],
        arena: &arena,
        names: &names,
        lvls: vec![mk_name("u"), mk_name("v")],
        univ_patches: FxHashMap::default(),
        meta_univs: &[],
        local_refs: None,
        synth_counter: Cell::new(0),
      };
      let mut intern = InternTable::<Meta>::new();
      let ixon_env = IxonEnv::new();
      let mut cache = ExprCache::<Meta>::default();
      let mut univ_cache = UnivCache::<Meta>::default();
      let mut stats = ConvertStats::default();
      let k = ingress_expr(
        &IxonExpr::sort(0),
        root,
        &ctx,
        &mut intern,
        (&ixon_env).into(),
        &mut cache,
        &mut univ_cache,
        &mut stats,
      )
      .unwrap();
      let decor = Meta::meta_get(k.univ_decor()).cloned().flatten();
      assert_eq!(
        decor, None,
        "canonical entry {canon:?} must ingress without decoration"
      );
      let ExprData::Sort(zu, _) = k.data() else {
        panic!("expected Sort");
      };
      assert!(
        ixon_matches_kuniv(&canon, zu),
        "canonical entry {canon:?} must ingress as identity"
      );
    }
  }

  /// Const-occurrence patches carry the FULL level-arg list: virtual
  /// indices resolve extension spellings, primary indices ride along
  /// for unchanged args.
  #[test]
  fn patch_sourced_const_decoration_full_list() {
    let canon0 = IxonUniv::max(
      IxonUniv::succ(IxonUniv::var(0)),
      IxonUniv::succ(IxonUniv::var(1)),
    );
    let canon1 = IxonUniv::var(0);
    let orig0 =
      IxonUniv::succ(IxonUniv::max(IxonUniv::var(0), IxonUniv::var(1)));
    let univs = vec![canon0, canon1.clone()];
    let meta_univs = vec![orig0.clone()];
    let ref_name = mk_name("Target");
    let ref_name_addr = lean_name_to_addr(&ref_name);
    let ref_addr = Address::hash(b"target-content");
    let mut names = FxHashMap::default();
    names.insert(ref_name_addr.clone(), ref_name.clone());
    let mut arena = ExprMeta::default();
    let root = arena.alloc(ExprMetaData::Ref { name: ref_name_addr });
    // Arg 0 patched (virtual 2 = univs.len() 2 + slot 0), arg 1
    // unchanged (primary 1).
    let patch_idxs: Vec<u64> = vec![2, 1];
    let mut univ_patches: FxHashMap<u64, &[u64]> = FxHashMap::default();
    univ_patches.insert(root, patch_idxs.as_slice());
    let refs = vec![ref_addr.clone()];
    let ctx = Ctx::<Meta> {
      sharing: &[],
      refs: &refs,
      univs: &univs,
      mut_ctx: vec![],
      arena: &arena,
      names: &names,
      lvls: vec![mk_name("u"), mk_name("v")],
      univ_patches,
      meta_univs: &meta_univs,
      local_refs: None,
      synth_counter: Cell::new(0),
    };
    let mut intern = InternTable::<Meta>::new();
    let ixon_env = IxonEnv::new();
    let mut cache = ExprCache::<Meta>::default();
    let mut univ_cache = UnivCache::<Meta>::default();
    let mut stats = ConvertStats::default();
    let k = ingress_expr(
      &IxonExpr::reference(0, vec![0, 1]),
      root,
      &ctx,
      &mut intern,
      (&ixon_env).into(),
      &mut cache,
      &mut univ_cache,
      &mut stats,
    )
    .unwrap();
    let decor = Meta::meta_get(k.univ_decor()).cloned().flatten();
    let Some(UnivDecor::Const(spellings)) = decor else {
      panic!("expected Const decoration, got {decor:?}");
    };
    assert_eq!(spellings.len(), 2);
    assert_eq!(spellings[0], orig0);
    assert_eq!(spellings[1], canon1);
  }

  #[test]
  fn ingress_cache_differentiates_by_param_names() {
    let mut env = KEnv::<Meta>::new();
    // Same Lean expression, but different param names should produce
    // different cache keys and (for Param-containing exprs) different
    // KExprs.
    let u_name = mk_name("u");
    let v_name = mk_name("v");
    let e = LeanExpr::sort(Level::param(u_name.clone()));
    let k1 = lean_expr_to_zexpr_with_kenv(
      &e,
      std::slice::from_ref(&u_name),
      &mut env,
      None,
      None,
    )
    .unwrap();
    let k2 = lean_expr_to_zexpr_with_kenv(
      &e,
      &[v_name, u_name.clone()],
      &mut env,
      None,
      None,
    )
    .unwrap();
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

  fn cached_for_frames(
    e: &LeanExpr,
    binders: &mut Vec<Name>,
    kenv: &mut KEnv<Meta>,
  ) -> Result<KExpr<Meta>, String> {
    lean_expr_to_zexpr_cached(
      e,
      &[],
      binders,
      &mut kenv.intern,
      None,
      None,
      Some(&mut kenv.ingress_cache),
      Some(&param_names_hash(&[])),
    )
  }

  fn frame_binder(kind: u8, dom: LeanExpr, body: LeanExpr) -> LeanExpr {
    let name = mk_name("inner");
    let value = LeanExpr::lit(env::Literal::NatVal(n_lit(42)));
    match kind {
      0 => LeanExpr::lam(name, dom, body, BinderInfo::Implicit),
      1 => LeanExpr::all(name, dom, body, BinderInfo::Implicit),
      _ => LeanExpr::letE(name, dom, value, body, true),
    }
  }

  #[test]
  fn lean_frames_restore_context_and_keep_successful_children() {
    let good = LeanExpr::sort(Level::zero());
    let bad = frame_binder(0, good.clone(), LeanExpr::fvar(mk_name("bad")));
    let key = |e: &LeanExpr| (*e.get_hash(), param_names_hash(&[]));
    for kind in 0..3 {
      for failure in 0..3 {
        let mut kenv = KEnv::<Meta>::new();
        let prefix = vec![mk_name("outer")];
        let mut binders = prefix.clone();
        let dom = if failure == 0 { bad.clone() } else { good.clone() };
        let body =
          if failure == 1 { bad.clone() } else { LeanExpr::bvar(n_lit(0)) };
        let e = frame_binder(kind, dom, body);
        let result = cached_for_frames(&e, &mut binders, &mut kenv);
        assert_eq!(binders, prefix);
        if failure < 2 {
          assert_eq!(
            result.unwrap_err(),
            "unexpected FVar(bad) in elaborated kernel term during ingress"
          );
          assert!(kenv.ingress_cache.contains_key(&key(&good)));
          assert!(!kenv.ingress_cache.contains_key(&key(&e)));
          assert!(!kenv.ingress_cache.contains_key(&key(&bad)));
        } else {
          let k = result.unwrap();
          let body = match k.data() {
            ExprData::Lam(n, bi, _, _, b, _)
            | ExprData::All(n, bi, _, _, _, b, _) => {
              assert_eq!(n, &mk_name("inner"));
              assert_eq!(bi, &BinderInfo::Implicit);
              b
            },
            ExprData::Let(n, _, _, b, nd, _) => {
              assert_eq!(n, &mk_name("inner"));
              assert!(nd.non_dep);
              b
            },
            _ => panic!("expected binder"),
          };
          assert!(
            matches!(body.data(), ExprData::Var(0, n, _) if n == &mk_name("inner"))
          );
        }
      }
    }
    let mut binders = vec![mk_name("outer"), mk_name("middle")];
    let prefix = binders.clone();
    let e = LeanExpr::letE(
      mk_name("inner"),
      LeanExpr::bvar(n_lit(1)),
      LeanExpr::bvar(n_lit(0)),
      LeanExpr::bvar(n_lit(2)),
      true,
    );
    let k = cached_for_frames(&e, &mut binders, &mut KEnv::new()).unwrap();
    assert_eq!(binders, prefix);
    let ExprData::Let(_, ty, val, body, _, _) = k.data() else { panic!() };
    for (e, expected) in [(ty, "outer"), (val, "middle"), (body, "outer")] {
      assert!(
        matches!(e.data(), ExprData::Var(_, n, _) if n == &mk_name(expected))
      );
    }
    assert!(
      ty.addr() < val.addr()
        && val.addr() < body.addr()
        && body.addr() < k.addr()
    );
  }

  #[test]
  fn lean_frames_metadata_cache_and_allocation_order() {
    let layer = |s| vec![(mk_name(s), env::DataValue::OfBool(true))];
    let child = LeanExpr::mdata(
      layer("child"),
      LeanExpr::lit(env::Literal::NatVal(n_lit(42))),
    );
    let core =
      LeanExpr::app(child, LeanExpr::lit(env::Literal::StrVal("tail".into())));
    let inner = LeanExpr::mdata(layer("inner"), core.clone());
    let e = LeanExpr::mdata(layer("outer"), inner.clone());
    let mut kenv = KEnv::new();
    let mut binders = vec![];
    let k = cached_for_frames(&e, &mut binders, &mut kenv).unwrap();
    assert_eq!(k.mdata(), &vec![layer("outer"), layer("inner")]);
    let ExprData::App(f, a, _) = k.data() else { panic!() };
    assert_eq!(f.mdata(), &vec![layer("child")]);
    assert!(matches!(f.data(), ExprData::Nat(n, _, _) if n == &n_lit(42)));
    assert!(matches!(a.data(), ExprData::Str(s, _, _) if s == "tail"));
    assert!(f.addr() < a.addr() && a.addr() < k.addr());
    let key = |e: &LeanExpr| (*e.get_hash(), param_names_hash(&[]));
    assert_eq!(kenv.ingress_cache.len(), 3);
    assert!(!kenv.ingress_cache.contains_key(&key(&core)));
    assert!(!kenv.ingress_cache.contains_key(&key(&inner)));
    assert!(k.ptr_eq(&cached_for_frames(&e, &mut binders, &mut kenv).unwrap()));
    assert_eq!(kenv.ingress_cache.len(), 3);
    let var = LeanExpr::bvar(n_lit(0));
    binders.push(mk_name("first"));
    let first = cached_for_frames(&var, &mut binders, &mut kenv).unwrap();
    binders[0] = mk_name("second");
    let second = cached_for_frames(&var, &mut binders, &mut kenv).unwrap();
    assert!(first.ptr_eq(&second));
    assert!(
      matches!(second.data(), ExprData::Var(0, n, _) if n == &mk_name("first"))
    );
    assert_eq!(binders, vec![mk_name("second")]);
  }

  #[test]
  fn lean_frames_error_precedence() {
    let first = LeanExpr::fvar(mk_name("first"));
    let second = LeanExpr::fvar(mk_name("second"));
    let let_e =
      |ty, val, body| LeanExpr::letE(mk_name("x"), ty, val, body, false);
    for e in [
      LeanExpr::app(first.clone(), second.clone()),
      let_e(first.clone(), second.clone(), second.clone()),
      let_e(LeanExpr::sort(Level::zero()), first.clone(), second),
      LeanExpr::proj(mk_name("Prod"), past_u64(), first),
    ] {
      assert_eq!(
        try_ingress(&e, &[]).unwrap_err(),
        "unexpected FVar(first) in elaborated kernel term during ingress"
      );
    }
  }

  #[test]
  fn lean_frames_deep_bodies_and_staged_teardown() {
    for kind in 0..3 {
      let mut e = LeanExpr::bvar(n_lit(0));
      for _ in 0..500 {
        e = match kind {
          0 => frame_binder(0, LeanExpr::sort(Level::zero()), e),
          1 => frame_binder(2, LeanExpr::sort(Level::zero()), e),
          _ => LeanExpr::proj(mk_name("Prod"), n_lit(0), e),
        };
      }
      let mut kenv = KEnv::new();
      let k = cached_for_frames(&e, &mut vec![], &mut kenv).unwrap();
      drop(k);
      drop(kenv);
      while let LeanExprData::Lam(_, _, b, _, _)
      | LeanExprData::LetE(_, _, _, b, _, _)
      | LeanExprData::Proj(_, _, b, _) = e.as_data()
      {
        let next = b.clone();
        drop(e);
        e = next;
      }
      drop(e);
    }
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
      ixon::env::Named::with_addr(list_addr.clone()),
    );

    let (name_map, addr_map) = build_ingress_lookups(&ie);
    assert_eq!(name_map.get(&nat_addr), Some(&nat_name));
    assert_eq!(addr_map.get(&list_name), Some(&list_addr));
  }

  // ---- Anon-mode determinism ----

  #[test]
  fn anon_proj_addrs_are_deterministic() {
    let block = Address::hash(b"test-block-deterministic");
    // Same inputs → same outputs.
    assert_eq!(anon_defn_proj_addr(&block, 0), anon_defn_proj_addr(&block, 0));
    assert_eq!(anon_indc_proj_addr(&block, 1), anon_indc_proj_addr(&block, 1));
    assert_eq!(anon_recr_proj_addr(&block, 2), anon_recr_proj_addr(&block, 2));
    assert_eq!(
      anon_ctor_proj_addr(&block, 3, 4),
      anon_ctor_proj_addr(&block, 3, 4)
    );
    // Different inputs → different outputs (catches accidental aliasing).
    assert_ne!(anon_defn_proj_addr(&block, 0), anon_defn_proj_addr(&block, 1));
    assert_ne!(anon_defn_proj_addr(&block, 0), anon_indc_proj_addr(&block, 0));
    assert_ne!(
      anon_ctor_proj_addr(&block, 0, 0),
      anon_ctor_proj_addr(&block, 0, 1)
    );
    assert_ne!(
      anon_ctor_proj_addr(&block, 0, 0),
      anon_ctor_proj_addr(&block, 1, 0)
    );
  }

  #[test]
  fn anon_proj_addr_matches_constant_commit() {
    // The helper must agree with the explicit `Constant::commit` over
    // the synthesized projection — that's the contract the rest of the
    // anon pipeline depends on (verifying the computed address against
    // the address actually stored in `env.consts`).
    use ixon::constant::{
      Constant, ConstantInfo, ConstructorProj, DefinitionProj, InductiveProj,
      RecursorProj,
    };
    let b = Address::hash(b"another-block");
    let (defn_addr, _) = Constant::new(ConstantInfo::DPrj(DefinitionProj {
      idx: 5,
      block: b.clone(),
    }))
    .commit();
    assert_eq!(defn_addr, anon_defn_proj_addr(&b, 5));
    let (indc_addr, _) = Constant::new(ConstantInfo::IPrj(InductiveProj {
      idx: 7,
      block: b.clone(),
    }))
    .commit();
    assert_eq!(indc_addr, anon_indc_proj_addr(&b, 7));
    let (recr_addr, _) = Constant::new(ConstantInfo::RPrj(RecursorProj {
      idx: 9,
      block: b.clone(),
    }))
    .commit();
    assert_eq!(recr_addr, anon_recr_proj_addr(&b, 9));
    let (ctor_addr, _) = Constant::new(ConstantInfo::CPrj(ConstructorProj {
      idx: 2,
      cidx: 3,
      block: b.clone(),
    }))
    .commit();
    assert_eq!(ctor_addr, anon_ctor_proj_addr(&b, 2, 3));
  }
}
