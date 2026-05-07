//! TypeChecker struct and core helpers.
//!
//! The TypeChecker is a lightweight handle for type-checking against one
//! worker-owned `KEnv`.
//!
//! WHNF, type inference, def-eq, and constant checking are in separate modules
//! that add `impl TypeChecker` blocks.

use std::sync::LazyLock;

use rustc_hash::FxHashMap;
use rustc_hash::FxHashSet;

use crate::ix::address::Address;
use crate::ix::ixon::env::Env as IxonEnv;

use super::constant::{KConst, RecRule};
use super::env::{Addr, KEnv};
use super::equiv::EquivManager;
use super::error::{TcError, u64_to_usize};
use super::expr::{ExprData, FVarId, KExpr};
use super::id::KId;
use super::ingress::{
  IxonIngressLookups, ingress_addr_shallow_into_kenv_with_lookups,
};
use super::lctx::LocalDecl;
use super::level::{KUniv, UnivData};
use super::mode::KernelMode;
use super::primitive::Primitives;
use super::subst::{instantiate_rev, lift};

/// Content-addressed context identity for the empty context (no bindings).
pub fn empty_ctx_addr() -> Addr {
  use std::sync::LazyLock;
  static ADDR: LazyLock<Addr> =
    LazyLock::new(|| blake3::hash(b"ix.kernel.ctx.empty"));
  *ADDR
}

/// Maximum iterations in the WHNF delta loop (local per-call).
pub const MAX_WHNF_FUEL: u32 = 10_000;

/// Maximum recursion depth for `is_def_eq`.
pub const MAX_DEF_EQ_DEPTH: u32 = 2_000;

/// Shared recursive fuel budget, consumed by each call to whnf/infer/isDefEq.
/// lean4lean uses 10,000 with step-indexed recursion; the lean4 C++ kernel
/// uses ~200,000 heartbeats. We use a higher budget than both because this
/// kernel lacks compiled native reduction and checks some large proof terms
/// by interpreting their full expression trees. In particular, BVDecide's
/// generated mutual proofs can legitimately exceed one million recursive
/// kernel steps even after cache hits stop consuming fuel.
///
/// Mathlib-scale category/algebra proof terms also exceed the old 1.5M budget
/// without hitting the actual `MAX_DEF_EQ_DEPTH` guard. Keep this high enough
/// for legitimate large proofs while retaining the `IX_MAX_REC_FUEL` override
/// for bisecting suspected loops.
pub const MAX_REC_FUEL: u64 = 10_000_000;

static IX_MAX_REC_FUEL: LazyLock<Option<u64>> = LazyLock::new(|| {
  std::env::var("IX_MAX_REC_FUEL").ok().and_then(|s| s.parse().ok())
});

static IX_HOT_MISSES: LazyLock<bool> =
  LazyLock::new(|| std::env::var("IX_HOT_MISSES").is_ok());

static IX_HOT_MISS_CTX: LazyLock<bool> =
  LazyLock::new(|| std::env::var("IX_HOT_MISS_CTX").is_ok());

pub fn max_rec_fuel() -> u64 {
  (*IX_MAX_REC_FUEL).unwrap_or(MAX_REC_FUEL)
}

/// Temporary struct for recursor info during iota reduction,
/// avoiding borrow conflicts with `&self.env`.
pub struct IotaInfo<M: KernelMode> {
  pub k: bool,
  pub params: usize,
  pub motives: usize,
  pub minors: usize,
  pub indices: usize,
  pub major_idx: usize,
  pub rules: Vec<RecRule<M>>,
  pub lvls: u64,
}

pub struct LazyIxonIngress<'a> {
  ixon_env: &'a IxonEnv,
  lookups: &'a IxonIngressLookups,
  faulted_addrs: FxHashSet<Address>,
}

/// Thread-local type-checking handle. Cheap to create — only allocates empty
/// vectors and counters. Kernel state lives in the borrowed worker `KEnv`.
pub struct TypeChecker<'a, M: KernelMode> {
  /// Worker-owned kernel environment (constants, caches, intern table).
  pub env: &'a mut KEnv<M>,
  /// Optional read-only Ixon source used to fault constants into `env` when
  /// typechecking discovers a missing address.
  lazy_ixon: Option<LazyIxonIngress<'a>>,
  /// Primitive constant KIds. Copied from `env.prims()` at construction;
  /// overridable for tests via `tc.prims = custom`.
  pub prims: Primitives<M>,

  // -- Thread-local context --
  /// Local variable types, indexed by de Bruijn level.
  pub ctx: Vec<KExpr<M>>,
  /// Let-bound values, parallel to `ctx`. `Some(val)` for let-bindings, `None`
  /// for lambda/forall bindings. Used for let-variable zeta-reduction in whnf_core.
  pub let_vals: Vec<Option<KExpr<M>>>,
  /// Number of active let-bindings in `ctx`.
  pub num_let_bindings: usize,
  /// Content-addressed context identity: a blake3 hash derived from the
  /// binding-type chain. Immune to the ABA pointer-reuse problem.
  pub ctx_id: Addr,
  /// Stack of previous ctx_ids for O(1) pop.
  ctx_id_stack: Vec<Addr>,

  // -- Thread-local optimization --
  /// Union-find for transitive def-eq caching (lean4lean EquivManager).
  /// Thread-local: path halving mutates on reads, not safe to share.
  pub equiv_manager: EquivManager,

  // -- Thread-local control --
  /// When true, `infer` skips def-eq checks (arg-type and let-value validation).
  pub infer_only: bool,
  /// Re-entrancy guard for native reduction (prevents whnf → native → whnf loops).
  pub in_native_reduce: bool,
  /// Counter incremented while inside def-eq's cheap projection reductions.
  /// Used by `is_def_eq` to route cheap false negatives into a cheap-only
  /// cache while projected values are reduced structurally instead of through
  /// full WHNF.
  pub cheap_recursion_depth: u32,
  /// When true, the Bool.true fast-path in is_def_eq fires even on open terms.
  pub eager_reduce: bool,
  /// Current def-eq recursion depth.
  pub def_eq_depth: u32,
  /// Stack depth of active `IX_DEF_EQ_TRACE` outer frames. While > 0,
  /// inner def-eq tier dumps fire too. Diagnostic-only.
  pub def_eq_trace_depth: u32,
  /// Peak def-eq depth (diagnostics).
  pub def_eq_peak: u32,
  /// Shared recursive fuel remaining for this constant check.
  pub rec_fuel: u64,
  /// Optional diagnostic label for the current top-level constant.
  pub debug_label: Option<String>,
  /// Gated miss sampler for fuel-exhaustion diagnostics. Populated only when
  /// `IX_HOT_MISSES=1`, keyed by a compact phase/head/lbr shape.
  hot_misses: FxHashMap<String, u64>,

  /// Memoization cache for [`Self::ctx_addr_for_lbr`].
  ///
  /// `ctx_addr_for_lbr(lbr)` is a pure function of `(self.ctx_id, lbr)`:
  /// the function walks `self.ctx` from a depth-derived start, runs a
  /// fixpoint over loose-bound-variable closures, and finalizes a blake3
  /// hash of the suffix. With millions of cache probes per big mathlib
  /// block (each `whnf_key` / `infer_key` / `def_eq_ctx_key` triggers
  /// one), this dominates lookup overhead. Memoizing on `(ctx_id, lbr)`
  /// is sound because two contexts sharing the same `ctx_id` are bytewise
  /// equal in the suffix-relevant prefix (`ctx_id` content-addresses the
  /// full context). The cache lifetime is the `TypeChecker` (one per
  /// `check_const`), so it is automatically reclaimed.
  ctx_addr_cache: FxHashMap<(Addr, u64), Addr>,

  // -- Free-variable infrastructure --
  /// Local context for fvar-based binder opening. Some validation paths still
  /// use the legacy `ctx`/`let_vals` stack, so `depth()` accounts for both
  /// during the transition.
  pub lctx: super::lctx::LocalContext<M>,
}

impl<'a, M: KernelMode> TypeChecker<'a, M> {
  pub fn new(env: &'a mut KEnv<M>) -> Self {
    let prims = env.prims().clone();
    TypeChecker {
      env,
      lazy_ixon: None,
      prims,
      ctx: Vec::new(),
      let_vals: Vec::new(),
      num_let_bindings: 0,
      ctx_id: empty_ctx_addr(),
      ctx_id_stack: Vec::new(),
      equiv_manager: EquivManager::new(),
      infer_only: false,
      in_native_reduce: false,
      cheap_recursion_depth: 0,
      eager_reduce: false,
      def_eq_depth: 0,
      def_eq_trace_depth: 0,
      def_eq_peak: 0,
      rec_fuel: max_rec_fuel(),
      debug_label: None,
      hot_misses: FxHashMap::default(),
      ctx_addr_cache: FxHashMap::default(),
      lctx: super::lctx::LocalContext::new(),
    }
  }

  pub fn new_with_lazy_ixon(
    env: &'a mut KEnv<M>,
    ixon_env: &'a IxonEnv,
    lookups: &'a IxonIngressLookups,
  ) -> Self {
    if !env.has_prims() {
      let prims = Primitives::from_addr_names(|addr| {
        lookups.name_for_addr(addr).cloned()
      });
      let _ = env.set_prims(prims);
    }
    let mut tc = Self::new(env);
    tc.lazy_ixon = Some(LazyIxonIngress {
      ixon_env,
      lookups,
      faulted_addrs: FxHashSet::default(),
    });
    tc
  }

  pub fn try_get_const(
    &mut self,
    id: &KId<M>,
  ) -> Result<Option<KConst<M>>, TcError<M>> {
    if let Some(c) = self.env.get(id) {
      return Ok(Some(c));
    }
    let lazy_enabled = self.lazy_ixon.is_some();
    self.lazy_ingress_addr(&id.addr)?;
    match self.env.get(id) {
      Some(c) => Ok(Some(c)),
      None if lazy_enabled => Err(TcError::UnknownConst(id.addr.clone())),
      None => Ok(None),
    }
  }

  pub fn get_const(&mut self, id: &KId<M>) -> Result<KConst<M>, TcError<M>> {
    self
      .try_get_const(id)?
      .ok_or_else(|| TcError::UnknownConst(id.addr.clone()))
  }

  pub fn has_const(&mut self, id: &KId<M>) -> Result<bool, TcError<M>> {
    Ok(self.try_get_const(id)?.is_some())
  }

  pub fn try_get_block(
    &mut self,
    id: &KId<M>,
  ) -> Result<Option<Vec<KId<M>>>, TcError<M>> {
    if let Some(members) = self.env.get_block(id) {
      return Ok(Some(members));
    }
    self.lazy_ingress_addr(&id.addr)?;
    Ok(self.env.get_block(id))
  }

  fn lazy_ingress_addr(&mut self, addr: &Address) -> Result<(), TcError<M>> {
    let Some(lazy) = self.lazy_ixon.as_mut() else {
      return Ok(());
    };
    if !lazy.faulted_addrs.insert(addr.clone()) {
      return Ok(());
    }
    ingress_addr_shallow_into_kenv_with_lookups(
      self.env,
      lazy.ixon_env,
      lazy.lookups,
      addr,
    )
    .map(|_| ())
    .map_err(|msg| {
      TcError::Other(format!("lazy ingress {}: {msg}", addr.hex()))
    })
  }

  // -----------------------------------------------------------------------
  // Context management
  // -----------------------------------------------------------------------

  /// Current logical binding depth.
  ///
  /// During the FVar transition, some code pushes legacy de-Bruijn locals into
  /// `ctx` while newer code opens binders into `lctx`. Most paths use one or
  /// the other, but mixed validation code can observe both; the logical depth
  /// is the sum of the two stacks.
  pub fn depth(&self) -> u64 {
    (self.ctx.len() + self.lctx.len()) as u64
  }

  /// WHNF cache key: (expr_hash, ctx_hash).
  ///
  /// Uses the same suffix-aware key shape as [`infer_key`]: closed expressions
  /// (lbr == 0) collapse to the empty context hash, and open expressions use
  /// `ctx_addr_for_lbr(e.lbr())` to capture only the context suffix reachable
  /// from the term's loose bound variables.
  ///
  /// Soundness: WHNF only consults the local context in three places, and
  /// each is bounded by `e.lbr()`:
  /// (1) let-zeta: `Var(i)` reduction looks up `let_vals[level]` for `i < e.lbr`
  ///     — frames `≥ depth - e.lbr` are covered by the suffix and `ctx_addr_for_lbr`
  ///     transitively closes over their types and values;
  /// (2) recursive `infer` from `try_struct_eta_iota` / `synth_ctor_when_k` /
  ///     `try_proof_irrel` — those callees use their argument's own lbr, which
  ///     is `≤ e.lbr`, so the WHNF suffix dominates;
  /// (3) native reduction body unfold — closed body, no context dependence.
  ///
  /// Sharing two distinct outer contexts that share a relevant suffix is the
  /// payoff: the same WHNF subterm can hit cache across them.
  #[inline]
  pub fn whnf_key(&mut self, e: &KExpr<M>) -> (Addr, Addr) {
    (e.hash_key(), self.ctx_addr_for_lbr(e.lbr()))
  }

  /// Type-inference cache key: (expr_hash, ctx_hash).
  /// Closed expressions (lbr == 0) are context-independent. For open
  /// expressions, only the context suffix reachable from their loose bound
  /// variables matters. The suffix length is closed over binder type/value
  /// dependencies, so two equal open subterms can share an infer result across
  /// different outer binders when the relevant local suffix is identical.
  #[inline]
  pub fn infer_key(&mut self, e: &KExpr<M>) -> (Addr, Addr) {
    (e.hash_key(), self.ctx_addr_for_lbr(e.lbr()))
  }

  /// Context key for a definitional-equality pair.
  ///
  /// Def-eq may inspect both sides through WHNF, inference, proof
  /// irrelevance, eta, and structural recursion. All of those operations are
  /// bounded by the loose-bound-variable range reachable from the compared
  /// expressions, so the relevant context is the suffix needed by the larger
  /// `lbr`.
  #[inline]
  pub fn def_eq_ctx_key(&mut self, a: &KExpr<M>, b: &KExpr<M>) -> Addr {
    self.ctx_addr_for_lbr(a.lbr().max(b.lbr()))
  }

  pub(crate) fn ctx_addr_for_lbr(&mut self, lbr: u64) -> Addr {
    if lbr == 0 || self.ctx.is_empty() {
      return empty_ctx_addr();
    }

    // Memoize on (ctx_id, lbr) — the result is a pure function of these
    // two inputs (ctx_id content-addresses the suffix-relevant prefix of
    // self.ctx). Hot path on big mathlib blocks; called once per
    // whnf_key / infer_key / def_eq_ctx_key.
    let cache_key = (self.ctx_id, lbr);
    if let Some(cached) = self.ctx_addr_cache.get(&cache_key) {
      return *cached;
    }

    let n = self.ctx.len();
    let mut need = usize::try_from(lbr).unwrap_or(usize::MAX).min(n);

    loop {
      let start = n - need;
      let mut next_need = need;
      for i in start..n {
        let frame_offset = n - i;
        let ty_need = usize::try_from(self.ctx[i].lbr()).unwrap_or(usize::MAX);
        next_need = next_need.max(frame_offset.saturating_add(ty_need));
        if let Some(val) = &self.let_vals[i] {
          let val_need = usize::try_from(val.lbr()).unwrap_or(usize::MAX);
          next_need = next_need.max(frame_offset.saturating_add(val_need));
        }
      }
      next_need = next_need.min(n);
      if next_need == need {
        break;
      }
      need = next_need;
    }

    let result = if need == n {
      self.ctx_id
    } else {
      let mut h = blake3::Hasher::new();
      h.update(b"ctx.suffix");
      h.update(&(need as u64).to_le_bytes());
      for i in (n - need)..n {
        match &self.let_vals[i] {
          Some(val) => {
            h.update(b"let");
            h.update(self.ctx[i].addr().as_bytes());
            h.update(val.addr().as_bytes());
          },
          None => {
            h.update(b"local");
            h.update(self.ctx[i].addr().as_bytes());
          },
        }
      }
      h.finalize()
    };

    self.ctx_addr_cache.insert(cache_key, result);
    result
  }

  /// Push a local variable type (lambda/forall binding, no let-value).
  pub fn push_local(&mut self, ty: KExpr<M>) {
    let mut h = blake3::Hasher::new();
    h.update(b"ctx.local");
    h.update(ty.addr().as_bytes());
    h.update(self.ctx_id.as_bytes());
    self.ctx_id_stack.push(self.ctx_id);
    self.ctx_id = h.finalize();
    self.ctx.push(ty);
    self.let_vals.push(None);
  }

  /// Push a let-bound variable (type + value). WHNF will zeta-reduce references
  /// to this variable by substituting the value (lean4lean withExtendedLetCtx).
  pub fn push_let(&mut self, ty: KExpr<M>, val: KExpr<M>) {
    let mut h = blake3::Hasher::new();
    h.update(b"ctx.let");
    h.update(ty.addr().as_bytes());
    h.update(val.addr().as_bytes());
    h.update(self.ctx_id.as_bytes());
    self.ctx_id_stack.push(self.ctx_id);
    self.ctx_id = h.finalize();
    self.ctx.push(ty);
    self.let_vals.push(Some(val));
    self.num_let_bindings += 1;
  }

  pub fn fresh_fvar_id(&mut self) -> FVarId {
    self.env.fresh_fvar_id()
  }

  /// Pop the most recent local variable.
  pub fn pop_local(&mut self) {
    if let Some(Some(_)) = self.let_vals.pop() {
      self.num_let_bindings -= 1;
    }
    self.ctx.pop();
    self.ctx_id = self.ctx_id_stack.pop().unwrap_or_else(empty_ctx_addr);
  }

  /// Look up a let-bound variable's value, lifted to the current depth.
  /// Returns None if the variable is lambda/forall-bound (not a let).
  pub fn lookup_let_val(&mut self, idx: u64) -> Option<KExpr<M>> {
    let n = self.ctx.len();
    let idx_us = usize::try_from(idx).ok()?;
    if idx_us >= n {
      return None;
    }
    let level = n - 1 - idx_us;
    let val = self.let_vals[level].as_ref()?.clone();
    Some(lift(&mut self.env.intern, &val, idx + 1, 0))
  }

  /// Whether a de-Bruijn variable points at a let-bound local.
  pub fn is_let_var(&self, idx: u64) -> bool {
    let n = self.ctx.len();
    let Some(idx_us) = usize::try_from(idx).ok() else {
      return false;
    };
    if idx_us >= n {
      return false;
    }
    let level = n - 1 - idx_us;
    self.let_vals[level].is_some()
  }

  /// Save current depth for later restore.
  pub fn save_depth(&self) -> usize {
    self.ctx.len()
  }

  /// Restore context to a previously saved depth.
  pub fn restore_depth(&mut self, saved: usize) {
    while self.ctx.len() > saved {
      self.pop_local();
    }
  }

  // -----------------------------------------------------------------------
  // Free-variable binder opening helpers
  // -----------------------------------------------------------------------

  /// Open a binder by minting a fresh [`FVarId`], pushing a `CDecl` to
  /// `lctx`, and instantiating `body` so its `Var(0)` becomes the new
  /// fvar (with `Var(>=1)` shifting down). Returns the opened body and
  /// the fresh fvar id (the caller may pass `_` to discard).
  ///
  /// Mirrors lean4lean's `withLocalDecl` in shape; differs in that the
  /// caller is responsible for `lctx.truncate(saved_len)` when leaving
  /// the binder scope.
  pub fn open_binder(
    &mut self,
    name: M::MField<crate::ix::env::Name>,
    bi: M::MField<crate::ix::env::BinderInfo>,
    ty: KExpr<M>,
    body: &KExpr<M>,
  ) -> (KExpr<M>, FVarId) {
    let fv_id = self.fresh_fvar_id();
    let fv = self.intern(KExpr::fvar(fv_id, name.clone()));
    self.lctx.push(fv_id, LocalDecl::CDecl { name, bi, ty });
    let body_open = instantiate_rev(&mut self.env.intern, body, &[fv]);
    (body_open, fv_id)
  }

  /// Anonymous variant of [`Self::open_binder`] that uses
  /// `Name::anon()` / `BinderInfo::Default`. Convenient for kernel-internal
  /// walks (inductive validation, recursor synthesis) that don't carry
  /// user-visible binder metadata.
  pub fn open_binder_anon(
    &mut self,
    ty: KExpr<M>,
    body: &KExpr<M>,
  ) -> (KExpr<M>, FVarId) {
    let name = M::meta_field(crate::ix::env::Name::anon());
    let bi = M::meta_field(crate::ix::env::BinderInfo::Default);
    self.open_binder(name, bi, ty, body)
  }

  /// Like [`Self::open_binder`] but also returns the fvar `KExpr` itself
  /// (for callers that need to record it in a Vec for later
  /// abstract_fvars / structural identity comparisons).
  pub fn open_binder_with_fv(
    &mut self,
    name: M::MField<crate::ix::env::Name>,
    bi: M::MField<crate::ix::env::BinderInfo>,
    ty: KExpr<M>,
    body: &KExpr<M>,
  ) -> (KExpr<M>, KExpr<M>, FVarId) {
    let fv_id = self.fresh_fvar_id();
    let fv = self.intern(KExpr::fvar(fv_id, name.clone()));
    self.lctx.push(fv_id, LocalDecl::CDecl { name, bi, ty });
    let body_open =
      instantiate_rev(&mut self.env.intern, body, std::slice::from_ref(&fv));
    (body_open, fv, fv_id)
  }

  /// Anonymous-name variant of [`Self::open_binder_with_fv`].
  pub fn open_binder_anon_with_fv(
    &mut self,
    ty: KExpr<M>,
    body: &KExpr<M>,
  ) -> (KExpr<M>, KExpr<M>, FVarId) {
    let name = M::meta_field(crate::ix::env::Name::anon());
    let bi = M::meta_field(crate::ix::env::BinderInfo::Default);
    self.open_binder_with_fv(name, bi, ty, body)
  }

  /// Push an `LDecl` for a let-bound fvar and instantiate the body. Returns
  /// the opened body and the fresh fvar id. Mirrors `withLetDecl`-shaped
  /// flows (e.g. inductive validation that needs to model the let value
  /// for downstream WHNF zeta-reduction).
  pub fn open_let(
    &mut self,
    name: M::MField<crate::ix::env::Name>,
    ty: KExpr<M>,
    val: KExpr<M>,
    body: &KExpr<M>,
  ) -> (KExpr<M>, FVarId) {
    let fv_id = self.fresh_fvar_id();
    let fv = self.intern(KExpr::fvar(fv_id, name.clone()));
    self.lctx.push(fv_id, LocalDecl::LDecl { name, ty, val });
    let body_open = instantiate_rev(&mut self.env.intern, body, &[fv]);
    (body_open, fv_id)
  }

  /// Push a fresh fvar declaration without any body to instantiate.
  /// Useful for paths that introduce a binder for type-tracking purposes
  /// only (e.g. inductive validation walks where the binder is consumed
  /// later or in parallel). Returns the fvar id and the interned fvar
  /// expression.
  pub fn push_fvar_decl_anon(&mut self, ty: KExpr<M>) -> (FVarId, KExpr<M>) {
    let name = M::meta_field(crate::ix::env::Name::anon());
    let bi = M::meta_field(crate::ix::env::BinderInfo::Default);
    let fv_id = self.fresh_fvar_id();
    let fv = self.intern(KExpr::fvar(fv_id, name.clone()));
    self.lctx.push(fv_id, LocalDecl::CDecl { name, bi, ty });
    (fv_id, fv)
  }

  /// Look up a bound variable's type, lifted to the current depth.
  pub fn lookup_var(&mut self, idx: u64) -> Result<KExpr<M>, TcError<M>> {
    let n = self.ctx.len();
    let idx_us = u64_to_usize::<M>(idx)?;
    if idx_us >= n {
      return Err(TcError::VarOutOfRange { idx, ctx_len: n });
    }
    let level = n - 1 - idx_us;
    let ty = self.ctx[level].clone();
    Ok(lift(&mut self.env.intern, &ty, idx + 1, 0))
  }

  // -----------------------------------------------------------------------
  // Universe helpers
  // -----------------------------------------------------------------------

  /// WHNF, then ensure it's a Sort. Returns the universe level.
  pub fn ensure_sort(&mut self, e: &KExpr<M>) -> Result<KUniv<M>, TcError<M>> {
    // Fast path: already a Sort, skip WHNF + tick.
    if let ExprData::Sort(u, _) = e.data() {
      return Ok(u.clone());
    }
    let w = self.whnf(e)?;
    match w.data() {
      ExprData::Sort(u, _) => Ok(u.clone()),
      _ => Err(TcError::TypeExpected),
    }
  }

  /// WHNF, then ensure it's a forall (All). Returns (domain, codomain).
  pub fn ensure_forall(
    &mut self,
    e: &KExpr<M>,
  ) -> Result<(KExpr<M>, KExpr<M>), TcError<M>> {
    // Fast path: already a forall, skip WHNF + tick.
    if let ExprData::All(_, _, a, b, _) = e.data() {
      return Ok((a.clone(), b.clone()));
    }
    let w = self.whnf(e)?;
    match w.data() {
      ExprData::All(_, _, a, b, _) => Ok((a.clone(), b.clone())),
      _ => Err(TcError::FunExpected { e: e.clone(), whnf: w }),
    }
  }

  /// Substitute universe parameters: replace `Param(i)` with `us[i]`.
  ///
  /// Returns `Err(UnivParamOutOfRange)` if any interior `Param(i)` has
  /// `i >= us.len()`. Callers are expected to have validated the universe
  /// arity upstream (e.g. `infer` of a `Const` node — see
  /// `src/ix/kernel/infer.rs:41`); the `Result` here is defense-in-depth
  /// against code paths that reach substitution without that check.
  pub fn instantiate_univ_params(
    &mut self,
    e: &KExpr<M>,
    us: &[KUniv<M>],
  ) -> Result<KExpr<M>, TcError<M>> {
    if us.is_empty() {
      return Ok(e.clone());
    }
    // Per-call pointer-identity memoization: universe substitution does
    // not change the term's bound-variable structure, so two sub-terms
    // with the same content hash produce the same result for the same
    // `us`. Shared sub-terms in a body (common under hash-consing) get
    // visited once per call. See `src/ix/kernel/subst.rs` for the
    // analogous optimisation on de-Bruijn substitution and the general
    // "walk the DAG as a DAG" rationale.
    let mut cache: FxHashMap<Addr, KExpr<M>> = FxHashMap::default();
    self.inst_univ_inner(e, us, &mut cache)
  }

  fn inst_univ_inner(
    &mut self,
    e: &KExpr<M>,
    us: &[KUniv<M>],
    cache: &mut FxHashMap<Addr, KExpr<M>>,
  ) -> Result<KExpr<M>, TcError<M>> {
    // Key by content hash only — `us` is fixed across the whole call.
    let key = e.hash_key();
    if let Some(cached) = cache.get(&key) {
      return Ok(cached.clone());
    }

    let result = match e.data() {
      ExprData::Var(..)
      | ExprData::FVar(..)
      | ExprData::Nat(..)
      | ExprData::Str(..) => {
        // These have no universe parameters, so substitution is a no-op.
        // Cache the pass-through so the ptr-identity check above fires
        // for subsequent visits to the same sub-term.
        let r = e.clone();
        cache.insert(key, r.clone());
        return Ok(r);
      },

      ExprData::Sort(u, _) => {
        let u2 = self.subst_univ(u, us)?;
        KExpr::sort(u2)
      },

      ExprData::Const(id, cur_us, _) => {
        let new_us: Box<[KUniv<M>]> = cur_us
          .iter()
          .map(|u| self.subst_univ(u, us))
          .collect::<Result<Box<[_]>, _>>()?;
        KExpr::cnst(id.clone(), new_us)
      },

      ExprData::App(f, a, _) => {
        let f2 = self.inst_univ_inner(f, us, cache)?;
        let a2 = self.inst_univ_inner(a, us, cache)?;
        KExpr::app(f2, a2)
      },

      ExprData::Lam(name, bi, ty, body, _) => {
        let ty2 = self.inst_univ_inner(ty, us, cache)?;
        let body2 = self.inst_univ_inner(body, us, cache)?;
        KExpr::lam(name.clone(), bi.clone(), ty2, body2)
      },

      ExprData::All(name, bi, ty, body, _) => {
        let ty2 = self.inst_univ_inner(ty, us, cache)?;
        let body2 = self.inst_univ_inner(body, us, cache)?;
        KExpr::all(name.clone(), bi.clone(), ty2, body2)
      },

      ExprData::Let(name, ty, val, body, nd, _) => {
        let ty2 = self.inst_univ_inner(ty, us, cache)?;
        let val2 = self.inst_univ_inner(val, us, cache)?;
        let body2 = self.inst_univ_inner(body, us, cache)?;
        KExpr::let_(name.clone(), ty2, val2, body2, *nd)
      },

      ExprData::Prj(id, field, val, _) => {
        let val2 = self.inst_univ_inner(val, us, cache)?;
        KExpr::prj(id.clone(), *field, val2)
      },
    };
    let interned = self.env.intern.intern_expr(result);
    cache.insert(key, interned.clone());
    Ok(interned)
  }

  /// Substitute universe params in a universe level.
  ///
  /// Fails with `UnivParamOutOfRange { idx, bound }` if an interior
  /// `Param(idx)` references beyond `us.len()`. In a well-typed kernel
  /// run, every call site supplies `us` whose length matches the
  /// arity of the enclosing constant (validated by `infer` at the Const
  /// gate), so this error never fires on well-formed input. It exists
  /// to turn any internal invariant slip into a loud failure instead of
  /// a silent orphan `Param` propagating downstream.
  pub fn subst_univ(
    &mut self,
    u: &KUniv<M>,
    us: &[KUniv<M>],
  ) -> Result<KUniv<M>, TcError<M>> {
    match u.data() {
      UnivData::Zero(_) => Ok(u.clone()),
      UnivData::Param(i, _, _) => {
        match usize::try_from(*i).ok().and_then(|i| us.get(i)) {
          Some(v) => Ok(v.clone()),
          None => {
            Err(TcError::UnivParamOutOfRange { idx: *i, bound: us.len() })
          },
        }
      },
      UnivData::Succ(inner, _) => {
        let inner2 = self.subst_univ(inner, us)?;
        Ok(KUniv::succ(inner2))
      },
      UnivData::Max(a, b, _) => {
        let a2 = self.subst_univ(a, us)?;
        let b2 = self.subst_univ(b, us)?;
        Ok(KUniv::max(a2, b2))
      },
      UnivData::IMax(a, b, _) => {
        let a2 = self.subst_univ(a, us)?;
        let b2 = self.subst_univ(b, us)?;
        Ok(KUniv::imax(a2, b2))
      },
    }
  }

  // -----------------------------------------------------------------------
  // Per-constant reset (thread-local state only)
  // -----------------------------------------------------------------------

  /// Reset thread-local state between constants. Global caches in `KEnv` are
  /// NOT cleared — they grow monotonically and are shared across all TCs.
  pub fn reset(&mut self) {
    self.ctx.clear();
    self.let_vals.clear();
    self.num_let_bindings = 0;
    self.ctx_id = empty_ctx_addr();
    self.ctx_id_stack.clear();
    self.equiv_manager.clear();
    self.infer_only = false;
    self.in_native_reduce = false;
    self.cheap_recursion_depth = 0;
    self.eager_reduce = false;
    self.def_eq_depth = 0;
    self.def_eq_peak = 0;
    // Record fuel consumed by the *previous* constant check (if any) before
    // wiping it. `Drop` records the final check in a TypeChecker's lifetime.
    self.record_current_fuel_used();
    self.rec_fuel = max_rec_fuel();
    self.hot_misses.clear();
    // Reset the local context (it must always be empty between constants).
    // The fvar id counter lives on KEnv and is intentionally not reset here:
    // caches also live on KEnv, so reused fvar ids would make open-term cache
    // entries unsound across TypeChecker instances.
    self.lctx = super::lctx::LocalContext::new();
  }

  pub fn set_debug_label(&mut self, label: impl Into<String>) {
    self.debug_label = Some(label.into());
  }

  pub fn debug_label_matches_env(&self) -> bool {
    match std::env::var("IX_KERNEL_DEBUG_CONST") {
      Ok(filter) if filter.is_empty() => true,
      Ok(filter) => {
        self.debug_label.as_ref().is_some_and(|label| label.contains(&filter))
      },
      Err(_) => true,
    }
  }

  /// Consume one unit of shared recursive fuel. Returns Err if exhausted.
  #[inline]
  pub fn tick(&mut self) -> Result<(), TcError<M>> {
    if self.rec_fuel == 0 {
      if std::env::var("IX_REC_FUEL_DUMP").is_ok()
        && self.debug_label_matches_env()
      {
        eprintln!(
          "[rec fuel] exhausted const={} depth={} def_eq_depth={} infer_only={} native_reduce={} eager_reduce={}",
          self.debug_label.as_deref().unwrap_or("<unknown>"),
          self.depth(),
          self.def_eq_depth,
          self.infer_only,
          self.in_native_reduce,
          self.eager_reduce
        );
        self.dump_hot_misses();
        eprintln!("{}", std::backtrace::Backtrace::force_capture());
      }
      return Err(TcError::MaxRecFuel);
    }
    self.rec_fuel -= 1;
    Ok(())
  }

  /// Starting fuel for the current check. Used by diagnostics that want
  /// to report fuel consumed at a given point.
  pub fn fuel_used(&self) -> u64 {
    max_rec_fuel().saturating_sub(self.rec_fuel)
  }

  pub fn finish_constant_accounting(&mut self) {
    self.record_current_fuel_used();
    self.rec_fuel = max_rec_fuel();
  }

  fn record_current_fuel_used(&mut self) {
    let used = self.fuel_used();
    if used > 0 {
      self.env.perf.record_constant_fuel_used(used);
    }
  }

  // -----------------------------------------------------------------------
  // Infer-only mode
  // -----------------------------------------------------------------------

  /// Run a closure with `infer_only` mode enabled. Restores the previous
  /// mode on exit. In this mode, `infer` skips def-eq checks for App arg
  /// types and Let value types — it only synthesizes the type.
  pub fn with_infer_only<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
    let prev = self.infer_only;
    self.infer_only = true;
    let result = f(self);
    self.infer_only = prev;
    result
  }

  // -----------------------------------------------------------------------
  // Interning helper
  // -----------------------------------------------------------------------

  /// Check if expression is of the form `eagerReduce _ _` (2 args applied to the eagerReduce const).
  pub fn is_eager_reduce(&self, e: &KExpr<M>) -> bool {
    let (head, args) = collect_app_spine(e);
    if args.len() != 2 {
      return false;
    }
    match head.data() {
      ExprData::Const(id, _, _) => id.addr == self.prims.eager_reduce.addr,
      _ => false,
    }
  }

  /// Intern an expression through the mutable intern environment.
  pub fn intern(&mut self, e: KExpr<M>) -> KExpr<M> {
    self.env.intern.intern_expr(e)
  }

  /// Intern a universe through the mutable intern environment.
  pub fn intern_univ(&mut self, u: KUniv<M>) -> KUniv<M> {
    self.env.intern.intern_univ(u)
  }

  pub fn record_hot_miss(&mut self, phase: &'static str, e: &KExpr<M>) {
    if !*IX_HOT_MISSES {
      return;
    }
    let mut key = format!("{} {}", phase, hot_expr_shape(e));
    if *IX_HOT_MISS_CTX {
      let ctx = self.ctx_addr_for_lbr(e.lbr());
      key.push_str(&format!(
        " ctx={} depth={}",
        short_addr(&ctx),
        self.depth()
      ));
    }
    *self.hot_misses.entry(key).or_insert(0) += 1;
  }

  pub fn record_hot_def_eq_miss(&mut self, a: &KExpr<M>, b: &KExpr<M>) {
    if !*IX_HOT_MISSES {
      return;
    }
    let mut key =
      format!("defeq {} =?= {}", hot_expr_shape(a), hot_expr_shape(b));
    if *IX_HOT_MISS_CTX {
      let ctx = self.def_eq_ctx_key(a, b);
      key.push_str(&format!(
        " ctx={} depth={}",
        short_addr(&ctx),
        self.depth()
      ));
    }
    *self.hot_misses.entry(key).or_insert(0) += 1;
  }

  fn dump_hot_misses(&self) {
    if !*IX_HOT_MISSES || self.hot_misses.is_empty() {
      return;
    }
    let mut entries: Vec<_> = self.hot_misses.iter().collect();
    entries.sort_unstable_by(|a, b| b.1.cmp(a.1).then_with(|| a.0.cmp(b.0)));
    eprintln!("[hot misses] top {}:", entries.len().min(25));
    for (key, count) in entries.into_iter().take(25) {
      eprintln!("  {count:>8}  {key}");
    }
  }
}

// -----------------------------------------------------------------------
// Free-standing helpers
// -----------------------------------------------------------------------

/// Check whether an expression mentions a constant with the given address.
/// Iterative (stack-based) — immune to stack overflow on deeply nested input.
pub fn expr_mentions_addr<M: KernelMode>(e: &KExpr<M>, addr: &Address) -> bool {
  let mut stack: Vec<&KExpr<M>> = vec![e];
  while let Some(e) = stack.pop() {
    match e.data() {
      ExprData::Const(id, _, _) => {
        if id.addr == *addr {
          return true;
        }
      },
      ExprData::App(f, a, _) => {
        stack.push(f);
        stack.push(a);
      },
      ExprData::Lam(_, _, ty, body, _) | ExprData::All(_, _, ty, body, _) => {
        stack.push(ty);
        stack.push(body);
      },
      ExprData::Let(_, ty, val, body, _, _) => {
        stack.push(ty);
        stack.push(val);
        stack.push(body);
      },
      ExprData::Prj(id, _, val, _) => {
        if id.addr == *addr {
          return true;
        }
        stack.push(val);
      },
      ExprData::Var(..)
      | ExprData::FVar(..)
      | ExprData::Sort(..)
      | ExprData::Nat(..)
      | ExprData::Str(..) => {},
    }
  }
  false
}

/// Check whether an expression mentions any constant from a set of addresses.
pub fn expr_mentions_any_addr<M: KernelMode>(
  e: &KExpr<M>,
  addrs: &[Address],
) -> bool {
  addrs.iter().any(|a| expr_mentions_addr(e, a))
}

/// Collect the application spine: `App(App(f, a1), a2)` → `(f, [a1, a2])`.
///
/// Counts args first so the result `Vec` is allocated exactly once with
/// the correct capacity, sparing the first-push grow allocation on the
/// hot path. Most applications in mathlib have 1–8 args, so the count
/// pass is cheap (a chain walk) and saves one allocation + memcpy
/// compared to repeatedly growing from the default capacity.
pub fn collect_app_spine<M: KernelMode>(
  e: &KExpr<M>,
) -> (KExpr<M>, Vec<KExpr<M>>) {
  // First pass: count arity without cloning.
  let mut count = 0usize;
  {
    let mut cur = e;
    while let ExprData::App(f, _, _) = cur.data() {
      count += 1;
      cur = f;
    }
  }
  if count == 0 {
    return (e.clone(), Vec::new());
  }
  let mut args = Vec::with_capacity(count);
  let mut cur = e.clone();
  while let ExprData::App(f, a, _) = cur.data() {
    args.push(a.clone());
    cur = f.clone();
  }
  args.reverse();
  (cur, args)
}

fn hot_expr_shape<M: KernelMode>(e: &KExpr<M>) -> String {
  let (head, args) = collect_app_spine(e);
  let head = match head.data() {
    ExprData::Var(i, _, _) => format!("#{i}"),
    ExprData::FVar(id, _, _) => format!("{id}"),
    ExprData::Sort(u, _) => format!("Sort({u})"),
    ExprData::Const(id, us, _) => format!("{id}.{{{}}}", us.len()),
    ExprData::App(..) => "app".to_string(),
    ExprData::Lam(..) => "lam".to_string(),
    ExprData::All(..) => "forall".to_string(),
    ExprData::Let(..) => "let".to_string(),
    ExprData::Prj(id, field, _, _) => format!("Prj({id}.{field})"),
    ExprData::Nat(v, _, _) => format!("Nat({})", v.0),
    ExprData::Str(v, _, _) => format!("Str(len={})", v.len()),
  };
  format!("{head}/{} lbr={} @{}", args.len(), e.lbr(), short_addr(e.addr()))
}

fn short_addr(addr: &Addr) -> String {
  addr.to_hex().chars().take(12).collect()
}

#[cfg(test)]
mod tests {
  use super::super::testing::{
    apps, cnst, mk_addr, mk_id, mk_name, pi, sort0, sort1, uzero, var,
  };
  use super::*;
  use crate::ix::address::Address;
  use crate::ix::kernel::mode::Meta;

  fn new_tc() -> TypeChecker<'static, Meta> {
    let env = Box::leak(Box::new(KEnv::<Meta>::new()));
    TypeChecker::new(env)
  }

  // ---- Context push/pop ----

  #[test]
  fn push_pop_local_roundtrip() {
    let mut tc = new_tc();
    assert_eq!(tc.depth(), 0);
    tc.push_local(sort0());
    assert_eq!(tc.depth(), 1);
    tc.push_local(sort1());
    assert_eq!(tc.depth(), 2);
    tc.pop_local();
    assert_eq!(tc.depth(), 1);
    tc.pop_local();
    assert_eq!(tc.depth(), 0);
  }

  #[test]
  fn fvar_ids_are_env_scoped_across_type_checkers() {
    let mut env = KEnv::<Meta>::new();
    let first = {
      let mut tc = TypeChecker::new(&mut env);
      tc.fresh_fvar_id()
    };
    let second = {
      let mut tc = TypeChecker::new(&mut env);
      tc.fresh_fvar_id()
    };
    assert_ne!(first, second);
    assert_eq!(first.0, 0);
    assert_eq!(second.0, 1);
  }

  #[test]
  fn push_let_increments_let_count() {
    let mut tc = new_tc();
    assert_eq!(tc.num_let_bindings, 0);
    tc.push_let(sort0(), sort0());
    assert_eq!(tc.num_let_bindings, 1);
    tc.push_let(sort1(), sort1());
    assert_eq!(tc.num_let_bindings, 2);
    tc.pop_local();
    assert_eq!(tc.num_let_bindings, 1);
    tc.pop_local();
    assert_eq!(tc.num_let_bindings, 0);
  }

  #[test]
  fn push_local_does_not_touch_let_count() {
    let mut tc = new_tc();
    tc.push_local(sort0());
    assert_eq!(tc.num_let_bindings, 0);
    tc.push_let(sort0(), sort0());
    assert_eq!(tc.num_let_bindings, 1);
    tc.push_local(sort0());
    assert_eq!(tc.num_let_bindings, 1);
    tc.pop_local(); // pops the lambda-bound frame
    assert_eq!(tc.num_let_bindings, 1);
    tc.pop_local(); // pops the let
    assert_eq!(tc.num_let_bindings, 0);
    tc.pop_local(); // pops the original lambda
    assert_eq!(tc.num_let_bindings, 0);
  }

  // ---- ctx_id determinism and stack ----

  #[test]
  fn empty_ctx_id_is_the_same_const() {
    let tc1 = new_tc();
    let tc2 = new_tc();
    assert_eq!(tc1.ctx_id, tc2.ctx_id);
    assert_eq!(tc1.ctx_id, empty_ctx_addr());
  }

  #[test]
  fn ctx_id_changes_when_pushing_different_types() {
    let mut tc = new_tc();
    let initial = tc.ctx_id;
    tc.push_local(sort0());
    let after_sort0 = tc.ctx_id;
    assert_ne!(initial, after_sort0);
    tc.push_local(sort1());
    let after_sort1 = tc.ctx_id;
    assert_ne!(after_sort0, after_sort1);
  }

  #[test]
  fn ctx_id_same_pushes_yield_same_hash() {
    let mut tc1 = new_tc();
    let mut tc2 = new_tc();
    tc1.push_local(sort0());
    tc1.push_local(sort1());
    tc2.push_local(sort0());
    tc2.push_local(sort1());
    assert_eq!(tc1.ctx_id, tc2.ctx_id);
  }

  #[test]
  fn ctx_id_restores_on_pop() {
    let mut tc = new_tc();
    let initial = tc.ctx_id;
    tc.push_local(sort0());
    let level1 = tc.ctx_id;
    tc.push_local(sort1());
    assert_ne!(level1, tc.ctx_id);
    tc.pop_local();
    assert_eq!(tc.ctx_id, level1);
    tc.pop_local();
    assert_eq!(tc.ctx_id, initial);
  }

  #[test]
  fn pop_from_empty_resets_to_empty_ctx_addr() {
    let mut tc = new_tc();
    // Popping an empty stack must not panic — the implementation uses
    // `unwrap_or_else(empty_ctx_addr)` as defensive fallback.
    tc.pop_local();
    assert_eq!(tc.ctx_id, empty_ctx_addr());
  }

  #[test]
  fn let_contributes_to_ctx_id_differently_than_local() {
    let mut t_local = new_tc();
    let mut t_let = new_tc();
    t_local.push_local(sort0());
    t_let.push_let(sort0(), sort0());
    // Different frame domains: lambda vs let must hash distinctly.
    assert_ne!(t_local.ctx_id, t_let.ctx_id);
  }

  // ---- whnf_key ----

  #[test]
  fn whnf_key_empty_ctx_for_closed_expr() {
    let mut tc = new_tc();
    let e = sort0();
    let (h, ctx) = tc.whnf_key(&e);
    assert_eq!(h, e.hash_key());
    assert_eq!(ctx, empty_ctx_addr());
  }

  #[test]
  fn whnf_key_includes_ctx_id_for_open_expr_without_lets() {
    let mut tc = new_tc();
    // Push a lambda-bound local — num_let_bindings stays 0.
    tc.push_local(sort0());
    let e = var(0);
    let (h, ctx) = tc.whnf_key(&e);
    assert_eq!(h, e.hash_key());
    assert_eq!(ctx, tc.ctx_id);
    assert_ne!(ctx, empty_ctx_addr());
  }

  #[test]
  fn whnf_key_includes_ctx_id_under_let_with_open_expr() {
    let mut tc = new_tc();
    tc.push_let(sort0(), sort0());
    let e = var(0);
    let (h, ctx) = tc.whnf_key(&e);
    assert_eq!(h, e.hash_key());
    assert_ne!(ctx, empty_ctx_addr());
    assert_eq!(ctx, tc.ctx_id);
  }

  #[test]
  fn whnf_key_closed_expr_ignores_ctx_even_under_let() {
    let mut tc = new_tc();
    tc.push_let(sort0(), sort0());
    let e = sort0(); // lbr == 0
    let (_, ctx) = tc.whnf_key(&e);
    // Closed expression: empty ctx regardless of let-binding state.
    assert_eq!(ctx, empty_ctx_addr());
  }

  #[test]
  fn whnf_key_uses_suffix_across_different_outer_ctx() {
    // The suffix-aware key should let an open subterm hit cache across
    // different OUTER contexts when only the inner suffix matters.
    //
    // Both checkers push the same innermost local frame after a different
    // outer frame. A `var(0)` with lbr=1 should key only by the inner
    // suffix, so the two `whnf_key`s should match even though the outer
    // contexts (and hence ctx_ids) differ.
    let mut tc1 = new_tc();
    tc1.push_local(sort0()); // outer A
    tc1.push_local(sort1()); // inner X

    let mut tc2 = new_tc();
    tc2.push_local(sort1()); // outer B (different from A)
    tc2.push_local(sort1()); // inner X (same as tc1's inner)

    // ctx_ids differ (different outer frames).
    assert_ne!(tc1.ctx_id, tc2.ctx_id);

    let e = var(0); // lbr = 1, depends only on innermost frame
    let (h1, ctx1) = tc1.whnf_key(&e);
    let (h2, ctx2) = tc2.whnf_key(&e);
    assert_eq!(h1, h2);
    assert_eq!(
      ctx1, ctx2,
      "suffix-aware key should match across different outers"
    );
    assert_ne!(ctx1, empty_ctx_addr());
  }

  // ---- infer_key ----

  #[test]
  fn infer_key_closed_expr_ignores_ctx() {
    let mut tc = new_tc();
    tc.push_local(sort0());
    let e = sort0();
    let (h, ctx) = tc.infer_key(&e);
    assert_eq!(h, e.hash_key());
    assert_eq!(ctx, empty_ctx_addr());
  }

  #[test]
  fn infer_key_open_expr_includes_ctx_even_without_lets() {
    let mut tc = new_tc();
    tc.push_local(sort0());
    let e = var(0);
    let (h, ctx) = tc.infer_key(&e);
    assert_eq!(h, e.hash_key());
    assert_eq!(ctx, tc.ctx_id);
    assert_ne!(ctx, empty_ctx_addr());
  }

  // ---- lookup_var ----

  #[test]
  fn lookup_var_out_of_range() {
    let mut tc = new_tc();
    tc.push_local(sort0());
    // idx 5 in a depth-1 context is OOR
    let r = tc.lookup_var(5);
    match r {
      Err(TcError::VarOutOfRange { idx, ctx_len }) => {
        assert_eq!(idx, 5);
        assert_eq!(ctx_len, 1);
      },
      other => panic!("expected VarOutOfRange, got {other:?}"),
    }
  }

  #[test]
  fn lookup_var_returns_lifted_type() {
    let mut tc = new_tc();
    // Outer binder: type is (Var 0). Inner binder: type is (Sort 1).
    // lookup_var(1) should be the outer type lifted by 2 (depth - level = 2).
    // Use a type with loose bvars so lifting is observable.
    tc.push_local(var(3));
    tc.push_local(sort1());
    let t = tc.lookup_var(1).unwrap();
    // Lifted from Var(3) with lift-by-(idx+1)=2 → Var(3+2)=Var(5).
    // The implementation calls `lift(&intern, &ty, idx + 1, 0)` which
    // shifts all free bvars by idx+1.
    match t.data() {
      ExprData::Var(i, _, _) => assert_eq!(*i, 5),
      other => panic!("expected Var, got {other:?}"),
    }
  }

  #[test]
  fn lookup_let_val_returns_none_for_lambda_binding() {
    let mut tc = new_tc();
    tc.push_local(sort0());
    assert!(tc.lookup_let_val(0).is_none());
  }

  #[test]
  fn lookup_let_val_returns_some_for_let_binding() {
    let mut tc = new_tc();
    tc.push_let(sort0(), sort1());
    let v = tc.lookup_let_val(0).expect("expected Some for let-bound var");
    // Closed value (Sort 1) — lift by 1 is a no-op on closed expressions.
    assert!(matches!(v.data(), ExprData::Sort(..)));
  }

  #[test]
  fn lookup_let_val_out_of_range() {
    let mut tc = new_tc();
    tc.push_let(sort0(), sort1());
    assert!(tc.lookup_let_val(10).is_none());
  }

  // ---- save_depth / restore_depth ----

  #[test]
  fn save_and_restore_depth_basic() {
    let mut tc = new_tc();
    tc.push_local(sort0());
    let s = tc.save_depth();
    tc.push_local(sort1());
    tc.push_local(sort1());
    assert_eq!(tc.depth(), 3);
    tc.restore_depth(s);
    assert_eq!(tc.depth(), 1);
  }

  #[test]
  fn restore_depth_drops_let_count() {
    let mut tc = new_tc();
    let s = tc.save_depth();
    tc.push_let(sort0(), sort0());
    tc.push_local(sort0());
    tc.push_let(sort1(), sort1());
    assert_eq!(tc.num_let_bindings, 2);
    tc.restore_depth(s);
    assert_eq!(tc.depth(), 0);
    assert_eq!(tc.num_let_bindings, 0);
  }

  // ---- tick / fuel ----

  #[test]
  fn tick_consumes_fuel() {
    let mut tc = new_tc();
    tc.rec_fuel = 3;
    assert!(tc.tick().is_ok());
    assert!(tc.tick().is_ok());
    assert!(tc.tick().is_ok());
    match tc.tick() {
      Err(TcError::MaxRecFuel) => {},
      other => panic!("expected MaxRecFuel, got {other:?}"),
    }
  }

  #[test]
  fn tick_exhaustion_at_zero() {
    let mut tc = new_tc();
    tc.rec_fuel = 0;
    match tc.tick() {
      Err(TcError::MaxRecFuel) => {},
      other => panic!("expected MaxRecFuel at zero fuel, got {other:?}"),
    }
  }

  // ---- with_infer_only ----

  #[test]
  fn with_infer_only_scoping() {
    let mut tc = new_tc();
    assert!(!tc.infer_only);
    let r = tc.with_infer_only(|tc| {
      assert!(tc.infer_only);
      42
    });
    assert_eq!(r, 42);
    assert!(!tc.infer_only);
  }

  #[test]
  fn with_infer_only_nested_restores() {
    let mut tc = new_tc();
    tc.infer_only = true;
    tc.with_infer_only(|tc| {
      assert!(tc.infer_only);
    });
    assert!(tc.infer_only, "outer infer_only=true must be preserved");
    tc.infer_only = false;
    tc.with_infer_only(|tc| {
      assert!(tc.infer_only);
    });
    assert!(!tc.infer_only, "outer infer_only=false must be preserved");
  }

  // ---- reset ----

  #[test]
  fn reset_clears_thread_local_state() {
    let mut tc = new_tc();
    tc.push_local(sort0());
    tc.push_let(sort1(), sort1());
    tc.infer_only = true;
    tc.in_native_reduce = true;
    tc.eager_reduce = true;
    tc.def_eq_depth = 5;
    tc.def_eq_peak = 10;
    tc.rec_fuel = 1;

    tc.reset();

    assert_eq!(tc.depth(), 0);
    assert_eq!(tc.num_let_bindings, 0);
    assert_eq!(tc.ctx_id, empty_ctx_addr());
    assert!(!tc.infer_only);
    assert!(!tc.in_native_reduce);
    assert!(!tc.eager_reduce);
    assert_eq!(tc.def_eq_depth, 0);
    assert_eq!(tc.def_eq_peak, 0);
    assert_eq!(tc.rec_fuel, max_rec_fuel());
  }

  // ---- instantiate_univ_params / subst_univ ----

  #[test]
  fn instantiate_univ_params_empty_us_is_noop() {
    let mut tc = new_tc();
    let e = sort0();
    let r = tc.instantiate_univ_params(&e, &[]).unwrap();
    // Empty us triggers the ptr-equal fast path.
    assert!(e.ptr_eq(&r));
  }

  #[test]
  fn instantiate_univ_params_sort_param() {
    let mut tc = new_tc();
    // Sort (Param 0) with us = [Zero] → Sort Zero.
    let e = KExpr::<Meta>::sort(KUniv::param(0, mk_name("u")));
    let r = tc.instantiate_univ_params(&e, &[uzero()]).unwrap();
    match r.data() {
      ExprData::Sort(u, _) => match u.data() {
        UnivData::Zero(_) => {},
        other => panic!("expected Zero, got {other:?}"),
      },
      _ => panic!("expected Sort"),
    }
  }

  #[test]
  fn subst_univ_out_of_range_errors() {
    let mut tc = new_tc();
    // Param(5) with only 2 universes supplied → UnivParamOutOfRange.
    let u = KUniv::<Meta>::param(5, mk_name("u"));
    match tc.subst_univ(&u, &[uzero(), uzero()]) {
      Err(TcError::UnivParamOutOfRange { idx, bound }) => {
        assert_eq!(idx, 5);
        assert_eq!(bound, 2);
      },
      other => panic!("expected UnivParamOutOfRange, got {other:?}"),
    }
  }

  #[test]
  fn subst_univ_through_succ_max_imax() {
    let mut tc = new_tc();
    // max(succ(Param(0)), imax(Param(1), Zero)) with us=[Zero, succ(Zero)].
    let u = KUniv::<Meta>::max(
      KUniv::succ(KUniv::param(0, mk_name("u"))),
      KUniv::imax(KUniv::param(1, mk_name("v")), KUniv::zero()),
    );
    let us = [KUniv::zero(), KUniv::succ(KUniv::zero())];
    let r = tc.subst_univ(&u, &us).unwrap();
    // Structural traversal must succeed. Exact normalization output is
    // owned by KUniv::max/imax simplification — we only verify no error.
    // The result is still some KUniv value.
    let _ = r;
  }

  // ---- ensure_sort / ensure_forall fast paths ----

  #[test]
  fn ensure_sort_on_sort_succeeds() {
    let mut tc = new_tc();
    let u = tc.ensure_sort(&sort0()).unwrap();
    assert!(matches!(u.data(), UnivData::Zero(_)));
  }

  #[test]
  fn ensure_forall_on_forall_succeeds() {
    let mut tc = new_tc();
    let e = pi(sort0(), sort1());
    let (dom, cod) = tc.ensure_forall(&e).unwrap();
    assert!(matches!(dom.data(), ExprData::Sort(..)));
    assert!(matches!(cod.data(), ExprData::Sort(..)));
  }

  // ---- Free-standing helpers ----

  #[test]
  fn collect_app_spine_non_app_empty_args() {
    let e = sort0();
    let (head, args) = collect_app_spine(&e);
    assert_eq!(args.len(), 0);
    assert!(head.ptr_eq(&e) || head.hash_eq(&e));
  }

  #[test]
  fn collect_app_spine_single_app() {
    let f = cnst("f", &[]);
    let a = sort0();
    let e = KExpr::<Meta>::app(f.clone(), a.clone());
    let (head, args) = collect_app_spine(&e);
    assert_eq!(args.len(), 1);
    assert!(head.hash_eq(&f));
  }

  #[test]
  fn collect_app_spine_multi_app_preserves_order() {
    let f = cnst("f", &[]);
    let a = sort0();
    let b = sort1();
    let c = var(0);
    let e = apps(f.clone(), &[a.clone(), b.clone(), c.clone()]);
    let (head, args) = collect_app_spine(&e);
    assert_eq!(args.len(), 3);
    assert!(head.hash_eq(&f));
    assert!(args[0].hash_eq(&a));
    assert!(args[1].hash_eq(&b));
    assert!(args[2].hash_eq(&c));
  }

  #[test]
  fn expr_mentions_addr_finds_const() {
    let target_id = mk_id("target");
    let target = cnst("target", &[]);
    // Deep embedding: λ x. app target (var 0)
    let e = KExpr::<Meta>::lam(
      mk_name("x"),
      crate::ix::env::BinderInfo::Default,
      sort0(),
      KExpr::app(target, var(0)),
    );
    assert!(expr_mentions_addr(&e, &target_id.addr));
  }

  #[test]
  fn expr_mentions_addr_not_found() {
    let other_addr = mk_addr("other");
    let e = pi(sort0(), sort1());
    assert!(!expr_mentions_addr::<Meta>(&e, &other_addr));
  }

  #[test]
  fn expr_mentions_any_addr_finds_one() {
    let a = mk_id("a");
    let b = mk_id("b");
    let e = cnst("b", &[]);
    let addrs: Vec<Address> = vec![a.addr.clone(), b.addr.clone()];
    assert!(expr_mentions_any_addr::<Meta>(&e, &addrs));
  }

  #[test]
  fn expr_mentions_addr_through_let_all_branches() {
    let target_id = mk_id("target");
    let e = KExpr::<Meta>::let_(
      mk_name("x"),
      sort0(),
      sort0(),
      cnst("target", &[]),
      false,
    );
    assert!(expr_mentions_addr(&e, &target_id.addr));
  }

  #[test]
  fn expr_mentions_addr_detects_proj_struct_id() {
    let target_id = mk_id("MyStruct");
    let e = KExpr::<Meta>::prj(target_id.clone(), 0, var(0));
    assert!(expr_mentions_addr(&e, &target_id.addr));
  }
}
