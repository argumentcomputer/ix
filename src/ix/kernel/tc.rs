//! TypeChecker struct and core helpers.
//!
//! The TypeChecker is a lightweight thread-local handle for type-checking.
//! All shared state (caches, intern table, constants) lives in `KEnv` and
//! is accessed through `self.env`. Multiple TypeChecker instances can run
//! in parallel, all sharing one `Arc<KEnv>`.
//!
//! WHNF, type inference, def-eq, and constant checking are in separate modules
//! that add `impl TypeChecker` blocks.

use std::sync::{Arc, LazyLock};

use rustc_hash::FxHashMap;

use crate::ix::address::Address;

use super::constant::RecRule;
use super::env::{Addr, KEnv};
use super::equiv::EquivManager;
use super::error::{TcError, u64_to_usize};
use super::expr::{ExprData, KExpr};
use super::level::{KUniv, UnivData};
use super::mode::KernelMode;
use super::primitive::Primitives;
use super::subst::lift;

/// Content-addressed context identity for the empty context (no bindings).
pub fn empty_ctx_addr() -> Addr {
  use std::sync::LazyLock;
  static ADDR: LazyLock<Addr> =
    LazyLock::new(|| Arc::new(blake3::hash(b"ix.kernel.ctx.empty")));
  ADDR.clone()
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
pub const MAX_REC_FUEL: u64 = 1_500_000;

static IX_MAX_REC_FUEL: LazyLock<Option<u64>> = LazyLock::new(|| {
  std::env::var("IX_MAX_REC_FUEL").ok().and_then(|s| s.parse().ok())
});

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

/// Thread-local type-checking handle. Cheap to create — only allocates empty
/// vectors and counters. All shared state lives in `Arc<KEnv>`.
pub struct TypeChecker<M: KernelMode> {
  /// Shared kernel environment (constants, caches, intern table).
  pub env: Arc<KEnv<M>>,
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
  /// When true, the Bool.true fast-path in is_def_eq fires even on open terms.
  pub eager_reduce: bool,
  /// Current def-eq recursion depth.
  pub def_eq_depth: u32,
  /// Peak def-eq depth (diagnostics).
  pub def_eq_peak: u32,
  /// Shared recursive fuel remaining for this constant check.
  pub rec_fuel: u64,
  /// Count of Nat-literal iota reductions on values above the large-literal
  /// threshold for the current constant.
  pub nat_iota_large_expansions: u32,
  /// Consecutive `Nat` literal iota reductions on the same recursor where the
  /// major premise is being peeled by one each time. This catches runaway
  /// `Nat.rec ... N` paths whose step immediately forces `ih` while still
  /// allowing large-fuel definitions that make only bounded progress.
  pub nat_iota_last: Option<(Address, num_bigint::BigUint)>,
  pub nat_iota_run: u32,
  /// Optional diagnostic label for the current top-level constant.
  pub debug_label: Option<String>,
}

impl<M: KernelMode> TypeChecker<M> {
  pub fn new(env: Arc<KEnv<M>>) -> Self {
    let prims = env.prims().clone();
    TypeChecker {
      env,
      prims,
      ctx: Vec::new(),
      let_vals: Vec::new(),
      num_let_bindings: 0,
      ctx_id: empty_ctx_addr(),
      ctx_id_stack: Vec::new(),
      equiv_manager: EquivManager::new(),
      infer_only: false,
      in_native_reduce: false,
      eager_reduce: false,
      def_eq_depth: 0,
      def_eq_peak: 0,
      rec_fuel: max_rec_fuel(),
      nat_iota_large_expansions: 0,
      nat_iota_last: None,
      nat_iota_run: 0,
      debug_label: None,
    }
  }

  // -----------------------------------------------------------------------
  // Context management
  // -----------------------------------------------------------------------

  /// Current binding depth.
  pub fn depth(&self) -> u64 {
    self.ctx.len() as u64
  }

  /// WHNF cache key: (expr_hash, ctx_hash).
  /// Closed expressions (lbr == 0) use the empty context hash since they
  /// can't reference bindings. Open expressions use ctx_id to distinguish
  /// contexts: WHNF itself is syntactic for most open terms, but reduction can
  /// call infer through K/structure iota and projection paths, and infer of a
  /// loose variable depends on the local binder types.
  #[inline]
  pub fn whnf_key(&self, e: &KExpr<M>) -> (Addr, Addr) {
    if e.lbr() == 0 {
      (e.hash_key(), empty_ctx_addr())
    } else {
      (e.hash_key(), self.ctx_id.clone())
    }
  }

  /// Type-inference cache key: (expr_hash, ctx_hash).
  /// Closed expressions (lbr == 0) are context-independent. Open expressions
  /// depend on local types, so they must stay isolated by ctx_id even when
  /// there are no let-bindings.
  #[inline]
  pub fn infer_key(&self, e: &KExpr<M>) -> (Addr, Addr) {
    if e.lbr() == 0 {
      (e.hash_key(), empty_ctx_addr())
    } else {
      (e.hash_key(), self.ctx_id.clone())
    }
  }

  /// Push a local variable type (lambda/forall binding, no let-value).
  pub fn push_local(&mut self, ty: KExpr<M>) {
    let mut h = blake3::Hasher::new();
    h.update(b"ctx.local");
    h.update(ty.addr().as_bytes());
    h.update(self.ctx_id.as_bytes());
    self.ctx_id_stack.push(self.ctx_id.clone());
    self.ctx_id = Arc::new(h.finalize());
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
    self.ctx_id_stack.push(self.ctx_id.clone());
    self.ctx_id = Arc::new(h.finalize());
    self.ctx.push(ty);
    self.let_vals.push(Some(val));
    self.num_let_bindings += 1;
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
    Some(lift(&self.env.intern, &val, idx + 1, 0))
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

  /// Look up a bound variable's type, lifted to the current depth.
  pub fn lookup_var(&mut self, idx: u64) -> Result<KExpr<M>, TcError<M>> {
    let n = self.ctx.len();
    let idx_us = u64_to_usize::<M>(idx)?;
    if idx_us >= n {
      return Err(TcError::VarOutOfRange { idx, ctx_len: n });
    }
    let level = n - 1 - idx_us;
    let ty = self.ctx[level].clone();
    Ok(lift(&self.env.intern, &ty, idx + 1, 0))
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
      ExprData::Var(..) | ExprData::Nat(..) | ExprData::Str(..) => {
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
    self.eager_reduce = false;
    self.def_eq_depth = 0;
    self.def_eq_peak = 0;
    self.rec_fuel = max_rec_fuel();
    self.nat_iota_large_expansions = 0;
    self.nat_iota_last = None;
    self.nat_iota_run = 0;
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
        eprintln!("{}", std::backtrace::Backtrace::force_capture());
      }
      return Err(TcError::MaxRecDepth);
    }
    self.rec_fuel -= 1;
    Ok(())
  }

  /// Starting fuel for the current check. Used by diagnostics that want
  /// to report fuel consumed at a given point.
  pub fn fuel_used(&self) -> u64 {
    max_rec_fuel().saturating_sub(self.rec_fuel)
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
pub fn collect_app_spine<M: KernelMode>(
  e: &KExpr<M>,
) -> (KExpr<M>, Vec<KExpr<M>>) {
  let mut args = Vec::new();
  let mut cur = e.clone();
  while let ExprData::App(f, a, _) = cur.data() {
    args.push(a.clone());
    cur = f.clone();
  }
  args.reverse();
  (cur, args)
}

#[cfg(test)]
mod tests {
  use super::super::testing::{
    apps, cnst, mk_addr, mk_id, mk_name, pi, sort0, sort1, uzero, var,
  };
  use super::*;
  use crate::ix::address::Address;
  use crate::ix::kernel::mode::Meta;

  fn new_tc() -> TypeChecker<Meta> {
    TypeChecker::new(Arc::new(KEnv::<Meta>::new()))
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
    let initial = tc.ctx_id.clone();
    tc.push_local(sort0());
    let after_sort0 = tc.ctx_id.clone();
    assert_ne!(initial, after_sort0);
    tc.push_local(sort1());
    let after_sort1 = tc.ctx_id.clone();
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
    let initial = tc.ctx_id.clone();
    tc.push_local(sort0());
    let level1 = tc.ctx_id.clone();
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
    let tc = new_tc();
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
      Err(TcError::MaxRecDepth) => {},
      other => panic!("expected MaxRecDepth, got {other:?}"),
    }
  }

  #[test]
  fn tick_exhaustion_at_zero() {
    let mut tc = new_tc();
    tc.rec_fuel = 0;
    match tc.tick() {
      Err(TcError::MaxRecDepth) => {},
      other => panic!("expected MaxRecDepth at zero fuel, got {other:?}"),
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
