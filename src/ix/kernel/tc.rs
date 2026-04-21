//! TypeChecker struct and core helpers.
//!
//! The TypeChecker is a lightweight thread-local handle for type-checking.
//! All shared state (caches, intern table, constants) lives in `KEnv` and
//! is accessed through `self.env`. Multiple TypeChecker instances can run
//! in parallel, all sharing one `Arc<KEnv>`.
//!
//! WHNF, type inference, def-eq, and constant checking are in separate modules
//! that add `impl TypeChecker` blocks.

use std::sync::Arc;

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
/// uses ~200,000 heartbeats. We use a higher budget than lean4lean because
/// we lack compiled native reduction for large Nat/Bool computations.
pub const MAX_REC_FUEL: u64 = 200_000;

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
  /// Number of active let-bindings in `ctx`. When > 0, WHNF cache keys include
  /// ctx_id to avoid cross-context contamination.
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
      rec_fuel: MAX_REC_FUEL,
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
  /// can't reference bindings. Open expressions under let-bindings use
  /// ctx_id to distinguish contexts.
  #[inline]
  pub fn whnf_key(&self, e: &KExpr<M>) -> (Addr, Addr) {
    if self.num_let_bindings > 0 && e.lbr() > 0 {
      (e.hash_key(), self.ctx_id.clone())
    } else {
      (e.hash_key(), empty_ctx_addr())
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
    self.inst_univ_inner(e, us)
  }

  fn inst_univ_inner(
    &mut self,
    e: &KExpr<M>,
    us: &[KUniv<M>],
  ) -> Result<KExpr<M>, TcError<M>> {
    let result = match e.data() {
      ExprData::Var(..) | ExprData::Nat(..) | ExprData::Str(..) => {
        return Ok(e.clone());
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
        let f2 = self.inst_univ_inner(f, us)?;
        let a2 = self.inst_univ_inner(a, us)?;
        KExpr::app(f2, a2)
      },

      ExprData::Lam(name, bi, ty, body, _) => {
        let ty2 = self.inst_univ_inner(ty, us)?;
        let body2 = self.inst_univ_inner(body, us)?;
        KExpr::lam(name.clone(), bi.clone(), ty2, body2)
      },

      ExprData::All(name, bi, ty, body, _) => {
        let ty2 = self.inst_univ_inner(ty, us)?;
        let body2 = self.inst_univ_inner(body, us)?;
        KExpr::all(name.clone(), bi.clone(), ty2, body2)
      },

      ExprData::Let(name, ty, val, body, nd, _) => {
        let ty2 = self.inst_univ_inner(ty, us)?;
        let val2 = self.inst_univ_inner(val, us)?;
        let body2 = self.inst_univ_inner(body, us)?;
        KExpr::let_(name.clone(), ty2, val2, body2, *nd)
      },

      ExprData::Prj(id, field, val, _) => {
        let val2 = self.inst_univ_inner(val, us)?;
        KExpr::prj(id.clone(), *field, val2)
      },
    };
    Ok(self.env.intern.intern_expr(result))
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
          None => Err(TcError::UnivParamOutOfRange {
            idx: *i,
            bound: us.len(),
          }),
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
    self.rec_fuel = MAX_REC_FUEL;
  }

  /// Consume one unit of shared recursive fuel. Returns Err if exhausted.
  #[inline]
  pub fn tick(&mut self) -> Result<(), TcError<M>> {
    if self.rec_fuel == 0 {
      return Err(TcError::MaxRecDepth);
    }
    self.rec_fuel -= 1;
    Ok(())
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
