//! TypeChecker struct and core helpers.
//!
//! The TypeChecker manages local context, caches, and environment access.
//! WHNF, type inference, def-eq, and constant checking are in separate modules
//! that add `impl TypeChecker` blocks.

use std::sync::Arc;

use rustc_hash::FxHashMap;

use crate::ix::address::Address;
use crate::ix::env::Name;

use super::constant::RecRule;
use super::env::{Addr, InternTable, KEnv};
use super::equiv::EquivManager;
use super::error::TcError;
use super::expr::{ExprData, ExprInfo, KExpr, MData};
use super::id::KId;
use super::level::{KUniv, UnivData};
use super::mode::KernelMode;
use super::primitive::Primitives;
use super::subst::lift;

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

/// Generated recursor, cached after inductive validation.
#[derive(Clone, Debug)]
pub struct GeneratedRecursor<M: KernelMode> {
  pub ind_addr: Address,
  pub ty: KExpr<M>,
  pub rules: Vec<RecRule<M>>,
}

pub struct TypeChecker<'env, M: KernelMode> {
  /// The global constant environment.
  pub env: &'env KEnv<M>,
  /// Canonical intern table (hash-consing for pointer dedup).
  pub ienv: InternTable<M>,
  /// Primitive constant KIds (resolved from env).
  pub prims: Primitives<M>,

  // -- Local context --
  /// Local variable types, indexed by de Bruijn level.
  pub ctx: Vec<KExpr<M>>,
  /// Let-bound values, parallel to `ctx`. `Some(val)` for let-bindings, `None`
  /// for lambda/forall bindings. Used for let-variable zeta-reduction in whnf_core.
  pub let_vals: Vec<Option<KExpr<M>>>,
  /// Number of active let-bindings in `ctx`. When > 0, WHNF caches are skipped
  /// because cached results may not account for let-bound variable substitution.
  pub num_let_bindings: usize,
  /// Hash-consed context identity.
  pub ctx_id: usize,
  /// Stack of previous ctx_ids for O(1) pop.
  ctx_id_stack: Vec<usize>,
  /// Intern table for context cons cells.
  /// Key: (ty_ptr_key, val_ptr_key_or_0, parent_ctx_id).
  /// For push_local (no value), val_ptr_key = 0.
  /// For push_let, val_ptr_key = val.ptr_key().
  ctx_intern: FxHashMap<(usize, usize, usize), Arc<()>>,

  // -- Caches --
  // Interning guarantees pointer uniqueness by hash, so ptr_key suffices
  // as a cache key. WHNF is context-independent; infer and def-eq are
  // context-dependent (ctx_id needed).
  /// WHNF cache (full, with delta): (ptr_key, ctx_component)-keyed.
  /// Context-aware: open expressions under let-bindings use ctx_id.
  pub whnf_cache: FxHashMap<(usize, usize), KExpr<M>>,
  /// WHNF cache (no delta): (ptr_key, ctx_component)-keyed.
  pub whnf_no_delta_cache: FxHashMap<(usize, usize), KExpr<M>>,
  /// Infer cache: keyed by (ptr_key, ctx_id). Context-dependent.
  pub infer_cache: FxHashMap<(usize, usize), KExpr<M>>,
  /// Def-eq cache: keyed by (ptr_key, ptr_key, ctx_id). Context-dependent.
  pub def_eq_cache: FxHashMap<(usize, usize, usize), bool>,
  /// Failed def-eq pairs in lazy delta: canonical (min_ptr, max_ptr, ctx_id) ordering.
  /// Prevents re-attempting expensive spine comparisons on same-head constants.
  /// Context-aware to avoid suppressing retries across different binding contexts.
  pub def_eq_failure: rustc_hash::FxHashSet<(usize, usize, usize)>,
  /// Infer-only cache: results from infer_only mode (no def-eq checks).
  /// Separate from infer_cache because full-check results are stricter.
  pub infer_only_cache: FxHashMap<(usize, usize), KExpr<M>>,
  /// When true, `infer` skips def-eq checks (arg-type and let-value validation).
  pub infer_only: bool,
  /// Re-entrancy guard for native reduction (prevents whnf → native → whnf loops).
  pub in_native_reduce: bool,
  /// When true, the Bool.true fast-path in is_def_eq fires even on open terms.
  /// Set when an `eagerReduce` argument is encountered during App inference.
  pub eager_reduce: bool,
  /// Union-find for transitive def-eq caching (lean4lean EquivManager).
  pub equiv_manager: EquivManager,
  /// Current def-eq recursion depth.
  pub def_eq_depth: u32,
  /// Peak def-eq depth (diagnostics).
  pub def_eq_peak: u32,
  /// Shared recursive fuel remaining for this constant check.
  pub rec_fuel: u64,

  // -- Recursor generation cache --
  /// Generated recursors, keyed by inductive Muts block id.
  pub recursor_cache: FxHashMap<KId<M>, Vec<GeneratedRecursor<M>>>,
  /// Maps the set of major inductive KIds (across all recursors in a block)
  /// to (inductive_block_id, generated_recursors). Used to look up auxiliary
  /// recursors whose major is an external inductive.
  pub rec_majors_cache:
    std::collections::BTreeMap<std::collections::BTreeSet<KId<M>>, KId<M>>,
}

impl<'env, M: KernelMode> TypeChecker<'env, M> {
  pub fn new(env: &'env KEnv<M>, ienv: InternTable<M>) -> Self {
    let prims = Primitives::from_env(env);
    TypeChecker {
      env,
      ienv,
      prims,
      ctx: Vec::new(),
      let_vals: Vec::new(),
      num_let_bindings: 0,
      ctx_id: 0,
      ctx_id_stack: Vec::new(),
      ctx_intern: FxHashMap::default(),
      whnf_cache: FxHashMap::default(),
      whnf_no_delta_cache: FxHashMap::default(),
      infer_cache: FxHashMap::default(),
      infer_only_cache: FxHashMap::default(),
      infer_only: false,
      in_native_reduce: false,
      eager_reduce: false,
      def_eq_cache: FxHashMap::default(),
      def_eq_failure: rustc_hash::FxHashSet::default(),
      equiv_manager: EquivManager::new(),
      def_eq_depth: 0,
      def_eq_peak: 0,
      rec_fuel: MAX_REC_FUEL,
      recursor_cache: FxHashMap::default(),
      rec_majors_cache: std::collections::BTreeMap::new(),
    }
  }

  // -----------------------------------------------------------------------
  // Context management
  // -----------------------------------------------------------------------

  /// Current binding depth.
  pub fn depth(&self) -> u64 {
    self.ctx.len() as u64
  }

  /// WHNF cache key: (ptr_key, context_component).
  /// Closed expressions (lbr == 0) use ctx=0 since they can't reference bindings.
  /// Open expressions under let-bindings use ctx_id to distinguish contexts.
  #[inline]
  pub fn whnf_key(&self, e: &KExpr<M>) -> (usize, usize) {
    if self.num_let_bindings > 0 && e.lbr() > 0 {
      (e.ptr_key(), self.ctx_id)
    } else {
      (e.ptr_key(), 0)
    }
  }

  /// Push a local variable type (lambda/forall binding, no let-value).
  pub fn push_local(&mut self, ty: KExpr<M>) {
    let key = (ty.ptr_key(), 0, self.ctx_id);
    let token =
      self.ctx_intern.entry(key).or_insert_with(|| Arc::new(())).clone();
    self.ctx_id_stack.push(self.ctx_id);
    self.ctx_id = Arc::as_ptr(&token) as usize;
    self.ctx.push(ty);
    self.let_vals.push(None);
  }

  /// Push a let-bound variable (type + value). WHNF will zeta-reduce references
  /// to this variable by substituting the value (lean4lean withExtendedLetCtx).
  pub fn push_let(&mut self, ty: KExpr<M>, val: KExpr<M>) {
    let key = (ty.ptr_key(), val.ptr_key(), self.ctx_id);
    let token =
      self.ctx_intern.entry(key).or_insert_with(|| Arc::new(())).clone();
    self.ctx_id_stack.push(self.ctx_id);
    self.ctx_id = Arc::as_ptr(&token) as usize;
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
    self.ctx_id = self.ctx_id_stack.pop().unwrap_or(0);
  }

  /// Look up a let-bound variable's value, lifted to the current depth.
  /// Returns None if the variable is lambda/forall-bound (not a let).
  pub fn lookup_let_val(&mut self, idx: u64) -> Option<KExpr<M>> {
    let n = self.ctx.len();
    if idx as usize >= n {
      return None;
    }
    let level = n - 1 - idx as usize;
    let val = self.let_vals[level].as_ref()?.clone();
    Some(lift(&self.ienv, &val, idx + 1, 0))
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
    if idx as usize >= n {
      return Err(TcError::VarOutOfRange { idx, ctx_len: n });
    }
    let level = n - 1 - idx as usize;
    let ty = self.ctx[level].clone();
    Ok(lift(&self.ienv, &ty, idx + 1, 0))
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

  /// Substitute universe parameters: replace Param(i) with us[i].
  pub fn instantiate_univ_params(
    &mut self,
    e: &KExpr<M>,
    us: &[KUniv<M>],
  ) -> KExpr<M> {
    if us.is_empty() {
      return e.clone();
    }
    self.inst_univ_inner(e, us)
  }

  fn inst_univ_inner(&mut self, e: &KExpr<M>, us: &[KUniv<M>]) -> KExpr<M> {
    let result = match e.data() {
      ExprData::Var(..) | ExprData::Nat(..) | ExprData::Str(..) => {
        return e.clone();
      },

      ExprData::Sort(u, _) => {
        let u2 = self.subst_univ(u, us);
        KExpr::sort(u2)
      },

      ExprData::Const(id, cur_us, _) => {
        let new_us: Box<[KUniv<M>]> =
          cur_us.iter().map(|u| self.subst_univ(u, us)).collect();
        KExpr::cnst(id.clone(), new_us)
      },

      ExprData::App(f, a, _) => {
        let f2 = self.inst_univ_inner(f, us);
        let a2 = self.inst_univ_inner(a, us);
        KExpr::app(f2, a2)
      },

      ExprData::Lam(name, bi, ty, body, _) => {
        let ty2 = self.inst_univ_inner(ty, us);
        let body2 = self.inst_univ_inner(body, us);
        KExpr::lam(name.clone(), bi.clone(), ty2, body2)
      },

      ExprData::All(name, bi, ty, body, _) => {
        let ty2 = self.inst_univ_inner(ty, us);
        let body2 = self.inst_univ_inner(body, us);
        KExpr::all(name.clone(), bi.clone(), ty2, body2)
      },

      ExprData::Let(name, ty, val, body, nd, _) => {
        let ty2 = self.inst_univ_inner(ty, us);
        let val2 = self.inst_univ_inner(val, us);
        let body2 = self.inst_univ_inner(body, us);
        KExpr::let_(name.clone(), ty2, val2, body2, *nd)
      },

      ExprData::Prj(id, field, val, _) => {
        let val2 = self.inst_univ_inner(val, us);
        KExpr::prj(id.clone(), *field, val2)
      },
    };
    self.ienv.intern_expr(result)
  }

  /// Substitute universe params in a universe level.
  pub fn subst_univ(&mut self, u: &KUniv<M>, us: &[KUniv<M>]) -> KUniv<M> {
    match u.data() {
      UnivData::Zero(_) => u.clone(),
      UnivData::Param(i, _, _) => {
        let i = *i as usize;
        if i < us.len() { us[i].clone() } else { u.clone() }
      },
      UnivData::Succ(inner, _) => {
        let inner2 = self.subst_univ(inner, us);
        KUniv::succ(inner2)
      },
      UnivData::Max(a, b, _) => {
        let a2 = self.subst_univ(a, us);
        let b2 = self.subst_univ(b, us);
        KUniv::max(a2, b2)
      },
      UnivData::IMax(a, b, _) => {
        let a2 = self.subst_univ(a, us);
        let b2 = self.subst_univ(b, us);
        KUniv::imax(a2, b2)
      },
    }
  }

  // -----------------------------------------------------------------------
  // Cache clearing (between constants)
  // -----------------------------------------------------------------------

  /// Clear per-constant caches, keeping persistent intern tables.
  pub fn clear_caches(&mut self) {
    self.ctx.clear();
    self.let_vals.clear();
    self.num_let_bindings = 0;
    self.ctx_id = 0;
    self.ctx_id_stack.clear();
    self.whnf_cache.clear();
    self.whnf_no_delta_cache.clear();
    self.infer_cache.clear();
    self.infer_only_cache.clear();
    self.infer_only = false;
    self.in_native_reduce = false;
    self.eager_reduce = false;
    self.def_eq_cache.clear();
    self.def_eq_failure.clear();
    self.equiv_manager.clear();
    self.def_eq_depth = 0;
    self.def_eq_peak = 0;
    self.rec_fuel = MAX_REC_FUEL;
    // Keep: ctx_intern, whnf_hash_cache, recursor_cache, ienv
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
    self.ienv.intern_expr(e)
  }

  /// Intern a universe through the mutable intern environment.
  pub fn intern_univ(&mut self, u: KUniv<M>) -> KUniv<M> {
    self.ienv.intern_univ(u)
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
  loop {
    match cur.data() {
      ExprData::App(f, a, _) => {
        args.push(a.clone());
        cur = f.clone();
      },
      _ => break,
    }
  }
  args.reverse();
  (cur, args)
}
