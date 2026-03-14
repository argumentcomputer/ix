//! TypeChecker struct and context management.
//!
//! The `TypeChecker` is the central state object for Kernel2. It holds the
//! context (types, let-values, binder names), caches, and counters.

use std::collections::BTreeMap;

use rustc_hash::FxHashMap;

use crate::ix::address::Address;
use crate::ix::env::{DefinitionSafety, Name};

use super::equiv::EquivManager;
use super::error::TcError;
use super::helpers;
use super::types::*;
use super::value::*;

/// Result type for type checking operations.
pub type TcResult<T, M> = Result<T, TcError<M>>;

// ============================================================================
// Constants
// ============================================================================

pub const DEFAULT_MAX_HEARTBEATS: usize = 200_000_000;
pub const DEFAULT_MAX_THUNKS: u64 = 10_000_000;

// ============================================================================
// Stats
// ============================================================================

/// Performance counters for the type checker.
#[derive(Debug, Clone, Default)]
pub struct Stats {
  pub infer_calls: u64,
  pub eval_calls: u64,
  pub force_calls: u64,
  pub def_eq_calls: u64,
  pub thunk_count: u64,
  pub thunk_forces: u64,
  pub thunk_hits: u64,
  pub cache_hits: u64,
  // isDefEq breakdown
  pub quick_true: u64,
  pub quick_false: u64,
  pub equiv_hits: u64,
  pub ptr_success_hits: u64,
  pub ptr_failure_hits: u64,
  pub proof_irrel_hits: u64,
  pub step10_fires: u64,
  pub step11_fires: u64,
  // whnf breakdown
  pub whnf_cache_hits: u64,
  pub whnf_cache_misses: u64,
  pub whnf_equiv_hits: u64,
  pub whnf_core_cache_hits: u64,
  pub whnf_core_cache_misses: u64,
  // delta breakdown
  pub delta_steps: u64,
  pub unfold_cache_hits: u64,
  pub native_reduces: u64,
  pub lazy_delta_iters: u64,
  pub same_head_checks: u64,
  pub same_head_hits: u64,
}

// ============================================================================
// TypeChecker
// ============================================================================

/// The Kernel2 type checker.
pub struct TypeChecker<'env, M: MetaMode> {
  // -- Context (save/restore on scope entry/exit) --

  /// Local variable types, indexed by de Bruijn level.
  pub types: Vec<Val<M>>,
  /// Let-bound values (None for lambda-bound).
  pub let_values: Vec<Option<Val<M>>>,
  /// Binder names (for debugging).
  pub binder_names: Vec<M::Field<Name>>,
  /// The global kernel environment.
  pub env: &'env KEnv<M>,
  /// Primitive type/operation addresses.
  pub prims: &'env Primitives<M>,
  /// Current declaration's safety level.
  pub safety: DefinitionSafety,
  /// Whether Quot types exist in the environment.
  pub quot_init: bool,
  /// Mutual type fixpoint map: key -> (address, level-parametric val factory).
  pub mut_types:
    BTreeMap<usize, (Address, Box<dyn Fn(&[KLevel<M>]) -> Val<M>>)>,
  /// Address of current recursive definition being checked.
  pub rec_addr: Option<Address>,
  /// If true, skip type-checking (only infer types).
  pub infer_only: bool,
  /// If true, use eager reduction mode.
  pub eager_reduce: bool,
  /// Word size for platform-dependent reduction (System.Platform.numBits).
  pub word_size: WordSize,

  // -- Caches (reset between constants) --

  /// Already type-checked constants (keyed by MetaId for identity-safe lookups).
  pub typed_consts: FxHashMap<MetaId<M>, TypedConst<M>>,
  /// Pointer-keyed def-eq failure cache.
  pub ptr_failure_cache: FxHashMap<(usize, usize), (Val<M>, Val<M>)>,
  /// Pointer-keyed def-eq success cache.
  pub ptr_success_cache: FxHashMap<(usize, usize), (Val<M>, Val<M>)>,
  /// Union-find for transitive def-eq.
  pub equiv_manager: EquivManager,
  /// Inference cache: expr -> (context_types_ptrs, typed_expr, type_val).
  /// Keyed by structural KExpr equality (with Rc pointer short-circuit).
  /// Context validated by element-wise pointer comparison of types array.
  pub infer_cache: FxHashMap<KExpr<M>, (Vec<usize>, TypedExpr<M>, Val<M>)>,
  /// WHNF cache: input ptr -> (input_val, output_val).
  pub whnf_cache: FxHashMap<usize, (Val<M>, Val<M>)>,
  /// Structural WHNF cache for constant-headed neutrals:
  /// (const_addr, thunk_ptr_ids) -> whnf result.
  /// Catches cases where the same constant application with shared thunks
  /// is wrapped in different Neutral Rcs.
  pub whnf_structural_cache: FxHashMap<(Address, Vec<usize>), Val<M>>,
  /// Structural WHNF cache (cheap_proj=false): input ptr -> (input_val, output_val).
  pub whnf_core_cache: FxHashMap<usize, (Val<M>, Val<M>)>,
  /// Structural WHNF cache (cheap_proj=true): input ptr -> (input_val, output_val).
  /// Matches Lean's whnfCoreCheapCacheRef.
  pub whnf_core_cheap_cache: FxHashMap<usize, (Val<M>, Val<M>)>,
  /// Delta body evaluation cache: (const addr, levels) -> evaluated body Val.
  /// Mirrors C++ Lean's m_unfold cache. Caches the result of
  /// eval(instantiate_levels(body, levels), empty_env()) before spine application.
  pub unfold_cache: FxHashMap<(Address, Vec<KLevel<M>>), Val<M>>,
  /// Heartbeat counter (monotonically increasing work counter).
  pub heartbeats: usize,
  /// Maximum heartbeats before error.
  pub max_heartbeats: usize,
  /// Maximum thunks before error.
  pub max_thunks: u64,

  // -- Counters --
  pub stats: Stats,

  // -- Keep alive: prevents Rc address reuse from corrupting equiv_manager --
  // The equiv_manager stores raw pointer addresses (usize). If an Rc is dropped
  // and a new Rc reuses the same address, the equiv_manager would incorrectly
  // treat the new value as equivalent to the old one. This vec keeps all values
  // that have been registered in the equiv_manager alive for the TypeChecker's
  // lifetime, matching Lean's `keepAlive` field.
  pub keep_alive: Vec<Val<M>>,

  // -- Debug tracing --
  pub trace: bool,
  pub trace_depth: usize,
  pub trace_prefix: String,
}

impl<'env, M: MetaMode> TypeChecker<'env, M> {
  /// Create a new TypeChecker.
  pub fn new(env: &'env KEnv<M>, prims: &'env Primitives<M>) -> Self {
    TypeChecker {
      types: Vec::new(),
      let_values: Vec::new(),
      binder_names: Vec::new(),
      env,
      prims,
      safety: DefinitionSafety::Safe,
      quot_init: false,
      mut_types: BTreeMap::new(),
      rec_addr: None,
      infer_only: false,
      eager_reduce: false,
      word_size: WordSize::default(),
      typed_consts: FxHashMap::default(),
      ptr_failure_cache: FxHashMap::default(),
      ptr_success_cache: FxHashMap::default(),
      equiv_manager: EquivManager::new(),
      infer_cache: FxHashMap::default(),
      whnf_cache: FxHashMap::default(),
      whnf_structural_cache: FxHashMap::default(),
      whnf_core_cache: FxHashMap::default(),
      whnf_core_cheap_cache: FxHashMap::default(),
      unfold_cache: FxHashMap::default(),
      heartbeats: 0,
      max_heartbeats: DEFAULT_MAX_HEARTBEATS,
      max_thunks: DEFAULT_MAX_THUNKS,
      stats: Stats::default(),
      keep_alive: Vec::new(),
      trace: false,
      trace_depth: 0,
      trace_prefix: String::new(),
    }
  }

  pub fn trace_msg(&self, msg: &str) {
    if self.trace {
      let indent = "  ".repeat(self.trace_depth.min(20));
      eprintln!("{}{indent}{msg}", self.trace_prefix);
    }
  }

  /// Add equivalence between two values, keeping both alive to prevent
  /// Rc address reuse from corrupting the equiv_manager.
  pub fn add_equiv_val(&mut self, a: &Val<M>, b: &Val<M>) {
    self.keep_alive.push(a.clone());
    self.keep_alive.push(b.clone());
    self.equiv_manager.add_equiv(a.ptr_id(), b.ptr_id());
  }

  // -- Depth and context queries --

  /// Current binding depth (= number of locally bound variables).
  pub fn depth(&self) -> usize {
    self.types.len()
  }

  /// Create a fresh free variable at the current depth with the given type.
  pub fn mk_fresh_fvar(&self, ty: Val<M>) -> Val<M> {
    Val::mk_fvar(self.depth(), ty)
  }

  // -- Context management --

  /// Execute `f` with a lambda-bound variable pushed onto the context.
  pub fn with_binder<R>(
    &mut self,
    var_type: Val<M>,
    name: M::Field<Name>,
    f: impl FnOnce(&mut Self) -> R,
  ) -> R {
    self.types.push(var_type);
    self.let_values.push(None);
    self.binder_names.push(name);
    let result = f(self);
    self.binder_names.pop();
    self.let_values.pop();
    self.types.pop();
    result
  }

  /// Execute `f` with a let-bound variable pushed onto the context.
  pub fn with_let_binder<R>(
    &mut self,
    var_type: Val<M>,
    val: Val<M>,
    name: M::Field<Name>,
    f: impl FnOnce(&mut Self) -> R,
  ) -> R {
    self.types.push(var_type);
    self.let_values.push(Some(val));
    self.binder_names.push(name);
    let result = f(self);
    self.binder_names.pop();
    self.let_values.pop();
    self.types.pop();
    result
  }

  /// Execute `f` with context reset (for checking a new constant).
  pub fn with_reset_ctx<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
    let saved_types = std::mem::take(&mut self.types);
    let saved_lets = std::mem::take(&mut self.let_values);
    let saved_names = std::mem::take(&mut self.binder_names);
    let saved_mut_types = std::mem::take(&mut self.mut_types);
    let saved_rec_addr = self.rec_addr.take();
    let saved_infer_only = self.infer_only;
    let saved_eager_reduce = self.eager_reduce;
    self.infer_only = false;
    self.eager_reduce = false;

    let result = f(self);

    self.types = saved_types;
    self.let_values = saved_lets;
    self.binder_names = saved_names;
    self.mut_types = saved_mut_types;
    self.rec_addr = saved_rec_addr;
    self.infer_only = saved_infer_only;
    self.eager_reduce = saved_eager_reduce;
    result
  }

  /// Execute `f` with the given mutual type map.
  pub fn with_mut_types<R>(
    &mut self,
    mt: BTreeMap<usize, (Address, Box<dyn Fn(&[KLevel<M>]) -> Val<M>>)>,
    f: impl FnOnce(&mut Self) -> R,
  ) -> R {
    let saved = std::mem::replace(&mut self.mut_types, mt);
    let result = f(self);
    self.mut_types = saved;
    result
  }

  /// Execute `f` with the given recursive address.
  pub fn with_rec_addr<R>(
    &mut self,
    addr: Address,
    f: impl FnOnce(&mut Self) -> R,
  ) -> R {
    let saved = self.rec_addr.replace(addr);
    let result = f(self);
    self.rec_addr = saved;
    result
  }

  /// Execute `f` in infer-only mode (skip def-eq checks).
  pub fn with_infer_only<R>(
    &mut self,
    f: impl FnOnce(&mut Self) -> R,
  ) -> R {
    let saved = self.infer_only;
    self.infer_only = true;
    let result = f(self);
    self.infer_only = saved;
    result
  }

  /// Execute `f` with the given safety level.
  pub fn with_safety<R>(
    &mut self,
    safety: DefinitionSafety,
    f: impl FnOnce(&mut Self) -> R,
  ) -> R {
    let saved = self.safety;
    self.safety = safety;
    let result = f(self);
    self.safety = saved;
    result
  }

  /// Execute `f` with eager reduction mode.
  pub fn with_eager_reduce<R>(
    &mut self,
    eager: bool,
    f: impl FnOnce(&mut Self) -> R,
  ) -> R {
    let saved = self.eager_reduce;
    self.eager_reduce = eager;
    let result = f(self);
    self.eager_reduce = saved;
    result
  }

  // -- Heartbeat --

  /// Increment heartbeat counter. Returns error if limit exceeded.
  #[inline]
  pub fn heartbeat(&mut self) -> TcResult<(), M> {
    if self.heartbeats >= self.max_heartbeats {
      return Err(TcError::HeartbeatLimitExceeded);
    }
    if self.stats.thunk_count >= self.max_thunks {
      return Err(TcError::KernelException {
        msg: format!(
          "thunk limit exceeded ({})",
          self.max_thunks
        ),
      });
    }
    self.heartbeats += 1;
    Ok(())
  }

  // -- Constant lookup --

  /// Look up a constant in the environment by MetaId.
  pub fn deref_const(&self, id: &MetaId<M>) -> TcResult<&KConstantInfo<M>, M> {
    self.env.get(id).ok_or_else(|| TcError::UnknownConst {
      msg: format!("constant {}", id),
    })
  }

  /// Look up a typed (already checked) constant by MetaId.
  pub fn deref_typed_const(
    &self,
    id: &MetaId<M>,
  ) -> Option<&TypedConst<M>> {
    self.typed_consts.get(id)
  }

  /// Look up a typed constant by address (content-only, for struct-like checks).
  pub fn typed_const_by_addr(
    &self,
    addr: &Address,
  ) -> Option<&TypedConst<M>> {
    let id = self.env.get_id_by_addr(addr)?;
    self.typed_consts.get(id)
  }

  /// Ensure a constant has been typed. If not, creates a provisional entry.
  pub fn ensure_typed_const(&mut self, id: &MetaId<M>) -> TcResult<(), M> {
    if self.typed_consts.contains_key(id) {
      return Ok(());
    }
    let ci = self.env.get(id).ok_or_else(|| TcError::UnknownConst {
      msg: format!("constant {}", id),
    })?;
    let mut tc = provisional_typed_const(ci);

    // Compute is_struct for inductives using env
    if let KConstantInfo::Inductive(iv) = ci {
      let is_struct = !iv.is_rec
        && iv.num_indices == 0
        && iv.ctors.len() == 1
        && matches!(
          self.env.get(&iv.ctors[0]),
          Some(KConstantInfo::Constructor(_))
        );
      if let TypedConst::Inductive {
        is_struct: ref mut s,
        ..
      } = tc
      {
        *s = is_struct;
      }
    }

    self.typed_consts.insert(id.clone(), tc);
    Ok(())
  }

  // -- Cache management --

  /// Reset ephemeral caches (called between constants).
  pub fn reset_caches(&mut self) {
    self.ptr_failure_cache.clear();
    self.ptr_success_cache.clear();
    self.equiv_manager.clear();
    self.infer_cache.clear();
    self.whnf_cache.clear();
    self.whnf_structural_cache.clear();
    self.whnf_core_cache.clear();
    self.whnf_core_cheap_cache.clear();
    // Note: unfold_cache is NOT cleared between constants — definition bodies
    // with the same levels produce the same Val regardless of context.
    self.heartbeats = 0;
  }
}

/// Create a provisional TypedConst from a ConstantInfo (before full checking).
fn provisional_typed_const<M: MetaMode>(ci: &KConstantInfo<M>) -> TypedConst<M> {
  let typ = TypedExpr {
    info: TypeInfo::None,
    body: ci.typ().clone(),
  };
  match ci {
    KConstantInfo::Axiom(_) => TypedConst::Axiom { typ },
    KConstantInfo::Definition(v) => TypedConst::Definition {
      typ,
      value: TypedExpr {
        info: TypeInfo::None,
        body: v.value.clone(),
      },
      is_partial: v.safety == DefinitionSafety::Partial,
    },
    KConstantInfo::Theorem(v) => TypedConst::Theorem {
      typ,
      value: TypedExpr {
        info: TypeInfo::Proof,
        body: v.value.clone(),
      },
    },
    KConstantInfo::Opaque(v) => TypedConst::Opaque {
      typ,
      value: TypedExpr {
        info: TypeInfo::None,
        body: v.value.clone(),
      },
    },
    KConstantInfo::Quotient(v) => TypedConst::Quotient {
      typ,
      kind: v.kind,
    },
    KConstantInfo::Inductive(_) => TypedConst::Inductive {
      typ,
      is_struct: false,
    },
    KConstantInfo::Constructor(v) => TypedConst::Constructor {
      typ,
      cidx: v.cidx,
      num_fields: v.num_fields,
    },
    KConstantInfo::Recursor(v) => TypedConst::Recursor {
      typ,
      num_params: v.num_params,
      num_motives: v.num_motives,
      num_minors: v.num_minors,
      num_indices: v.num_indices,
      k: v.k,
      induct_addr: helpers::get_major_induct(
        &v.cv.typ,
        v.num_params,
        v.num_motives,
        v.num_minors,
        v.num_indices,
      )
      .map(|id| id.addr)
      .unwrap_or_else(|| Address::hash(b"unknown")),
      rules: v
        .rules
        .iter()
        .map(|r| {
          (
            r.nfields,
            TypedExpr {
              info: TypeInfo::None,
              body: r.rhs.clone(),
            },
          )
        })
        .collect(),
    },
  }
}
