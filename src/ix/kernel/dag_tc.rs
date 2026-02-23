use core::ptr::NonNull;

use num_bigint::BigUint;
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
use rustc_hash::FxHashMap;

use crate::ix::env::{
  BinderInfo, ConstantInfo, Env, Level, Literal, Name, ReducibilityHints,
};
use crate::lean::nat::Nat;

use super::convert::{from_expr, to_expr};
use super::dag::*;
use super::error::TcError;
use super::level::{
  all_expr_uparams_defined, eq_antisymm, eq_antisymm_many, is_zero,
  no_dupes_all_params,
};
use super::upcopy::replace_child;
use super::whnf::{
  has_loose_bvars, mk_name2, nat_lit_dag, subst_expr_levels,
  try_reduce_native_dag, try_reduce_nat_dag, whnf_dag,
};

type TcResult<T> = Result<T, TcError>;

/// DAG-native type checker.
///
/// Operates directly on `DAGPtr` nodes, avoiding Expr↔DAG round-trips.
/// Caches are keyed by `dag_ptr_key` (raw pointer address), which is safe
/// because DAG nodes are never freed during a single `check_declar` call.
pub struct DagTypeChecker<'env> {
  pub env: &'env Env,
  pub whnf_cache: FxHashMap<usize, DAGPtr>,
  pub whnf_no_delta_cache: FxHashMap<usize, DAGPtr>,
  pub infer_cache: FxHashMap<usize, DAGPtr>,
  /// Cache for `infer_const` results, keyed by the Blake3 hash of the
  /// Cnst node's Expr representation (name + levels).  Avoids repeated
  /// `from_expr` calls for the same constant at the same universe levels.
  pub const_type_cache: FxHashMap<blake3::Hash, DAGPtr>,
  pub local_counter: u64,
  pub local_types: FxHashMap<Name, DAGPtr>,
  /// Stack of corresponding bound variable pairs for binder comparison.
  /// Each entry `(key_x, key_y)` means `Var_x` and `Var_y` should be
  /// treated as equal when comparing under their respective binders.
  binder_eq_map: Vec<(usize, usize)>,
  // Debug counters
  whnf_calls: u64,
  def_eq_calls: u64,
  infer_calls: u64,
  infer_depth: u64,
  infer_max_depth: u64,
}

impl<'env> DagTypeChecker<'env> {
  pub fn new(env: &'env Env) -> Self {
    DagTypeChecker {
      env,
      whnf_cache: FxHashMap::default(),
      whnf_no_delta_cache: FxHashMap::default(),
      infer_cache: FxHashMap::default(),
      const_type_cache: FxHashMap::default(),
      local_counter: 0,
      local_types: FxHashMap::default(),
      binder_eq_map: Vec::new(),
      whnf_calls: 0,
      def_eq_calls: 0,
      infer_calls: 0,
      infer_depth: 0,
      infer_max_depth: 0,
    }
  }

  // ==========================================================================
  // WHNF with caching
  // ==========================================================================

  /// Reduce a DAG node to weak head normal form.
  ///
  /// Checks the cache first, then calls `whnf_dag` and caches the result.
  pub fn whnf(&mut self, ptr: DAGPtr) -> DAGPtr {
    self.whnf_calls += 1;
    let key = dag_ptr_key(ptr);
    if let Some(&cached) = self.whnf_cache.get(&key) {
      return cached;
    }
    let t0 = std::time::Instant::now();
    let mut dag = DAG { head: ptr };
    whnf_dag(&mut dag, self.env, false);
    let result = dag.head;
    let ms = t0.elapsed().as_millis();
    if ms > 100 {
      eprintln!("[whnf SLOW] {}ms whnf_calls={}", ms, self.whnf_calls);
    }
    self.whnf_cache.insert(key, result);
    result
  }

  /// Reduce to WHNF without delta (definition) unfolding.
  ///
  /// Used in definitional equality to try structural comparison before
  /// committing to delta reduction.
  pub fn whnf_no_delta(&mut self, ptr: DAGPtr) -> DAGPtr {
    self.whnf_calls += 1;
    if self.whnf_calls % 100 == 0 {
      eprintln!("[DagTC::whnf_no_delta] calls={}", self.whnf_calls);
    }
    let key = dag_ptr_key(ptr);
    if let Some(&cached) = self.whnf_no_delta_cache.get(&key) {
      return cached;
    }
    let mut dag = DAG { head: ptr };
    whnf_dag(&mut dag, self.env, true);
    let result = dag.head;
    self.whnf_no_delta_cache.insert(key, result);
    result
  }

  // ==========================================================================
  // Ensure helpers
  // ==========================================================================

  /// If `ptr` is already a Sort, return its level. Otherwise WHNF and check.
  pub fn ensure_sort(&mut self, ptr: DAGPtr) -> TcResult<Level> {
    if let DAGPtr::Sort(p) = ptr {
      let level = unsafe { &(*p.as_ptr()).level };
      return Ok(level.clone());
    }
    let t0 = std::time::Instant::now();
    let whnfd = self.whnf(ptr);
    let ms = t0.elapsed().as_millis();
    if ms > 100 {
      eprintln!("[ensure_sort] whnf took {}ms", ms);
    }
    match whnfd {
      DAGPtr::Sort(p) => {
        let level = unsafe { &(*p.as_ptr()).level };
        Ok(level.clone())
      },
      _ => Err(TcError::TypeExpected {
        expr: dag_to_expr(ptr),
        inferred: dag_to_expr(whnfd),
      }),
    }
  }

  /// If `ptr` is already a Pi, return it. Otherwise WHNF and check.
  pub fn ensure_pi(&mut self, ptr: DAGPtr) -> TcResult<DAGPtr> {
    if let DAGPtr::Pi(_) = ptr {
      return Ok(ptr);
    }
    let t0 = std::time::Instant::now();
    let whnfd = self.whnf(ptr);
    let ms = t0.elapsed().as_millis();
    if ms > 100 {
      eprintln!("[ensure_pi] whnf took {}ms", ms);
    }
    match whnfd {
      DAGPtr::Pi(_) => Ok(whnfd),
      _ => Err(TcError::FunctionExpected {
        expr: dag_to_expr(ptr),
        inferred: dag_to_expr(whnfd),
      }),
    }
  }

  /// Infer the type of `ptr` and ensure it's a Sort; return the universe level.
  pub fn infer_sort_of(&mut self, ptr: DAGPtr) -> TcResult<Level> {
    let ty = self.infer(ptr)?;
    let whnfd = self.whnf(ty);
    self.ensure_sort(whnfd)
  }

  // ==========================================================================
  // Definitional equality
  // ==========================================================================

  /// Check definitional equality of two DAG nodes.
  ///
  /// Uses a conjunction work stack: processes pairs iteratively, all must
  /// be equal. Binder comparison uses recursive calls with a binder
  /// correspondence map rather than pushing raw bodies.
  pub fn def_eq(&mut self, x: DAGPtr, y: DAGPtr) -> bool {
    self.def_eq_calls += 1;
    eprintln!("[def_eq#{}] depth={}", self.def_eq_calls, self.infer_depth);
    const STEP_LIMIT: u64 = 1_000_000;
    let mut work: Vec<(DAGPtr, DAGPtr)> = vec![(x, y)];
    let mut steps: u64 = 0;
    while let Some((x, y)) = work.pop() {
      steps += 1;
      if steps > STEP_LIMIT {
        return false;
      }
      if !self.def_eq_step(x, y, &mut work) {
        return false;
      }
    }
    true
  }

  /// Quick syntactic checks at DAG level.
  fn def_eq_quick_check(&self, x: DAGPtr, y: DAGPtr) -> Option<bool> {
    if dag_ptr_key(x) == dag_ptr_key(y) {
      return Some(true);
    }
    unsafe {
      match (x, y) {
        (DAGPtr::Sort(a), DAGPtr::Sort(b)) => {
          Some(eq_antisymm(&(*a.as_ptr()).level, &(*b.as_ptr()).level))
        },
        (DAGPtr::Cnst(a), DAGPtr::Cnst(b)) => {
          let ca = &*a.as_ptr();
          let cb = &*b.as_ptr();
          if ca.name == cb.name && eq_antisymm_many(&ca.levels, &cb.levels) {
            Some(true)
          } else {
            None // different names may still be delta-equal
          }
        },
        (DAGPtr::Lit(a), DAGPtr::Lit(b)) => {
          Some((*a.as_ptr()).val == (*b.as_ptr()).val)
        },
        (DAGPtr::Var(a), DAGPtr::Var(b)) => {
          let va = &*a.as_ptr();
          let vb = &*b.as_ptr();
          match (&va.fvar_name, &vb.fvar_name) {
            (Some(na), Some(nb)) => {
              if na == nb { Some(true) } else { None }
            },
            (None, None) => {
              let ka = dag_ptr_key(x);
              let kb = dag_ptr_key(y);
              Some(
                self
                  .binder_eq_map
                  .iter()
                  .any(|&(ma, mb)| ma == ka && mb == kb),
              )
            },
            _ => Some(false),
          }
        },
        _ => None,
      }
    }
  }

  /// Process one def_eq pair.
  fn def_eq_step(
    &mut self,
    x: DAGPtr,
    y: DAGPtr,
    work: &mut Vec<(DAGPtr, DAGPtr)>,
  ) -> bool {
    if let Some(quick) = self.def_eq_quick_check(x, y) {
      return quick;
    }
    let x_n = self.whnf_no_delta(x);
    let y_n = self.whnf_no_delta(y);
    if let Some(quick) = self.def_eq_quick_check(x_n, y_n) {
      return quick;
    }
    if self.proof_irrel_eq(x_n, y_n) {
      return true;
    }
    match self.lazy_delta_step(x_n, y_n) {
      DagDeltaResult::Found(result) => result,
      DagDeltaResult::Exhausted(x_e, y_e) => {
        if self.def_eq_const(x_e, y_e) { return true; }
        if self.def_eq_proj_push(x_e, y_e, work) { return true; }
        if self.def_eq_app_push(x_e, y_e, work) { return true; }
        if self.def_eq_binder_full(x_e, y_e) { return true; }
        if self.try_eta_expansion(x_e, y_e) { return true; }
        if self.try_eta_struct(x_e, y_e) { return true; }
        if self.is_def_eq_unit_like(x_e, y_e) { return true; }
        false
      },
    }
  }

  // --- Proof irrelevance ---

  /// If both x and y are proofs of the same proposition, they are def-eq.
  fn proof_irrel_eq(&mut self, x: DAGPtr, y: DAGPtr) -> bool {
    // Skip for binder types: inferring Fun/Pi/Lam would recurse into
    // binder bodies. Kept as a conservative guard for def_eq_binder_full.
    if matches!(x, DAGPtr::Fun(_) | DAGPtr::Pi(_) | DAGPtr::Lam(_)) {
      return false;
    }
    if matches!(y, DAGPtr::Fun(_) | DAGPtr::Pi(_) | DAGPtr::Lam(_)) {
      return false;
    }
    let x_ty = match self.infer(x) {
      Ok(ty) => ty,
      Err(_) => return false,
    };
    if !self.is_proposition(x_ty) {
      return false;
    }
    let y_ty = match self.infer(y) {
      Ok(ty) => ty,
      Err(_) => return false,
    };
    if !self.is_proposition(y_ty) {
      return false;
    }
    self.def_eq(x_ty, y_ty)
  }

  /// Check if a type lives in Prop (Sort 0).
  fn is_proposition(&mut self, ty: DAGPtr) -> bool {
    let whnfd = self.whnf(ty);
    match whnfd {
      DAGPtr::Sort(s) => unsafe { is_zero(&(*s.as_ptr()).level) },
      _ => false,
    }
  }

  // --- Lazy delta ---

  fn lazy_delta_step(
    &mut self,
    x: DAGPtr,
    y: DAGPtr,
  ) -> DagDeltaResult {
    let mut x = x;
    let mut y = y;
    let mut iters: u32 = 0;
    const MAX_DELTA_ITERS: u32 = 10_000;
    loop {
      iters += 1;
      if iters > MAX_DELTA_ITERS {
        return DagDeltaResult::Exhausted(x, y);
      }

      if let Some(quick) = self.def_eq_nat_offset(x, y) {
        return DagDeltaResult::Found(quick);
      }

      if let Some(x_r) = try_lazy_delta_nat_native(x, self.env) {
        let x_r = self.whnf_no_delta(x_r);
        if let Some(quick) = self.def_eq_quick_check(x_r, y) {
          return DagDeltaResult::Found(quick);
        }
        x = x_r;
        continue;
      }
      if let Some(y_r) = try_lazy_delta_nat_native(y, self.env) {
        let y_r = self.whnf_no_delta(y_r);
        if let Some(quick) = self.def_eq_quick_check(x, y_r) {
          return DagDeltaResult::Found(quick);
        }
        y = y_r;
        continue;
      }

      let x_def = dag_get_applied_def(x, self.env);
      let y_def = dag_get_applied_def(y, self.env);
      match (&x_def, &y_def) {
        (None, None) => return DagDeltaResult::Exhausted(x, y),
        (Some(_), None) => {
          x = self.dag_delta(x);
        },
        (None, Some(_)) => {
          y = self.dag_delta(y);
        },
        (Some((x_name, x_hint)), Some((y_name, y_hint))) => {
          if x_name == y_name && x_hint == y_hint {
            if self.def_eq_app_eager(x, y) {
              return DagDeltaResult::Found(true);
            }
            x = self.dag_delta(x);
            y = self.dag_delta(y);
          } else if hint_lt(x_hint, y_hint) {
            y = self.dag_delta(y);
          } else {
            x = self.dag_delta(x);
          }
        },
      }

      if let Some(quick) = self.def_eq_quick_check(x, y) {
        return DagDeltaResult::Found(quick);
      }
    }
  }

  /// Unfold a definition and do cheap WHNF (no delta).
  fn dag_delta(&mut self, ptr: DAGPtr) -> DAGPtr {
    match dag_try_unfold_def(ptr, self.env) {
      Some(unfolded) => self.whnf_no_delta(unfolded),
      None => ptr,
    }
  }

  // --- Nat offset equality ---

  fn def_eq_nat_offset(
    &mut self,
    x: DAGPtr,
    y: DAGPtr,
  ) -> Option<bool> {
    if is_nat_zero_dag(x) && is_nat_zero_dag(y) {
      return Some(true);
    }
    match (is_nat_succ_dag(x), is_nat_succ_dag(y)) {
      (Some(x_pred), Some(y_pred)) => Some(self.def_eq(x_pred, y_pred)),
      _ => None,
    }
  }

  // --- Congruence ---

  fn def_eq_const(&self, x: DAGPtr, y: DAGPtr) -> bool {
    unsafe {
      match (x, y) {
        (DAGPtr::Cnst(a), DAGPtr::Cnst(b)) => {
          let ca = &*a.as_ptr();
          let cb = &*b.as_ptr();
          ca.name == cb.name && eq_antisymm_many(&ca.levels, &cb.levels)
        },
        _ => false,
      }
    }
  }

  fn def_eq_proj_push(
    &self,
    x: DAGPtr,
    y: DAGPtr,
    work: &mut Vec<(DAGPtr, DAGPtr)>,
  ) -> bool {
    unsafe {
      match (x, y) {
        (DAGPtr::Proj(a), DAGPtr::Proj(b)) => {
          let pa = &*a.as_ptr();
          let pb = &*b.as_ptr();
          if pa.idx == pb.idx {
            work.push((pa.expr, pb.expr));
            true
          } else {
            false
          }
        },
        _ => false,
      }
    }
  }

  fn def_eq_app_push(
    &self,
    x: DAGPtr,
    y: DAGPtr,
    work: &mut Vec<(DAGPtr, DAGPtr)>,
  ) -> bool {
    let (f1, args1) = dag_unfold_apps(x);
    if args1.is_empty() {
      return false;
    }
    let (f2, args2) = dag_unfold_apps(y);
    if args2.is_empty() {
      return false;
    }
    if args1.len() != args2.len() {
      return false;
    }
    work.push((f1, f2));
    for (&a, &b) in args1.iter().zip(args2.iter()) {
      work.push((a, b));
    }
    true
  }

  /// Eager app congruence (used by lazy_delta_step).
  fn def_eq_app_eager(&mut self, x: DAGPtr, y: DAGPtr) -> bool {
    let (f1, args1) = dag_unfold_apps(x);
    if args1.is_empty() {
      return false;
    }
    let (f2, args2) = dag_unfold_apps(y);
    if args2.is_empty() {
      return false;
    }
    if args1.len() != args2.len() {
      return false;
    }
    if !self.def_eq(f1, f2) {
      return false;
    }
    args1.iter().zip(args2.iter()).all(|(&a, &b)| self.def_eq(a, b))
  }

  // --- Binder full ---

  /// Compare Pi/Fun binders: peel matching layers, push var correspondence
  /// into `binder_eq_map`, and compare bodies recursively.
  fn def_eq_binder_full(&mut self, x: DAGPtr, y: DAGPtr) -> bool {
    let mut cx = x;
    let mut cy = y;
    let mut matched = false;
    let mut n_pushed: usize = 0;
    loop {
      unsafe {
        match (cx, cy) {
          (DAGPtr::Pi(px), DAGPtr::Pi(py)) => {
            let pi_x = &*px.as_ptr();
            let pi_y = &*py.as_ptr();
            if !self.def_eq(pi_x.dom, pi_y.dom) {
              for _ in 0..n_pushed {
                self.binder_eq_map.pop();
              }
              return false;
            }
            let lam_x = &*pi_x.img.as_ptr();
            let lam_y = &*pi_y.img.as_ptr();
            let var_x_ptr = NonNull::new(
              &lam_x.var as *const Var as *mut Var,
            )
            .unwrap();
            let var_y_ptr = NonNull::new(
              &lam_y.var as *const Var as *mut Var,
            )
            .unwrap();
            self.binder_eq_map.push((
              dag_ptr_key(DAGPtr::Var(var_x_ptr)),
              dag_ptr_key(DAGPtr::Var(var_y_ptr)),
            ));
            n_pushed += 1;
            cx = lam_x.bod;
            cy = lam_y.bod;
            matched = true;
          },
          (DAGPtr::Fun(fx), DAGPtr::Fun(fy)) => {
            let fun_x = &*fx.as_ptr();
            let fun_y = &*fy.as_ptr();
            if !self.def_eq(fun_x.dom, fun_y.dom) {
              for _ in 0..n_pushed {
                self.binder_eq_map.pop();
              }
              return false;
            }
            let lam_x = &*fun_x.img.as_ptr();
            let lam_y = &*fun_y.img.as_ptr();
            let var_x_ptr = NonNull::new(
              &lam_x.var as *const Var as *mut Var,
            )
            .unwrap();
            let var_y_ptr = NonNull::new(
              &lam_y.var as *const Var as *mut Var,
            )
            .unwrap();
            self.binder_eq_map.push((
              dag_ptr_key(DAGPtr::Var(var_x_ptr)),
              dag_ptr_key(DAGPtr::Var(var_y_ptr)),
            ));
            n_pushed += 1;
            cx = lam_x.bod;
            cy = lam_y.bod;
            matched = true;
          },
          _ => break,
        }
      }
    }
    if !matched {
      return false;
    }
    let result = self.def_eq(cx, cy);
    for _ in 0..n_pushed {
      self.binder_eq_map.pop();
    }
    result
  }

  // --- Eta expansion ---

  fn try_eta_expansion(&mut self, x: DAGPtr, y: DAGPtr) -> bool {
    self.try_eta_expansion_aux(x, y)
      || self.try_eta_expansion_aux(y, x)
  }

  /// Eta: `fun x => f x` ≡ `f` when `f : (x : A) → B`.
  fn try_eta_expansion_aux(
    &mut self,
    x: DAGPtr,
    y: DAGPtr,
  ) -> bool {
    let fx = match x {
      DAGPtr::Fun(f) => f,
      _ => return false,
    };
    let y_ty = match self.infer(y) {
      Ok(t) => t,
      Err(_) => return false,
    };
    let y_ty_whnf = self.whnf(y_ty);
    if !matches!(y_ty_whnf, DAGPtr::Pi(_)) {
      return false;
    }
    unsafe {
      let fun_x = &*fx.as_ptr();
      let lam_x = &*fun_x.img.as_ptr();
      let var_x_ptr =
        NonNull::new(&lam_x.var as *const Var as *mut Var).unwrap();
      let var_x = DAGPtr::Var(var_x_ptr);
      // Build eta body: App(y, var_x)
      // Using the SAME var_x on both sides, so pointer identity
      // handles bound variable matching without binder_eq_map.
      let eta_body = DAGPtr::App(alloc_app(y, var_x, None));
      self.def_eq(lam_x.bod, eta_body)
    }
  }

  // --- Struct eta ---

  fn try_eta_struct(&mut self, x: DAGPtr, y: DAGPtr) -> bool {
    self.try_eta_struct_core(x, y)
      || self.try_eta_struct_core(y, x)
  }

  /// Structure eta: `p =def= S.mk (S.1 p) (S.2 p)` when S is a
  /// single-constructor non-recursive inductive with no indices.
  fn try_eta_struct_core(&mut self, t: DAGPtr, s: DAGPtr) -> bool {
    let (head, args) = dag_unfold_apps(s);
    let ctor_name = match head {
      DAGPtr::Cnst(c) => unsafe { (*c.as_ptr()).name.clone() },
      _ => return false,
    };
    let ctor_info = match self.env.get(&ctor_name) {
      Some(ConstantInfo::CtorInfo(c)) => c,
      _ => return false,
    };
    if !is_structure_like(&ctor_info.induct, self.env) {
      return false;
    }
    let num_params = ctor_info.num_params.to_u64().unwrap() as usize;
    let num_fields = ctor_info.num_fields.to_u64().unwrap() as usize;
    if args.len() != num_params + num_fields {
      return false;
    }
    for i in 0..num_fields {
      let field = args[num_params + i];
      let proj = alloc_proj(
        ctor_info.induct.clone(),
        Nat::from(i as u64),
        t,
        None,
      );
      if !self.def_eq(field, DAGPtr::Proj(proj)) {
        return false;
      }
    }
    true
  }

  // --- Unit-like equality ---

  /// Types with a single zero-field constructor have all inhabitants def-eq.
  fn is_def_eq_unit_like(&mut self, x: DAGPtr, y: DAGPtr) -> bool {
    let x_ty = match self.infer(x) {
      Ok(ty) => ty,
      Err(_) => return false,
    };
    let y_ty = match self.infer(y) {
      Ok(ty) => ty,
      Err(_) => return false,
    };
    if !self.def_eq(x_ty, y_ty) {
      return false;
    }
    let whnf_ty = self.whnf(x_ty);
    let (head, _) = dag_unfold_apps(whnf_ty);
    let name = match head {
      DAGPtr::Cnst(c) => unsafe { (*c.as_ptr()).name.clone() },
      _ => return false,
    };
    match self.env.get(&name) {
      Some(ConstantInfo::InductInfo(iv)) => {
        if iv.ctors.len() != 1 {
          return false;
        }
        if let Some(ConstantInfo::CtorInfo(c)) =
          self.env.get(&iv.ctors[0])
        {
          c.num_fields == Nat::ZERO
        } else {
          false
        }
      },
      _ => false,
    }
  }

  /// Assert that two DAG nodes are definitionally equal; return TcError if not.
  pub fn assert_def_eq(
    &mut self,
    x: DAGPtr,
    y: DAGPtr,
  ) -> TcResult<()> {
    if self.def_eq(x, y) {
      Ok(())
    } else {
      Err(TcError::DefEqFailure {
        lhs: dag_to_expr(x),
        rhs: dag_to_expr(y),
      })
    }
  }

  // ==========================================================================
  // Local context management
  // ==========================================================================

  /// Create a fresh free variable for entering a binder.
  ///
  /// Returns a `DAGPtr::Var` with a unique `fvar_name` (derived from the
  /// binder name and a monotonic counter) and records `ty` as its type
  /// in `local_types`.
  pub fn mk_dag_local(&mut self, name: &Name, ty: DAGPtr) -> DAGPtr {
    let id = self.local_counter;
    self.local_counter += 1;
    let local_name = Name::num(name.clone(), Nat::from(id));
    let var = alloc_val(Var {
      depth: 0,
      binder: BinderPtr::Free,
      fvar_name: Some(local_name.clone()),
      parents: None,
    });
    self.local_types.insert(local_name, ty);
    DAGPtr::Var(var)
  }

  // ==========================================================================
  // Type inference
  // ==========================================================================

  /// Infer the type of a DAG node.
  ///
  /// Stub: will be fully implemented in Step 3.
  pub fn infer(&mut self, ptr: DAGPtr) -> TcResult<DAGPtr> {
    self.infer_calls += 1;
    self.infer_depth += 1;
    // Heartbeat every 500 calls
    if self.infer_calls % 500 == 0 {
      eprintln!("[infer HEARTBEAT] calls={} depth={} cache={} whnf={} def_eq={} copy_subst_total_nodes=?",
        self.infer_calls, self.infer_depth, self.infer_cache.len(), self.whnf_calls, self.def_eq_calls);
    }
    if self.infer_depth > self.infer_max_depth {
      self.infer_max_depth = self.infer_depth;
      if self.infer_max_depth % 5 == 0 || self.infer_max_depth > 20 {
        let detail = unsafe { match ptr {
          DAGPtr::Cnst(p) => format!("Cnst({})", (*p.as_ptr()).name.pretty()),
          DAGPtr::App(_) => "App".to_string(),
          DAGPtr::Fun(p) => format!("Fun({})", (*p.as_ptr()).binder_name.pretty()),
          DAGPtr::Pi(p) => format!("Pi({})", (*p.as_ptr()).binder_name.pretty()),
          _ => format!("{:?}", std::mem::discriminant(&ptr)),
        }};
        eprintln!("[infer] NEW MAX DEPTH={} calls={} cache={} {detail}", self.infer_max_depth, self.infer_calls, self.infer_cache.len());
      }
    }
    if self.infer_calls % 1000 == 0 {
      eprintln!("[infer] calls={} depth={} cache={}", self.infer_calls, self.infer_depth, self.infer_cache.len());
    }
    let key = dag_ptr_key(ptr);
    if let Some(&cached) = self.infer_cache.get(&key) {
      self.infer_depth -= 1;
      return Ok(cached);
    }
    let t0 = std::time::Instant::now();
    let result = self.infer_core(ptr)?;
    let ms = t0.elapsed().as_millis();
    if ms > 100 {
      let detail = unsafe { match ptr {
        DAGPtr::Cnst(p) => format!("Cnst({})", (*p.as_ptr()).name.pretty()),
        DAGPtr::App(_) => "App".to_string(),
        DAGPtr::Fun(p) => format!("Fun({})", (*p.as_ptr()).binder_name.pretty()),
        DAGPtr::Pi(p) => format!("Pi({})", (*p.as_ptr()).binder_name.pretty()),
        _ => format!("{:?}", std::mem::discriminant(&ptr)),
      }};
      eprintln!("[infer] depth={} took {}ms {detail}", self.infer_depth, ms);
    }
    self.infer_cache.insert(key, result);
    self.infer_depth -= 1;
    Ok(result)
  }

  fn infer_core(&mut self, ptr: DAGPtr) -> TcResult<DAGPtr> {
    match ptr {
      DAGPtr::Var(p) => unsafe {
        let var = &*p.as_ptr();
        match &var.fvar_name {
          Some(name) => match self.local_types.get(name) {
            Some(&ty) => Ok(ty),
            None => Err(TcError::KernelException {
              msg: "cannot infer type of free variable without context"
                .into(),
            }),
          },
          None => match var.binder {
            BinderPtr::Free => Err(TcError::FreeBoundVariable {
              idx: var.depth,
            }),
            BinderPtr::Lam(_) => Err(TcError::KernelException {
              msg: "unexpected bound variable during inference".into(),
            }),
          },
        }
      },
      DAGPtr::Sort(p) => {
        let level = unsafe { &(*p.as_ptr()).level };
        let result = alloc_val(Sort {
          level: Level::succ(level.clone()),
          parents: None,
        });
        Ok(DAGPtr::Sort(result))
      },
      DAGPtr::Cnst(p) => {
        let (name, levels) = unsafe {
          let cnst = &*p.as_ptr();
          (cnst.name.clone(), cnst.levels.clone())
        };
        self.infer_const(&name, &levels)
      },
      DAGPtr::App(_) => self.infer_app(ptr),
      DAGPtr::Fun(_) => self.infer_lambda(ptr),
      DAGPtr::Pi(_) => self.infer_pi(ptr),
      DAGPtr::Let(p) => {
        let (typ, val, bod_lam) = unsafe {
          let let_node = &*p.as_ptr();
          (let_node.typ, let_node.val, let_node.bod)
        };
        let val_ty = self.infer(val)?;
        self.assert_def_eq(val_ty, typ)?;
        let body = dag_copy_subst(bod_lam, val);
        self.infer(body)
      },
      DAGPtr::Lit(p) => {
        let val = unsafe { &(*p.as_ptr()).val };
        self.infer_lit(val)
      },
      DAGPtr::Proj(p) => {
        let (type_name, idx, structure) = unsafe {
          let proj = &*p.as_ptr();
          (proj.type_name.clone(), proj.idx.clone(), proj.expr)
        };
        self.infer_proj(&type_name, &idx, structure, ptr)
      },
      DAGPtr::Lam(_) => Err(TcError::KernelException {
        msg: "unexpected standalone Lam during inference".into(),
      }),
    }
  }

  fn infer_const(
    &mut self,
    name: &Name,
    levels: &[Level],
  ) -> TcResult<DAGPtr> {
    // Build a cache key from the constant's name + universe level hashes.
    let cache_key = {
      let mut hasher = blake3::Hasher::new();
      hasher.update(name.get_hash().as_bytes());
      for l in levels {
        hasher.update(l.get_hash().as_bytes());
      }
      hasher.finalize()
    };
    if let Some(&cached) = self.const_type_cache.get(&cache_key) {
      return Ok(cached);
    }

    let ci = self
      .env
      .get(name)
      .ok_or_else(|| TcError::UnknownConst { name: name.clone() })?;

    let decl_params = ci.get_level_params();
    if levels.len() != decl_params.len() {
      return Err(TcError::KernelException {
        msg: format!(
          "universe parameter count mismatch for {}",
          name.pretty()
        ),
      });
    }

    let ty = ci.get_type();
    let dag = from_expr(ty);
    let result = subst_dag_levels(dag.head, decl_params, levels);
    self.const_type_cache.insert(cache_key, result);
    Ok(result)
  }

  fn infer_app(&mut self, e: DAGPtr) -> TcResult<DAGPtr> {
    let (fun, args) = dag_unfold_apps(e);
    let mut fun_ty = self.infer(fun)?;

    for &arg in args.iter() {
      let pi = self.ensure_pi(fun_ty)?;

      let (dom, img) = unsafe {
        match pi {
          DAGPtr::Pi(p) => {
            let pi_ref = &*p.as_ptr();
            (pi_ref.dom, pi_ref.img)
          },
          _ => unreachable!(),
        }
      };
      let arg_ty = self.infer(arg)?;
      if !self.def_eq(arg_ty, dom) {
        return Err(TcError::DefEqFailure {
          lhs: dag_to_expr(arg_ty),
          rhs: dag_to_expr(dom),
        });
      }
      eprintln!("[infer_app] before dag_copy_subst");
      fun_ty = dag_copy_subst(img, arg);
      eprintln!("[infer_app] after dag_copy_subst");
    }

    Ok(fun_ty)
  }

  fn infer_lambda(&mut self, e: DAGPtr) -> TcResult<DAGPtr> {
    let mut cursor = e;
    let mut locals: Vec<DAGPtr> = Vec::new();
    let mut binder_doms: Vec<DAGPtr> = Vec::new();
    let mut binder_infos: Vec<BinderInfo> = Vec::new();
    let mut binder_names: Vec<Name> = Vec::new();

    // Peel Fun layers
    let mut binder_idx = 0usize;
    while let DAGPtr::Fun(fun_ptr) = cursor {
      let t_binder = std::time::Instant::now();
      let (name, bi, dom, img) = unsafe {
        let fun = &*fun_ptr.as_ptr();
        (
          fun.binder_name.clone(),
          fun.binder_info.clone(),
          fun.dom,
          fun.img,
        )
      };

      let t_sort = std::time::Instant::now();
      self.infer_sort_of(dom)?;
      let sort_ms = t_sort.elapsed().as_millis();

      let local = self.mk_dag_local(&name, dom);
      locals.push(local);
      binder_doms.push(dom);
      binder_infos.push(bi);
      binder_names.push(name.clone());

      // Enter the binder: deep copy because img is from the TERM DAG
      let t_copy = std::time::Instant::now();
      cursor = dag_copy_subst(img, local);
      let copy_ms = t_copy.elapsed().as_millis();

      let total_ms = t_binder.elapsed().as_millis();
      if total_ms > 5 {
        eprintln!("[infer_lambda] binder#{binder_idx} {} total={}ms sort={}ms copy={}ms",
          name.pretty(), total_ms, sort_ms, copy_ms);
      }
      binder_idx += 1;
    }

    // Infer the body type
    let t_body = std::time::Instant::now();
    let body_ty = self.infer(cursor)?;
    let body_ms = t_body.elapsed().as_millis();
    if body_ms > 5 {
      eprintln!("[infer_lambda] body={}ms after {} binders", body_ms, binder_idx);
    }

    // Abstract back: build Pi telescope over the locals
    Ok(build_pi_over_locals(
      body_ty,
      &locals,
      &binder_names,
      &binder_infos,
      &binder_doms,
    ))
  }

  fn infer_pi(&mut self, e: DAGPtr) -> TcResult<DAGPtr> {
    let mut cursor = e;
    let mut locals: Vec<DAGPtr> = Vec::new();
    let mut universes: Vec<Level> = Vec::new();

    // Peel Pi layers
    while let DAGPtr::Pi(pi_ptr) = cursor {
      let (name, dom, img) = unsafe {
        let pi = &*pi_ptr.as_ptr();
        (pi.binder_name.clone(), pi.dom, pi.img)
      };

      let dom_univ = self.infer_sort_of(dom)?;
      universes.push(dom_univ);

      let local = self.mk_dag_local(&name, dom);
      locals.push(local);

      // Enter the binder: deep copy because img is from the TERM DAG
      cursor = dag_copy_subst(img, local);
    }

    // The body must also be a type
    let mut result_level = self.infer_sort_of(cursor)?;

    // Compute imax of all levels (innermost first)
    for univ in universes.into_iter().rev() {
      result_level = Level::imax(univ, result_level);
    }

    let result = alloc_val(Sort {
      level: result_level,
      parents: None,
    });
    Ok(DAGPtr::Sort(result))
  }

  fn infer_lit(&mut self, lit: &Literal) -> TcResult<DAGPtr> {
    let name = match lit {
      Literal::NatVal(_) => Name::str(Name::anon(), "Nat".into()),
      Literal::StrVal(_) => Name::str(Name::anon(), "String".into()),
    };
    let cnst = alloc_val(Cnst { name, levels: vec![], parents: None });
    Ok(DAGPtr::Cnst(cnst))
  }

  fn infer_proj(
    &mut self,
    type_name: &Name,
    idx: &Nat,
    structure: DAGPtr,
    _proj_expr: DAGPtr,
  ) -> TcResult<DAGPtr> {
    let structure_ty = self.infer(structure)?;
    let structure_ty_whnf = self.whnf(structure_ty);

    let (head, struct_ty_args) = dag_unfold_apps(structure_ty_whnf);
    let (head_name, head_levels) = unsafe {
      match head {
        DAGPtr::Cnst(p) => {
          let cnst = &*p.as_ptr();
          (cnst.name.clone(), cnst.levels.clone())
        },
        _ => {
          return Err(TcError::KernelException {
            msg: "projection structure type is not a constant".into(),
          })
        },
      }
    };

    let ind = self.env.get(&head_name).ok_or_else(|| {
      TcError::UnknownConst { name: head_name.clone() }
    })?;

    let (num_params, ctor_name) = match ind {
      ConstantInfo::InductInfo(iv) => {
        let ctor = iv.ctors.first().ok_or_else(|| {
          TcError::KernelException {
            msg: "inductive has no constructors".into(),
          }
        })?;
        (iv.num_params.to_u64().unwrap(), ctor.clone())
      },
      _ => {
        return Err(TcError::KernelException {
          msg: "projection type is not an inductive".into(),
        })
      },
    };

    let ctor_ci = self.env.get(&ctor_name).ok_or_else(|| {
      TcError::UnknownConst { name: ctor_name.clone() }
    })?;

    let ctor_ty_dag = from_expr(ctor_ci.get_type());
    let mut ctor_ty = subst_dag_levels(
      ctor_ty_dag.head,
      ctor_ci.get_level_params(),
      &head_levels,
    );

    // Skip params: instantiate with the actual type arguments
    for i in 0..num_params as usize {
      let whnf_ty = self.whnf(ctor_ty);
      match whnf_ty {
        DAGPtr::Pi(p) => {
          let img = unsafe { (*p.as_ptr()).img };
          ctor_ty = dag_copy_subst(img, struct_ty_args[i]);
        },
        _ => {
          return Err(TcError::KernelException {
            msg: "ran out of constructor telescope (params)".into(),
          })
        },
      }
    }

    // Walk to the idx-th field, substituting projections
    let idx_usize = idx.to_u64().unwrap() as usize;
    for i in 0..idx_usize {
      let whnf_ty = self.whnf(ctor_ty);
      match whnf_ty {
        DAGPtr::Pi(p) => {
          let img = unsafe { (*p.as_ptr()).img };
          let proj = alloc_proj(
            type_name.clone(),
            Nat::from(i as u64),
            structure,
            None,
          );
          ctor_ty = dag_copy_subst(img, DAGPtr::Proj(proj));
        },
        _ => {
          return Err(TcError::KernelException {
            msg: "ran out of constructor telescope (fields)".into(),
          })
        },
      }
    }

    // Extract the target field's type (the domain of the next Pi)
    let whnf_ty = self.whnf(ctor_ty);
    match whnf_ty {
      DAGPtr::Pi(p) => {
        let dom = unsafe { (*p.as_ptr()).dom };
        Ok(dom)
      },
      _ => Err(TcError::KernelException {
        msg: "ran out of constructor telescope (target field)".into(),
      }),
    }
  }

  // ==========================================================================
  // Declaration checking
  // ==========================================================================

  /// Validate a declaration's type: no duplicate uparams, no loose bvars,
  /// all uparams defined, and type infers to a Sort.
  pub fn check_declar_info(
    &mut self,
    info: &crate::ix::env::ConstantVal,
  ) -> TcResult<()> {
    if !no_dupes_all_params(&info.level_params) {
      return Err(TcError::KernelException {
        msg: format!(
          "duplicate universe parameters in {}",
          info.name.pretty()
        ),
      });
    }
    if has_loose_bvars(&info.typ) {
      return Err(TcError::KernelException {
        msg: format!(
          "free bound variables in type of {}",
          info.name.pretty()
        ),
      });
    }
    if !all_expr_uparams_defined(&info.typ, &info.level_params) {
      return Err(TcError::KernelException {
        msg: format!(
          "undeclared universe parameters in type of {}",
          info.name.pretty()
        ),
      });
    }
    let ty_dag = from_expr(&info.typ).head;
    self.infer_sort_of(ty_dag)?;
    Ok(())
  }

  /// Check a declaration with both type and value (DefnInfo, ThmInfo, OpaqueInfo).
  fn check_value_declar(
    &mut self,
    cnst: &crate::ix::env::ConstantVal,
    value: &crate::ix::env::Expr,
  ) -> TcResult<()> {
    let t_start = std::time::Instant::now();
    self.check_declar_info(cnst)?;
    eprintln!("[cvd @{}ms] check_declar_info done", t_start.elapsed().as_millis());
    if !all_expr_uparams_defined(value, &cnst.level_params) {
      return Err(TcError::KernelException {
        msg: format!(
          "undeclared universe parameters in value of {}",
          cnst.name.pretty()
        ),
      });
    }
    let t1 = std::time::Instant::now();
    let val_dag = from_expr(value).head;
    eprintln!("[check_value_declar] {} from_expr(value): {}ms", cnst.name.pretty(), t1.elapsed().as_millis());
    let t2 = std::time::Instant::now();
    let inferred_type = self.infer(val_dag)?;
    eprintln!("[check_value_declar] {} infer: {}ms", cnst.name.pretty(), t2.elapsed().as_millis());
    let t3 = std::time::Instant::now();
    let ty_dag = from_expr(&cnst.typ).head;
    eprintln!("[check_value_declar] {} from_expr(type): {}ms", cnst.name.pretty(), t3.elapsed().as_millis());
    if !self.def_eq(inferred_type, ty_dag) {
      let lhs_expr = dag_to_expr(inferred_type);
      let rhs_expr = dag_to_expr(ty_dag);
      return Err(TcError::DefEqFailure {
        lhs: lhs_expr,
        rhs: rhs_expr,
      });
    }
    Ok(())
  }

  /// Check a single declaration.
  pub fn check_declar(
    &mut self,
    ci: &ConstantInfo,
  ) -> TcResult<()> {
    match ci {
      ConstantInfo::AxiomInfo(v) => {
        self.check_declar_info(&v.cnst)?;
      },
      ConstantInfo::DefnInfo(v) => {
        self.check_value_declar(&v.cnst, &v.value)?;
      },
      ConstantInfo::ThmInfo(v) => {
        self.check_value_declar(&v.cnst, &v.value)?;
      },
      ConstantInfo::OpaqueInfo(v) => {
        self.check_value_declar(&v.cnst, &v.value)?;
      },
      ConstantInfo::QuotInfo(v) => {
        self.check_declar_info(&v.cnst)?;
        super::quot::check_quot(self.env)?;
      },
      ConstantInfo::InductInfo(v) => {
        // Use Expr-level TypeChecker for structural inductive validation
        // (positivity, return types, field universes). These checks aren't
        // performance-critical and work on small type telescopes.
        let mut expr_tc = super::tc::TypeChecker::new(self.env);
        super::inductive::check_inductive(v, &mut expr_tc)?;
      },
      ConstantInfo::CtorInfo(v) => {
        self.check_declar_info(&v.cnst)?;
        if self.env.get(&v.induct).is_none() {
          return Err(TcError::UnknownConst {
            name: v.induct.clone(),
          });
        }
      },
      ConstantInfo::RecInfo(v) => {
        self.check_declar_info(&v.cnst)?;
        for ind_name in &v.all {
          if self.env.get(ind_name).is_none() {
            return Err(TcError::UnknownConst {
              name: ind_name.clone(),
            });
          }
        }
        super::inductive::validate_k_flag(v, self.env)?;
      },
    }
    Ok(())
  }
}


/// Convert a DAGPtr to an Expr. Used only when constructing TcError values.
fn dag_to_expr(ptr: DAGPtr) -> crate::ix::env::Expr {
  let dag = DAG { head: ptr };
  to_expr(&dag)
}

/// Check all declarations in an environment in parallel using the DAG TC.
pub fn dag_check_env(env: &Env) -> Vec<(Name, TcError)> {
  use std::collections::BTreeSet;
  use std::io::Write;
  use std::sync::Mutex;
  use std::sync::atomic::{AtomicUsize, Ordering};

  let total = env.len();
  let checked = AtomicUsize::new(0);

  struct Display {
    active: BTreeSet<String>,
    prev_lines: usize,
  }
  let display =
    Mutex::new(Display { active: BTreeSet::new(), prev_lines: 0 });

  let refresh = |d: &mut Display, checked: usize| {
    let mut stderr = std::io::stderr().lock();
    if d.prev_lines > 0 {
      write!(stderr, "\x1b[{}A", d.prev_lines).ok();
    }
    write!(
      stderr,
      "\x1b[2K[dag_check_env] {}/{} — {} active\n",
      checked,
      total,
      d.active.len()
    )
    .ok();
    let mut new_lines = 1;
    for name in &d.active {
      write!(stderr, "\x1b[2K  {}\n", name).ok();
      new_lines += 1;
    }
    let extra = d.prev_lines.saturating_sub(new_lines);
    for _ in 0..extra {
      write!(stderr, "\x1b[2K\n").ok();
    }
    if extra > 0 {
      write!(stderr, "\x1b[{}A", extra).ok();
    }
    d.prev_lines = new_lines;
    stderr.flush().ok();
  };

  env
    .par_iter()
    .filter_map(|(name, ci): (&Name, &ConstantInfo)| {
      let pretty = name.pretty();
      {
        let mut d = display.lock().unwrap();
        d.active.insert(pretty.clone());
        refresh(&mut d, checked.load(Ordering::Relaxed));
      }

      let mut tc = DagTypeChecker::new(env);
      let result = tc.check_declar(ci);

      let n = checked.fetch_add(1, Ordering::Relaxed) + 1;
      {
        let mut d = display.lock().unwrap();
        d.active.remove(&pretty);
        refresh(&mut d, n);
      }

      match result {
        Ok(()) => None,
        Err(e) => Some((name.clone(), e)),
      }
    })
    .collect()
}

// ============================================================================
// build_pi_over_locals
// ============================================================================

/// Abstract free variables back into a Pi telescope.
///
/// Given a `body` type (DAGPtr containing free Vars created by `mk_dag_local`)
/// and corresponding binder information, builds a Pi telescope at the DAG level.
///
/// Processes binders from innermost (last) to outermost (first). For each:
/// 1. Allocates a `Lam` with `bod = current_result`
/// 2. Calls `replace_child(free_var, lam.var)` to redirect all references
/// 3. Allocates `Pi(name, bi, dom, lam)` and wires parent pointers
pub fn build_pi_over_locals(
  body: DAGPtr,
  locals: &[DAGPtr],
  names: &[Name],
  bis: &[BinderInfo],
  doms: &[DAGPtr],
) -> DAGPtr {
  let mut result = body;
  // Process from innermost (last) to outermost (first)
  for i in (0..locals.len()).rev() {
    // 1. Allocate Lam wrapping the current result
    let lam = alloc_lam(0, result, None);
    unsafe {
      let lam_ref = &mut *lam.as_ptr();
      // Wire bod_ref as parent of result
      let bod_ref =
        NonNull::new(&mut lam_ref.bod_ref as *mut Parents).unwrap();
      add_to_parents(result, bod_ref);
      // 2. Redirect all references from the free var to the bound var
      let new_var = NonNull::new(&mut lam_ref.var as *mut Var).unwrap();
      replace_child(locals[i], DAGPtr::Var(new_var));
    }
    // 3. Allocate Pi
    let pi = alloc_pi(names[i].clone(), bis[i].clone(), doms[i], lam, None);
    unsafe {
      let pi_ref = &mut *pi.as_ptr();
      // Wire dom_ref as parent of doms[i]
      let dom_ref =
        NonNull::new(&mut pi_ref.dom_ref as *mut Parents).unwrap();
      add_to_parents(doms[i], dom_ref);
      // Wire img_ref as parent of Lam
      let img_ref =
        NonNull::new(&mut pi_ref.img_ref as *mut Parents).unwrap();
      add_to_parents(DAGPtr::Lam(lam), img_ref);
    }
    result = DAGPtr::Pi(pi);
  }
  result
}

// ============================================================================
// Definitional equality helpers (free functions)
// ============================================================================

/// Result of lazy delta reduction at DAG level.
enum DagDeltaResult {
  Found(bool),
  Exhausted(DAGPtr, DAGPtr),
}

/// Get the name and reducibility hint of an applied definition.
fn dag_get_applied_def(
  ptr: DAGPtr,
  env: &Env,
) -> Option<(Name, ReducibilityHints)> {
  let (head, _) = dag_unfold_apps(ptr);
  let name = match head {
    DAGPtr::Cnst(c) => unsafe { (*c.as_ptr()).name.clone() },
    _ => return None,
  };
  let ci = env.get(&name)?;
  match ci {
    ConstantInfo::DefnInfo(d) => {
      if d.hints == ReducibilityHints::Opaque {
        None
      } else {
        Some((name, d.hints))
      }
    },
    ConstantInfo::ThmInfo(_) => {
      Some((name, ReducibilityHints::Opaque))
    },
    _ => None,
  }
}

/// Try to unfold a definition at DAG level.
fn dag_try_unfold_def(ptr: DAGPtr, env: &Env) -> Option<DAGPtr> {
  let (head, args) = dag_unfold_apps(ptr);
  let (name, levels) = match head {
    DAGPtr::Cnst(c) => unsafe {
      let cr = &*c.as_ptr();
      (cr.name.clone(), cr.levels.clone())
    },
    _ => return None,
  };
  let ci = env.get(&name)?;
  let (def_params, def_value) = match ci {
    ConstantInfo::DefnInfo(d) => {
      if d.hints == ReducibilityHints::Opaque {
        return None;
      }
      (&d.cnst.level_params, &d.value)
    },
    ConstantInfo::ThmInfo(t) => (&t.cnst.level_params, &t.value),
    _ => return None,
  };
  if levels.len() != def_params.len() {
    return None;
  }
  let val = subst_expr_levels(def_value, def_params, &levels);
  let val_dag = from_expr(&val);
  Some(dag_foldl_apps(val_dag.head, &args))
}

/// Try nat/native reduction before delta.
fn try_lazy_delta_nat_native(ptr: DAGPtr, env: &Env) -> Option<DAGPtr> {
  let (head, args) = dag_unfold_apps(ptr);
  match head {
    DAGPtr::Cnst(c) => unsafe {
      let name = &(*c.as_ptr()).name;
      if let Some(r) = try_reduce_native_dag(name, &args) {
        return Some(r);
      }
      if let Some(r) = try_reduce_nat_dag(name, &args, env) {
        return Some(r);
      }
      None
    },
    _ => None,
  }
}

/// Check if a DAGPtr is Nat.zero (either constructor or literal 0).
fn is_nat_zero_dag(ptr: DAGPtr) -> bool {
  unsafe {
    match ptr {
      DAGPtr::Cnst(c) => (*c.as_ptr()).name == mk_name2("Nat", "zero"),
      DAGPtr::Lit(l) => {
        matches!(&(*l.as_ptr()).val, Literal::NatVal(n) if n.0 == BigUint::ZERO)
      },
      _ => false,
    }
  }
}

/// If expression is `Nat.succ arg` or `lit (n+1)`, return the predecessor.
fn is_nat_succ_dag(ptr: DAGPtr) -> Option<DAGPtr> {
  unsafe {
    match ptr {
      DAGPtr::App(app) => {
        let a = &*app.as_ptr();
        match a.fun {
          DAGPtr::Cnst(c)
            if (*c.as_ptr()).name == mk_name2("Nat", "succ") =>
          {
            Some(a.arg)
          },
          _ => None,
        }
      },
      DAGPtr::Lit(l) => match &(*l.as_ptr()).val {
        Literal::NatVal(n) if n.0 > BigUint::ZERO => {
          Some(nat_lit_dag(Nat(n.0.clone() - BigUint::from(1u64))))
        },
        _ => None,
      },
      _ => None,
    }
  }
}

/// Check if a name refers to a structure-like inductive:
/// exactly 1 constructor, not recursive, no indices.
fn is_structure_like(name: &Name, env: &Env) -> bool {
  match env.get(name) {
    Some(ConstantInfo::InductInfo(iv)) => {
      iv.ctors.len() == 1 && !iv.is_rec && iv.num_indices == Nat::ZERO
    },
    _ => false,
  }
}

/// Compare reducibility hints for ordering.
fn hint_lt(a: &ReducibilityHints, b: &ReducibilityHints) -> bool {
  match (a, b) {
    (ReducibilityHints::Opaque, _) => true,
    (_, ReducibilityHints::Opaque) => false,
    (ReducibilityHints::Abbrev, _) => false,
    (_, ReducibilityHints::Abbrev) => true,
    (ReducibilityHints::Regular(ha), ReducibilityHints::Regular(hb)) => {
      ha < hb
    },
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::ix::env::{BinderInfo, Expr, Level, Literal};
  use crate::ix::kernel::convert::from_expr;

  fn mk_name(s: &str) -> Name {
    Name::str(Name::anon(), s.into())
  }

  fn nat_type() -> Expr {
    Expr::cnst(mk_name("Nat"), vec![])
  }

  // ========================================================================
  // subst_dag_levels tests
  // ========================================================================

  #[test]
  fn subst_dag_levels_empty_params() {
    let e = Expr::sort(Level::param(mk_name("u")));
    let dag = from_expr(&e);
    let result = subst_dag_levels(dag.head, &[], &[]);
    let result_dag = DAG { head: result };
    let result_expr = to_expr(&result_dag);
    assert_eq!(result_expr, e);
  }

  #[test]
  fn subst_dag_levels_sort() {
    let u_name = mk_name("u");
    let e = Expr::sort(Level::param(u_name.clone()));
    let dag = from_expr(&e);
    let result = subst_dag_levels(dag.head, &[u_name], &[Level::zero()]);
    let result_dag = DAG { head: result };
    let result_expr = to_expr(&result_dag);
    assert_eq!(result_expr, Expr::sort(Level::zero()));
  }

  #[test]
  fn subst_dag_levels_cnst() {
    let u_name = mk_name("u");
    let e = Expr::cnst(mk_name("List"), vec![Level::param(u_name.clone())]);
    let dag = from_expr(&e);
    let one = Level::succ(Level::zero());
    let result = subst_dag_levels(dag.head, &[u_name], &[one.clone()]);
    let result_dag = DAG { head: result };
    let result_expr = to_expr(&result_dag);
    assert_eq!(result_expr, Expr::cnst(mk_name("List"), vec![one]));
  }

  #[test]
  fn subst_dag_levels_nested() {
    // Pi (A : Sort u) → Sort u  with u := 1
    let u_name = mk_name("u");
    let sort_u = Expr::sort(Level::param(u_name.clone()));
    let e = Expr::all(
      mk_name("A"),
      sort_u.clone(),
      sort_u,
      BinderInfo::Default,
    );
    let dag = from_expr(&e);
    let one = Level::succ(Level::zero());
    let result = subst_dag_levels(dag.head, &[u_name], &[one.clone()]);
    let result_dag = DAG { head: result };
    let result_expr = to_expr(&result_dag);
    let sort_1 = Expr::sort(one);
    let expected = Expr::all(
      mk_name("A"),
      sort_1.clone(),
      sort_1,
      BinderInfo::Default,
    );
    assert_eq!(result_expr, expected);
  }

  #[test]
  fn subst_dag_levels_no_levels_unchanged() {
    // Expression with no Sort or Cnst nodes — pure lambda
    let e = Expr::lam(
      mk_name("x"),
      Expr::lit(Literal::NatVal(Nat::from(0u64))),
      Expr::bvar(Nat::from(0u64)),
      BinderInfo::Default,
    );
    let dag = from_expr(&e);
    let u_name = mk_name("u");
    let result =
      subst_dag_levels(dag.head, &[u_name], &[Level::zero()]);
    let result_dag = DAG { head: result };
    let result_expr = to_expr(&result_dag);
    assert_eq!(result_expr, e);
  }

  // ========================================================================
  // mk_dag_local tests
  // ========================================================================

  #[test]
  fn mk_dag_local_creates_free_var() {
    let env = Env::default();
    let mut tc = DagTypeChecker::new(&env);
    let name = mk_name("x");
    let ty = from_expr(&nat_type()).head;
    let local = tc.mk_dag_local(&name, ty);
    match local {
      DAGPtr::Var(p) => unsafe {
        let var = &*p.as_ptr();
        assert!(matches!(var.binder, BinderPtr::Free));
        assert!(var.fvar_name.is_some());
      },
      _ => panic!("Expected Var"),
    }
    assert_eq!(tc.local_counter, 1);
    assert_eq!(tc.local_types.len(), 1);
  }

  #[test]
  fn mk_dag_local_unique_names() {
    let env = Env::default();
    let mut tc = DagTypeChecker::new(&env);
    let name = mk_name("x");
    let ty = from_expr(&nat_type()).head;
    let l1 = tc.mk_dag_local(&name, ty);
    let ty2 = from_expr(&nat_type()).head;
    let l2 = tc.mk_dag_local(&name, ty2);
    // Different pointer identities
    assert_ne!(dag_ptr_key(l1), dag_ptr_key(l2));
    // Different fvar names
    unsafe {
      let n1 = match l1 {
        DAGPtr::Var(p) => (*p.as_ptr()).fvar_name.clone().unwrap(),
        _ => panic!(),
      };
      let n2 = match l2 {
        DAGPtr::Var(p) => (*p.as_ptr()).fvar_name.clone().unwrap(),
        _ => panic!(),
      };
      assert_ne!(n1, n2);
    }
  }

  // ========================================================================
  // build_pi_over_locals tests
  // ========================================================================

  #[test]
  fn build_pi_single_binder() {
    // Build: Pi (x : Nat) → Nat
    // body = Nat (doesn't reference x), locals = [x_free]
    let env = Env::default();
    let mut tc = DagTypeChecker::new(&env);
    let nat_dag = from_expr(&nat_type()).head;
    let x_local = tc.mk_dag_local(&mk_name("x"), nat_dag);
    // Body doesn't use x
    let body = from_expr(&nat_type()).head;
    let result = build_pi_over_locals(
      body,
      &[x_local],
      &[mk_name("x")],
      &[BinderInfo::Default],
      &[nat_dag],
    );
    let result_dag = DAG { head: result };
    let result_expr = to_expr(&result_dag);
    let expected = Expr::all(
      mk_name("x"),
      nat_type(),
      nat_type(),
      BinderInfo::Default,
    );
    assert_eq!(result_expr, expected);
  }

  #[test]
  fn build_pi_dependent() {
    // Build: Pi (A : Sort 0) → A
    // body = A_local (references A), locals = [A_local]
    let env = Env::default();
    let mut tc = DagTypeChecker::new(&env);
    let sort0 = from_expr(&Expr::sort(Level::zero())).head;
    let a_local = tc.mk_dag_local(&mk_name("A"), sort0);
    // Body IS the local variable
    let result = build_pi_over_locals(
      a_local,
      &[a_local],
      &[mk_name("A")],
      &[BinderInfo::Default],
      &[sort0],
    );
    let result_dag = DAG { head: result };
    let result_expr = to_expr(&result_dag);
    let expected = Expr::all(
      mk_name("A"),
      Expr::sort(Level::zero()),
      Expr::bvar(Nat::from(0u64)),
      BinderInfo::Default,
    );
    assert_eq!(result_expr, expected);
  }

  #[test]
  fn build_pi_two_binders() {
    // Build: Pi (A : Sort 0) (x : A) → A
    // Should produce: ForallE A (Sort 0) (ForallE x (bvar 0) (bvar 1))
    let env = Env::default();
    let mut tc = DagTypeChecker::new(&env);
    let sort0 = from_expr(&Expr::sort(Level::zero())).head;
    let a_local = tc.mk_dag_local(&mk_name("A"), sort0);
    let x_local = tc.mk_dag_local(&mk_name("x"), a_local);
    // Body is a_local (the type A)
    let result = build_pi_over_locals(
      a_local,
      &[a_local, x_local],
      &[mk_name("A"), mk_name("x")],
      &[BinderInfo::Default, BinderInfo::Default],
      &[sort0, a_local],
    );
    let result_dag = DAG { head: result };
    let result_expr = to_expr(&result_dag);
    let expected = Expr::all(
      mk_name("A"),
      Expr::sort(Level::zero()),
      Expr::all(
        mk_name("x"),
        Expr::bvar(Nat::from(0u64)),
        Expr::bvar(Nat::from(1u64)),
        BinderInfo::Default,
      ),
      BinderInfo::Default,
    );
    assert_eq!(result_expr, expected);
  }

  // ========================================================================
  // DagTypeChecker core method tests
  // ========================================================================

  #[test]
  fn whnf_sort_is_identity() {
    let env = Env::default();
    let mut tc = DagTypeChecker::new(&env);
    let sort = alloc_val(Sort { level: Level::zero(), parents: None });
    let ptr = DAGPtr::Sort(sort);
    let result = tc.whnf(ptr);
    assert_eq!(dag_ptr_key(result), dag_ptr_key(ptr));
  }

  #[test]
  fn whnf_caches_result() {
    let env = Env::default();
    let mut tc = DagTypeChecker::new(&env);
    let sort = alloc_val(Sort { level: Level::zero(), parents: None });
    let ptr = DAGPtr::Sort(sort);
    let r1 = tc.whnf(ptr);
    let r2 = tc.whnf(ptr);
    assert_eq!(dag_ptr_key(r1), dag_ptr_key(r2));
    assert_eq!(tc.whnf_cache.len(), 1);
  }

  #[test]
  fn whnf_no_delta_caches_result() {
    let env = Env::default();
    let mut tc = DagTypeChecker::new(&env);
    let sort = alloc_val(Sort { level: Level::zero(), parents: None });
    let ptr = DAGPtr::Sort(sort);
    let r1 = tc.whnf_no_delta(ptr);
    let r2 = tc.whnf_no_delta(ptr);
    assert_eq!(dag_ptr_key(r1), dag_ptr_key(r2));
    assert_eq!(tc.whnf_no_delta_cache.len(), 1);
  }

  #[test]
  fn ensure_sort_on_sort() {
    let env = Env::default();
    let mut tc = DagTypeChecker::new(&env);
    let sort = alloc_val(Sort { level: Level::zero(), parents: None });
    let result = tc.ensure_sort(DAGPtr::Sort(sort));
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), Level::zero());
  }

  #[test]
  fn ensure_sort_on_non_sort() {
    let env = Env::default();
    let mut tc = DagTypeChecker::new(&env);
    let lit = alloc_val(LitNode {
      val: Literal::NatVal(Nat::from(42u64)),
      parents: None,
    });
    let result = tc.ensure_sort(DAGPtr::Lit(lit));
    assert!(result.is_err());
  }

  #[test]
  fn ensure_pi_on_pi() {
    let env = Env::default();
    let mut tc = DagTypeChecker::new(&env);
    let sort = alloc_val(Sort { level: Level::zero(), parents: None });
    let lam = alloc_lam(0, DAGPtr::Sort(sort), None);
    let pi = alloc_pi(
      mk_name("x"),
      BinderInfo::Default,
      DAGPtr::Sort(sort),
      lam,
      None,
    );
    let result = tc.ensure_pi(DAGPtr::Pi(pi));
    assert!(result.is_ok());
  }

  #[test]
  fn ensure_pi_on_non_pi() {
    let env = Env::default();
    let mut tc = DagTypeChecker::new(&env);
    let lit = alloc_val(LitNode {
      val: Literal::NatVal(Nat::from(42u64)),
      parents: None,
    });
    let result = tc.ensure_pi(DAGPtr::Lit(lit));
    assert!(result.is_err());
  }

  #[test]
  fn infer_sort_zero() {
    let env = Env::default();
    let mut tc = DagTypeChecker::new(&env);
    let sort = alloc_val(Sort { level: Level::zero(), parents: None });
    let result = tc.infer(DAGPtr::Sort(sort)).unwrap();
    match result {
      DAGPtr::Sort(p) => unsafe {
        assert_eq!((*p.as_ptr()).level, Level::succ(Level::zero()));
      },
      _ => panic!("Expected Sort"),
    }
  }

  #[test]
  fn infer_fvar() {
    let env = Env::default();
    let mut tc = DagTypeChecker::new(&env);
    let nat_dag = from_expr(&nat_type()).head;
    let local = tc.mk_dag_local(&mk_name("x"), nat_dag);
    let result = tc.infer(local).unwrap();
    assert_eq!(dag_ptr_key(result), dag_ptr_key(nat_dag));
  }

  #[test]
  fn infer_caches_result() {
    let env = Env::default();
    let mut tc = DagTypeChecker::new(&env);
    let sort = alloc_val(Sort { level: Level::zero(), parents: None });
    let ptr = DAGPtr::Sort(sort);
    let r1 = tc.infer(ptr).unwrap();
    let r2 = tc.infer(ptr).unwrap();
    assert_eq!(dag_ptr_key(r1), dag_ptr_key(r2));
    assert_eq!(tc.infer_cache.len(), 1);
  }

  #[test]
  fn def_eq_pointer_identity() {
    let env = Env::default();
    let mut tc = DagTypeChecker::new(&env);
    let sort = alloc_val(Sort { level: Level::zero(), parents: None });
    let ptr = DAGPtr::Sort(sort);
    assert!(tc.def_eq(ptr, ptr));
  }

  #[test]
  fn def_eq_sort_structural() {
    let env = Env::default();
    let mut tc = DagTypeChecker::new(&env);
    let s1 = alloc_val(Sort { level: Level::zero(), parents: None });
    let s2 = alloc_val(Sort { level: Level::zero(), parents: None });
    // Same level, different pointers — structurally equal
    assert!(tc.def_eq(DAGPtr::Sort(s1), DAGPtr::Sort(s2)));
  }

  #[test]
  fn def_eq_sort_different_levels() {
    let env = Env::default();
    let mut tc = DagTypeChecker::new(&env);
    let s1 = alloc_val(Sort { level: Level::zero(), parents: None });
    let s2 = alloc_val(Sort {
      level: Level::succ(Level::zero()),
      parents: None,
    });
    assert!(!tc.def_eq(DAGPtr::Sort(s1), DAGPtr::Sort(s2)));
  }

  #[test]
  fn assert_def_eq_ok() {
    let env = Env::default();
    let mut tc = DagTypeChecker::new(&env);
    let sort = alloc_val(Sort { level: Level::zero(), parents: None });
    let ptr = DAGPtr::Sort(sort);
    assert!(tc.assert_def_eq(ptr, ptr).is_ok());
  }

  #[test]
  fn assert_def_eq_err() {
    let env = Env::default();
    let mut tc = DagTypeChecker::new(&env);
    let s1 = alloc_val(Sort { level: Level::zero(), parents: None });
    let s2 = alloc_val(Sort {
      level: Level::succ(Level::zero()),
      parents: None,
    });
    assert!(tc.assert_def_eq(DAGPtr::Sort(s1), DAGPtr::Sort(s2)).is_err());
  }

  // ========================================================================
  // Type inference tests (Step 3)
  // ========================================================================

  use crate::ix::env::{
    AxiomVal, ConstantVal, ConstructorVal, InductiveVal,
  };

  fn mk_name2(a: &str, b: &str) -> Name {
    Name::str(Name::str(Name::anon(), a.into()), b.into())
  }

  fn nat_zero() -> Expr {
    Expr::cnst(mk_name2("Nat", "zero"), vec![])
  }

  fn prop() -> Expr {
    Expr::sort(Level::zero())
  }

  /// Build a minimal environment with Nat, Nat.zero, Nat.succ.
  fn mk_nat_env() -> Env {
    let mut env = Env::default();
    let nat_name = mk_name("Nat");
    env.insert(
      nat_name.clone(),
      ConstantInfo::InductInfo(InductiveVal {
        cnst: ConstantVal {
          name: nat_name.clone(),
          level_params: vec![],
          typ: Expr::sort(Level::succ(Level::zero())),
        },
        num_params: Nat::from(0u64),
        num_indices: Nat::from(0u64),
        all: vec![nat_name.clone()],
        ctors: vec![mk_name2("Nat", "zero"), mk_name2("Nat", "succ")],
        num_nested: Nat::from(0u64),
        is_rec: true,
        is_unsafe: false,
        is_reflexive: false,
      }),
    );
    let zero_name = mk_name2("Nat", "zero");
    env.insert(
      zero_name.clone(),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: zero_name.clone(),
          level_params: vec![],
          typ: nat_type(),
        },
        induct: mk_name("Nat"),
        cidx: Nat::from(0u64),
        num_params: Nat::from(0u64),
        num_fields: Nat::from(0u64),
        is_unsafe: false,
      }),
    );
    let succ_name = mk_name2("Nat", "succ");
    let succ_ty = Expr::all(
      mk_name("n"),
      nat_type(),
      nat_type(),
      BinderInfo::Default,
    );
    env.insert(
      succ_name.clone(),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: succ_name.clone(),
          level_params: vec![],
          typ: succ_ty,
        },
        induct: mk_name("Nat"),
        cidx: Nat::from(1u64),
        num_params: Nat::from(0u64),
        num_fields: Nat::from(1u64),
        is_unsafe: false,
      }),
    );
    env
  }

  /// Helper: infer the type of an Expr via the DAG TC, return as Expr.
  fn dag_infer(env: &Env, e: &Expr) -> Result<Expr, TcError> {
    let mut tc = DagTypeChecker::new(env);
    let dag = from_expr(e);
    let result = tc.infer(dag.head)?;
    Ok(dag_to_expr(result))
  }

  // -- Const inference --

  #[test]
  fn dag_infer_const_nat() {
    let env = mk_nat_env();
    let ty = dag_infer(&env, &Expr::cnst(mk_name("Nat"), vec![])).unwrap();
    assert_eq!(ty, Expr::sort(Level::succ(Level::zero())));
  }

  #[test]
  fn dag_infer_const_nat_zero() {
    let env = mk_nat_env();
    let ty = dag_infer(&env, &nat_zero()).unwrap();
    assert_eq!(ty, nat_type());
  }

  #[test]
  fn dag_infer_const_nat_succ() {
    let env = mk_nat_env();
    let ty =
      dag_infer(&env, &Expr::cnst(mk_name2("Nat", "succ"), vec![])).unwrap();
    let expected = Expr::all(
      mk_name("n"),
      nat_type(),
      nat_type(),
      BinderInfo::Default,
    );
    assert_eq!(ty, expected);
  }

  #[test]
  fn dag_infer_const_unknown() {
    let env = Env::default();
    assert!(dag_infer(&env, &Expr::cnst(mk_name("Nope"), vec![])).is_err());
  }

  #[test]
  fn dag_infer_const_universe_mismatch() {
    let env = mk_nat_env();
    assert!(
      dag_infer(&env, &Expr::cnst(mk_name("Nat"), vec![Level::zero()]))
        .is_err()
    );
  }

  // -- Lit inference --

  #[test]
  fn dag_infer_nat_lit() {
    let env = Env::default();
    let ty =
      dag_infer(&env, &Expr::lit(Literal::NatVal(Nat::from(42u64)))).unwrap();
    assert_eq!(ty, nat_type());
  }

  #[test]
  fn dag_infer_string_lit() {
    let env = Env::default();
    let ty =
      dag_infer(&env, &Expr::lit(Literal::StrVal("hello".into()))).unwrap();
    assert_eq!(ty, Expr::cnst(mk_name("String"), vec![]));
  }

  // -- App inference --

  #[test]
  fn dag_infer_app_succ_zero() {
    // Nat.succ Nat.zero : Nat
    let env = mk_nat_env();
    let e = Expr::app(
      Expr::cnst(mk_name2("Nat", "succ"), vec![]),
      nat_zero(),
    );
    let ty = dag_infer(&env, &e).unwrap();
    assert_eq!(ty, nat_type());
  }

  #[test]
  fn dag_infer_app_identity() {
    // (fun x : Nat => x) Nat.zero : Nat
    let env = mk_nat_env();
    let id_fn = Expr::lam(
      mk_name("x"),
      nat_type(),
      Expr::bvar(Nat::from(0u64)),
      BinderInfo::Default,
    );
    let e = Expr::app(id_fn, nat_zero());
    let ty = dag_infer(&env, &e).unwrap();
    assert_eq!(ty, nat_type());
  }

  // -- Lambda inference --

  #[test]
  fn dag_infer_identity_lambda() {
    // fun (x : Nat) => x  :  Nat → Nat
    let env = mk_nat_env();
    let e = Expr::lam(
      mk_name("x"),
      nat_type(),
      Expr::bvar(Nat::from(0u64)),
      BinderInfo::Default,
    );
    let ty = dag_infer(&env, &e).unwrap();
    let expected = Expr::all(
      mk_name("x"),
      nat_type(),
      nat_type(),
      BinderInfo::Default,
    );
    assert_eq!(ty, expected);
  }

  #[test]
  fn dag_infer_const_lambda() {
    // fun (x : Nat) (y : Nat) => x  :  Nat → Nat → Nat
    let env = mk_nat_env();
    let k_fn = Expr::lam(
      mk_name("x"),
      nat_type(),
      Expr::lam(
        mk_name("y"),
        nat_type(),
        Expr::bvar(Nat::from(1u64)),
        BinderInfo::Default,
      ),
      BinderInfo::Default,
    );
    let ty = dag_infer(&env, &k_fn).unwrap();
    let expected = Expr::all(
      mk_name("x"),
      nat_type(),
      Expr::all(
        mk_name("y"),
        nat_type(),
        nat_type(),
        BinderInfo::Default,
      ),
      BinderInfo::Default,
    );
    assert_eq!(ty, expected);
  }

  // -- Pi inference --

  #[test]
  fn dag_infer_pi_nat_to_nat() {
    // (Nat → Nat) : Sort 1
    let env = mk_nat_env();
    let pi = Expr::all(
      mk_name("x"),
      nat_type(),
      nat_type(),
      BinderInfo::Default,
    );
    let ty = dag_infer(&env, &pi).unwrap();
    if let crate::ix::env::ExprData::Sort(level, _) = ty.as_data() {
      assert!(
        crate::ix::kernel::level::eq_antisymm(
          level,
          &Level::succ(Level::zero())
        ),
        "Nat → Nat should live in Sort 1, got {:?}",
        level
      );
    } else {
      panic!("Expected Sort, got {:?}", ty);
    }
  }

  #[test]
  fn dag_infer_pi_prop_to_prop() {
    // P → P : Prop  (where P : Prop)
    let mut env = Env::default();
    let p_name = mk_name("P");
    env.insert(
      p_name.clone(),
      ConstantInfo::AxiomInfo(AxiomVal {
        cnst: ConstantVal {
          name: p_name.clone(),
          level_params: vec![],
          typ: prop(),
        },
        is_unsafe: false,
      }),
    );
    let p = Expr::cnst(p_name, vec![]);
    let pi =
      Expr::all(mk_name("x"), p.clone(), p.clone(), BinderInfo::Default);
    let ty = dag_infer(&env, &pi).unwrap();
    if let crate::ix::env::ExprData::Sort(level, _) = ty.as_data() {
      assert!(
        crate::ix::kernel::level::is_zero(level),
        "Prop → Prop should live in Prop, got {:?}",
        level
      );
    } else {
      panic!("Expected Sort, got {:?}", ty);
    }
  }

  // -- Let inference --

  #[test]
  fn dag_infer_let_simple() {
    // let x : Nat := Nat.zero in x  :  Nat
    let env = mk_nat_env();
    let e = Expr::letE(
      mk_name("x"),
      nat_type(),
      nat_zero(),
      Expr::bvar(Nat::from(0u64)),
      false,
    );
    let ty = dag_infer(&env, &e).unwrap();
    assert_eq!(ty, nat_type());
  }

  // -- Error cases --

  #[test]
  fn dag_infer_free_bvar_fails() {
    let env = Env::default();
    assert!(dag_infer(&env, &Expr::bvar(Nat::from(0u64))).is_err());
  }

  #[test]
  fn dag_infer_fvar_unknown_fails() {
    let env = Env::default();
    assert!(dag_infer(&env, &Expr::fvar(mk_name("x"))).is_err());
  }

  // ========================================================================
  // Definitional equality tests (Step 4)
  // ========================================================================

  use crate::ix::env::{
    DefinitionSafety, DefinitionVal, ReducibilityHints, TheoremVal,
  };

  /// Helper: check def_eq of two Expr via the DAG TC.
  fn dag_def_eq(env: &Env, x: &Expr, y: &Expr) -> bool {
    let mut tc = DagTypeChecker::new(env);
    let dx = from_expr(x);
    let dy = from_expr(y);
    tc.def_eq(dx.head, dy.head)
  }

  // -- Reflexivity --

  #[test]
  fn dag_def_eq_reflexive_sort() {
    let env = Env::default();
    let e = Expr::sort(Level::zero());
    assert!(dag_def_eq(&env, &e, &e));
  }

  #[test]
  fn dag_def_eq_reflexive_const() {
    let env = mk_nat_env();
    let e = nat_zero();
    assert!(dag_def_eq(&env, &e, &e));
  }

  // -- Sort equality --

  #[test]
  fn dag_def_eq_sort_max_comm() {
    let env = Env::default();
    let u = Level::param(mk_name("u"));
    let v = Level::param(mk_name("v"));
    let s1 = Expr::sort(Level::max(u.clone(), v.clone()));
    let s2 = Expr::sort(Level::max(v, u));
    assert!(dag_def_eq(&env, &s1, &s2));
  }

  #[test]
  fn dag_def_eq_sort_not_equal() {
    let env = Env::default();
    let s0 = Expr::sort(Level::zero());
    let s1 = Expr::sort(Level::succ(Level::zero()));
    assert!(!dag_def_eq(&env, &s0, &s1));
  }

  // -- Alpha equivalence --

  #[test]
  fn dag_def_eq_alpha_lambda() {
    let env = mk_nat_env();
    let e1 = Expr::lam(
      mk_name("x"),
      nat_type(),
      Expr::bvar(Nat::from(0u64)),
      BinderInfo::Default,
    );
    let e2 = Expr::lam(
      mk_name("y"),
      nat_type(),
      Expr::bvar(Nat::from(0u64)),
      BinderInfo::Default,
    );
    assert!(dag_def_eq(&env, &e1, &e2));
  }

  #[test]
  fn dag_def_eq_alpha_pi() {
    let env = mk_nat_env();
    let e1 = Expr::all(
      mk_name("x"),
      nat_type(),
      nat_type(),
      BinderInfo::Default,
    );
    let e2 = Expr::all(
      mk_name("y"),
      nat_type(),
      nat_type(),
      BinderInfo::Default,
    );
    assert!(dag_def_eq(&env, &e1, &e2));
  }

  // -- Beta equivalence --

  #[test]
  fn dag_def_eq_beta() {
    let env = mk_nat_env();
    let id_fn = Expr::lam(
      mk_name("x"),
      nat_type(),
      Expr::bvar(Nat::from(0u64)),
      BinderInfo::Default,
    );
    let lhs = Expr::app(id_fn, nat_zero());
    assert!(dag_def_eq(&env, &lhs, &nat_zero()));
  }

  #[test]
  fn dag_def_eq_beta_nested() {
    let env = mk_nat_env();
    let inner = Expr::lam(
      mk_name("y"),
      nat_type(),
      Expr::bvar(Nat::from(1u64)),
      BinderInfo::Default,
    );
    let k_fn = Expr::lam(
      mk_name("x"),
      nat_type(),
      inner,
      BinderInfo::Default,
    );
    let lhs = Expr::app(Expr::app(k_fn, nat_zero()), nat_zero());
    assert!(dag_def_eq(&env, &lhs, &nat_zero()));
  }

  // -- Delta equivalence --

  #[test]
  fn dag_def_eq_delta() {
    let mut env = mk_nat_env();
    let my_zero = mk_name("myZero");
    env.insert(
      my_zero.clone(),
      ConstantInfo::DefnInfo(DefinitionVal {
        cnst: ConstantVal {
          name: my_zero.clone(),
          level_params: vec![],
          typ: nat_type(),
        },
        value: nat_zero(),
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![my_zero.clone()],
      }),
    );
    let lhs = Expr::cnst(my_zero, vec![]);
    assert!(dag_def_eq(&env, &lhs, &nat_zero()));
  }

  #[test]
  fn dag_def_eq_delta_both_sides() {
    let mut env = mk_nat_env();
    for name_str in &["a", "b"] {
      let n = mk_name(name_str);
      env.insert(
        n.clone(),
        ConstantInfo::DefnInfo(DefinitionVal {
          cnst: ConstantVal {
            name: n.clone(),
            level_params: vec![],
            typ: nat_type(),
          },
          value: nat_zero(),
          hints: ReducibilityHints::Abbrev,
          safety: DefinitionSafety::Safe,
          all: vec![n],
        }),
      );
    }
    let a = Expr::cnst(mk_name("a"), vec![]);
    let b = Expr::cnst(mk_name("b"), vec![]);
    assert!(dag_def_eq(&env, &a, &b));
  }

  // -- Zeta equivalence --

  #[test]
  fn dag_def_eq_zeta() {
    let env = mk_nat_env();
    let lhs = Expr::letE(
      mk_name("x"),
      nat_type(),
      nat_zero(),
      Expr::bvar(Nat::from(0u64)),
      false,
    );
    assert!(dag_def_eq(&env, &lhs, &nat_zero()));
  }

  // -- Negative tests --

  #[test]
  fn dag_def_eq_different_consts() {
    let env = Env::default();
    let nat = nat_type();
    let string = Expr::cnst(mk_name("String"), vec![]);
    assert!(!dag_def_eq(&env, &nat, &string));
  }

  // -- App congruence --

  #[test]
  fn dag_def_eq_app_congruence() {
    let env = mk_nat_env();
    let f = Expr::cnst(mk_name2("Nat", "succ"), vec![]);
    let a = nat_zero();
    let lhs = Expr::app(f.clone(), a.clone());
    let rhs = Expr::app(f, a);
    assert!(dag_def_eq(&env, &lhs, &rhs));
  }

  #[test]
  fn dag_def_eq_app_different_args() {
    let env = mk_nat_env();
    let succ = Expr::cnst(mk_name2("Nat", "succ"), vec![]);
    let lhs = Expr::app(succ.clone(), nat_zero());
    let rhs = Expr::app(succ.clone(), Expr::app(succ, nat_zero()));
    assert!(!dag_def_eq(&env, &lhs, &rhs));
  }

  // -- Eta expansion --

  #[test]
  fn dag_def_eq_eta_lam_vs_const() {
    let env = mk_nat_env();
    let succ = Expr::cnst(mk_name2("Nat", "succ"), vec![]);
    let eta_expanded = Expr::lam(
      mk_name("x"),
      nat_type(),
      Expr::app(succ.clone(), Expr::bvar(Nat::from(0u64))),
      BinderInfo::Default,
    );
    assert!(dag_def_eq(&env, &eta_expanded, &succ));
  }

  #[test]
  fn dag_def_eq_eta_symmetric() {
    let env = mk_nat_env();
    let succ = Expr::cnst(mk_name2("Nat", "succ"), vec![]);
    let eta_expanded = Expr::lam(
      mk_name("x"),
      nat_type(),
      Expr::app(succ.clone(), Expr::bvar(Nat::from(0u64))),
      BinderInfo::Default,
    );
    assert!(dag_def_eq(&env, &succ, &eta_expanded));
  }

  // -- Binder full comparison --

  #[test]
  fn dag_def_eq_binder_full_different_domains() {
    // (x : myNat) → Nat =def= (x : Nat) → Nat
    let mut env = mk_nat_env();
    let my_nat = mk_name("myNat");
    env.insert(
      my_nat.clone(),
      ConstantInfo::DefnInfo(DefinitionVal {
        cnst: ConstantVal {
          name: my_nat.clone(),
          level_params: vec![],
          typ: Expr::sort(Level::succ(Level::zero())),
        },
        value: nat_type(),
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![my_nat.clone()],
      }),
    );
    let lhs = Expr::all(
      mk_name("x"),
      Expr::cnst(my_nat, vec![]),
      nat_type(),
      BinderInfo::Default,
    );
    let rhs = Expr::all(
      mk_name("x"),
      nat_type(),
      nat_type(),
      BinderInfo::Default,
    );
    assert!(dag_def_eq(&env, &lhs, &rhs));
  }

  #[test]
  fn dag_def_eq_binder_dependent() {
    // Pi (A : Sort 0) (x : A) → A  =def=  Pi (B : Sort 0) (y : B) → B
    let env = Env::default();
    let lhs = Expr::all(
      mk_name("A"),
      Expr::sort(Level::zero()),
      Expr::all(
        mk_name("x"),
        Expr::bvar(Nat::from(0u64)),
        Expr::bvar(Nat::from(1u64)),
        BinderInfo::Default,
      ),
      BinderInfo::Default,
    );
    let rhs = Expr::all(
      mk_name("B"),
      Expr::sort(Level::zero()),
      Expr::all(
        mk_name("y"),
        Expr::bvar(Nat::from(0u64)),
        Expr::bvar(Nat::from(1u64)),
        BinderInfo::Default,
      ),
      BinderInfo::Default,
    );
    assert!(dag_def_eq(&env, &lhs, &rhs));
  }

  // -- Nat offset equality --

  #[test]
  fn dag_def_eq_nat_zero_ctor_vs_lit() {
    let env = mk_nat_env();
    let lit0 = Expr::lit(Literal::NatVal(Nat::from(0u64)));
    assert!(dag_def_eq(&env, &nat_zero(), &lit0));
  }

  #[test]
  fn dag_def_eq_nat_lit_vs_succ_lit() {
    let env = mk_nat_env();
    let succ_4 = Expr::app(
      Expr::cnst(mk_name2("Nat", "succ"), vec![]),
      Expr::lit(Literal::NatVal(Nat::from(4u64))),
    );
    let lit5 = Expr::lit(Literal::NatVal(Nat::from(5u64)));
    assert!(dag_def_eq(&env, &lit5, &succ_4));
  }

  #[test]
  fn dag_def_eq_nat_lit_not_equal() {
    let env = Env::default();
    let a = Expr::lit(Literal::NatVal(Nat::from(1u64)));
    let b = Expr::lit(Literal::NatVal(Nat::from(2u64)));
    assert!(!dag_def_eq(&env, &a, &b));
  }

  // -- Lazy delta with hints --

  #[test]
  fn dag_def_eq_lazy_delta_higher_unfolds_first() {
    let mut env = mk_nat_env();
    let a = mk_name("a");
    let b = mk_name("b");
    env.insert(
      a.clone(),
      ConstantInfo::DefnInfo(DefinitionVal {
        cnst: ConstantVal {
          name: a.clone(),
          level_params: vec![],
          typ: nat_type(),
        },
        value: nat_zero(),
        hints: ReducibilityHints::Regular(1),
        safety: DefinitionSafety::Safe,
        all: vec![a.clone()],
      }),
    );
    env.insert(
      b.clone(),
      ConstantInfo::DefnInfo(DefinitionVal {
        cnst: ConstantVal {
          name: b.clone(),
          level_params: vec![],
          typ: nat_type(),
        },
        value: Expr::cnst(a, vec![]),
        hints: ReducibilityHints::Regular(2),
        safety: DefinitionSafety::Safe,
        all: vec![b.clone()],
      }),
    );
    let lhs = Expr::cnst(b, vec![]);
    assert!(dag_def_eq(&env, &lhs, &nat_zero()));
  }

  // -- Proof irrelevance --

  #[test]
  fn dag_def_eq_proof_irrel() {
    let mut env = mk_nat_env();
    let true_name = mk_name("True");
    let intro_name = mk_name2("True", "intro");
    env.insert(
      true_name.clone(),
      ConstantInfo::InductInfo(InductiveVal {
        cnst: ConstantVal {
          name: true_name.clone(),
          level_params: vec![],
          typ: prop(),
        },
        num_params: Nat::from(0u64),
        num_indices: Nat::from(0u64),
        all: vec![true_name.clone()],
        ctors: vec![intro_name.clone()],
        num_nested: Nat::from(0u64),
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
      }),
    );
    env.insert(
      intro_name.clone(),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: intro_name.clone(),
          level_params: vec![],
          typ: Expr::cnst(true_name.clone(), vec![]),
        },
        induct: true_name.clone(),
        cidx: Nat::from(0u64),
        num_params: Nat::from(0u64),
        num_fields: Nat::from(0u64),
        is_unsafe: false,
      }),
    );
    let true_ty = Expr::cnst(true_name, vec![]);
    let thm_a = mk_name("thmA");
    let thm_b = mk_name("thmB");
    env.insert(
      thm_a.clone(),
      ConstantInfo::ThmInfo(TheoremVal {
        cnst: ConstantVal {
          name: thm_a.clone(),
          level_params: vec![],
          typ: true_ty.clone(),
        },
        value: Expr::cnst(intro_name.clone(), vec![]),
        all: vec![thm_a.clone()],
      }),
    );
    env.insert(
      thm_b.clone(),
      ConstantInfo::ThmInfo(TheoremVal {
        cnst: ConstantVal {
          name: thm_b.clone(),
          level_params: vec![],
          typ: true_ty,
        },
        value: Expr::cnst(intro_name, vec![]),
        all: vec![thm_b.clone()],
      }),
    );
    let a = Expr::cnst(thm_a, vec![]);
    let b = Expr::cnst(thm_b, vec![]);
    assert!(dag_def_eq(&env, &a, &b));
  }

  // -- Proj congruence --

  #[test]
  fn dag_def_eq_proj_congruence() {
    let env = Env::default();
    let s = nat_zero();
    let lhs = Expr::proj(mk_name("S"), Nat::from(0u64), s.clone());
    let rhs = Expr::proj(mk_name("S"), Nat::from(0u64), s);
    assert!(dag_def_eq(&env, &lhs, &rhs));
  }

  #[test]
  fn dag_def_eq_proj_different_idx() {
    let env = Env::default();
    let s = nat_zero();
    let lhs = Expr::proj(mk_name("S"), Nat::from(0u64), s.clone());
    let rhs = Expr::proj(mk_name("S"), Nat::from(1u64), s);
    assert!(!dag_def_eq(&env, &lhs, &rhs));
  }

  // -- Beta-delta combined --

  #[test]
  fn dag_def_eq_beta_delta_combined() {
    let mut env = mk_nat_env();
    let my_id = mk_name("myId");
    let fun_ty = Expr::all(
      mk_name("x"),
      nat_type(),
      nat_type(),
      BinderInfo::Default,
    );
    env.insert(
      my_id.clone(),
      ConstantInfo::DefnInfo(DefinitionVal {
        cnst: ConstantVal {
          name: my_id.clone(),
          level_params: vec![],
          typ: fun_ty,
        },
        value: Expr::lam(
          mk_name("x"),
          nat_type(),
          Expr::bvar(Nat::from(0u64)),
          BinderInfo::Default,
        ),
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![my_id.clone()],
      }),
    );
    let lhs = Expr::app(Expr::cnst(my_id, vec![]), nat_zero());
    assert!(dag_def_eq(&env, &lhs, &nat_zero()));
  }

  // -- Unit-like equality --

  #[test]
  fn dag_def_eq_unit_like() {
    let mut env = mk_nat_env();
    let unit_name = mk_name("Unit");
    let unit_star = mk_name2("Unit", "star");
    env.insert(
      unit_name.clone(),
      ConstantInfo::InductInfo(InductiveVal {
        cnst: ConstantVal {
          name: unit_name.clone(),
          level_params: vec![],
          typ: Expr::sort(Level::succ(Level::zero())),
        },
        num_params: Nat::from(0u64),
        num_indices: Nat::from(0u64),
        all: vec![unit_name.clone()],
        ctors: vec![unit_star.clone()],
        num_nested: Nat::from(0u64),
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
      }),
    );
    env.insert(
      unit_star.clone(),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: unit_star.clone(),
          level_params: vec![],
          typ: Expr::cnst(unit_name.clone(), vec![]),
        },
        induct: unit_name.clone(),
        cidx: Nat::from(0u64),
        num_params: Nat::from(0u64),
        num_fields: Nat::from(0u64),
        is_unsafe: false,
      }),
    );
    // Two distinct fvars of type Unit should be def-eq
    let unit_ty = Expr::cnst(unit_name, vec![]);
    let mut tc = DagTypeChecker::new(&env);
    let x_ty = from_expr(&unit_ty).head;
    let x = tc.mk_dag_local(&mk_name("x"), x_ty);
    let y_ty = from_expr(&unit_ty).head;
    let y = tc.mk_dag_local(&mk_name("y"), y_ty);
    assert!(tc.def_eq(x, y));
  }

  // -- Nat add through def_eq --

  #[test]
  fn dag_def_eq_nat_add_result_vs_lit() {
    let env = mk_nat_env();
    let add_3_4 = Expr::app(
      Expr::app(
        Expr::cnst(mk_name2("Nat", "add"), vec![]),
        Expr::lit(Literal::NatVal(Nat::from(3u64))),
      ),
      Expr::lit(Literal::NatVal(Nat::from(4u64))),
    );
    let lit7 = Expr::lit(Literal::NatVal(Nat::from(7u64)));
    assert!(dag_def_eq(&env, &add_3_4, &lit7));
  }
}
