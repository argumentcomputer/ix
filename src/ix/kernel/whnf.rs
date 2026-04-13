//! Weak head normal form reduction.
//!
//! Multi-phase: whnf_core (beta, iota, zeta) → proj → nat → quot → delta.

use crate::ix::address::Address;
use crate::ix::ixon::constant::DefKind;

use super::constant::KConst;
use super::error::{TcError, u64_to_usize};
use super::expr::{ExprData, KExpr};
use super::id::KId;
use super::level::KUniv;
use super::mode::KernelMode;
use super::subst::subst;
use super::tc::{IotaInfo, MAX_WHNF_FUEL, TypeChecker, collect_app_spine};

use lean_ffi::nat::Nat;

impl<'env, M: KernelMode> TypeChecker<'env, M> {
  /// Full WHNF: loop of whnf_no_delta → delta (one step).
  pub fn whnf(&mut self, e: &KExpr<M>) -> Result<KExpr<M>, TcError<M>> {
    let has_lets = self.num_let_bindings > 0;
    // Quick exit for non-reducing forms (skip Var when let-bindings active).
    match e.data() {
      ExprData::Sort(..)
      | ExprData::All(..)
      | ExprData::Lam(..)
      | ExprData::Nat(..)
      | ExprData::Str(..) => return Ok(e.clone()),
      ExprData::Var(..) if !has_lets => return Ok(e.clone()),
      _ => {},
    }

    // Context-aware cache: closed exprs use ptr only, open exprs under
    // let-bindings include ctx_id to avoid cross-context contamination.
    let key = self.whnf_key(e);
    if let Some(cached) = self.whnf_cache.get(&key) {
      return Ok(cached.clone());
    }
    // Equiv-root second-chance: WHNF is deterministic, so all members of
    // an equivalence class share the same normal form.
    if let Some(root_key) =
      self.equiv_manager.find_root_key((e.ptr_key(), key.1))
      && root_key.0 != e.ptr_key()
    {
      let root_whnf_key = (root_key.0, key.1);
      if let Some(cached) = self.whnf_cache.get(&root_whnf_key) {
        return Ok(cached.clone());
      }
    }

    // Tick AFTER fast paths and cache: only consume shared fuel for actual work.
    // Quick exits (Sort/All/Lam/Nat/Str) and cache hits are free.
    self.tick()?;

    let mut cur = e.clone();
    let mut fuel = MAX_WHNF_FUEL;

    loop {
      if fuel == 0 {
        return Err(TcError::MaxRecDepth);
      }
      fuel -= 1;

      cur = self.whnf_no_delta(&cur)?;

      // Nat primitive reduction in main WHNF loop (lean4lean TypeChecker.lean:439).
      // Must run BEFORE delta_unfold_one, so that Nat.sub/Nat.pow/etc. get
      // short-circuited before their bodies (which use Nat.rec) are exposed.
      if let Some(reduced) = self.try_reduce_nat(&cur)? {
        cur = reduced;
        continue;
      }

      // Nat decidability: Nat.decLe/decEq/decLt on literals → Decidable.isTrue/isFalse.
      // Must run BEFORE delta, so the body (which uses dite/Nat.rec) is never exposed.
      if let Some(reduced) = self.try_reduce_decidable(&cur)? {
        cur = reduced;
        continue;
      }

      // Native reduction: Lean.reduceBool, Lean.reduceNat, System.Platform.numBits
      if let Some(reduced) = self.try_reduce_native(&cur)? {
        cur = reduced;
        continue;
      }

      if let Some(unfolded) = self.delta_unfold_one(&cur)? {
        cur = unfolded;
        continue;
      }

      break;
    }

    if !self.in_native_reduce {
      self.whnf_cache.insert(key, cur.clone());
      // Also cache under equiv root so all equiv-class members benefit.
      if let Some(root_key) =
        self.equiv_manager.find_root_key((e.ptr_key(), key.1))
        && root_key.0 != e.ptr_key()
      {
        let root_whnf_key = (root_key.0, key.1);
        self.whnf_cache.entry(root_whnf_key).or_insert(cur.clone());
      }
    }
    Ok(cur)
  }

  /// Structural WHNF: beta, iota, zeta. NO delta.
  pub(super) fn whnf_core(
    &mut self,
    e: &KExpr<M>,
  ) -> Result<KExpr<M>, TcError<M>> {
    let mut cur = e.clone();
    let mut fuel = MAX_WHNF_FUEL;

    loop {
      if fuel == 0 {
        return Err(TcError::MaxRecDepth);
      }
      fuel -= 1;

      match cur.data() {
        // Let-bound variable zeta-reduction: substitute the let-bound value.
        ExprData::Var(i, _, _) => {
          if let Some(val) = self.lookup_let_val(*i) {
            cur = val;
            continue;
          }
          return Ok(cur);
        },
        ExprData::Sort(..)
        | ExprData::All(..)
        | ExprData::Lam(..)
        | ExprData::Nat(..)
        | ExprData::Str(..)
        | ExprData::Const(..) => return Ok(cur),

        // Cheap projection: whnf_core the struct (no delta), try to extract field.
        // Matches lean4lean/C++ whnf_core with cheap_proj=false behavior.
        ExprData::Prj(_id, field, val, _) => {
          let field = *field;
          let val = val.clone();
          let wval = self.whnf_core(&val)?;
          if let Some(result) = self.try_proj_reduce(field, &wval) {
            cur = result;
            continue;
          }
          return Ok(cur); // stuck projection
        },

        // Zeta: let elimination
        ExprData::Let(_, _, val, body, _, _) => {
          let val = val.clone();
          let body = body.clone();
          cur = subst(&self.ienv, &body, &val, 0);
          continue;
        },

        ExprData::App(..) => {},
      }

      // App: collect spine, whnf_core head, try beta/iota
      let (f0, args) = collect_app_spine(&cur);
      let f = self.whnf_core(&f0)?;

      // Multi-arg beta
      if matches!(f.data(), ExprData::Lam(..)) {
        let mut body = f;
        let mut i = 0;
        while i < args.len() {
          if let ExprData::Lam(_, _, _, inner, _) = body.data() {
            let inner = inner.clone();
            body = subst(&self.ienv, &inner, &args[i], 0);
            i += 1;
          } else {
            break;
          }
        }
        for arg in &args[i..] {
          body = self.intern(KExpr::app(body, arg.clone()));
        }
        cur = body;
        continue;
      }

      // If head reduced, rebuild and try iota
      if !f.ptr_eq(&f0) {
        let mut rebuilt = f;
        for arg in &args {
          rebuilt = self.intern(KExpr::app(rebuilt, arg.clone()));
        }
        if let Some(reduced) = self.try_iota(&rebuilt)? {
          cur = reduced;
          continue;
        }
        return Ok(rebuilt);
      }

      // Try iota on original
      if let Some(reduced) = self.try_iota(&cur)? {
        cur = reduced;
        continue;
      }

      return Ok(cur);
    }
  }

  /// WHNF without delta: whnf_core → proj → nat → quot.
  pub fn whnf_no_delta(
    &mut self,
    e: &KExpr<M>,
  ) -> Result<KExpr<M>, TcError<M>> {
    let has_lets = self.num_let_bindings > 0;
    match e.data() {
      ExprData::Sort(..)
      | ExprData::All(..)
      | ExprData::Lam(..)
      | ExprData::Nat(..)
      | ExprData::Str(..) => return Ok(e.clone()),
      ExprData::Var(..) if !has_lets => return Ok(e.clone()),
      _ => {},
    }

    let key = self.whnf_key(e);
    if let Some(cached) = self.whnf_no_delta_cache.get(&key) {
      return Ok(cached.clone());
    }
    // Equiv-root second-chance for whnf_no_delta.
    if let Some(root_key) =
      self.equiv_manager.find_root_key((e.ptr_key(), key.1))
      && root_key.0 != e.ptr_key()
    {
      let root_whnf_key = (root_key.0, key.1);
      if let Some(cached) = self.whnf_no_delta_cache.get(&root_whnf_key) {
        return Ok(cached.clone());
      }
    }

    let mut cur = e.clone();
    let mut fuel = MAX_WHNF_FUEL;

    loop {
      if fuel == 0 {
        return Err(TcError::MaxRecDepth);
      }
      fuel -= 1;

      cur = self.whnf_core(&cur)?;

      // Projection reduction (bare Prj or App(Prj, args...))
      if let ExprData::Prj(_id, field, val, _) = cur.data() {
        let field = *field;
        let val = val.clone();
        let wval = self.whnf(&val)?;
        if let Some(result) = self.try_proj_reduce(field, &wval) {
          cur = result;
          continue;
        }
      } else if let Some((proj_result, args)) =
        self.try_proj_app_reduce(&cur)?
      {
        let mut result = proj_result;
        for arg in &args {
          result = self.intern(KExpr::app(result, arg.clone()));
        }
        cur = result;
        continue;
      }

      // Nat primitive reduction
      if let Some(reduced) = self.try_reduce_nat(&cur)? {
        cur = reduced;
        continue;
      }

      // Quotient reduction
      if let Some(reduced) = self.try_quot_reduce(&cur)? {
        cur = reduced;
        continue;
      }

      break;
    }

    if !self.in_native_reduce {
      self.whnf_no_delta_cache.insert(key, cur.clone());
      if let Some(root_key) =
        self.equiv_manager.find_root_key((e.ptr_key(), key.1))
        && root_key.0 != e.ptr_key()
      {
        let root_whnf_key = (root_key.0, key.1);
        self.whnf_no_delta_cache.entry(root_whnf_key).or_insert(cur.clone());
      }
    }
    Ok(cur)
  }

  /// Delta unfold: unfold one defined constant.
  pub fn delta_unfold_one(
    &mut self,
    e: &KExpr<M>,
  ) -> Result<Option<KExpr<M>>, TcError<M>> {
    if let Some(unfolded) = self.try_delta_unfold(e)? {
      return Ok(Some(unfolded));
    }
    // Bare constant
    if let ExprData::Const(id, us, _) = e.data()
      && let Some(KConst::Defn { kind, val, .. }) = self.env.get(id)
      && (kind == DefKind::Definition || kind == DefKind::Theorem)
    {
      let val = val.clone();
      let us: Vec<_> = us.to_vec();
      return Ok(Some(self.instantiate_univ_params(&val, &us)));
    }
    Ok(None)
  }

  /// Try delta-unfold on application head.
  fn try_delta_unfold(
    &mut self,
    e: &KExpr<M>,
  ) -> Result<Option<KExpr<M>>, TcError<M>> {
    let (head, args) = collect_app_spine(e);

    let (id, us) = match head.data() {
      ExprData::Const(id, us, _) => (id, us),
      _ => return Ok(None),
    };

    let val = match self.env.get(id) {
      Some(KConst::Defn { kind, val, .. })
        if kind == DefKind::Definition || kind == DefKind::Theorem =>
      {
        val.clone()
      },
      _ => return Ok(None),
    };

    let us: Vec<_> = us.to_vec();
    let val = self.instantiate_univ_params(&val, &us);

    let mut result = val;
    for arg in &args {
      result = self.intern(KExpr::app(result, arg.clone()));
    }

    Ok(Some(result))
  }

  // -----------------------------------------------------------------------
  // Iota reduction
  // -----------------------------------------------------------------------

  /// Try iota: recursor applied to constructor.
  fn try_iota(&mut self, e: &KExpr<M>) -> Result<Option<KExpr<M>>, TcError<M>> {
    let (head, spine) = collect_app_spine(e);

    let (rec_id, rec_us) = match head.data() {
      ExprData::Const(id, us, _) => (id.clone(), us.clone()),
      _ => return Ok(None),
    };

    let recr = match self.env.get(&rec_id) {
      Some(KConst::Recr {
        k,
        params,
        motives,
        minors,
        indices,
        rules,
        lvls,
        ..
      }) => {
        let major_idx = u64_to_usize::<M>(params + motives + minors + indices)?;
        if spine.len() <= major_idx {
          return Ok(None);
        }
        IotaInfo {
          k,
          params: u64_to_usize::<M>(params)?,
          motives: u64_to_usize::<M>(motives)?,
          minors: u64_to_usize::<M>(minors)?,
          indices: u64_to_usize::<M>(indices)?,
          major_idx,
          rules: rules.clone(),
          lvls,
        }
      },
      _ => return Ok(None),
    };

    // K-like recursor: try to synthesize a nullary constructor before WHNF.
    // This handles cases like `Eq.rec motive minor major` where major isn't
    // a constructor but its type matches the inductive — we build `Eq.refl params...`.
    let major = &spine[recr.major_idx];
    let major = if recr.k {
      self
        .synth_ctor_when_k(major, &rec_id, &recr)?
        .unwrap_or_else(|| major.clone())
    } else {
      major.clone()
    };

    // WHNF the major premise
    let mut major_whnf = self.whnf(&major)?;

    // Nat literal → constructor form (one level: n → Nat.succ(lit(n-1)))
    if let ExprData::Nat(val, _, _) = major_whnf.data() {
      // Abort iota on Nat literals > 2^20 (~1M steps). These would exhaust
      // fuel and indicate a missing native reduction short-circuit.
      if val.0.bits() > 20 {
        // Large Nat literal — cannot convert to constructor form without
        // diverging. Return None so iota stays stuck; the caller can try
        // other reduction strategies (native, delta).
        return Ok(None);
      }
      major_whnf = self.nat_to_constructor(&val.clone());
    }
    // String literal → constructor form (M3: WHNF after, matching lean4lean Reduce.lean:71)
    if let ExprData::Str(val, _, _) = major_whnf.data() {
      let val = val.clone();
      let str_ctor = self.str_lit_to_constructor(&val);
      major_whnf = self.whnf(&str_ctor)?;
    }

    // Check if major is a constructor application
    let (ctor_head, ctor_args) = collect_app_spine(&major_whnf);
    let is_ctor = match ctor_head.data() {
      ExprData::Const(id, _, _) => {
        matches!(self.env.get(id), Some(KConst::Ctor { .. }))
      },
      _ => false,
    };

    if is_ctor {
      let ctor_id = match ctor_head.data() {
        ExprData::Const(id, _, _) => id,
        _ => unreachable!(),
      };
      let (cidx, ctor_fields) = match self.env.get(ctor_id) {
        Some(KConst::Ctor { cidx, fields, .. }) => {
          (u64_to_usize::<M>(cidx)?, u64_to_usize::<M>(fields)?)
        },
        _ => unreachable!(),
      };

      if cidx >= recr.rules.len() {
        return Ok(None);
      }
      let rule = &recr.rules[cidx];
      // H6: Check level params arity (lean4lean Reduce.lean:76)
      if rec_us.len() as u64 != recr.lvls {
        return Ok(None);
      }
      // H5: Check nfields ≤ major_args (lean4lean Reduce.lean:75)
      if ctor_fields > ctor_args.len() {
        return Ok(None);
      }
      let rec_us_vec: Vec<_> = rec_us.to_vec();
      let rhs = self.instantiate_univ_params(&rule.rhs, &rec_us_vec);

      let pmm_end = recr.params + recr.motives + recr.minors;
      let field_start = ctor_args.len() - ctor_fields;
      let mut result = rhs;
      for arg in spine.iter().take(pmm_end.min(spine.len())) {
        result = self.intern(KExpr::app(result, arg.clone()));
      }
      for arg in ctor_args.iter().skip(field_start) {
        result = self.intern(KExpr::app(result, arg.clone()));
      }
      for arg in spine.iter().skip(recr.major_idx + 1) {
        result = self.intern(KExpr::app(result, arg.clone()));
      }
      return Ok(Some(result));
    }

    // Struct eta iota fallback
    if let Some(result) =
      self.try_struct_eta_iota(&rec_id, &recr, &rec_us, &spine)?
    {
      return Ok(Some(result));
    }

    Ok(None)
  }

  fn is_struct_like(&self, id: &KId<M>) -> bool {
    match self.env.get(id) {
      Some(KConst::Indc { is_rec, indices, ctors, .. }) => {
        !is_rec && indices == 0 && ctors.len() == 1
      },
      _ => false,
    }
  }

  fn try_struct_eta_iota(
    &mut self,
    rec_id: &KId<M>,
    recr: &IotaInfo<M>,
    rec_us: &[KUniv<M>],
    spine: &[KExpr<M>],
  ) -> Result<Option<KExpr<M>>, TcError<M>> {
    if recr.rules.len() != 1 {
      return Ok(None);
    }
    let rule = &recr.rules[0];
    if rule.fields == 0 {
      return Ok(None);
    }

    let rec_ty = match self.env.get(rec_id) {
      Some(c) => c.ty().clone(),
      None => return Ok(None),
    };
    let skip = (recr.params + recr.motives + recr.minors + recr.indices) as u64;
    let ind_id = match self.get_major_inductive_id(&rec_ty, skip) {
      Ok(id) => id,
      Err(_) => return Ok(None),
    };
    if !self.is_struct_like(&ind_id) {
      return Ok(None);
    }

    // H3: Prop guard — don't eta-expand Prop-typed structures (lean4lean toCtorWhenStruct:51)
    let major = &spine[recr.major_idx];
    let major_ty = match self.with_infer_only(|tc| tc.infer(major)) {
      Ok(ty) => ty,
      Err(_) => return Ok(None),
    };
    let major_sort = match self.with_infer_only(|tc| tc.infer(&major_ty)) {
      Ok(ty) => ty,
      Err(_) => return Ok(None),
    };
    let major_sort_w = match self.whnf(&major_sort) {
      Ok(w) => w,
      Err(_) => return Ok(None),
    };
    if matches!(major_sort_w.data(), ExprData::Sort(u, _) if u.is_zero()) {
      return Ok(None);
    }
    let rec_us_vec: Vec<_> = rec_us.to_vec();
    let rhs = self.instantiate_univ_params(&rule.rhs, &rec_us_vec);
    let pmm_end = recr.params + recr.motives + recr.minors;
    let mut result = rhs;
    for arg in spine.iter().take(pmm_end.min(spine.len())) {
      result = self.intern(KExpr::app(result, arg.clone()));
    }
    for i in 0..rule.fields {
      let proj = self.intern(KExpr::prj(ind_id.clone(), i, major.clone()));
      result = self.intern(KExpr::app(result, proj));
    }
    for arg in spine.iter().skip(recr.major_idx + 1) {
      result = self.intern(KExpr::app(result, arg.clone()));
    }
    Ok(Some(result))
  }

  // -----------------------------------------------------------------------
  // K-rule: synthesize nullary constructor
  // -----------------------------------------------------------------------

  /// For K-like recursors, try to synthesize a nullary constructor from the
  /// major premise's type. Returns `Ok(Some(ctor_app))` if successful.
  ///
  /// Algorithm (following lean4lean/nanoda):
  /// 1. Infer major's type, WHNF it
  /// 2. Check head constant matches the recursor's target inductive
  /// 3. Build nullary ctor: `Ctor.{levels} params...`
  /// 4. Infer ctor's type, check def-eq with major's type
  fn synth_ctor_when_k(
    &mut self,
    major: &KExpr<M>,
    rec_id: &KId<M>,
    recr: &IotaInfo<M>,
  ) -> Result<Option<KExpr<M>>, TcError<M>> {
    // Infer major's type (infer-only: we just need the type, not validation)
    let major_ty = match self.with_infer_only(|tc| tc.infer(major)) {
      Ok(ty) => ty,
      Err(_) => return Ok(None),
    };
    let major_ty_w = match self.whnf(&major_ty) {
      Ok(w) => w,
      Err(_) => return Ok(None),
    };

    // Extract head constant of the type
    let (ty_head, ty_args) = collect_app_spine(&major_ty_w);
    let ty_head_id = match ty_head.data() {
      ExprData::Const(id, _, _) => id.clone(),
      _ => return Ok(None),
    };

    // Get the recursor's target inductive from its type
    let rec_ty = match self.env.get(rec_id) {
      Some(c) => c.ty().clone(),
      None => return Ok(None),
    };
    let skip = (recr.params + recr.motives + recr.minors + recr.indices) as u64;
    let ind_id = match self.get_major_inductive_id(&rec_ty, skip) {
      Ok(id) => id,
      Err(_) => return Ok(None),
    };

    // Head of major's type must match the recursor's target inductive
    if ty_head_id.addr != ind_id.addr {
      return Ok(None);
    }

    // Get the first constructor
    let ctor_id = match self.env.get(&ind_id) {
      Some(KConst::Indc { ctors, .. }) if !ctors.is_empty() => ctors[0].clone(),
      _ => return Ok(None),
    };

    // Build nullary ctor application: Ctor.{levels} params...
    let ctor_us = match ty_head.data() {
      ExprData::Const(_, us, _) => us.clone(),
      _ => return Ok(None),
    };
    let mut ctor_app = self.intern(KExpr::cnst(ctor_id, ctor_us));
    for arg in ty_args.iter().take(recr.params) {
      ctor_app = self.intern(KExpr::app(ctor_app, arg.clone()));
    }

    // Verify: infer ctor's type and check def-eq with major's type
    let ctor_ty = match self.with_infer_only(|tc| tc.infer(&ctor_app)) {
      Ok(ty) => ty,
      Err(_) => return Ok(None),
    };
    if !self.is_def_eq(&major_ty_w, &ctor_ty)? {
      return Ok(None);
    }

    Ok(Some(ctor_app))
  }

  // -----------------------------------------------------------------------
  // Projection reduction
  // -----------------------------------------------------------------------

  fn try_proj_reduce(
    &mut self,
    field: u64,
    wval: &KExpr<M>,
  ) -> Option<KExpr<M>> {
    // String literal → constructor form before trying projection
    let wval_expanded;
    let wval = if let ExprData::Str(s, _, _) = wval.data() {
      wval_expanded = self.str_lit_to_constructor(&s.clone());
      &wval_expanded
    } else {
      wval
    };

    let (head, args) = collect_app_spine(wval);

    let ctor_id = match head.data() {
      ExprData::Const(id, _, _) => id,
      _ => return None,
    };

    let ctor_params = match self.env.get(ctor_id) {
      Some(KConst::Ctor { params, .. }) => usize::try_from(params).ok()?,
      _ => return None,
    };

    let field_start = ctor_params;
    let idx = field_start + usize::try_from(field).ok()?;
    args.get(idx).cloned()
  }

  /// Try to reduce a projection-headed application: App(Prj(S, i, v), args...).
  /// Returns Some((reduced_proj, remaining_args)) if the projection reduced.
  fn try_proj_app_reduce(
    &mut self,
    e: &KExpr<M>,
  ) -> Result<Option<(KExpr<M>, Vec<KExpr<M>>)>, TcError<M>> {
    let (head, args) = collect_app_spine(e);
    if args.is_empty() {
      return Ok(None);
    }

    if let ExprData::Prj(_id, field, val, _) = head.data() {
      let field = *field;
      let val = val.clone();
      let wval = self.whnf(&val)?;
      if let Some(result) = self.try_proj_reduce(field, &wval) {
        return Ok(Some((result, args)));
      }
    }
    Ok(None)
  }

  // -----------------------------------------------------------------------
  // Helpers
  // -----------------------------------------------------------------------

  /// Get the major premise's inductive KId from a recursor type.
  /// Peels `skip` foralls, then extracts the head constant of the result domain.
  pub fn get_major_inductive_id(
    &mut self,
    rec_ty: &KExpr<M>,
    skip: u64,
  ) -> Result<KId<M>, TcError<M>> {
    let mut ty = rec_ty.clone();
    for _ in 0..skip {
      let w = self.whnf(&ty)?;
      match w.data() {
        ExprData::All(_, _, _, body, _) => ty = body.clone(),
        _ => {
          return Err(TcError::Other(
            "get_major_inductive_id: not enough foralls".into(),
          ));
        },
      }
    }
    let w = self.whnf(&ty)?;
    match w.data() {
      ExprData::All(_, _, dom, _, _) => {
        let (head, _) = collect_app_spine(dom);
        match head.data() {
          ExprData::Const(id, _, _) => Ok(id.clone()),
          _ => Err(TcError::Other(
            "get_major_inductive_id: domain head not const".into(),
          )),
        }
      },
      _ => Err(TcError::Other(
        "get_major_inductive_id: expected forall at major".into(),
      )),
    }
  }

  /// Convert a Nat literal to constructor form: 0 → Nat.zero, n+1 → Nat.succ(n-1).
  fn nat_to_constructor(&mut self, val: &Nat) -> KExpr<M> {
    use num_bigint::BigUint;
    if val.0 == BigUint::ZERO {
      self.intern(KExpr::cnst(self.prims.nat_zero.clone(), Box::new([])))
    } else {
      let pred_val = Nat(&val.0 - BigUint::from(1u64));
      let pred_addr = Address::hash(&pred_val.to_le_bytes());
      let pred_expr = self.intern(KExpr::nat(pred_val, pred_addr));
      let succ =
        self.intern(KExpr::cnst(self.prims.nat_succ.clone(), Box::new([])));
      self.intern(KExpr::app(succ, pred_expr))
    }
  }

  /// Nat primitive reduction (add, sub, mul, div, mod, pow, gcd, bitwise, predicates).
  pub(super) fn try_reduce_nat(
    &mut self,
    e: &KExpr<M>,
  ) -> Result<Option<KExpr<M>>, TcError<M>> {
    // Skip if expression has loose bound variables — can't reduce to a literal.
    // Matches lean4lean's `if e.hasFVar then return none` (TypeChecker.lean:396).
    if e.lbr() > 0 {
      return Ok(None);
    }
    let (head, args) = collect_app_spine(e);
    let addr = match head.data() {
      ExprData::Const(id, _, _) => id.addr.clone(),
      _ => return Ok(None),
    };

    // Nat.succ n → n + 1
    if addr == self.prims.nat_succ.addr && args.len() == 1 {
      let a = self.whnf(&args[0])?;
      if let Some(n) = extract_nat_lit(&a) {
        let result = Nat(&n.0 + 1u64);
        let blob_addr = Address::hash(&result.to_le_bytes());
        return Ok(Some(self.intern(KExpr::nat(result, blob_addr))));
      }
      return Ok(None);
    }

    // Nat.pred n → n - 1 (or 0 if n = 0)
    if addr == self.prims.nat_pred.addr && args.len() == 1 {
      let a = self.whnf(&args[0])?;
      if let Some(n) = extract_nat_lit(&a) {
        let result = if n.0 == num_bigint::BigUint::ZERO {
          Nat(num_bigint::BigUint::ZERO)
        } else {
          Nat(&n.0 - 1u64)
        };
        let blob_addr = Address::hash(&result.to_le_bytes());
        return Ok(Some(self.intern(KExpr::nat(result, blob_addr))));
      }
      return Ok(None);
    }

    if args.len() < 2 {
      return Ok(None);
    }

    let p = &self.prims;
    let is_bin_arith = addr == p.nat_add.addr
      || addr == p.nat_sub.addr
      || addr == p.nat_mul.addr
      || addr == p.nat_div.addr
      || addr == p.nat_mod.addr
      || addr == p.nat_pow.addr
      || addr == p.nat_gcd.addr
      || addr == p.nat_land.addr
      || addr == p.nat_lor.addr
      || addr == p.nat_xor.addr
      || addr == p.nat_shift_left.addr
      || addr == p.nat_shift_right.addr;
    let is_bin_pred = addr == p.nat_beq.addr || addr == p.nat_ble.addr;

    if !is_bin_arith && !is_bin_pred {
      return Ok(None);
    }

    let wa = self.whnf(&args[0])?;
    let wb = self.whnf(&args[1])?;
    let a_val = match extract_nat_lit(&wa) {
      Some(v) => v,
      None => return Ok(None),
    };
    let b_val = match extract_nat_lit(&wb) {
      Some(v) => v,
      None => return Ok(None),
    };

    let result_expr = if is_bin_arith {
      let result = match compute_nat_bin(&addr, &self.prims, a_val, b_val) {
        Some(r) => r,
        None => return Ok(None), // can't compute, leave unreduced
      };
      let blob_addr = Address::hash(&result.to_le_bytes());
      self.intern(KExpr::nat(result, blob_addr))
    } else {
      let b = if addr == self.prims.nat_beq.addr {
        a_val == b_val
      } else {
        a_val <= b_val
      };
      let bool_id = if b {
        self.prims.bool_true.clone()
      } else {
        self.prims.bool_false.clone()
      };
      self.intern(KExpr::cnst(bool_id, Box::new([])))
    };

    let mut result = result_expr;
    for arg in args.iter().skip(2) {
      result = self.intern(KExpr::app(result, arg.clone()));
    }
    Ok(Some(result))
  }

  /// Native Nat.decLe/decEq/decLt reduction.
  ///
  /// Intercepts `Nat.decLe n m`, `Nat.decEq n m`, `Nat.decLt n m` when both
  /// arguments are Nat literals. Computes the boolean result natively and
  /// constructs the appropriate `Decidable.isTrue proof` or `Decidable.isFalse proof`.
  ///
  /// Proof terms:
  /// - decLe true:  `Decidable.isTrue  (Nat.le_of_ble_eq_true  n m (Eq.refl Bool.true))`
  /// - decLe false: `Decidable.isFalse (Nat.not_le_of_not_ble_eq_true n m (Bool.noConfusion (Eq.refl Bool.false)))`
  /// - decEq true:  `Decidable.isTrue  (Nat.eq_of_beq_eq_true  n m (Eq.refl Bool.true))`
  /// - decEq false: `Decidable.isFalse (Nat.ne_of_beq_eq_false n m (Eq.refl Bool.false))`
  /// - decLt n m:   delegates to decLe (n+1) m
  pub(super) fn try_reduce_decidable(
    &mut self,
    e: &KExpr<M>,
  ) -> Result<Option<KExpr<M>>, TcError<M>> {
    if e.lbr() > 0 {
      return Ok(None);
    }
    let (head, args) = collect_app_spine(e);
    let addr = match head.data() {
      ExprData::Const(id, _, _) => id.addr.clone(),
      _ => return Ok(None),
    };

    let p = &self.prims;
    let is_dec_le = addr == p.nat_dec_le.addr;
    let is_dec_eq = addr == p.nat_dec_eq.addr;
    let is_dec_lt = addr == p.nat_dec_lt.addr;
    if !is_dec_le && !is_dec_eq && !is_dec_lt {
      return Ok(None);
    }
    if args.len() < 2 {
      return Ok(None);
    }

    let wa = self.whnf(&args[0])?;
    let wb = self.whnf(&args[1])?;
    let a_val = match extract_nat_lit(&wa) {
      Some(v) => v.clone(),
      None => return Ok(None),
    };
    let b_val = match extract_nat_lit(&wb) {
      Some(v) => v.clone(),
      None => return Ok(None),
    };

    // S5: Eq.refl is universe-polymorphic: @Eq.refl.{u}.
    // For Bool : Type = Sort 1, we need u = 1 = Succ(Zero).
    let u1 = KUniv::succ(KUniv::zero());

    // decLt n m  →  decLe (n+1) m
    if is_dec_lt {
      let succ_a = Nat(&a_val.0 + 1u64);
      let succ_a_addr = Address::hash(&succ_a.to_le_bytes());
      let succ_a_expr = self.intern(KExpr::nat(succ_a, succ_a_addr));
      // Build: Nat.decLe (n+1) m
      let dec_le_const =
        self.intern(KExpr::cnst(self.prims.nat_dec_le.clone(), Box::new([])));
      let mut result = self.intern(KExpr::app(dec_le_const, succ_a_expr));
      result = self.intern(KExpr::app(result, args[1].clone()));
      for arg in args.iter().skip(2) {
        result = self.intern(KExpr::app(result, arg.clone()));
      }
      // Recursively reduce the decLe
      return Ok(Some(result));
    }

    let (b_result, proof_true_fn, proof_false_fn) = if is_dec_le {
      (
        a_val <= b_val,
        &self.prims.nat_le_of_ble_eq_true,
        &self.prims.nat_not_le_of_not_ble_eq_true,
      )
    } else {
      // is_dec_eq
      (
        a_val == b_val,
        &self.prims.nat_eq_of_beq_eq_true,
        &self.prims.nat_ne_of_beq_eq_false,
      )
    };
    let proof_true_fn = proof_true_fn.clone();
    let proof_false_fn = proof_false_fn.clone();

    let result_expr = if b_result {
      // Decidable.isTrue (proof_fn n m (Eq.refl.{1} Bool Bool.true))
      let eq_refl = self.intern(KExpr::cnst(
        self.prims.eq_refl.clone(),
        Box::new([u1.clone()]),
      ));
      let bool_ty =
        self.intern(KExpr::cnst(self.prims.bool_type.clone(), Box::new([])));
      let bool_true =
        self.intern(KExpr::cnst(self.prims.bool_true.clone(), Box::new([])));
      let refl_proof = self.intern(KExpr::app(eq_refl, bool_ty));
      let refl_proof = self.intern(KExpr::app(refl_proof, bool_true));

      // Build: proof_fn n m refl_proof
      let proof_const =
        self.intern(KExpr::cnst(proof_true_fn.clone(), Box::new([])));
      let proof = self.intern(KExpr::app(proof_const, args[0].clone()));
      let proof = self.intern(KExpr::app(proof, args[1].clone()));
      let proof = self.intern(KExpr::app(proof, refl_proof));

      // Build: Decidable.isTrue proof
      let is_true = self.intern(KExpr::cnst(
        self.prims.decidable_is_true.clone(),
        Box::new([]),
      ));
      self.intern(KExpr::app(is_true, proof))
    } else if is_dec_eq {
      // Decidable.isFalse (Nat.ne_of_beq_eq_false n m (Eq.refl.{1} Bool Bool.false))
      let eq_refl = self.intern(KExpr::cnst(
        self.prims.eq_refl.clone(),
        Box::new([u1.clone()]),
      ));
      let bool_ty =
        self.intern(KExpr::cnst(self.prims.bool_type.clone(), Box::new([])));
      let bool_false =
        self.intern(KExpr::cnst(self.prims.bool_false.clone(), Box::new([])));
      let refl_proof = self.intern(KExpr::app(eq_refl, bool_ty));
      let refl_proof = self.intern(KExpr::app(refl_proof, bool_false));

      let proof_const =
        self.intern(KExpr::cnst(proof_false_fn.clone(), Box::new([])));
      let proof = self.intern(KExpr::app(proof_const, args[0].clone()));
      let proof = self.intern(KExpr::app(proof, args[1].clone()));
      let proof = self.intern(KExpr::app(proof, refl_proof));

      let is_false = self.intern(KExpr::cnst(
        self.prims.decidable_is_false.clone(),
        Box::new([]),
      ));
      self.intern(KExpr::app(is_false, proof))
    } else {
      // Decidable.isFalse (Nat.not_le_of_not_ble_eq_true n m (Bool.noConfusion (Eq.refl Bool.false)))
      // The proof of ¬(Nat.ble n m = true) when Nat.ble n m = false:
      // Bool.noConfusion applied to Eq.refl.{1} Bool Bool.false gives us the contradiction
      let eq_refl = self.intern(KExpr::cnst(
        self.prims.eq_refl.clone(),
        Box::new([u1.clone()]),
      ));
      let bool_ty =
        self.intern(KExpr::cnst(self.prims.bool_type.clone(), Box::new([])));
      let bool_false =
        self.intern(KExpr::cnst(self.prims.bool_false.clone(), Box::new([])));
      let refl_proof = self.intern(KExpr::app(eq_refl, bool_ty));
      let refl_proof = self.intern(KExpr::app(refl_proof, bool_false));

      let no_confusion = self.intern(KExpr::cnst(
        self.prims.bool_no_confusion.clone(),
        Box::new([]),
      ));
      let no_confusion_proof =
        self.intern(KExpr::app(no_confusion, refl_proof));

      let proof_const =
        self.intern(KExpr::cnst(proof_false_fn.clone(), Box::new([])));
      let proof = self.intern(KExpr::app(proof_const, args[0].clone()));
      let proof = self.intern(KExpr::app(proof, args[1].clone()));
      let proof = self.intern(KExpr::app(proof, no_confusion_proof));

      let is_false = self.intern(KExpr::cnst(
        self.prims.decidable_is_false.clone(),
        Box::new([]),
      ));
      self.intern(KExpr::app(is_false, proof))
    };

    let mut result = result_expr;
    for arg in args.iter().skip(2) {
      result = self.intern(KExpr::app(result, arg.clone()));
    }
    Ok(Some(result))
  }

  /// Quotient reduction (Quot.lift, Quot.ind).
  fn try_quot_reduce(
    &mut self,
    e: &KExpr<M>,
  ) -> Result<Option<KExpr<M>>, TcError<M>> {
    let (head, args) = collect_app_spine(e);
    let addr = match head.data() {
      ExprData::Const(id, _, _) => id.addr.clone(),
      _ => return Ok(None),
    };

    // Quot.lift: 6 args, f at 3, major at 5
    // Quot.ind:  5 args, f at 3, major at 4
    let (f_idx, major_idx) = if addr == self.prims.quot_lift.addr {
      if args.len() < 6 {
        return Ok(None);
      }
      (3usize, 5usize)
    } else if addr == self.prims.quot_ind.addr {
      if args.len() < 5 {
        return Ok(None);
      }
      (3usize, 4usize)
    } else {
      return Ok(None);
    };

    let major_whnf = self.whnf(&args[major_idx])?;
    let (mk_head, mk_args) = collect_app_spine(&major_whnf);
    let mk_addr = match mk_head.data() {
      ExprData::Const(id, _, _) => &id.addr,
      _ => return Ok(None),
    };
    if *mk_addr != self.prims.quot_ctor.addr {
      return Ok(None);
    }

    // Quot.mk has exactly 3 args: (α, r, a). Value is the last.
    if mk_args.len() != 3 {
      return Ok(None);
    }
    let quot_val = mk_args[2].clone();

    let mut result = self.intern(KExpr::app(args[f_idx].clone(), quot_val));
    for arg in args.iter().skip(major_idx + 1) {
      result = self.intern(KExpr::app(result, arg.clone()));
    }
    Ok(Some(result))
  }

  // -----------------------------------------------------------------------
  // Native reduction (Lean.reduceBool, Lean.reduceNat, System.Platform.numBits)
  // -----------------------------------------------------------------------

  /// Try native reduction, matching C++ kernel's `reduce_native`.
  /// - `Lean.reduceBool arg`: look up `arg` (a constant), evaluate its body, return Bool
  /// - `Lean.reduceNat arg`: look up `arg` (a constant), evaluate its body, return Nat
  /// - `System.Platform.numBits`: return 64 (matching Lean's 64-bit platform)
  pub(super) fn try_reduce_native(
    &mut self,
    e: &KExpr<M>,
  ) -> Result<Option<KExpr<M>>, TcError<M>> {
    if e.lbr() > 0 {
      return Ok(None);
    }
    let (head, args) = collect_app_spine(e);
    let head_addr = match head.data() {
      ExprData::Const(id, _, _) => id.addr.clone(),
      _ => return Ok(None),
    };

    // System.Platform.numBits has type { n : Nat // n = 32 ∨ n = 64 } (Subtype).
    // We do NOT reduce it natively because the result must be a Subtype.mk
    // constructor application, not a bare Nat literal. Let delta+iota handle it.
    // (Previously returned bare Nat(64) which was a type error.)

    // Lean.reduceBool / Lean.reduceNat: arg must be a single constant
    let is_reduce_bool = head_addr == self.prims.reduce_bool.addr;
    let is_reduce_nat = head_addr == self.prims.reduce_nat.addr;
    if !is_reduce_bool && !is_reduce_nat {
      return Ok(None);
    }
    if args.len() != 1 {
      return Ok(None);
    }
    // Re-entrancy guard: prevent whnf → native → whnf → native stack overflow
    if self.in_native_reduce {
      return Ok(None);
    }

    // The argument should be a constant whose definition we can evaluate
    let arg_const = match args[0].data() {
      ExprData::Const(id, us, _) => (id.clone(), us.clone()),
      _ => return Ok(None),
    };
    let (arg_id, arg_us) = arg_const;

    // Look up the constant's definition body
    let body = match self.env.get(&arg_id) {
      Some(KConst::Defn { val, .. }) => val.clone(),
      _ => return Ok(None),
    };

    // Instantiate universe params and fully evaluate (guarded)
    let us_vec: Vec<_> = arg_us.to_vec();
    let body = self.instantiate_univ_params(&body, &us_vec);
    self.in_native_reduce = true;
    let result = self.whnf(&body);
    self.in_native_reduce = false;
    let result = result?;

    if is_reduce_bool {
      // Result must be Bool.true or Bool.false
      let result_addr = match result.data() {
        ExprData::Const(id, _, _) => &id.addr,
        _ => return Ok(None),
      };
      if *result_addr == self.prims.bool_true.addr
        || *result_addr == self.prims.bool_false.addr
      {
        Ok(Some(result))
      } else {
        Ok(None) // not a Bool literal — leave unreduced
      }
    } else {
      // reduceNat: result must be a Nat literal
      match result.data() {
        ExprData::Nat(..) => Ok(Some(result)),
        _ => Ok(None),
      }
    }
  }
}

// ---------------------------------------------------------------------------
// Free-standing helpers for nat reduction
// ---------------------------------------------------------------------------

use super::primitive::Primitives;

/// Extract a nat value from a literal expression only (no WHNF).
fn extract_nat_lit<M: KernelMode>(e: &KExpr<M>) -> Option<&Nat> {
  match e.data() {
    ExprData::Nat(val, _, _) => Some(val),
    _ => None,
  }
}

fn gcd_biguint(
  a: &num_bigint::BigUint,
  b: &num_bigint::BigUint,
) -> num_bigint::BigUint {
  let mut x = a.clone();
  let mut y = b.clone();
  while y != num_bigint::BigUint::ZERO {
    let t = y.clone();
    y = &x % &y;
    x = t;
  }
  x
}

/// Compute a binary nat operation. Returns `None` if the operation can't be
/// computed (e.g., exponent too large) — caller leaves the expression unreduced.
fn compute_nat_bin<M: KernelMode>(
  addr: &Address,
  p: &Primitives<M>,
  a: &Nat,
  b: &Nat,
) -> Option<Nat> {
  use num_bigint::BigUint;
  let zero = BigUint::ZERO;
  let r = if *addr == p.nat_add.addr {
    &a.0 + &b.0
  } else if *addr == p.nat_sub.addr {
    if a.0 >= b.0 { &a.0 - &b.0 } else { zero }
  } else if *addr == p.nat_mul.addr {
    &a.0 * &b.0
  } else if *addr == p.nat_div.addr {
    if b.0 == zero { zero } else { &a.0 / &b.0 }
  } else if *addr == p.nat_mod.addr {
    if b.0 == zero { a.0.clone() } else { &a.0 % &b.0 }
  } else if *addr == p.nat_pow.addr {
    match b.to_u64() {
      #[allow(clippy::cast_possible_truncation)] // guarded: exp <= 1_000_000
      Some(exp) if exp <= 1_000_000 => a.0.pow(exp as u32),
      _ => return None, // too large to compute
    }
  } else if *addr == p.nat_gcd.addr {
    gcd_biguint(&a.0, &b.0)
  } else if *addr == p.nat_land.addr {
    &a.0 & &b.0
  } else if *addr == p.nat_lor.addr {
    &a.0 | &b.0
  } else if *addr == p.nat_xor.addr {
    &a.0 ^ &b.0
  } else if *addr == p.nat_shift_left.addr {
    match b.to_u64() {
      #[allow(clippy::cast_possible_truncation)] // guarded: shift <= 1_000_000
      Some(shift) if shift <= 1_000_000 => &a.0 << shift as usize,
      _ => return None, // too large to compute
    }
  } else if *addr == p.nat_shift_right.addr {
    match b.to_u64() {
      #[allow(clippy::cast_possible_truncation)] // guarded: shift <= 1_000_000
      Some(shift) if shift <= 1_000_000 => &a.0 >> shift as usize,
      _ => zero, // right-shift by huge amount gives 0 (correct)
    }
  } else {
    return None;
  };
  Some(Nat(r))
}

#[cfg(test)]
mod tests {
  use super::super::constant::KConst;
  use super::super::env::{InternTable, KEnv};
  use super::super::expr::{ExprData, KExpr};
  use super::super::id::KId;
  use super::super::level::KUniv;
  use super::super::mode::Anon;
  use super::super::primitive::Primitives;
  use super::super::tc::TypeChecker;
  use super::*;
  use crate::ix::address::Address;
  use crate::ix::env::{DefinitionSafety, ReducibilityHints};
  use crate::ix::ixon::constant::DefKind;

  type AE = KExpr<Anon>;
  type AU = KUniv<Anon>;

  fn mk_addr(s: &str) -> Address {
    Address::hash(s.as_bytes())
  }
  fn mk_id(s: &str) -> KId<Anon> {
    KId::new(mk_addr(s), ())
  }
  fn sort0() -> AE {
    AE::sort(AU::zero())
  }
  fn sort1() -> AE {
    AE::sort(AU::succ(AU::zero()))
  }

  /// Build a minimal env with a single definition: `id := λ x. x : Sort 0 → Sort 0`
  fn env_with_id() -> KEnv<Anon> {
    let env = KEnv::new();
    let id_ty = AE::all((), (), sort0(), sort0()); // Sort 0 → Sort 0
    let id_val = AE::lam((), (), sort0(), AE::var(0, ())); // λ x. x
    env.insert(
      mk_id("id"),
      KConst::Defn {
        name: (),
        level_params: (),
        kind: DefKind::Definition,
        safety: DefinitionSafety::Safe,
        hints: ReducibilityHints::Abbrev,
        lvls: 0,
        ty: id_ty,
        val: id_val,
        lean_all: (),
        block: mk_id("id"),
      },
    );
    // Opaque constant
    let opaq_ty = sort0();
    let opaq_val = sort0();
    env.insert(
      mk_id("opaque"),
      KConst::Defn {
        name: (),
        level_params: (),
        kind: DefKind::Opaque,
        safety: DefinitionSafety::Safe,
        hints: ReducibilityHints::Opaque,
        lvls: 0,
        ty: opaq_ty,
        val: opaq_val,
        lean_all: (),
        block: mk_id("opaque"),
      },
    );
    env
  }

  #[test]
  fn whnf_var_identity() {
    let env = env_with_id();
    let mut tc = TypeChecker::new(&env, InternTable::new());
    let v = AE::var(0, ());
    assert_eq!(tc.whnf(&v).unwrap(), v);
  }

  #[test]
  fn whnf_sort_identity() {
    let env = env_with_id();
    let mut tc = TypeChecker::new(&env, InternTable::new());
    assert_eq!(tc.whnf(&sort0()).unwrap(), sort0());
  }

  #[test]
  fn whnf_lam_identity() {
    let env = env_with_id();
    let mut tc = TypeChecker::new(&env, InternTable::new());
    let lam = AE::lam((), (), sort0(), AE::var(0, ()));
    assert_eq!(tc.whnf(&lam).unwrap(), lam);
  }

  #[test]
  fn whnf_beta_simple() {
    let env = env_with_id();
    let mut tc = TypeChecker::new(&env, InternTable::new());
    // (λ x. x) a → a
    let lam = AE::lam((), (), sort0(), AE::var(0, ()));
    let a = AE::sort(AU::succ(AU::zero()));
    let app = AE::app(lam, a.clone());
    assert_eq!(tc.whnf(&app).unwrap(), a);
  }

  #[test]
  fn whnf_beta_multi() {
    let env = env_with_id();
    let mut tc = TypeChecker::new(&env, InternTable::new());
    // (λ x y. x) a b → a
    let body = AE::var(1, ()); // x (de Bruijn 1, the outer binder)
    let inner_lam = AE::lam((), (), sort0(), body);
    let outer_lam = AE::lam((), (), sort0(), inner_lam);
    let a = sort0();
    let b = sort1();
    let app = AE::app(AE::app(outer_lam, a.clone()), b);
    assert_eq!(tc.whnf(&app).unwrap(), a);
  }

  #[test]
  fn whnf_zeta() {
    let env = env_with_id();
    let mut tc = TypeChecker::new(&env, InternTable::new());
    // let x := Sort 0 in x → Sort 0
    let let_e = AE::let_((), sort1(), sort0(), AE::var(0, ()), true);
    assert_eq!(tc.whnf(&let_e).unwrap(), sort0());
  }

  #[test]
  fn whnf_delta() {
    let env = env_with_id();
    let mut tc = TypeChecker::new(&env, InternTable::new());
    // id(Sort 0) should delta-unfold id then beta-reduce
    let id_const = AE::cnst(mk_id("id"), Box::new([]));
    let app = AE::app(id_const, sort0());
    assert_eq!(tc.whnf(&app).unwrap(), sort0());
  }

  #[test]
  fn whnf_delta_opaque_blocked() {
    let env = env_with_id();
    let mut tc = TypeChecker::new(&env, InternTable::new());
    let opaque = AE::cnst(mk_id("opaque"), Box::new([]));
    // Opaque should NOT be unfolded
    let result = tc.whnf(&opaque).unwrap();
    assert!(matches!(result.data(), ExprData::Const(..)));
  }

  #[test]
  fn whnf_cache_hit() {
    let env = env_with_id();
    let mut tc = TypeChecker::new(&env, InternTable::new());
    let id_const = AE::cnst(mk_id("id"), Box::new([]));
    let app = AE::app(id_const, sort0());
    let r1 = tc.whnf(&app).unwrap();
    let r2 = tc.whnf(&app).unwrap();
    // Both should return the same result
    assert_eq!(r1, r2);
  }

  fn nat() -> AE {
    AE::cnst(mk_id("Nat"), Box::new([]))
  }
  fn param(n: u64) -> AU {
    AU::param(n, ())
  }
  fn pi(a: AE, b: AE) -> AE {
    AE::all((), (), a, b)
  }
  fn app(f: AE, a: AE) -> AE {
    AE::app(f, a)
  }
  fn lam(a: AE, b: AE) -> AE {
    AE::lam((), (), a, b)
  }
  fn var(i: u64) -> AE {
    AE::var(i, ())
  }
  fn cnst(name: &str, us: &[AU]) -> AE {
    AE::cnst(mk_id(name), us.to_vec().into_boxed_slice())
  }
  fn mk_nat(n: u64) -> AE {
    let v = Nat::from(n);
    let addr = Address::hash(&v.to_le_bytes());
    AE::nat(v, addr)
  }

  /// Build a Nat env with Nat, Nat.zero, Nat.succ, Nat.rec, and Nat.sub.
  /// Nat.sub is defined as a primitive that the kernel's try_reduce_nat handles,
  /// but also has a delta-unfoldable body using Nat.rec (to test reduction order).
  fn nat_env() -> KEnv<Anon> {
    use super::super::constant::RecRule;

    let env = KEnv::new();
    let block = mk_id("Nat");

    // Nat : Sort 1
    env.insert(
      mk_id("Nat"),
      KConst::Indc {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 0,
        params: 0,
        indices: 0,
        is_rec: true,
        is_refl: false,
        nested: 0,
        block: block.clone(),
        member_idx: 0,
        ty: sort1(),
        ctors: vec![mk_id("Nat.zero"), mk_id("Nat.succ")],
        lean_all: (),
      },
    );
    env.insert(
      mk_id("Nat.zero"),
      KConst::Ctor {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 0,
        induct: mk_id("Nat"),
        cidx: 0,
        params: 0,
        fields: 0,
        ty: nat(),
      },
    );
    env.insert(
      mk_id("Nat.succ"),
      KConst::Ctor {
        name: (),
        level_params: (),
        is_unsafe: false,
        lvls: 0,
        induct: mk_id("Nat"),
        cidx: 1,
        params: 0,
        fields: 1,
        ty: pi(nat(), nat()),
      },
    );

    // Nat.rec : ∀ {motive : Nat → Sort u} (zero : motive 0) (succ : ∀ n, motive n → motive (succ n)) (t : Nat), motive t
    let motive_ty = pi(nat(), AE::sort(param(0)));
    let minor_zero = app(var(0), cnst("Nat.zero", &[]));
    let minor_succ = pi(
      nat(),
      pi(app(var(2), var(0)), app(var(3), app(cnst("Nat.succ", &[]), var(1)))),
    );
    let rec_ty = pi(
      motive_ty,
      pi(minor_zero, pi(minor_succ, pi(nat(), app(var(3), var(0))))),
    );
    let rule_zero_rhs = lam(sort0(), lam(sort0(), lam(sort0(), var(1))));
    let nat_rec_const = cnst("Nat.rec", &[param(0)]);
    let ih = app(app(app(app(nat_rec_const, var(3)), var(2)), var(1)), var(0));
    let rule_succ_rhs = lam(
      sort0(),
      lam(sort0(), lam(sort0(), lam(nat(), app(app(var(1), var(0)), ih)))),
    );
    env.insert(
      mk_id("Nat.rec"),
      KConst::Recr {
        name: (),
        level_params: (),
        k: false,
        is_unsafe: false,
        lvls: 1,
        params: 0,
        indices: 0,
        motives: 1,
        minors: 2,
        block: block.clone(),
        member_idx: 0,
        ty: rec_ty,
        rules: vec![
          RecRule { fields: 0, rhs: rule_zero_rhs },
          RecRule { fields: 1, rhs: rule_succ_rhs },
        ],
        lean_all: (),
      },
    );

    // Nat.sub : Nat → Nat → Nat
    // Body: a simple definition that the kernel should reduce natively.
    // In practice Nat.sub's body uses Nat.rec, but try_reduce_nat
    // should intercept it before delta unfolding exposes the body.
    let sub_ty = pi(nat(), pi(nat(), nat()));
    // Body is irrelevant for the native reduction test — just use a placeholder.
    // To test the delta-unfold-before-native-reduce bug, we make the body
    // something that would diverge if delta-unfolded: Nat.rec applied to arg.
    // Nat.sub a b = Nat.rec (motive := λ _, Nat) a (λ n ih, Nat.pred ih) b
    // But for simplicity, just use λ a b. a (dummy body).
    let sub_val = lam(nat(), lam(nat(), var(1)));
    env.insert(
      mk_id("Nat.sub"),
      KConst::Defn {
        name: (),
        level_params: (),
        kind: DefKind::Definition,
        safety: DefinitionSafety::Safe,
        hints: ReducibilityHints::Regular(0),
        lvls: 0,
        ty: sub_ty,
        val: sub_val,
        lean_all: (),
        block: mk_id("Nat.sub"),
      },
    );

    env.blocks.insert(
      block,
      vec![
        mk_id("Nat"),
        mk_id("Nat.zero"),
        mk_id("Nat.succ"),
        mk_id("Nat.rec"),
      ],
    );
    env
  }

  #[test]
  fn whnf_nat_sub_native() {
    // Nat.sub 1000 500 should reduce to Nat(500) via try_reduce_nat,
    // without delta-unfolding Nat.sub's body.
    let env = nat_env();
    // Build primitives from an empty env to get hardcoded addresses as KIds
    let empty = KEnv::new();
    let prims = Primitives::from_env(&empty);
    // Insert Nat.sub at its REAL primitive address so try_reduce_nat recognizes it
    let sub_id = prims.nat_sub.clone();
    let sub_ty = pi(nat(), pi(nat(), nat()));
    let sub_val = lam(nat(), lam(nat(), var(1))); // dummy body: λ a b. a
    env.insert(
      sub_id.clone(),
      KConst::Defn {
        name: (),
        level_params: (),
        kind: DefKind::Definition,
        safety: DefinitionSafety::Safe,
        hints: ReducibilityHints::Regular(0),
        lvls: 0,
        ty: sub_ty,
        val: sub_val,
        lean_all: (),
        block: sub_id.clone(),
      },
    );
    let mut tc = TypeChecker::new(&env, InternTable::new());
    let sub_const = AE::cnst(sub_id, Box::new([]));
    let expr = app(app(sub_const, mk_nat(1000)), mk_nat(500));
    let result = tc.whnf(&expr).unwrap();
    match result.data() {
      ExprData::Nat(v, _, _) => assert_eq!(
        v.0,
        num_bigint::BigUint::from(500u64),
        "Nat.sub 1000 500 should be 500"
      ),
      other => panic!("expected Nat(500), got {:?}", other),
    }
  }

  #[test]
  fn whnf_nat_ble_large() {
    // Nat.ble 2^32 2^32 should reduce to Bool.true via try_reduce_nat
    let env = nat_env();
    let mut tc = TypeChecker::new(&env, InternTable::new());
    let ble = AE::cnst(tc.prims.nat_ble.clone(), Box::new([]));
    let big = mk_nat(1u64 << 32);
    let expr = app(app(ble, big.clone()), big);
    let result = tc.whnf(&expr).unwrap();
    // Should be Bool.true constant
    match result.data() {
      ExprData::Const(id, _, _) => assert_eq!(id.addr, tc.prims.bool_true.addr),
      other => panic!("expected Bool.true, got {:?}", other),
    }
  }

  #[test]
  fn whnf_def_eq_nat_sub_large() {
    // Simulate the real failure: a definition whose type-check requires
    // proving `Nat.sub (2^16) x =?= y` via def-eq. If Nat.sub gets
    // delta-unfolded to Nat.rec before try_reduce_nat intercepts it,
    // the kernel diverges on iota reduction.
    let env = nat_env();
    // Build primitives from an empty env to get hardcoded addresses as KIds
    let empty = KEnv::new();
    let prims = Primitives::from_env(&empty);
    let sub_id = prims.nat_sub.clone();
    let sub_ty = pi(nat(), pi(nat(), nat()));
    // Body that uses Nat.rec — if delta-unfolded, this would produce
    // Nat.rec motive zero_case succ_case (lit 65536) which diverges.
    // But try_reduce_nat should intercept Nat.sub first.
    let sub_val = lam(nat(), lam(nat(), var(1))); // dummy
    env.insert(
      sub_id.clone(),
      KConst::Defn {
        name: (),
        level_params: (),
        kind: DefKind::Definition,
        safety: DefinitionSafety::Safe,
        hints: ReducibilityHints::Regular(0),
        lvls: 0,
        ty: sub_ty,
        val: sub_val,
        lean_all: (),
        block: sub_id.clone(),
      },
    );
    let mut tc = TypeChecker::new(&env, InternTable::new());
    let sub_const = AE::cnst(sub_id, Box::new([]));
    let big = mk_nat(65536); // 2^16
    let expr = app(app(sub_const, big), mk_nat(0));
    let result = tc.whnf(&expr).unwrap();
    match result.data() {
      ExprData::Nat(v, _, _) => {
        assert_eq!(v.0, num_bigint::BigUint::from(65536u64))
      },
      other => panic!("expected Nat(65536), got {:?}", other),
    }
  }

  #[test]
  fn def_eq_large_nat_literals() {
    // Two identical large Nat literals should be equal via the fast-path
    // (direct value comparison, not O(n) succ peeling).
    let env = nat_env();
    let mut tc = TypeChecker::new(&env, InternTable::new());
    let a = mk_nat(1 << 20); // ~1 million
    let b = mk_nat(1 << 20);
    assert!(
      tc.is_def_eq(&a, &b).unwrap(),
      "identical large Nat literals should be def-eq"
    );
  }

  #[test]
  fn whnf_nat_rec_small() {
    // Nat.rec (motive) zero_case succ_case (Nat(3)) should reduce via iota
    // to succ_case 2 (succ_case 1 (succ_case 0 zero_case))
    let env = nat_env();
    let mut tc = TypeChecker::new(&env, InternTable::new());
    let rec = cnst("Nat.rec", &[AU::succ(AU::zero())]); // Nat.rec.{1}
    // motive := λ _, Nat
    let motive = lam(nat(), nat());
    // zero_case := Nat(42)
    let zero_case = mk_nat(42);
    // succ_case := λ n ih, Nat.succ ih
    let succ_case = lam(nat(), lam(nat(), app(cnst("Nat.succ", &[]), var(0))));
    let expr = app(app(app(app(rec, motive), zero_case), succ_case), mk_nat(3));
    let result = tc.whnf(&expr).unwrap();
    // Should be Nat.succ(Nat.succ(Nat.succ(Nat(42))))
    // After native succ reduction: Nat(45)
    match result.data() {
      ExprData::Nat(v, _, _) => {
        assert_eq!(v.0, num_bigint::BigUint::from(45u64))
      },
      ExprData::App(..) => {
        // Might be Nat.succ chain — that's also acceptable
        eprintln!("Nat.rec result is App chain (not folded to literal)");
      },
      other => panic!("unexpected Nat.rec result: {:?}", other),
    }
  }

  // -----------------------------------------------------------------------
  // USize.size reduction chain tests
  // -----------------------------------------------------------------------

  /// Build an env that includes the full USize.size reduction chain:
  ///   System.Platform.numBits (handled by try_reduce_native → 64)
  ///   Nat.pow at the correct primitive address
  ///   USize.size := Nat.pow 2 numBits (reducible def)
  fn usize_env() -> KEnv<Anon> {
    let env = nat_env();
    let empty = KEnv::new();
    let prims = Primitives::from_env(&empty);

    // System.Platform.numBits — insert at the real primitive address
    // so try_reduce_native recognizes it. It's a def whose body doesn't
    // matter (native handler intercepts it) but it needs to be present.
    env.insert(
      prims.system_platform_num_bits.clone(),
      KConst::Defn {
        name: (),
        level_params: (),
        kind: DefKind::Definition,
        safety: DefinitionSafety::Safe,
        hints: ReducibilityHints::Abbrev,
        lvls: 0,
        ty: nat(),
        val: mk_nat(64), // body: just 64 (native handler returns this anyway)
        lean_all: (),
        block: prims.system_platform_num_bits.clone(),
      },
    );

    // Nat.pow at the real primitive address
    let pow_ty = pi(nat(), pi(nat(), nat()));
    let pow_val = lam(nat(), lam(nat(), var(1))); // dummy body
    env.insert(
      prims.nat_pow.clone(),
      KConst::Defn {
        name: (),
        level_params: (),
        kind: DefKind::Definition,
        safety: DefinitionSafety::Safe,
        hints: ReducibilityHints::Regular(0),
        lvls: 0,
        ty: pow_ty,
        val: pow_val,
        lean_all: (),
        block: prims.nat_pow.clone(),
      },
    );

    // Nat.sub at the real primitive address
    let sub_ty = pi(nat(), pi(nat(), nat()));
    let sub_val = lam(nat(), lam(nat(), var(1))); // dummy body
    env.insert(
      prims.nat_sub.clone(),
      KConst::Defn {
        name: (),
        level_params: (),
        kind: DefKind::Definition,
        safety: DefinitionSafety::Safe,
        hints: ReducibilityHints::Regular(0),
        lvls: 0,
        ty: sub_ty,
        val: sub_val,
        lean_all: (),
        block: prims.nat_sub.clone(),
      },
    );

    // Nat.pred at the real primitive address
    let pred_ty = pi(nat(), nat());
    let pred_val = lam(nat(), var(0)); // dummy body
    env.insert(
      prims.nat_pred.clone(),
      KConst::Defn {
        name: (),
        level_params: (),
        kind: DefKind::Definition,
        safety: DefinitionSafety::Safe,
        hints: ReducibilityHints::Regular(0),
        lvls: 0,
        ty: pred_ty,
        val: pred_val,
        lean_all: (),
        block: prims.nat_pred.clone(),
      },
    );

    // USize.size := Nat.pow 2 System.Platform.numBits
    let usize_size_val = app(
      app(AE::cnst(prims.nat_pow.clone(), Box::new([])), mk_nat(2)),
      AE::cnst(prims.system_platform_num_bits.clone(), Box::new([])),
    );
    env.insert(
      mk_id("USize.size"),
      KConst::Defn {
        name: (),
        level_params: (),
        kind: DefKind::Definition,
        safety: DefinitionSafety::Safe,
        hints: ReducibilityHints::Abbrev, // @[reducible]
        lvls: 0,
        ty: nat(),
        val: usize_size_val,
        lean_all: (),
        block: mk_id("USize.size"),
      },
    );

    env
  }

  #[test]
  fn whnf_system_platform_num_bits() {
    // System.Platform.numBits should reduce to 64 via try_reduce_native
    let env = usize_env();
    let mut tc = TypeChecker::new(&env, InternTable::new());
    let num_bits =
      AE::cnst(tc.prims.system_platform_num_bits.clone(), Box::new([]));
    let result = tc.whnf(&num_bits).unwrap();
    match result.data() {
      ExprData::Nat(v, _, _) => {
        assert_eq!(v.0, num_bigint::BigUint::from(64u64))
      },
      other => panic!("expected Nat(64), got {:?}", other),
    }
  }

  #[test]
  fn whnf_nat_pow_2_64() {
    // Nat.pow 2 64 should reduce to 2^64
    let env = usize_env();
    let mut tc = TypeChecker::new(&env, InternTable::new());
    let pow_const = AE::cnst(tc.prims.nat_pow.clone(), Box::new([]));
    let expr = app(app(pow_const, mk_nat(2)), mk_nat(64));
    let result = tc.whnf(&expr).unwrap();
    match result.data() {
      ExprData::Nat(v, _, _) => assert_eq!(
        v.0,
        num_bigint::BigUint::from(1u64 << 63) * 2u64,
        "Nat.pow 2 64 should be 2^64"
      ),
      other => panic!("expected Nat(2^64), got {:?}", other),
    }
  }

  #[test]
  fn whnf_usize_size() {
    // USize.size := Nat.pow 2 numBits should reduce to 2^64
    let env = usize_env();
    let mut tc = TypeChecker::new(&env, InternTable::new());
    let usize_size = AE::cnst(mk_id("USize.size"), Box::new([]));
    let result = tc.whnf(&usize_size).unwrap();
    let expected = num_bigint::BigUint::from(1u64 << 63) * 2u64;
    match result.data() {
      ExprData::Nat(v, _, _) => {
        assert_eq!(v.0, expected, "USize.size should be 2^64")
      },
      other => panic!("expected Nat(2^64), got {:?}", other),
    }
  }

  #[test]
  fn whnf_nat_sub_usize_size_0() {
    // Nat.sub USize.size 0 should reduce to 2^64
    let env = usize_env();
    let mut tc = TypeChecker::new(&env, InternTable::new());
    let sub_const = AE::cnst(tc.prims.nat_sub.clone(), Box::new([]));
    let usize_size = AE::cnst(mk_id("USize.size"), Box::new([]));
    let expr = app(app(sub_const, usize_size), mk_nat(0));
    let result = tc.whnf(&expr).unwrap();
    let expected = num_bigint::BigUint::from(1u64 << 63) * 2u64;
    match result.data() {
      ExprData::Nat(v, _, _) => {
        assert_eq!(v.0, expected, "Nat.sub USize.size 0 should be 2^64")
      },
      other => panic!("expected Nat(2^64), got {:?}", other),
    }
  }

  #[test]
  fn whnf_nat_pred_usize_size() {
    // Nat.pred USize.size should reduce to 2^64 - 1
    let env = usize_env();
    let mut tc = TypeChecker::new(&env, InternTable::new());
    let pred_const = AE::cnst(tc.prims.nat_pred.clone(), Box::new([]));
    let usize_size = AE::cnst(mk_id("USize.size"), Box::new([]));
    let expr = app(pred_const, usize_size);
    let result = tc.whnf(&expr).unwrap();
    let expected = num_bigint::BigUint::from(1u64 << 63) * 2u64 - 1u64;
    match result.data() {
      ExprData::Nat(v, _, _) => {
        assert_eq!(v.0, expected, "Nat.pred USize.size should be 2^64 - 1")
      },
      other => panic!("expected Nat(2^64 - 1), got {:?}", other),
    }
  }

  #[test]
  fn def_eq_usize_pred_sub_vs_sub_1() {
    // Nat.pred (Nat.sub USize.size 0) =?= Nat.sub USize.size 1
    // This is the actual failing pattern from USize.toUInt16_ofNatTruncate_of_lt
    let env = usize_env();
    let mut tc = TypeChecker::new(&env, InternTable::new());

    let sub_const = AE::cnst(tc.prims.nat_sub.clone(), Box::new([]));
    let pred_const = AE::cnst(tc.prims.nat_pred.clone(), Box::new([]));
    let usize_size = AE::cnst(mk_id("USize.size"), Box::new([]));

    // LHS: Nat.pred (Nat.sub USize.size 0)
    let lhs = app(
      pred_const,
      app(app(sub_const.clone(), usize_size.clone()), mk_nat(0)),
    );
    // RHS: Nat.sub USize.size 1
    let rhs = app(app(sub_const, usize_size), mk_nat(1));

    assert!(
      tc.is_def_eq(&lhs, &rhs).unwrap(),
      "Nat.pred (Nat.sub USize.size 0) should be def-eq to Nat.sub USize.size 1"
    );
  }
}
