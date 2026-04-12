//! Definitional equality checking.
//!
//! Multi-tier strategy following lean4lean:
//! 1. Quick structural (same constructor, same children)
//! 2. WHNF without delta, quick structural
//! 3. Proof irrelevance (before delta)
//! 4. Iterative lazy delta with same-head-spine optimization
//! 5. Full WHNF, structural comparison, eta, struct eta

use crate::ix::ixon::constant::DefKind;

use super::constant::KConst;
use super::error::{TcError, u64_to_usize};
use super::expr::{ExprData, KExpr};
use super::id::KId;
use super::level::{KUniv, univ_eq};
use super::mode::KernelMode;
use super::subst::lift;
use super::tc::{
  MAX_DEF_EQ_DEPTH, MAX_WHNF_FUEL, TypeChecker, collect_app_spine,
};

impl<'env, M: KernelMode> TypeChecker<'env, M> {
  /// Check definitional equality of two expressions.
  pub fn is_def_eq(
    &mut self,
    a: &KExpr<M>,
    b: &KExpr<M>,
  ) -> Result<bool, TcError<M>> {
    self.tick()?;
    if a.ptr_eq(b) {
      return Ok(true);
    }

    // Context-aware EquivManager: closed exprs (lbr==0) share across contexts,
    // open exprs under let-bindings are isolated by ctx_id.
    let eq_ctx = if self.num_let_bindings > 0 && (a.lbr() > 0 || b.lbr() > 0) {
      self.ctx_id
    } else {
      0
    };
    if self.equiv_manager.is_equiv((a.ptr_key(), eq_ctx), (b.ptr_key(), eq_ctx))
    {
      return Ok(true);
    }

    let (lo, hi) = canonical_pair(a.ptr_key(), b.ptr_key());
    let cache_key = (lo, hi, self.ctx_id);
    if let Some(&cached) = self.def_eq_cache.get(&cache_key) {
      return Ok(cached);
    }

    // Equiv-root second-chance: if (a,b) not cached, try (root(a), root(b)).
    // If a ≡ a' and b ≡ b' (in equiv_manager) and (a',b') was cached,
    // then (a,b) has the same result without recomputation.
    {
      let a_key = (a.ptr_key(), eq_ctx);
      let b_key = (b.ptr_key(), eq_ctx);
      if let (Some(a_root), Some(b_root)) = (
        self.equiv_manager.find_root_key(a_key),
        self.equiv_manager.find_root_key(b_key),
      ) && (a_root != a_key || b_root != b_key)
      {
        let (rlo, rhi) = canonical_pair(a_root.0, b_root.0);
        let root_cache_key = (rlo, rhi, self.ctx_id);
        if let Some(&cached) = self.def_eq_cache.get(&root_cache_key) {
          if cached {
            self.equiv_manager.add_equiv(a_key, b_key);
          }
          self.def_eq_cache.insert(cache_key, cached);
          return Ok(cached);
        }
      }
    }

    self.def_eq_depth += 1;
    if self.def_eq_depth > self.def_eq_peak {
      self.def_eq_peak = self.def_eq_depth;
    }
    if self.def_eq_depth > MAX_DEF_EQ_DEPTH {
      self.def_eq_depth -= 1;
      return Err(TcError::MaxRecDepth);
    }

    let result = self.is_def_eq_inner(a, b);
    self.def_eq_depth -= 1;

    let ok = result?;
    if ok {
      self
        .equiv_manager
        .add_equiv((a.ptr_key(), eq_ctx), (b.ptr_key(), eq_ctx));
    }
    self.def_eq_cache.insert(cache_key, ok);
    Ok(ok)
  }

  fn is_def_eq_inner(
    &mut self,
    a: &KExpr<M>,
    b: &KExpr<M>,
  ) -> Result<bool, TcError<M>> {
    // Tier 1: quick structural
    if self.quick_def_eq(a, b)? {
      return Ok(true);
    }

    // Tier 1b: Eager Bool reduction (lean4 type_checker.cpp:1066)
    // If one side is Bool.true and the other has no loose bound vars (or eagerReduce
    // is active), try full WHNF. Critical for Decidable/decide-based definitions.
    if self.is_bool_true(b) && (a.lbr() == 0 || self.eager_reduce) {
      let wa = self.whnf(a)?;
      if self.is_bool_true(&wa) {
        return Ok(true);
      }
    } else if self.is_bool_true(a) && (b.lbr() == 0 || self.eager_reduce) {
      let wb = self.whnf(b)?;
      if self.is_bool_true(&wb) {
        return Ok(true);
      }
    }

    // Tier 1c: String literal expansion (before any WHNF).
    // Expand string literals to String.ofList [Char.ofNat c₁, ...] form so
    // both sides can reduce in lockstep through lazy delta. Must happen before
    // WHNF to avoid committing the other side to a structural form that
    // diverges from the expansion.
    if matches!(a.data(), ExprData::Str(..))
      || matches!(b.data(), ExprData::Str(..))
    {
      if self.try_string_lit_expansion(a, b)? {
        return Ok(true);
      }
      if self.try_string_lit_expansion(b, a)? {
        return Ok(true);
      }
    }

    // Tier 2: WHNF without delta
    let mut wa = self.whnf_no_delta(a)?;
    let mut wb = self.whnf_no_delta(b)?;
    if wa.ptr_eq(&wb) {
      return Ok(true);
    }
    if self.quick_def_eq(&wa, &wb)? {
      return Ok(true);
    }

    // Tier 3: proof irrelevance (before delta)
    if self.try_proof_irrel(&wa, &wb)? {
      return Ok(true);
    }

    // Tier 4: iterative lazy delta (lean4lean lazyDeltaReduction)
    let mut fuel = MAX_WHNF_FUEL;
    loop {
      if fuel == 0 {
        return Err(TcError::MaxRecDepth);
      }
      fuel -= 1;

      // M2: Nat offset reduction at top of loop (lean4lean isDefEqOffset)
      if let Some(result) = self.try_def_eq_offset(&wa, &wb)? {
        return Ok(result);
      }

      // Nat primitive reduction inside lazy delta (lean4lean:620-623)
      if let Some(wa2) = self.try_reduce_nat(&wa)? {
        return self.is_def_eq(&wa2, &wb);
      }
      if let Some(wb2) = self.try_reduce_nat(&wb)? {
        return self.is_def_eq(&wa, &wb2);
      }

      // Native reduction inside lazy delta (lean4lean:625-628)
      if let Some(wa2) = self.try_reduce_native(&wa)? {
        return self.is_def_eq(&wa2, &wb);
      }
      if let Some(wb2) = self.try_reduce_native(&wb)? {
        return self.is_def_eq(&wa, &wb2);
      }

      let a_head = head_const_id(&wa);
      let b_head = head_const_id(&wb);
      let a_delta = a_head.as_ref().is_some_and(|h| self.is_delta(h));
      let b_delta = b_head.as_ref().is_some_and(|h| self.is_delta(h));

      if !a_delta && !b_delta {
        break;
      }

      // C6: Before unfolding a definition, try reducing projection apps
      // on the non-definition side (lean4lean tryUnfoldProjApp).
      if a_delta && !b_delta {
        if let Some(wb2) = self.try_unfold_proj_app(&wb)? {
          wb = wb2;
          continue;
        }
      } else if b_delta
        && !a_delta
        && let Some(wa2) = self.try_unfold_proj_app(&wa)?
      {
        wa = wa2;
        continue;
      }

      if a_delta && b_delta {
        let wa_w = a_head.as_ref().map_or(u32::MAX, |h| self.def_weight_id(h));
        let wb_w = b_head.as_ref().map_or(u32::MAX, |h| self.def_weight_id(h));

        if wa_w == wb_w {
          // H2: Same-head-spine optimization — only for Regular hints, same head,
          // and only cache failure when spine args are actually compared (lean4lean:589-596)
          if let (Some(ah), Some(bh)) = (&a_head, &b_head)
            && ah.addr == bh.addr
            && self.is_regular(ah)
          {
            let (lo, hi) = canonical_pair(wa.ptr_key(), wb.ptr_key());
            let failure_key = (lo, hi, self.ctx_id);
            if !self.def_eq_failure.contains(&failure_key) {
              if let Some(result) = self.try_same_head_spine(&wa, &wb)? {
                return Ok(result);
              }
              // Spine comparison was attempted and failed — cache it
              self.def_eq_failure.insert(failure_key);
            }
          }
          // H1: Equal height — unfold BOTH sides (lean4lean:596)
          let ua = self.delta_unfold_one(&wa)?;
          let ub = self.delta_unfold_one(&wb)?;
          match (ua, ub) {
            (Some(ua), Some(ub)) => {
              wa = self.whnf_no_delta(&ua)?;
              wb = self.whnf_no_delta(&ub)?;
            },
            (Some(ua), None) => {
              wa = self.whnf_no_delta(&ua)?;
            },
            (None, Some(ub)) => {
              wb = self.whnf_no_delta(&ub)?;
            },
            (None, None) => break,
          }
        } else if wa_w > wb_w {
          // a is heavier — unfold a first
          if let Some(ua) = self.delta_unfold_one(&wa)? {
            wa = self.whnf_no_delta(&ua)?;
          } else {
            break;
          }
        } else {
          // b is heavier — unfold b first
          if let Some(ub) = self.delta_unfold_one(&wb)? {
            wb = self.whnf_no_delta(&ub)?;
          } else {
            break;
          }
        }
      } else if a_delta {
        if let Some(ua) = self.delta_unfold_one(&wa)? {
          wa = self.whnf_no_delta(&ua)?;
        } else {
          break;
        }
      } else if let Some(ub) = self.delta_unfold_one(&wb)? {
        wb = self.whnf_no_delta(&ub)?;
      } else {
        break;
      }

      if wa.ptr_eq(&wb) {
        return Ok(true);
      }
      if self.quick_def_eq(&wa, &wb)? {
        return Ok(true);
      }
    }

    // Tier 4b: post-delta congruence checks (lean4lean isDefEqConst/Fvar/Proj)
    if self.try_structural_congruence(&wa, &wb)? {
      return Ok(true);
    }

    // Tier 4c: second structural pass (lean4lean:683-686, lean4 type_checker.cpp:1109-1110)
    // whnf_core with cheap projections — catches structural matches after delta exhaustion.
    let wa = self.whnf_core(&wa)?;
    let wb = self.whnf_core(&wb)?;
    if wa.ptr_eq(&wb) {
      return Ok(true);
    }
    if self.quick_def_eq(&wa, &wb)? {
      return Ok(true);
    }

    // Tier 4d: app spine comparison (lean4lean isDefEqApp, lean4 type_checker.cpp:1115)
    if self.try_def_eq_app(&wa, &wb)? {
      return Ok(true);
    }

    // Tier 5: full WHNF, structural comparison
    let wa = self.whnf(&wa)?;
    let wb = self.whnf(&wb)?;
    if wa.ptr_eq(&wb) {
      return Ok(true);
    }

    self.is_def_eq_whnf(&wa, &wb)
  }

  /// Quick structural: same constructor, recursively same children (no WHNF).
  fn quick_def_eq(
    &mut self,
    a: &KExpr<M>,
    b: &KExpr<M>,
  ) -> Result<bool, TcError<M>> {
    match (a.data(), b.data()) {
      (ExprData::Sort(u1, _), ExprData::Sort(u2, _)) => Ok(univ_eq(u1, u2)),
      (
        ExprData::Lam(_, _, ty1, body1, _),
        ExprData::Lam(_, _, ty2, body2, _),
      )
      | (
        ExprData::All(_, _, ty1, body1, _),
        ExprData::All(_, _, ty2, body2, _),
      ) => {
        if !self.is_def_eq(ty1, ty2)? {
          return Ok(false);
        }
        self.push_local(ty1.clone());
        let r = self.is_def_eq(body1, body2);
        self.pop_local();
        r
      },
      _ => Ok(false),
    }
  }

  /// Same-head constant: if both are `C us args`, compare spines without unfolding.
  fn try_same_head_spine(
    &mut self,
    a: &KExpr<M>,
    b: &KExpr<M>,
  ) -> Result<Option<bool>, TcError<M>> {
    let (a_head, a_args) = collect_app_spine(a);
    let (b_head, b_args) = collect_app_spine(b);
    let (a_id, a_us) = match a_head.data() {
      ExprData::Const(id, us, _) => (id, us),
      _ => return Ok(None),
    };
    let (b_id, b_us) = match b_head.data() {
      ExprData::Const(id, us, _) => (id, us),
      _ => return Ok(None),
    };
    if a_id.addr != b_id.addr || a_args.len() != b_args.len() {
      return Ok(None);
    }
    if a_us.len() != b_us.len()
      || !a_us.iter().zip(b_us.iter()).all(|(u, v)| univ_eq(u, v))
    {
      return Ok(None);
    }
    for (ai, bi) in a_args.iter().zip(b_args.iter()) {
      if !self.is_def_eq(ai, bi)? {
        return Ok(None);
      }
    }
    Ok(Some(true))
  }

  /// Full structural comparison after WHNF.
  fn is_def_eq_whnf(
    &mut self,
    a: &KExpr<M>,
    b: &KExpr<M>,
  ) -> Result<bool, TcError<M>> {
    // First try purely structural comparison
    let structural = match (a.data(), b.data()) {
      (ExprData::Sort(u1, _), ExprData::Sort(u2, _)) => {
        return Ok(univ_eq(u1, u2));
      },
      (ExprData::Var(i, _, _), ExprData::Var(j, _, _)) if i == j => {
        return Ok(true);
      },
      (ExprData::Const(id1, us1, _), ExprData::Const(id2, us2, _)) => {
        if id1.addr == id2.addr
          && us1.len() == us2.len()
          && us1.iter().zip(us2.iter()).all(|(u, v)| univ_eq(u, v))
        {
          return Ok(true);
        }
        false
      },
      (ExprData::App(f1, a1, _), ExprData::App(f2, a2, _)) => {
        if self.is_def_eq(f1, f2)? && self.is_def_eq(a1, a2)? {
          return Ok(true);
        }
        false
      },
      (
        ExprData::Lam(_, _, ty1, body1, _),
        ExprData::Lam(_, _, ty2, body2, _),
      )
      | (
        ExprData::All(_, _, ty1, body1, _),
        ExprData::All(_, _, ty2, body2, _),
      ) => {
        if self.is_def_eq(ty1, ty2)? {
          self.push_local(ty1.clone());
          let r = self.is_def_eq(body1, body2)?;
          self.pop_local();
          if r {
            return Ok(true);
          }
        }
        false
      },
      (
        ExprData::Let(_, ty1, v1, body1, _, _),
        ExprData::Let(_, ty2, v2, body2, _, _),
      ) => {
        // H3: Let should be zeta-reduced by whnf_core before reaching this point.
        // Use push_let (not push_local) so the let-bound value is available for
        // reduction in the body comparison, in case this code IS reached.
        if self.is_def_eq(ty1, ty2)? && self.is_def_eq(v1, v2)? {
          self.push_let(ty1.clone(), v1.clone());
          let r = self.is_def_eq(body1, body2)?;
          self.pop_local();
          if r {
            return Ok(true);
          }
        }
        false
      },
      (ExprData::Nat(v1, _, _), ExprData::Nat(v2, _, _)) => {
        return Ok(v1 == v2);
      },
      (ExprData::Str(v1, _, _), ExprData::Str(v2, _, _)) => {
        return Ok(v1 == v2);
      },
      _ => false,
    };

    if structural {
      return Ok(true);
    }

    // Nat literal ↔ constructor: 0 ≡ Nat.zero, succ(n) ≡ n+1
    if self.is_nat_like(a) && self.is_nat_like(b) {
      return self.is_def_eq_nat(a, b);
    }

    // Eta expansion: try both directions
    if matches!(a.data(), ExprData::Lam(..))
      || matches!(b.data(), ExprData::Lam(..))
    {
      if self.try_eta_expansion(a, b)? {
        return Ok(true);
      }
      if self.try_eta_expansion(b, a)? {
        return Ok(true);
      }
    }

    // String literal expansion
    if matches!(a.data(), ExprData::Str(..))
      || matches!(b.data(), ExprData::Str(..))
    {
      if self.try_string_lit_expansion(a, b)? {
        return Ok(true);
      }
      if self.try_string_lit_expansion(b, a)? {
        return Ok(true);
      }
    }

    // Struct eta + unit-like + proof irrelevance fallback
    if self.try_eta_struct(a, b)? {
      return Ok(true);
    }
    if self.try_eta_struct(b, a)? {
      return Ok(true);
    }
    if self.try_def_eq_unit(a, b)? {
      return Ok(true);
    }
    self.try_proof_irrel(a, b)
  }

  /// Proof irrelevance: if both are proofs of propositions (types in Prop),
  /// they're def-eq. We check type(type(a)) = Sort(0), meaning type(a) : Prop.
  fn try_proof_irrel(
    &mut self,
    a: &KExpr<M>,
    b: &KExpr<M>,
  ) -> Result<bool, TcError<M>> {
    let a_ty = match self.with_infer_only(|tc| tc.infer(a)) {
      Ok(ty) => ty,
      Err(_) => return Ok(false),
    };
    // Check if a_ty lives in Prop: infer(a_ty) should be Sort(0)
    let a_ty_ty = match self.with_infer_only(|tc| tc.infer(&a_ty)) {
      Ok(ty) => ty,
      Err(_) => return Ok(false),
    };
    let a_ty_sort = match self.whnf(&a_ty_ty) {
      Ok(s) => s,
      Err(_) => return Ok(false),
    };
    match a_ty_sort.data() {
      ExprData::Sort(u, _) if u.is_zero() => {
        let b_ty = match self.with_infer_only(|tc| tc.infer(b)) {
          Ok(ty) => ty,
          Err(_) => return Ok(false),
        };
        self.is_def_eq(&a_ty, &b_ty)
      },
      _ => Ok(false),
    }
  }

  /// Unit-like type: non-recursive, 0 indices, 1 ctor with 0 fields.
  /// If both values inhabit the same unit-like type, they're def-eq.
  fn try_def_eq_unit(
    &mut self,
    a: &KExpr<M>,
    b: &KExpr<M>,
  ) -> Result<bool, TcError<M>> {
    let a_ty = match self.with_infer_only(|tc| tc.infer(a)) {
      Ok(ty) => ty,
      Err(_) => return Ok(false),
    };
    let a_ty_w = match self.whnf(&a_ty) {
      Ok(w) => w,
      Err(_) => return Ok(false),
    };
    let (a_head, _) = collect_app_spine(&a_ty_w);
    let a_ind = match a_head.data() {
      ExprData::Const(id, _, _) => id.clone(),
      _ => return Ok(false),
    };
    // Check unit-like: non-recursive, 0 indices, 1 ctor with 0 fields
    let is_unit = match self.env.get(&a_ind) {
      Some(KConst::Indc { is_rec, indices, ctors, .. }) => {
        if is_rec || indices != 0 || ctors.len() != 1 {
          false
        } else {
          match self.env.get(&ctors[0]) {
            Some(KConst::Ctor { fields, .. }) => fields == 0,
            _ => false,
          }
        }
      },
      _ => return Ok(false),
    };
    if !is_unit {
      return Ok(false);
    }
    // Both must have the same type
    let b_ty = match self.with_infer_only(|tc| tc.infer(b)) {
      Ok(ty) => ty,
      Err(_) => return Ok(false),
    };
    self.is_def_eq(&a_ty_w, &b_ty)
  }

  // -----------------------------------------------------------------------
  // Nat literal ↔ constructor comparison
  // -----------------------------------------------------------------------

  /// Check if an expression is a nat-like value (literal, Nat.zero, Nat.succ _).
  fn is_nat_like(&self, e: &KExpr<M>) -> bool {
    match e.data() {
      ExprData::Nat(..) => true,
      ExprData::Const(id, _, _) => id.addr == self.prims.nat_zero.addr,
      ExprData::App(f, _, _) => {
        matches!(f.data(), ExprData::Const(id, _, _) if id.addr == self.prims.nat_succ.addr)
      },
      _ => false,
    }
  }

  /// Check if expression is nat zero (literal 0 or Nat.zero constructor).
  fn is_nat_zero(&self, e: &KExpr<M>) -> bool {
    match e.data() {
      ExprData::Nat(v, _, _) => v.0 == num_bigint::BigUint::ZERO,
      ExprData::Const(id, _, _) => id.addr == self.prims.nat_zero.addr,
      _ => false,
    }
  }

  /// If expression is nat-succ, return the predecessor.
  /// Matches both `Nat(n+1)` → `Nat(n)` and `Nat.succ e` → `e`.
  fn nat_succ_of(&self, e: &KExpr<M>) -> Option<KExpr<M>> {
    match e.data() {
      ExprData::Nat(v, _, _) => {
        if v.0 == num_bigint::BigUint::ZERO {
          return None;
        }
        let pred = lean_ffi::nat::Nat(&v.0 - num_bigint::BigUint::from(1u64));
        let pred_addr = crate::ix::address::Address::hash(&pred.to_le_bytes());
        Some(self.ienv.intern_expr(KExpr::nat(pred, pred_addr)))
      },
      ExprData::App(f, arg, _) => match f.data() {
        ExprData::Const(id, _, _) if id.addr == self.prims.nat_succ.addr => {
          Some(arg.clone())
        },
        _ => None,
      },
      _ => None,
    }
  }

  /// Def-eq for nat-like values: handles mixed literal/constructor comparison.
  /// Fast-path: two Nat literals are compared directly by value (O(1) instead of
  /// O(n) recursion depth that would blow the def_eq_depth limit).
  fn is_def_eq_nat(
    &mut self,
    a: &KExpr<M>,
    b: &KExpr<M>,
  ) -> Result<bool, TcError<M>> {
    // Fast path: both literals — compare by value directly
    if let (ExprData::Nat(va, _, _), ExprData::Nat(vb, _, _)) =
      (a.data(), b.data())
    {
      return Ok(va == vb);
    }
    if self.is_nat_zero(a) && self.is_nat_zero(b) {
      return Ok(true);
    }
    match (self.nat_succ_of(a), self.nat_succ_of(b)) {
      (Some(a_pred), Some(b_pred)) => self.is_def_eq(&a_pred, &b_pred),
      _ => Ok(false),
    }
  }

  /// M2: Nat offset reduction for lazy delta loop (lean4lean isDefEqOffset).
  /// Returns Some(true/false) if both are nat-zero or nat-succ, None otherwise.
  fn try_def_eq_offset(
    &mut self,
    a: &KExpr<M>,
    b: &KExpr<M>,
  ) -> Result<Option<bool>, TcError<M>> {
    // Fast path: both literals — compare by value directly
    if let (ExprData::Nat(va, _, _), ExprData::Nat(vb, _, _)) =
      (a.data(), b.data())
    {
      return Ok(Some(va == vb));
    }
    if self.is_nat_zero(a) && self.is_nat_zero(b) {
      return Ok(Some(true));
    }
    match (self.nat_succ_of(a), self.nat_succ_of(b)) {
      (Some(a_pred), Some(b_pred)) => {
        Ok(Some(self.is_def_eq(&a_pred, &b_pred)?))
      },
      _ => Ok(None),
    }
  }

  // -----------------------------------------------------------------------
  // String literal expansion
  // -----------------------------------------------------------------------

  /// String literal expansion (C++ kernel: try_string_lit_expansion_core).
  ///
  /// When `t` is a string literal, expand it to constructor form via
  /// `str_lit_to_constructor` (String.ofList [Char.ofNat c₁, ...]), WHNF the
  /// result so String.ofList + Char.ofNat delta-unfold to the canonical
  /// `String.ofByteArray ...` form, then compare with `s`.
  fn try_string_lit_expansion(
    &mut self,
    t: &KExpr<M>,
    s: &KExpr<M>,
  ) -> Result<bool, TcError<M>> {
    let str_val = match t.data() {
      ExprData::Str(v, _, _) => v.clone(),
      _ => return Ok(false),
    };
    let expanded = self.str_lit_to_constructor(&str_val);
    self.is_def_eq(&expanded, s)
  }

  /// Convert a string literal to constructor form:
  /// `"abc"` → `String.ofList (List.cons (Char.ofNat 97) (List.cons (Char.ofNat 98) (... List.nil)))`
  ///
  /// Uses `Char.ofNat` (not `Char.mk`) matching lean4lean/C++ kernel.
  /// Uses `String.ofList` (= `String.mk` in our env) matching lean4lean/C++ kernel.
  pub(super) fn str_lit_to_constructor(&mut self, s: &str) -> KExpr<M> {
    let char_const =
      self.intern(KExpr::cnst(self.prims.char_type.clone(), Box::new([])));
    let char_of_nat =
      self.intern(KExpr::cnst(self.prims.char_of_nat.clone(), Box::new([])));
    let string_mk =
      self.intern(KExpr::cnst(self.prims.string_of_list.clone(), Box::new([])));

    // List.nil.{0} Char
    let list_nil_z = self.intern(KExpr::cnst(
      self.prims.list_nil.clone(),
      Box::new([KUniv::zero()]),
    ));
    let nil = self.intern(KExpr::app(list_nil_z, char_const.clone()));

    // List.cons.{0} Char
    let list_cons_z = self.intern(KExpr::cnst(
      self.prims.list_cons.clone(),
      Box::new([KUniv::zero()]),
    ));
    let cons = self.intern(KExpr::app(list_cons_z, char_const));

    // Build list right-to-left: foldr
    let mut list = nil;
    for c in s.chars().rev() {
      let nat_val = lean_ffi::nat::Nat::from(c as u64);
      let nat_addr = crate::ix::address::Address::hash(&nat_val.to_le_bytes());
      let nat_lit = self.intern(KExpr::nat(nat_val, nat_addr));
      let char_val = self.intern(KExpr::app(char_of_nat.clone(), nat_lit));
      let partial = self.intern(KExpr::app(cons.clone(), char_val));
      list = self.intern(KExpr::app(partial, list));
    }

    // String.mk list
    self.intern(KExpr::app(string_mk, list))
  }

  // -----------------------------------------------------------------------
  // Eta expansion
  // -----------------------------------------------------------------------

  /// Lambda eta expansion (lean4lean style): if `t` is a lambda and `s` is not,
  /// infer `s`'s type, WHNF to get a forall, wrap `s` as `λ(ty). s #0`, compare with `t`.
  fn try_eta_expansion(
    &mut self,
    t: &KExpr<M>,
    s: &KExpr<M>,
  ) -> Result<bool, TcError<M>> {
    if !matches!(t.data(), ExprData::Lam(..))
      || matches!(s.data(), ExprData::Lam(..))
    {
      return Ok(false);
    }
    // Infer s's type, WHNF to forall to get the binder type
    let s_ty = match self.with_infer_only(|tc| tc.infer(s)) {
      Ok(ty) => ty,
      Err(_) => return Ok(false),
    };
    let s_ty_whnf = match self.whnf(&s_ty) {
      Ok(w) => w,
      Err(_) => return Ok(false),
    };
    let (name, bi, ty) = match s_ty_whnf.data() {
      ExprData::All(name, bi, ty, _, _) => {
        (name.clone(), bi.clone(), ty.clone())
      },
      _ => return Ok(false),
    };
    // Wrap s as λ(ty). s #0
    let s_lifted = lift(&self.ienv, s, 1, 0);
    let v0 =
      self.intern(KExpr::var(0, M::meta_field(crate::ix::env::Name::anon())));
    let body = self.intern(KExpr::app(s_lifted, v0));
    let s_lam = self.intern(KExpr::lam(name, bi, ty, body));
    self.is_def_eq(t, &s_lam)
  }

  /// Struct eta (lean4lean style): if `s` is a fully-applied constructor of a
  /// struct-like type, check `proj(i, t) ≡ s.args[params+i]` for each field.
  /// Tries `tryEtaStructCore(t, s)` — caller should try both directions.
  fn try_eta_struct(
    &mut self,
    t: &KExpr<M>,
    s: &KExpr<M>,
  ) -> Result<bool, TcError<M>> {
    use super::tc::collect_app_spine;

    // s must be a constructor application
    let (s_head, s_args) = collect_app_spine(s);
    let ctor_id = match s_head.data() {
      ExprData::Const(id, _, _) => id.clone(),
      _ => return Ok(false),
    };

    // Head must be a constructor
    let (induct_id, num_params, num_fields) = match self.env.get(&ctor_id) {
      Some(KConst::Ctor { induct, params, fields, .. }) => {
        (induct.clone(), u64_to_usize::<M>(params)?, u64_to_usize::<M>(fields)?)
      },
      _ => return Ok(false),
    };

    // Must be fully applied
    if s_args.len() != num_params + num_fields {
      return Ok(false);
    }

    // Inductive must be struct-like (non-recursive, 0 indices, 1 ctor)
    match self.env.get(&induct_id) {
      Some(KConst::Indc { is_rec, indices, ctors, .. }) => {
        if is_rec || indices != 0 || ctors.len() != 1 {
          return Ok(false);
        }
      },
      _ => return Ok(false),
    }

    // Types must be def-eq (lean4lean tryEtaStructCore, line 515).
    // No Prop guard here — struct eta in def-eq is safe even for Prop types
    // because we're checking equality, not constructing terms. The Prop guard
    // is only needed in iota's toCtorWhenStruct (whnf.rs try_struct_eta_iota)
    // where eta-expanding creates projections that would be unsound for Prop.
    let s_ty = match self.with_infer_only(|tc| tc.infer(s)) {
      Ok(ty) => ty,
      Err(_) => return Ok(false),
    };
    let t_ty = match self.with_infer_only(|tc| tc.infer(t)) {
      Ok(ty) => ty,
      Err(_) => return Ok(false),
    };
    if !self.is_def_eq(&t_ty, &s_ty)? {
      return Ok(false);
    }

    // Compare each field: proj(induct, i, t) ≡ s_args[params + i]
    for i in 0..num_fields {
      let proj =
        self.intern(KExpr::prj(induct_id.clone(), i as u64, t.clone()));
      if !self.is_def_eq(&proj, &s_args[num_params + i])? {
        return Ok(false);
      }
    }

    Ok(true)
  }

  /// App spine comparison (lean4lean isDefEqApp): decompose both sides into
  /// head + args and compare componentwise. Handles multi-arg apps.
  fn try_def_eq_app(
    &mut self,
    a: &KExpr<M>,
    b: &KExpr<M>,
  ) -> Result<bool, TcError<M>> {
    if !matches!(a.data(), ExprData::App(..))
      || !matches!(b.data(), ExprData::App(..))
    {
      return Ok(false);
    }
    let (a_head, a_args) = collect_app_spine(a);
    let (b_head, b_args) = collect_app_spine(b);
    if a_args.len() != b_args.len() {
      return Ok(false);
    }
    if !self.is_def_eq(&a_head, &b_head)? {
      return Ok(false);
    }
    for (ai, bi) in a_args.iter().zip(b_args.iter()) {
      if !self.is_def_eq(ai, bi)? {
        return Ok(false);
      }
    }
    Ok(true)
  }

  /// Check if expression is the Bool.true constant.
  fn is_bool_true(&self, e: &KExpr<M>) -> bool {
    match e.data() {
      ExprData::Const(id, us, _) => {
        us.is_empty() && id.addr == self.prims.bool_true.addr
      },
      _ => false,
    }
  }

  /// Check if a constant is delta-reducible (definitions only, not theorems or opaques).
  fn is_delta(&self, id: &KId<M>) -> bool {
    matches!(
      self.env.get(id),
      Some(KConst::Defn { kind, .. }) if kind == DefKind::Definition
    )
  }

  /// Check if a constant has Regular reducibility hints (not Abbrev or Opaque).
  /// Used to guard the same-head-spine optimization (lean4lean: dt.hints.isRegular).
  fn is_regular(&self, id: &KId<M>) -> bool {
    use crate::ix::env::ReducibilityHints;
    matches!(
      self.env.get(id),
      Some(KConst::Defn { hints: ReducibilityHints::Regular(_), .. })
    )
  }

  /// Reducibility weight by id. Higher weight = unfold first.
  fn def_weight_id(&self, id: &KId<M>) -> u32 {
    use crate::ix::env::ReducibilityHints;
    match self.env.get(id) {
      Some(KConst::Defn { kind, hints, .. }) => match kind {
        DefKind::Opaque | DefKind::Theorem => 0,
        DefKind::Definition => match hints {
          ReducibilityHints::Abbrev => u32::MAX - 1,
          ReducibilityHints::Regular(h) => h.saturating_add(1),
          ReducibilityHints::Opaque => 0,
        },
      },
      _ => 0,
    }
  }

  // -----------------------------------------------------------------------
  // Post-delta congruence and projection unfolding (C5, C6)
  // -----------------------------------------------------------------------

  /// Structural congruence after lazy delta exhaustion (lean4lean isDefEqConst/Proj).
  /// Checks Const-Const, Var-Var, Prj-Prj without further reduction.
  fn try_structural_congruence(
    &mut self,
    a: &KExpr<M>,
    b: &KExpr<M>,
  ) -> Result<bool, TcError<M>> {
    match (a.data(), b.data()) {
      (ExprData::Const(id1, us1, _), ExprData::Const(id2, us2, _)) => Ok(
        id1.addr == id2.addr
          && us1.len() == us2.len()
          && us1.iter().zip(us2.iter()).all(|(u, v)| univ_eq(u, v)),
      ),
      (ExprData::Var(i, _, _), ExprData::Var(j, _, _)) => Ok(i == j),
      (ExprData::Prj(id1, f1, v1, _), ExprData::Prj(id2, f2, v2, _)) => {
        Ok(id1.addr == id2.addr && f1 == f2 && self.is_def_eq(v1, v2)?)
      },
      _ => Ok(false),
    }
  }

  /// If the head of `e` is a projection, try reducing it via whnf_no_delta.
  /// Returns the reduced form if it changed, None otherwise (lean4lean tryUnfoldProjApp).
  fn try_unfold_proj_app(
    &mut self,
    e: &KExpr<M>,
  ) -> Result<Option<KExpr<M>>, TcError<M>> {
    let (head, _) = collect_app_spine(e);
    if !matches!(head.data(), ExprData::Prj(..)) {
      return Ok(None);
    }
    let reduced = self.whnf_no_delta(e)?;
    if reduced.ptr_eq(e) { Ok(None) } else { Ok(Some(reduced)) }
  }
}

/// Canonical ordering for failure cache key: (min, max).
fn canonical_pair(a: usize, b: usize) -> (usize, usize) {
  if a <= b { (a, b) } else { (b, a) }
}

/// Extract head constant KId from expression or app spine.
fn head_const_id<M: KernelMode>(e: &KExpr<M>) -> Option<KId<M>> {
  match e.data() {
    ExprData::Const(id, _, _) => Some(id.clone()),
    ExprData::App(..) => {
      let (head, _) = collect_app_spine(e);
      match head.data() {
        ExprData::Const(id, _, _) => Some(id.clone()),
        _ => None,
      }
    },
    _ => None,
  }
}

#[cfg(test)]
mod tests {
  use super::super::constant::KConst;
  use super::super::env::{InternTable, KEnv};
  use super::super::expr::KExpr;
  use super::super::id::KId;
  use super::super::level::KUniv;
  use super::super::mode::Anon;
  use super::super::tc::TypeChecker;
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

  fn env_with_id() -> KEnv<Anon> {
    let env = KEnv::new();
    let id_ty = AE::all((), (), sort0(), sort0());
    let id_val = AE::lam((), (), sort0(), AE::var(0, ()));
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
    env
  }

  #[test]
  fn def_eq_ptr_eq() {
    let env = env_with_id();
    let mut tc = TypeChecker::new(&env, InternTable::new());
    let e = sort0();
    assert!(tc.is_def_eq(&e, &e).unwrap());
  }

  #[test]
  fn def_eq_sort_same() {
    let env = env_with_id();
    let mut tc = TypeChecker::new(&env, InternTable::new());
    let s1 = AE::sort(AU::zero());
    let s2 = AE::sort(AU::zero());
    assert!(tc.is_def_eq(&s1, &s2).unwrap());
  }

  #[test]
  fn def_eq_sort_diff() {
    let env = env_with_id();
    let mut tc = TypeChecker::new(&env, InternTable::new());
    let s0 = AE::sort(AU::zero());
    let s1 = AE::sort(AU::succ(AU::zero()));
    assert!(!tc.is_def_eq(&s0, &s1).unwrap());
  }

  #[test]
  fn def_eq_const_same() {
    let env = env_with_id();
    let mut tc = TypeChecker::new(&env, InternTable::new());
    let c1 = AE::cnst(mk_id("id"), Box::new([]));
    let c2 = AE::cnst(mk_id("id"), Box::new([]));
    assert!(tc.is_def_eq(&c1, &c2).unwrap());
  }

  #[test]
  fn def_eq_const_diff_addr() {
    let env = env_with_id();
    let mut tc = TypeChecker::new(&env, InternTable::new());
    let c1 = AE::cnst(mk_id("a"), Box::new([]));
    let c2 = AE::cnst(mk_id("b"), Box::new([]));
    assert!(!tc.is_def_eq(&c1, &c2).unwrap());
  }

  #[test]
  fn def_eq_lam_structural() {
    let env = env_with_id();
    let mut tc = TypeChecker::new(&env, InternTable::new());
    let l1 = AE::lam((), (), sort0(), AE::var(0, ()));
    let l2 = AE::lam((), (), sort0(), AE::var(0, ()));
    assert!(tc.is_def_eq(&l1, &l2).unwrap());
  }

  #[test]
  fn def_eq_all_structural() {
    let env = env_with_id();
    let mut tc = TypeChecker::new(&env, InternTable::new());
    let a1 = AE::all((), (), sort0(), sort0());
    let a2 = AE::all((), (), sort0(), sort0());
    assert!(tc.is_def_eq(&a1, &a2).unwrap());
  }

  #[test]
  fn def_eq_beta() {
    let env = env_with_id();
    let mut tc = TypeChecker::new(&env, InternTable::new());
    // (λ x. x)(Sort 0) ≡ Sort 0
    let lam = AE::lam((), (), sort0(), AE::var(0, ()));
    let app = AE::app(lam, sort0());
    assert!(tc.is_def_eq(&app, &sort0()).unwrap());
  }

  #[test]
  fn def_eq_delta_unfold() {
    let env = env_with_id();
    let mut tc = TypeChecker::new(&env, InternTable::new());
    // id(Sort 0) ≡ Sort 0 (via delta + beta)
    let id_app = AE::app(AE::cnst(mk_id("id"), Box::new([])), sort0());
    assert!(tc.is_def_eq(&id_app, &sort0()).unwrap());
  }

  #[test]
  fn def_eq_cache_hit() {
    let env = env_with_id();
    let mut tc = TypeChecker::new(&env, InternTable::new());
    let a = sort0();
    let b = AE::sort(AU::zero());
    assert!(tc.is_def_eq(&a, &b).unwrap());
    // Second call should hit cache
    assert!(tc.is_def_eq(&a, &b).unwrap());
  }
}
