//! Definitional equality checking.
//!
//! Implements the full isDefEq algorithm with caching, lazy delta unfolding,
//! proof irrelevance, eta expansion, struct eta, and unit-like types.

use num_bigint::BigUint;

use crate::ix::address::Address;
use crate::ix::env::{Literal, Name, ReducibilityHints};
use crate::lean::nat::Nat;

use super::error::TcError;
use super::helpers::*;
use super::level::equal_level;
use super::tc::{TcResult, TypeChecker};
use super::types::{KConstantInfo, MetaMode};
use super::value::*;

/// Maximum iterations for lazy delta unfolding.
const MAX_LAZY_DELTA_ITERS: usize = 10_000;
/// Maximum spine size for recursive structural equiv registration.
const MAX_EQUIV_SPINE: usize = 8;

impl<M: MetaMode> TypeChecker<'_, M> {
  /// Quick structural pre-check (pure, O(1)). Returns `Some(true/false)` if
  /// the result can be determined without further work, `None` otherwise.
  fn quick_is_def_eq_val(t: &Val<M>, s: &Val<M>) -> Option<bool> {
    // Pointer equality
    if t.ptr_eq(s) {
      return Some(true);
    }

    match (t.inner(), s.inner()) {
      // Sort equality
      (ValInner::Sort(a), ValInner::Sort(b)) => {
        Some(equal_level(a, b))
      }
      // Literal equality
      (ValInner::Lit(a), ValInner::Lit(b)) => Some(a == b),
      // Same-head const with empty spines
      (
        ValInner::Neutral {
          head: Head::Const { addr: a1, levels: l1, .. },
          spine: s1,
        },
        ValInner::Neutral {
          head: Head::Const { addr: a2, levels: l2, .. },
          spine: s2,
        },
      ) if a1 == a2 && s1.is_empty() && s2.is_empty() => {
        if l1.len() != l2.len() {
          return Some(false);
        }
        Some(
          l1.iter()
            .zip(l2.iter())
            .all(|(a, b)| equal_level(a, b)),
        )
      }
      _ => None,
    }
  }

  /// Top-level definitional equality check.
  pub fn is_def_eq(&mut self, t: &Val<M>, s: &Val<M>) -> TcResult<bool, M> {
    self.heartbeat()?;
    self.stats.def_eq_calls += 1;

    // 1. Quick structural check
    if let Some(result) = Self::quick_is_def_eq_val(t, s) {
      return Ok(result);
    }

    // 2. EquivManager check
    if self.equiv_manager.is_equiv(t.ptr_id(), s.ptr_id()) {
      return Ok(true);
    }

    // 3. Pointer-keyed caches
    let key = (t.ptr_id(), s.ptr_id());
    let key_rev = (s.ptr_id(), t.ptr_id());

    if let Some((ct, cs)) = self.ptr_success_cache.get(&key) {
      if ct.ptr_eq(t) && cs.ptr_eq(s) {
        return Ok(true);
      }
    }
    if let Some((ct, cs)) = self.ptr_success_cache.get(&key_rev) {
      if ct.ptr_eq(s) && cs.ptr_eq(t) {
        return Ok(true);
      }
    }
    if let Some((ct, cs)) = self.ptr_failure_cache.get(&key) {
      if ct.ptr_eq(t) && cs.ptr_eq(s) {
        return Ok(false);
      }
    }
    if let Some((ct, cs)) = self.ptr_failure_cache.get(&key_rev) {
      if ct.ptr_eq(s) && cs.ptr_eq(t) {
        return Ok(false);
      }
    }

    // 4. Bool.true reflection
    if let Some(true_addr) = &self.prims.bool_true {
      if t.const_addr() == Some(true_addr)
        && t.spine().map_or(false, |s| s.is_empty())
      {
        let s_whnf = self.whnf_val(s, 0)?;
        if s_whnf.const_addr() == Some(true_addr) {
          return Ok(true);
        }
      }
      if s.const_addr() == Some(true_addr)
        && s.spine().map_or(false, |s| s.is_empty())
      {
        let t_whnf = self.whnf_val(t, 0)?;
        if t_whnf.const_addr() == Some(true_addr) {
          return Ok(true);
        }
      }
    }

    // 5. whnf_core_val with cheap_proj
    let t1 = self.whnf_core_val(t, false, true)?;
    let s1 = self.whnf_core_val(s, false, true)?;

    // 6. Quick check after whnfCore
    if let Some(result) = Self::quick_is_def_eq_val(&t1, &s1) {
      if result {
        self.structural_add_equiv(&t1, &s1);
      }
      return Ok(result);
    }

    // 7. Proof irrelevance (best-effort: skip if type inference fails)
    match self.is_def_eq_proof_irrel(&t1, &s1) {
      Ok(Some(result)) => return Ok(result),
      Ok(None) => {}
      Err(_) => {} // type inference failed, skip proof irrelevance
    }

    // 8. Lazy delta
    let (t2, s2, delta_result) = self.lazy_delta(&t1, &s1)?;
    if let Some(result) = delta_result {
      if result {
        self.equiv_manager.add_equiv(t.ptr_id(), s.ptr_id());
      }
      return Ok(result);
    }

    // 9. Quick check after delta
    if let Some(result) = Self::quick_is_def_eq_val(&t2, &s2) {
      if result {
        self.structural_add_equiv(&t2, &s2);
        self.equiv_manager.add_equiv(t.ptr_id(), s.ptr_id());
      }
      return Ok(result);
    }

    // 10. Full WHNF (includes delta, native, nat prim reduction)
    let t3 = self.whnf_val(&t2, 0)?;
    let s3 = self.whnf_val(&s2, 0)?;

    // 11. Structural comparison
    let result = self.is_def_eq_core(&t3, &s3)?;

    // 12. Cache result
    if result {
      self.equiv_manager.add_equiv(t.ptr_id(), s.ptr_id());
      self.structural_add_equiv(&t3, &s3);
      self.ptr_success_cache.insert(key, (t.clone(), s.clone()));
    } else {
      self.ptr_failure_cache.insert(key, (t.clone(), s.clone()));
    }

    Ok(result)
  }

  /// Structural comparison of two values in WHNF.
  pub fn is_def_eq_core(
    &mut self,
    t: &Val<M>,
    s: &Val<M>,
  ) -> TcResult<bool, M> {
    match (t.inner(), s.inner()) {
      // Sort
      (ValInner::Sort(a), ValInner::Sort(b)) => {
        Ok(equal_level(a, b))
      }

      // Literal
      (ValInner::Lit(a), ValInner::Lit(b)) => Ok(a == b),

      // Neutral (fvar)
      (
        ValInner::Neutral {
          head: Head::FVar { level: l1, .. },
          spine: sp1,
        },
        ValInner::Neutral {
          head: Head::FVar { level: l2, .. },
          spine: sp2,
        },
      ) => {
        if l1 != l2 {
          return Ok(false);
        }
        self.is_def_eq_spine(sp1, sp2)
      }

      // Neutral (const)
      (
        ValInner::Neutral {
          head: Head::Const { addr: a1, levels: l1, .. },
          spine: sp1,
        },
        ValInner::Neutral {
          head: Head::Const { addr: a2, levels: l2, .. },
          spine: sp2,
        },
      ) => {
        if a1 != a2
          || l1.len() != l2.len()
          || !l1.iter().zip(l2.iter()).all(|(a, b)| equal_level(a, b))
        {
          return Ok(false);
        }
        self.is_def_eq_spine(sp1, sp2)
      }

      // Constructor
      (
        ValInner::Ctor {
          addr: a1,
          levels: l1,
          spine: sp1,
          ..
        },
        ValInner::Ctor {
          addr: a2,
          levels: l2,
          spine: sp2,
          ..
        },
      ) => {
        if a1 != a2
          || l1.len() != l2.len()
          || !l1.iter().zip(l2.iter()).all(|(a, b)| equal_level(a, b))
        {
          return Ok(false);
        }
        self.is_def_eq_spine(sp1, sp2)
      }

      // Lambda: compare domains, bodies under shared fvar
      (
        ValInner::Lam {
          dom: d1,
          body: b1,
          env: e1,
          ..
        },
        ValInner::Lam {
          dom: d2,
          body: b2,
          env: e2,
          ..
        },
      ) => {
        if !self.is_def_eq(d1, d2)? {
          return Ok(false);
        }
        let fvar = Val::mk_fvar(self.depth(), d1.clone());
        let mut env1 = e1.clone();
        env1.push(fvar.clone());
        let mut env2 = e2.clone();
        env2.push(fvar);
        let v1 = self.eval(b1, &env1)?;
        let v2 = self.eval(b2, &env2)?;
        self.with_binder(d1.clone(), M::Field::<Name>::default(), |tc| {
          tc.is_def_eq(&v1, &v2)
        })
      }

      // Pi: compare domains, bodies under shared fvar
      (
        ValInner::Pi {
          dom: d1,
          body: b1,
          env: e1,
          ..
        },
        ValInner::Pi {
          dom: d2,
          body: b2,
          env: e2,
          ..
        },
      ) => {
        if !self.is_def_eq(d1, d2)? {
          return Ok(false);
        }
        let fvar = Val::mk_fvar(self.depth(), d1.clone());
        let mut env1 = e1.clone();
        env1.push(fvar.clone());
        let mut env2 = e2.clone();
        env2.push(fvar);
        let v1 = self.eval(b1, &env1)?;
        let v2 = self.eval(b2, &env2)?;
        self.with_binder(d1.clone(), M::Field::<Name>::default(), |tc| {
          tc.is_def_eq(&v1, &v2)
        })
      }

      // Eta: lambda vs non-lambda
      (ValInner::Lam { dom, body, env, .. }, _) => {
        let fvar = Val::mk_fvar(self.depth(), dom.clone());
        let mut new_env = env.clone();
        new_env.push(fvar.clone());
        let lhs = self.eval(body, &new_env)?;
        let rhs_thunk = mk_thunk_val(fvar);
        let rhs = self.apply_val_thunk(s.clone(), rhs_thunk)?;
        self.with_binder(dom.clone(), M::Field::<Name>::default(), |tc| {
          tc.is_def_eq(&lhs, &rhs)
        })
      }
      (_, ValInner::Lam { dom, body, env, .. }) => {
        let fvar = Val::mk_fvar(self.depth(), dom.clone());
        let mut new_env = env.clone();
        new_env.push(fvar.clone());
        let rhs = self.eval(body, &new_env)?;
        let lhs_thunk = mk_thunk_val(fvar);
        let lhs = self.apply_val_thunk(t.clone(), lhs_thunk)?;
        self.with_binder(dom.clone(), M::Field::<Name>::default(), |tc| {
          tc.is_def_eq(&lhs, &rhs)
        })
      }

      // Projection
      (
        ValInner::Proj {
          type_addr: a1,
          idx: i1,
          strct: s1,
          spine: sp1,
          ..
        },
        ValInner::Proj {
          type_addr: a2,
          idx: i2,
          strct: s2,
          spine: sp2,
          ..
        },
      ) => {
        if a1 != a2 || i1 != i2 {
          return Ok(false);
        }
        let sv1 = self.force_thunk(s1)?;
        let sv2 = self.force_thunk(s2)?;
        if !self.is_def_eq(&sv1, &sv2)? {
          return Ok(false);
        }
        self.is_def_eq_spine(sp1, sp2)
      }

      // Nat literal ↔ constructor: direct O(1) comparison
      (
        ValInner::Lit(Literal::NatVal(n)),
        ValInner::Ctor { addr, num_params, spine: ctor_spine, .. },
      ) => {
        if n.0 == BigUint::ZERO {
          Ok(self.prims.nat_zero.as_ref() == Some(addr) && ctor_spine.len() == *num_params)
        } else {
          if self.prims.nat_succ.as_ref() != Some(addr) { return Ok(false); }
          if ctor_spine.len() != num_params + 1 { return Ok(false); }
          let pred_val = self.force_thunk(&ctor_spine[*num_params])?;
          let pred_lit = Val::mk_lit(Literal::NatVal(Nat(&n.0 - 1u64)));
          self.is_def_eq(&pred_lit, &pred_val)
        }
      }
      (
        ValInner::Ctor { addr, num_params, spine: ctor_spine, .. },
        ValInner::Lit(Literal::NatVal(n)),
      ) => {
        if n.0 == BigUint::ZERO {
          Ok(self.prims.nat_zero.as_ref() == Some(addr) && ctor_spine.len() == *num_params)
        } else {
          if self.prims.nat_succ.as_ref() != Some(addr) { return Ok(false); }
          if ctor_spine.len() != num_params + 1 { return Ok(false); }
          let pred_val = self.force_thunk(&ctor_spine[*num_params])?;
          let pred_lit = Val::mk_lit(Literal::NatVal(Nat(&n.0 - 1u64)));
          self.is_def_eq(&pred_val, &pred_lit)
        }
      }
      // Nat literal ↔ neutral succ: handle Lit(n+1) vs neutral(Nat.succ, [thunk])
      (
        ValInner::Lit(Literal::NatVal(n)),
        ValInner::Neutral { head: Head::Const { addr, .. }, spine: sp },
      ) => {
        if n.0 == BigUint::ZERO {
          Ok(self.prims.nat_zero.as_ref() == Some(addr) && sp.is_empty())
        } else if self.prims.nat_succ.as_ref() == Some(addr) && sp.len() == 1 {
          let pred_val = self.force_thunk(&sp[0])?;
          let pred_lit = Val::mk_lit(Literal::NatVal(Nat(&n.0 - 1u64)));
          self.is_def_eq(&pred_lit, &pred_val)
        } else {
          // Fallback: convert literal to ctor for other neutral heads
          let t2 = self.nat_lit_to_ctor_thunked(t)?;
          self.is_def_eq_core(&t2, s)
        }
      }
      (
        ValInner::Neutral { head: Head::Const { addr, .. }, spine: sp },
        ValInner::Lit(Literal::NatVal(n)),
      ) => {
        if n.0 == BigUint::ZERO {
          Ok(self.prims.nat_zero.as_ref() == Some(addr) && sp.is_empty())
        } else if self.prims.nat_succ.as_ref() == Some(addr) && sp.len() == 1 {
          let pred_val = self.force_thunk(&sp[0])?;
          let pred_lit = Val::mk_lit(Literal::NatVal(Nat(&n.0 - 1u64)));
          self.is_def_eq(&pred_val, &pred_lit)
        } else {
          let s2 = self.nat_lit_to_ctor_thunked(s)?;
          self.is_def_eq_core(t, &s2)
        }
      }
      // Nat literal ↔ other: fallback to ctor conversion
      (ValInner::Lit(Literal::NatVal(_)), _) => {
        let t2 = self.nat_lit_to_ctor_thunked(t)?;
        self.is_def_eq_core(&t2, s)
      }
      (_, ValInner::Lit(Literal::NatVal(_))) => {
        let s2 = self.nat_lit_to_ctor_thunked(s)?;
        self.is_def_eq_core(t, &s2)
      }

      // String literal expansion (compare after expanding to ctor form)
      (ValInner::Lit(Literal::StrVal(_)), _) => {
        match self.str_lit_to_ctor_val(t) {
          Ok(expanded) => self.is_def_eq(&expanded, s),
          Err(_) => Ok(false),
        }
      }
      (_, ValInner::Lit(Literal::StrVal(_))) => {
        match self.str_lit_to_ctor_val(s) {
          Ok(expanded) => self.is_def_eq(t, &expanded),
          Err(_) => Ok(false),
        }
      }

      // Struct eta fallback
      _ => {
        // Try struct eta
        if self.try_eta_struct_val(t, s)? {
          return Ok(true);
        }
        // Try unit-like
        if self.is_def_eq_unit_like_val(t, s)? {
          return Ok(true);
        }
        Ok(false)
      }
    }
  }

  /// Compare two spines element by element.
  pub fn is_def_eq_spine(
    &mut self,
    sp1: &[Thunk<M>],
    sp2: &[Thunk<M>],
  ) -> TcResult<bool, M> {
    if sp1.len() != sp2.len() {
      return Ok(false);
    }
    for (t1, t2) in sp1.iter().zip(sp2.iter()) {
      // Thunk pointer short-circuit: identical thunks are trivially equal
      if std::rc::Rc::ptr_eq(t1, t2) {
        continue;
      }
      let v1 = self.force_thunk(t1)?;
      let v2 = self.force_thunk(t2)?;
      if !self.is_def_eq(&v1, &v2)? {
        return Ok(false);
      }
    }
    Ok(true)
  }

  /// Lazy delta: hint-guided interleaved delta unfolding.
  pub fn lazy_delta(
    &mut self,
    t: &Val<M>,
    s: &Val<M>,
  ) -> TcResult<(Val<M>, Val<M>, Option<bool>), M> {
    let mut t = t.clone();
    let mut s = s.clone();

    for _ in 0..MAX_LAZY_DELTA_ITERS {
      let t_hints = get_delta_info(&t, self.env);
      let s_hints = get_delta_info(&s, self.env);

      // isDefEqOffset: short-circuit Nat.succ chain comparison
      if let Some(result) = self.is_def_eq_offset(&t, &s)? {
        return Ok((t.clone(), s.clone(), Some(result)));
      }

      // Nat prim reduction (before delta)
      if let Some(t2) = self.try_reduce_nat_val(&t)? {
        let result = self.is_def_eq(&t2, &s)?;
        return Ok((t2, s, Some(result)));
      }
      if let Some(s2) = self.try_reduce_nat_val(&s)? {
        let result = self.is_def_eq(&t, &s2)?;
        return Ok((t, s2, Some(result)));
      }

      // Native reduction (reduceBool/reduceNat markers)
      if let Some(t2) = self.reduce_native_val(&t)? {
        let result = self.is_def_eq(&t2, &s)?;
        return Ok((t2, s, Some(result)));
      }
      if let Some(s2) = self.reduce_native_val(&s)? {
        let result = self.is_def_eq(&t, &s2)?;
        return Ok((t, s2, Some(result)));
      }

      match (t_hints, s_hints) {
        (None, None) => return Ok((t, s, None)),

        (Some(_), None) => {
          if let Some(r) = self.delta_step_val(&t)? {
            t = self.whnf_core_val(&r, false, true)?;
          } else {
            return Ok((t, s, None));
          }
        }

        (None, Some(_)) => {
          if let Some(r) = self.delta_step_val(&s)? {
            s = self.whnf_core_val(&r, false, true)?;
          } else {
            return Ok((t, s, None));
          }
        }

        (Some(th), Some(sh)) => {
          let t_height = hint_height(&th);
          let s_height = hint_height(&sh);

          // Same-head optimization with failure cache guard
          if t.same_head_const(&s) && matches!(th, ReducibilityHints::Regular(_)) {
            if let (Some(l1), Some(l2)) =
              (t.head_levels(), s.head_levels())
            {
              if l1.len() == l2.len()
                && l1.iter().zip(l2.iter()).all(|(a, b)| equal_level(a, b))
              {
                // Check failure cache to avoid retrying
                let t_ptr = t.ptr_id();
                let s_ptr = s.ptr_id();
                let ptr_key = if t_ptr <= s_ptr {
                  (t_ptr, s_ptr)
                } else {
                  (s_ptr, t_ptr)
                };
                let skip = if let Some((ct, cs)) =
                  self.ptr_failure_cache.get(&ptr_key)
                {
                  (ct.ptr_eq(&t) && cs.ptr_eq(&s))
                    || (ct.ptr_eq(&s) && cs.ptr_eq(&t))
                } else {
                  false
                };

                if !skip {
                  if let (Some(sp1), Some(sp2)) = (t.spine(), s.spine()) {
                    if sp1.len() == sp2.len() {
                      if self.is_def_eq_spine(sp1, sp2)? {
                        return Ok((t, s, Some(true)));
                      } else {
                        // Record failure
                        self.ptr_failure_cache.insert(
                          ptr_key,
                          (t.clone(), s.clone()),
                        );
                      }
                    }
                  }
                }
              }
            }
          }

          // Unfold the higher-height one, apply whnf_core after delta
          if t_height > s_height {
            if let Some(r) = self.delta_step_val(&t)? {
              t = self.whnf_core_val(&r, false, true)?;
            } else if let Some(r) = self.delta_step_val(&s)? {
              s = self.whnf_core_val(&r, false, true)?;
            } else {
              return Ok((t, s, None));
            }
          } else if s_height > t_height {
            if let Some(r) = self.delta_step_val(&s)? {
              s = self.whnf_core_val(&r, false, true)?;
            } else if let Some(r) = self.delta_step_val(&t)? {
              t = self.whnf_core_val(&r, false, true)?;
            } else {
              return Ok((t, s, None));
            }
          } else {
            // Same height: unfold both
            let t2 = self.delta_step_val(&t)?;
            let s2 = self.delta_step_val(&s)?;
            match (t2, s2) {
              (Some(rt), Some(rs)) => {
                t = self.whnf_core_val(&rt, false, true)?;
                s = self.whnf_core_val(&rs, false, true)?;
              }
              (Some(rt), None) => {
                t = self.whnf_core_val(&rt, false, true)?;
              }
              (None, Some(rs)) => {
                s = self.whnf_core_val(&rs, false, true)?;
              }
              (None, None) => return Ok((t, s, None)),
            }
          }
        }
      }

      // Quick check
      if let Some(result) = Self::quick_is_def_eq_val(&t, &s) {
        return Ok((t, s, Some(result)));
      }
    }

    Err(TcError::KernelException {
      msg: "lazy delta iteration limit exceeded".to_string(),
    })
  }

  /// Recursively add sub-component equivalences after successful isDefEq.
  pub fn structural_add_equiv(&mut self, t: &Val<M>, s: &Val<M>) {
    self.equiv_manager.add_equiv(t.ptr_id(), s.ptr_id());

    // Recursively merge sub-components for matching structures
    match (t.inner(), s.inner()) {
      (
        ValInner::Neutral { spine: sp1, .. },
        ValInner::Neutral { spine: sp2, .. },
      )
      | (
        ValInner::Ctor { spine: sp1, .. },
        ValInner::Ctor { spine: sp2, .. },
      ) if sp1.len() == sp2.len() && sp1.len() < MAX_EQUIV_SPINE => {
        for (t1, t2) in sp1.iter().zip(sp2.iter()) {
          if let (Ok(v1), Ok(v2)) = (
            self.force_thunk_no_eval(t1),
            self.force_thunk_no_eval(t2),
          ) {
            self.equiv_manager.add_equiv(v1.ptr_id(), v2.ptr_id());
          }
        }
      }
      _ => {}
    }
  }

  /// Peek at a thunk without evaluating it (for structural_add_equiv).
  fn force_thunk_no_eval(
    &self,
    thunk: &Thunk<M>,
  ) -> Result<Val<M>, ()> {
    let entry = thunk.borrow();
    match &*entry {
      ThunkEntry::Evaluated(v) => Ok(v.clone()),
      _ => Err(()),
    }
  }

  /// Proof irrelevance: if both sides have Prop type, they're equal.
  fn is_def_eq_proof_irrel(
    &mut self,
    t: &Val<M>,
    s: &Val<M>,
  ) -> TcResult<Option<bool>, M> {
    // Infer types of both sides and check if they're in Prop
    let t_type = self.infer_type_of_val(t)?;
    let t_type_whnf = self.whnf_val(&t_type, 0)?;
    if !matches!(
      t_type_whnf.inner(),
      ValInner::Sort(l) if super::level::is_zero(l)
    ) {
      return Ok(None);
    }

    let s_type = self.infer_type_of_val(s)?;
    let s_type_whnf = self.whnf_val(&s_type, 0)?;
    if !matches!(
      s_type_whnf.inner(),
      ValInner::Sort(l) if super::level::is_zero(l)
    ) {
      return Ok(None);
    }

    // Both are proofs — check their types are equal
    Ok(Some(self.is_def_eq(&t_type, &s_type)?))
  }

  /// Convert a nat literal to constructor form with thunks.
  pub fn nat_lit_to_ctor_thunked(
    &mut self,
    v: &Val<M>,
  ) -> TcResult<Val<M>, M> {
    match v.inner() {
      ValInner::Lit(Literal::NatVal(n)) => {
        if n.0 == BigUint::ZERO {
          if let Some(zero_addr) = &self.prims.nat_zero {
            let nat_addr = self
              .prims
              .nat
              .as_ref()
              .ok_or_else(|| TcError::KernelException {
                msg: "Nat primitive not found".to_string(),
              })?;
            return Ok(Val::mk_ctor(
              zero_addr.clone(),
              Vec::new(),
              M::Field::<Name>::default(),
              0,
              0,
              0,
              nat_addr.clone(),
              Vec::new(),
            ));
          }
        }
        // Nat.succ (n-1)
        if let Some(succ_addr) = &self.prims.nat_succ {
          let nat_addr = self
            .prims
            .nat
            .as_ref()
            .ok_or_else(|| TcError::KernelException {
              msg: "Nat primitive not found".to_string(),
            })?;
          let pred = Val::mk_lit(Literal::NatVal(
            crate::lean::nat::Nat(&n.0 - 1u64),
          ));
          let pred_thunk = mk_thunk_val(pred);
          return Ok(Val::mk_ctor(
            succ_addr.clone(),
            Vec::new(),
            M::Field::<Name>::default(),
            1,
            0,
            1,
            nat_addr.clone(),
            vec![pred_thunk],
          ));
        }
        Ok(v.clone())
      }
      _ => Ok(v.clone()),
    }
  }

  /// Build a Val::mk_ctor for a constructor, looking up metadata from env.
  fn mk_ctor_val(
    &self,
    addr: &Address,
    levels: Vec<super::types::KLevel<M>>,
    spine: Vec<Thunk<M>>,
  ) -> Option<Val<M>> {
    if let Some(KConstantInfo::Constructor(cv)) = self.env.get(addr) {
      Some(Val::mk_ctor(
        addr.clone(),
        levels,
        M::Field::<Name>::default(),
        cv.cidx,
        cv.num_params,
        cv.num_fields,
        cv.induct.clone(),
        spine,
      ))
    } else {
      None
    }
  }

  /// Convert a string literal to its constructor form using proper Val::mk_ctor:
  /// `String.mk (List.cons Char (Char.mk c1) (List.cons ... (List.nil Char)))`.
  fn str_lit_to_ctor_val(&mut self, v: &Val<M>) -> TcResult<Val<M>, M> {
    match v.inner() {
      ValInner::Lit(Literal::StrVal(s)) => {
        use crate::lean::nat::Nat;
        let string_mk = self
          .prims
          .string_mk
          .as_ref()
          .ok_or_else(|| TcError::KernelException {
            msg: "String.mk not found".into(),
          })?
          .clone();
        let char_mk = self
          .prims
          .char_mk
          .as_ref()
          .ok_or_else(|| TcError::KernelException {
            msg: "Char.mk not found".into(),
          })?
          .clone();
        let list_nil = self
          .prims
          .list_nil
          .as_ref()
          .ok_or_else(|| TcError::KernelException {
            msg: "List.nil not found".into(),
          })?
          .clone();
        let list_cons = self
          .prims
          .list_cons
          .as_ref()
          .ok_or_else(|| TcError::KernelException {
            msg: "List.cons not found".into(),
          })?
          .clone();
        let char_type_addr = self
          .prims
          .char_type
          .as_ref()
          .ok_or_else(|| TcError::KernelException {
            msg: "Char type not found".into(),
          })?
          .clone();
        let zero = super::types::KLevel::zero();
        let char_type_val = Val::mk_const(
          char_type_addr,
          vec![],
          M::Field::<Name>::default(),
        );

        // Helper: build a ctor if env has metadata, else use neutral + apply
        let mk_ctor_or_apply = |tc: &mut Self,
                                 addr: &Address,
                                 levels: Vec<super::types::KLevel<M>>,
                                 args: Vec<Val<M>>|
         -> TcResult<Val<M>, M> {
          if let Some(v) = tc.mk_ctor_val(addr, levels.clone(), args.iter().map(|a| mk_thunk_val(a.clone())).collect()) {
            Ok(v)
          } else {
            let mut v = Val::mk_const(addr.clone(), levels, M::Field::<Name>::default());
            for arg in args {
              v = tc.apply_val_thunk(v, mk_thunk_val(arg))?;
            }
            Ok(v)
          }
        };

        // Build List.nil.{0} Char
        let mut list = mk_ctor_or_apply(
          self,
          &list_nil,
          vec![zero.clone()],
          vec![char_type_val.clone()],
        )?;

        for ch in s.chars().rev() {
          // Char.mk <code>
          let char_lit =
            Val::mk_lit(Literal::NatVal(Nat::from(ch as u64)));
          let char_applied = mk_ctor_or_apply(
            self,
            &char_mk,
            vec![],
            vec![char_lit],
          )?;

          // List.cons.{0} Char <char> <rest>
          list = mk_ctor_or_apply(
            self,
            &list_cons,
            vec![zero.clone()],
            vec![char_type_val.clone(), char_applied, list],
          )?;
        }

        // String.mk <list>
        let result = mk_ctor_or_apply(
          self,
          &string_mk,
          vec![],
          vec![list],
        )?;

        Ok(result)
      }
      _ => Ok(v.clone()),
    }
  }

  /// Try struct eta expansion for equality checking (both directions).
  fn try_eta_struct_val(
    &mut self,
    t: &Val<M>,
    s: &Val<M>,
  ) -> TcResult<bool, M> {
    if self.try_eta_struct_core(t, s)? {
      return Ok(true);
    }
    self.try_eta_struct_core(s, t)
  }

  /// Core struct eta: check if s is a ctor of a struct-like type,
  /// and t's projections match s's fields.
  fn try_eta_struct_core(
    &mut self,
    t: &Val<M>,
    s: &Val<M>,
  ) -> TcResult<bool, M> {
    match s.inner() {
      ValInner::Ctor {
        num_params,
        num_fields,
        induct_addr,
        spine,
        ..
      } => {
        if spine.len() != num_params + num_fields {
          return Ok(false);
        }
        if !is_struct_like_app(s, &self.typed_consts) {
          return Ok(false);
        }
        // Check types match
        let t_type = match self.infer_type_of_val(t) {
          Ok(ty) => ty,
          Err(_) => return Ok(false),
        };
        let s_type = match self.infer_type_of_val(s) {
          Ok(ty) => ty,
          Err(_) => return Ok(false),
        };
        if !self.is_def_eq(&t_type, &s_type)? {
          return Ok(false);
        }
        // Compare each field
        let t_thunk = mk_thunk_val(t.clone());
        for i in 0..*num_fields {
          let proj_val = Val::mk_proj(
            induct_addr.clone(),
            i,
            t_thunk.clone(),
            M::Field::<Name>::default(),
            Vec::new(),
          );
          let field_val = self.force_thunk(&spine[num_params + i])?;
          if !self.is_def_eq(&proj_val, &field_val)? {
            return Ok(false);
          }
        }
        Ok(true)
      }
      _ => Ok(false),
    }
  }

  /// Short-circuit Nat.succ chain / zero comparison.
  fn is_def_eq_offset(
    &mut self,
    t: &Val<M>,
    s: &Val<M>,
  ) -> TcResult<Option<bool>, M> {
    let is_zero = |v: &Val<M>, prims: &super::types::Primitives| -> bool {
      match v.inner() {
        ValInner::Lit(Literal::NatVal(n)) => n.0 == BigUint::ZERO,
        ValInner::Neutral {
          head: Head::Const { addr, .. },
          spine,
        } => prims.nat_zero.as_ref() == Some(addr) && spine.is_empty(),
        ValInner::Ctor { addr, spine, .. } => {
          prims.nat_zero.as_ref() == Some(addr) && spine.is_empty()
        }
        _ => false,
      }
    };

    if is_zero(t, self.prims) && is_zero(s, self.prims) {
      return Ok(Some(true));
    }

    let succ_of = |v: &Val<M>, tc: &mut Self| -> TcResult<Option<Val<M>>, M> {
      match v.inner() {
        ValInner::Lit(Literal::NatVal(n)) if n.0 > BigUint::ZERO => {
          Ok(Some(Val::mk_lit(Literal::NatVal(
            crate::lean::nat::Nat(&n.0 - 1u64),
          ))))
        }
        ValInner::Neutral {
          head: Head::Const { addr, .. },
          spine,
        } if tc.prims.nat_succ.as_ref() == Some(addr) && spine.len() == 1 => {
          Ok(Some(tc.force_thunk(&spine[0])?))
        }
        ValInner::Ctor { addr, spine, .. }
          if tc.prims.nat_succ.as_ref() == Some(addr) && spine.len() == 1 =>
        {
          Ok(Some(tc.force_thunk(&spine[0])?))
        }
        _ => Ok(None),
      }
    };

    // Thunk pointer short-circuit: if both are succ sharing the same thunk
    let t_succ_thunk = match t.inner() {
      ValInner::Neutral {
        head: Head::Const { addr, .. },
        spine,
      } if self.prims.nat_succ.as_ref() == Some(addr) && spine.len() == 1 => {
        Some(&spine[0])
      }
      ValInner::Ctor { addr, spine, .. }
        if self.prims.nat_succ.as_ref() == Some(addr) && spine.len() == 1 =>
      {
        Some(&spine[0])
      }
      _ => None,
    };
    let s_succ_thunk = match s.inner() {
      ValInner::Neutral {
        head: Head::Const { addr, .. },
        spine,
      } if self.prims.nat_succ.as_ref() == Some(addr) && spine.len() == 1 => {
        Some(&spine[0])
      }
      ValInner::Ctor { addr, spine, .. }
        if self.prims.nat_succ.as_ref() == Some(addr) && spine.len() == 1 =>
      {
        Some(&spine[0])
      }
      _ => None,
    };
    if let (Some(tt), Some(st)) = (t_succ_thunk, s_succ_thunk) {
      if std::rc::Rc::ptr_eq(tt, st) {
        return Ok(Some(true));
      }
      let tv = self.force_thunk(tt)?;
      let sv = self.force_thunk(st)?;
      return Ok(Some(self.is_def_eq(&tv, &sv)?));
    }

    // General case: peel matching succs
    let t2 = succ_of(t, self)?;
    let s2 = succ_of(s, self)?;
    match (t2, s2) {
      (Some(t2), Some(s2)) => Ok(Some(self.is_def_eq(&t2, &s2)?)),
      _ => Ok(None),
    }
  }

  /// Check unit-like type equality: single ctor, 0 fields, 0 indices, non-recursive.
  fn is_def_eq_unit_like_val(
    &mut self,
    t: &Val<M>,
    s: &Val<M>,
  ) -> TcResult<bool, M> {
    let t_type = match self.infer_type_of_val(t) {
      Ok(ty) => ty,
      Err(_) => return Ok(false),
    };
    let t_type_whnf = self.whnf_val(&t_type, 0)?;
    match t_type_whnf.inner() {
      ValInner::Neutral {
        head: Head::Const { addr, .. },
        ..
      } => {
        let ci = match self.env.get(addr) {
          Some(ci) => ci.clone(),
          None => return Ok(false),
        };
        match &ci {
          KConstantInfo::Inductive(iv) => {
            if iv.is_rec || iv.num_indices != 0 || iv.ctors.len() != 1 {
              return Ok(false);
            }
            match self.env.get(&iv.ctors[0]) {
              Some(KConstantInfo::Constructor(cv)) => {
                if cv.num_fields != 0 {
                  return Ok(false);
                }
                let s_type = match self.infer_type_of_val(s) {
                  Ok(ty) => ty,
                  Err(_) => return Ok(false),
                };
                self.is_def_eq(&t_type, &s_type)
              }
              _ => Ok(false),
            }
          }
          _ => Ok(false),
        }
      }
      _ => Ok(false),
    }
  }
}

/// Get the height from reducibility hints.
fn hint_height(h: &ReducibilityHints) -> u32 {
  match h {
    ReducibilityHints::Opaque => u32::MAX,
    ReducibilityHints::Abbrev => 0,
    ReducibilityHints::Regular(n) => *n,
  }
}
