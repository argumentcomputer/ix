//! Definitional equality checking.
//!
//! Implements the full isDefEq algorithm with caching, lazy delta unfolding,
//! proof irrelevance, eta expansion, struct eta, and unit-like types.

use std::rc::Rc;

use num_bigint::BigUint;

use crate::ix::address::Address;
use crate::ix::env::{Literal, Name, ReducibilityHints};
use crate::lean::nat::Nat;

use super::error::TcError;
use super::helpers::*;
use super::level::equal_level;
use super::tc::{TcResult, TypeChecker};
use super::types::{KConstantInfo, KExpr, MetaMode};
use super::value::*;

/// Maximum iterations for lazy delta unfolding.
const MAX_LAZY_DELTA_ITERS: usize = 10_002;
/// Maximum spine size for recursive structural equiv registration.
const MAX_EQUIV_SPINE: usize = 9;

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
      // Same-head ctor with empty spines
      (
        ValInner::Ctor { addr: a1, levels: l1, spine: s1, .. },
        ValInner::Ctor { addr: a2, levels: l2, spine: s2, .. },
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
      if result { self.stats.quick_true += 1; } else { self.stats.quick_false += 1; }
      if self.trace && !result {
        self.trace_msg(&format!("[is_def_eq QUICK FALSE] t={t}  s={s}"));
      }
      return Ok(result);
    }

    // Keep t and s alive to prevent Rc address reuse from corrupting
    // pointer-keyed caches and equiv_manager entries.
    self.keep_alive.push(t.clone());
    self.keep_alive.push(s.clone());

    // 2. EquivManager check
    if self.equiv_manager.is_equiv(t.ptr_id(), s.ptr_id()) {
      self.stats.equiv_hits += 1;
      return Ok(true);
    }

    // 3. Pointer-keyed caches
    let key = (t.ptr_id(), s.ptr_id());
    let key_rev = (s.ptr_id(), t.ptr_id());

    if let Some((ct, cs)) = self.ptr_success_cache.get(&key) {
      if ct.ptr_eq(t) && cs.ptr_eq(s) {
        self.stats.ptr_success_hits += 1;
        return Ok(true);
      }
    }
    if let Some((ct, cs)) = self.ptr_success_cache.get(&key_rev) {
      if ct.ptr_eq(s) && cs.ptr_eq(t) {
        self.stats.ptr_success_hits += 1;
        return Ok(true);
      }
    }
    if let Some((ct, cs)) = self.ptr_failure_cache.get(&key) {
      if ct.ptr_eq(t) && cs.ptr_eq(s) {
        self.stats.ptr_failure_hits += 1;
        if self.trace {
          self.trace_msg(&format!("[is_def_eq CACHE-HIT FALSE] t={t}  s={s}"));
        }
        return Ok(false);
      }
    }
    if let Some((ct, cs)) = self.ptr_failure_cache.get(&key_rev) {
      if ct.ptr_eq(s) && cs.ptr_eq(t) {
        self.stats.ptr_failure_hits += 1;
        if self.trace {
          self.trace_msg(&format!("[is_def_eq CACHE-HIT-REV FALSE] t={t}  s={s}"));
        }
        return Ok(false);
      }
    }

    // 4. Bool.true reflection (check s first, matching Lean's order)
    if let Some(true_addr) = &self.prims.bool_true {
      if s.const_addr() == Some(true_addr)
        && s.spine().map_or(false, |s| s.is_empty())
      {
        let t_whnf = self.whnf_val(t, 0)?;
        if t_whnf.const_addr() == Some(true_addr) {
          return Ok(true);
        }
      }
      if t.const_addr() == Some(true_addr)
        && t.spine().map_or(false, |s| s.is_empty())
      {
        let s_whnf = self.whnf_val(s, 0)?;
        if s_whnf.const_addr() == Some(true_addr) {
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

    // 7. Proof irrelevance (best-effort: skip if type inference fails,
    //    but propagate heartbeat/resource errors including thunk/delta limits)
    match self.is_def_eq_proof_irrel(&t1, &s1) {
      Ok(Some(result)) => { self.stats.proof_irrel_hits += 1; return Ok(result); }
      Ok(None) => {}
      Err(TcError::HeartbeatLimitExceeded) => {
        return Err(TcError::HeartbeatLimitExceeded)
      }
      Err(TcError::KernelException { ref msg }) if msg.contains("limit exceeded") => {
        return Err(TcError::KernelException { msg: msg.clone() })
      }
      Err(_) => {} // type inference failed, skip proof irrelevance
    }

    // 8. Lazy delta
    let (t2, s2, delta_result) = self.lazy_delta(&t1, &s1)?;
    if let Some(result) = delta_result {
      if self.trace && !result {
        self.trace_msg(&format!("[is_def_eq LAZY-DELTA FALSE] t1={t1}  s1={s1}"));
      }
      if result {
        self.add_equiv_val(t, s);
      }
      return Ok(result);
    }

    // 9. Quick check after delta
    if let Some(result) = Self::quick_is_def_eq_val(&t2, &s2) {
      if result {
        self.structural_add_equiv(&t2, &s2);
        self.add_equiv_val(t, s);
      }
      return Ok(result);
    }

    // 10. Second whnf_core (cheap_proj=false) — uses full is_def_eq (not
    //     structural-only is_def_eq_core) since the reference kernel's
    //     is_def_eq_core IS the full algorithm with lazy delta etc.
    let t2b = self.whnf_core_val(&t2, false, false)?;
    let s2b = self.whnf_core_val(&s2, false, false)?;
    if !t2b.ptr_eq(&t2) || !s2b.ptr_eq(&s2) {
      self.stats.step10_fires += 1;
      if self.trace {
        self.trace_msg(&format!("[is_def_eq STEP10 FIRED] t2={t2}  t2b={t2b}  s2={s2}  s2b={s2b}"));
      }
      let result = self.is_def_eq(&t2b, &s2b)?;
      if result {
        self.add_equiv_val(t, s);
        self.ptr_success_cache
          .insert(key, (t.clone(), s.clone()));
      } else {
        self.ptr_failure_cache
          .insert(key, (t.clone(), s.clone()));
      }
      return Ok(result);
    }

    // 11. Full WHNF (includes delta, native, nat prim reduction)
    let t3 = self.whnf_val(&t2, 0)?;
    let s3 = self.whnf_val(&s2, 0)?;
    if !t3.ptr_eq(&t2) || !s3.ptr_eq(&s2) {
      self.stats.step11_fires += 1;
    }

    if self.trace && !t3.ptr_eq(&t2) {
      self.trace_msg(&format!("[is_def_eq STEP11] t changed: t2={t2}  t3={t3}"));
    }
    if self.trace && !s3.ptr_eq(&s2) {
      self.trace_msg(&format!("[is_def_eq STEP11] s changed: s2={s2}  s3={s3}"));
    }

    // 12. Structural comparison
    let result = self.is_def_eq_core(&t3, &s3)?;

    // 13. Cache result
    if result {
      self.add_equiv_val(t, s);
      self.structural_add_equiv(&t3, &s3);
      self.ptr_success_cache.insert(key, (t.clone(), s.clone()));
    } else {
      if self.trace {
        self.trace_msg(&format!("[is_def_eq FALSE] t={t3}  s={s3}"));
        // Show spine details for same-head-const neutrals
        if let (
          ValInner::Neutral { head: Head::Const { addr: a1, .. }, spine: sp1 },
          ValInner::Neutral { head: Head::Const { addr: a2, .. }, spine: sp2 },
        ) = (t3.inner(), s3.inner()) {
          if a1 == a2 && sp1.len() == sp2.len() {
            for (i, (th1, th2)) in sp1.iter().zip(sp2.iter()).enumerate() {
              if std::rc::Rc::ptr_eq(th1, th2) {
                self.trace_msg(&format!("  spine[{i}]: ptr_eq"));
              } else {
                let v1 = self.force_thunk(th1);
                let v2 = self.force_thunk(th2);
                match (v1, v2) {
                  (Ok(v1), Ok(v2)) => {
                    let eq = self.is_def_eq(&v1, &v2).unwrap_or(false);
                    self.trace_msg(&format!("  spine[{i}]: {v1}  vs  {v2}  eq={eq}"));
                  }
                  _ => self.trace_msg(&format!("  spine[{i}]: force error")),
                }
              }
            }
          }
        }
      }
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
        let result = self.is_def_eq_spine(sp1, sp2)?;
        if !result && self.trace {
          self.trace_msg(&format!("[is_def_eq_core CTOR SPINE FAIL] ctor={t}  sp1.len={}  sp2.len={}", sp1.len(), sp2.len()));
          for (i, (t1, t2)) in sp1.iter().zip(sp2.iter()).enumerate() {
            if let (Ok(v1), Ok(v2)) = (self.force_thunk(t1), self.force_thunk(t2)) {
              let w1 = self.whnf_val(&v1, 0).unwrap_or(v1.clone());
              let w2 = self.whnf_val(&v2, 0).unwrap_or(v2.clone());
              self.trace_msg(&format!("  ctor_spine[{i}]: {v1} (whnf: {w1})  vs  {v2} (whnf: {w2})"));
            }
          }
        }
        Ok(result)
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
        // Closure short-circuit: same body + equivalent envs → skip eval
        if self.closure_envs_equiv(b1, b2, e1, e2) {
          return Ok(true);
        }
        let fvar = Val::mk_fvar(self.depth(), d1.clone());
        let env1 = env_push(e1, fvar.clone());
        let env2 = env_push(e2, fvar);
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
        // Closure short-circuit: same body + equivalent envs → skip eval
        if self.closure_envs_equiv(b1, b2, e1, e2) {
          return Ok(true);
        }
        let fvar = Val::mk_fvar(self.depth(), d1.clone());
        let env1 = env_push(e1, fvar.clone());
        let env2 = env_push(e2, fvar);
        let v1 = self.eval(b1, &env1)?;
        let v2 = self.eval(b2, &env2)?;
        self.with_binder(d1.clone(), M::Field::<Name>::default(), |tc| {
          tc.is_def_eq(&v1, &v2)
        })
      }

      // Eta: lambda vs non-lambda
      (ValInner::Lam { dom, body, env, .. }, _) => {
        let fvar = Val::mk_fvar(self.depth(), dom.clone());
        let new_env = env_push(env, fvar.clone());
        let lhs = self.eval(body, &new_env)?;
        let rhs_thunk = mk_thunk_val(fvar);
        let rhs = self.apply_val_thunk(s.clone(), rhs_thunk)?;
        self.with_binder(dom.clone(), M::Field::<Name>::default(), |tc| {
          tc.is_def_eq(&lhs, &rhs)
        })
      }
      (_, ValInner::Lam { dom, body, env, .. }) => {
        let fvar = Val::mk_fvar(self.depth(), dom.clone());
        let new_env = env_push(env, fvar.clone());
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
          type_name: tn1,
        },
        ValInner::Proj {
          type_addr: a2,
          idx: i2,
          strct: s2,
          spine: sp2,
          type_name: tn2,
        },
      ) => {
        if a1 != a2 || i1 != i2 {
          return Ok(false);
        }
        let sv1 = self.force_thunk(s1)?;
        let sv2 = self.force_thunk(s2)?;
        if !self.is_def_eq(&sv1, &sv2)? {
          if self.trace {
            self.trace_msg(&format!("[is_def_eq_core PROJ STRUCT FAIL] proj[{i1}] {tn1:?}  sv1={sv1}  sv2={sv2}"));
          }
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
        if self.trace {
          let t_kind = match t.inner() {
            ValInner::Sort(_) => "Sort",
            ValInner::Lit(_) => "Lit",
            ValInner::Neutral { .. } => "Neutral",
            ValInner::Ctor { .. } => "Ctor",
            ValInner::Lam { .. } => "Lam",
            ValInner::Pi { .. } => "Pi",
            ValInner::Proj { .. } => "Proj",
          };
          let s_kind = match s.inner() {
            ValInner::Sort(_) => "Sort",
            ValInner::Lit(_) => "Lit",
            ValInner::Neutral { .. } => "Neutral",
            ValInner::Ctor { .. } => "Ctor",
            ValInner::Lam { .. } => "Lam",
            ValInner::Pi { .. } => "Pi",
            ValInner::Proj { .. } => "Proj",
          };
          self.trace_msg(&format!("[is_def_eq_core FALLBACK FALSE] t_kind={t_kind} s_kind={s_kind}  t={t}  s={s}"));
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
        if self.trace {
          let w1 = self.whnf_val(&v1, 0).unwrap_or(v1.clone());
          let w2 = self.whnf_val(&v2, 0).unwrap_or(v2.clone());
          self.trace_msg(&format!("[is_def_eq_spine FALSE] v1={v1} (whnf: {w1})  v2={v2} (whnf: {w2})"));
        }
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
      self.heartbeat()?;
      self.stats.lazy_delta_iters += 1;

      // Quick check at top of loop: ptrEq, Sort, Lit only.
      // Must NOT include same-head-const check (lean4's quick_is_def_eq
      // explicitly skips Const). Including it could falsely terminate the
      // loop for same-name-different-univ consts that would become equal
      // after further delta unfolding.
      if t.ptr_eq(&s) {
        return Ok((t, s, Some(true)));
      }
      {
        let quick = match (t.inner(), s.inner()) {
          (ValInner::Sort(a), ValInner::Sort(b)) => Some(equal_level(a, b)),
          (ValInner::Lit(a), ValInner::Lit(b)) => Some(a == b),
          _ => None,
        };
        if let Some(result) = quick {
          return Ok((t, s, Some(result)));
        }
      }

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
          // Try unfolding a stuck projection on the non-delta side first
          // (mirrors lean4 C++ tryUnfoldProjApp optimization)
          if matches!(s.inner(), ValInner::Proj { .. }) {
            let s2 = self.whnf_core_val(&s, false, false)?;
            if !s2.ptr_eq(&s) {
              s = s2;
              continue;
            }
          }
          if let Some(r) = self.delta_step_val(&t)? {
            t = self.whnf_core_val(&r, false, true)?;
          } else {
            return Ok((t, s, None));
          }
        }

        (None, Some(_)) => {
          // Try unfolding a stuck projection on the non-delta side first
          if matches!(t.inner(), ValInner::Proj { .. }) {
            let t2 = self.whnf_core_val(&t, false, false)?;
            if !t2.ptr_eq(&t) {
              t = t2;
              continue;
            }
          }
          if let Some(r) = self.delta_step_val(&s)? {
            s = self.whnf_core_val(&r, false, true)?;
          } else {
            return Ok((t, s, None));
          }
        }

        (Some(th), Some(sh)) => {
          // Same-head optimization with failure cache guard
          if t.same_head_const(&s) && matches!(th, ReducibilityHints::Regular(_)) {
            if let (Some(l1), Some(l2)) =
              (t.head_levels(), s.head_levels())
            {
              if l1.len() == l2.len()
                && l1.iter().zip(l2.iter()).all(|(a, b)| equal_level(a, b))
              {
                self.stats.same_head_checks += 1;
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
                        self.stats.same_head_hits += 1;
                        return Ok((t, s, Some(true)));
                      } else {
                        // Record failure and keep values alive to prevent Rc address reuse
                        self.ptr_failure_cache.insert(
                          ptr_key,
                          (t.clone(), s.clone()),
                        );
                        self.keep_alive.push(t.clone());
                        self.keep_alive.push(s.clone());
                      }
                    }
                  }
                }
              }
            }
          }

          // Hint-guided unfolding (matches Lean's lt'-based ordering)
          // lt' ordering: opaque < regular(0) < ... < abbrev
          // Unfold the "bigger" (higher priority) side first
          if hints_lt(&th, &sh) {
            // th < sh → unfold s (higher priority)
            if let Some(r) = self.delta_step_val(&s)? {
              s = self.whnf_core_val(&r, false, true)?;
            } else if let Some(r) = self.delta_step_val(&t)? {
              t = self.whnf_core_val(&r, false, true)?;
            } else {
              return Ok((t, s, None));
            }
          } else if hints_lt(&sh, &th) {
            // sh < th → unfold t (higher priority)
            if let Some(r) = self.delta_step_val(&t)? {
              t = self.whnf_core_val(&r, false, true)?;
            } else if let Some(r) = self.delta_step_val(&s)? {
              s = self.whnf_core_val(&r, false, true)?;
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

    }

    Err(TcError::KernelException {
      msg: "lazy delta iteration limit exceeded".to_string(),
    })
  }

  /// Check if two closures have equivalent environments (same body + equiv envs).
  /// Does not allocate new equiv nodes for unknown pointers.
  fn closure_envs_equiv(
    &mut self,
    body1: &KExpr<M>,
    body2: &KExpr<M>,
    env1: &Env<M>,
    env2: &Env<M>,
  ) -> bool {
    if env1.len() != env2.len() {
      return false;
    }
    // Check body structural equality (Rc pointer eq first, then structural)
    if body1.ptr_id() != body2.ptr_id() && body1 != body2 {
      return false;
    }
    // Array pointer equality (same Rc)
    if Rc::ptr_eq(env1, env2) {
      return true;
    }
    // Element-wise pointer equality
    if env1.iter().zip(env2.iter()).all(|(a, b)| a.ptr_eq(b)) {
      return true;
    }
    // Element-wise equiv manager check (non-allocating)
    env1.iter().zip(env2.iter()).all(|(a, b)| {
      self.equiv_manager.try_is_equiv(a.ptr_id(), b.ptr_id())
    })
  }

  /// Recursively add sub-component equivalences after successful isDefEq.
  pub fn structural_add_equiv(&mut self, t: &Val<M>, s: &Val<M>) {
    self.add_equiv_val(t, s);

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
            self.add_equiv_val(&v1, &v2);
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

  /// Proof irrelevance: if both sides are proofs (their types are Prop), they're equal.
  fn is_def_eq_proof_irrel(
    &mut self,
    t: &Val<M>,
    s: &Val<M>,
  ) -> TcResult<Option<bool>, M> {
    // Infer types of both sides and check if those types live in Prop
    let t_type = self.infer_type_of_val(t)?;
    if !self.is_prop_val(&t_type)? {
      return Ok(None);
    }

    let s_type = self.infer_type_of_val(s)?;
    if !self.is_prop_val(&s_type)? {
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

/// Lean's `ReducibilityHints.lt'`: determines unfolding priority.
/// Ordering: opaque < regular(0) < regular(1) < ... < abbrev
/// The "bigger" side is unfolded first in lazy delta.
fn hints_lt(a: &ReducibilityHints, b: &ReducibilityHints) -> bool {
  match (a, b) {
    (_, ReducibilityHints::Opaque) => false,
    (ReducibilityHints::Abbrev, _) => false,
    (ReducibilityHints::Opaque, _) => true,
    (_, ReducibilityHints::Abbrev) => true,
    (ReducibilityHints::Regular(d1), ReducibilityHints::Regular(d2)) => {
      d1 < d2
    }
  }
}
