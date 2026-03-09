//! Weak Head Normal Form reduction.
//!
//! Implements structural WHNF (projection, iota, K, quotient reduction),
//! delta unfolding, nat primitive computation, and the full WHNF loop
//! with caching.

use num_bigint::BigUint;

use crate::ix::address::Address;
use crate::ix::env::{Literal, Name};
use crate::lean::nat::Nat;

use super::error::TcError;
use super::helpers::*;
use super::level::inst_bulk_reduce;
use super::tc::{TcResult, TypeChecker};
use super::types::{MetaMode, *};
use super::value::*;

/// Maximum delta steps before giving up.
const MAX_DELTA_STEPS: usize = 50_000;
/// Maximum delta steps in eager-reduce mode.
const MAX_DELTA_STEPS_EAGER: usize = 500_000;

impl<M: MetaMode> TypeChecker<'_, M> {
  /// Structural WHNF: reduce projections, iota (recursor), K, and quotient.
  /// Does NOT do delta unfolding.
  pub fn whnf_core_val(
    &mut self,
    v: &Val<M>,
    _cheap_rec: bool,
    cheap_proj: bool,
  ) -> TcResult<Val<M>, M> {
    match v.inner() {
      // Projection reduction
      ValInner::Proj {
        type_addr,
        idx,
        strct,
        type_name,
        spine,
      } => {
        let struct_val = self.force_thunk(strct)?;
        let struct_whnf = if cheap_proj {
          struct_val.clone()
        } else {
          self.whnf_val(&struct_val, 0)?
        };
        if let Some(field_thunk) =
          reduce_val_proj_forced(&struct_whnf, *idx, type_addr)
        {
          let mut result = self.force_thunk(&field_thunk)?;
          for s in spine {
            result = self.apply_val_thunk(result, s.clone())?;
          }
          Ok(result)
        } else {
          // Projection didn't reduce — return original to preserve
          // pointer identity (prevents infinite recursion in whnf_val)
          Ok(v.clone())
        }
      }

      // Recursor (iota) reduction
      ValInner::Neutral {
        head: Head::Const { addr, levels, .. },
        spine,
      } => {
        // Ensure this constant is in typed_consts (lazily populate)
        let _ = self.ensure_typed_const(addr);

        // Check if this is a recursor
        if let Some(TypedConst::Recursor {
          num_params,
          num_motives,
          num_minors,
          num_indices,
          k,
          induct_addr,
          rules,
          ..
        }) = self.typed_consts.get(addr).cloned()
        {
          let total_before_major =
            num_params + num_motives + num_minors;
          let major_idx = total_before_major + num_indices;

          if spine.len() <= major_idx {
            return Ok(v.clone());
          }

          // K-reduction
          if k {
            if let Some(result) = self.try_k_reduction(
              levels,
              spine,
              num_params,
              num_motives,
              num_minors,
              num_indices,
              &induct_addr,
              &rules,
            )? {
              return Ok(result);
            }
          }

          // Standard iota reduction
          if let Some(result) = self.try_iota_reduction(
            addr,
            levels,
            spine,
            num_params,
            num_motives,
            num_minors,
            num_indices,
            &rules,
            &induct_addr,
          )? {
            return Ok(result);
          }

          // Struct eta fallback
          if let Some(result) = self.try_struct_eta_iota(
            levels,
            spine,
            num_params,
            num_motives,
            num_minors,
            num_indices,
            &induct_addr,
            &rules,
          )? {
            return Ok(result);
          }
        }

        // Quotient reduction
        if let Some(TypedConst::Quotient { kind, .. }) =
          self.typed_consts.get(addr).cloned()
        {
          use crate::ix::env::QuotKind;
          match kind {
            QuotKind::Lift if spine.len() >= 6 => {
              if let Some(result) =
                self.try_quot_reduction(spine, 6, 3)?
              {
                return Ok(result);
              }
            }
            QuotKind::Ind if spine.len() >= 5 => {
              if let Some(result) =
                self.try_quot_reduction(spine, 5, 3)?
              {
                return Ok(result);
              }
            }
            _ => {}
          }
        }

        Ok(v.clone())
      }

      // Everything else is already in WHNF structurally
      _ => Ok(v.clone()),
    }
  }

  /// Try standard iota reduction (recursor on a constructor).
  fn try_iota_reduction(
    &mut self,
    _rec_addr: &Address,
    levels: &[KLevel<M>],
    spine: &[Thunk<M>],
    num_params: usize,
    num_motives: usize,
    num_minors: usize,
    num_indices: usize,
    rules: &[(usize, TypedExpr<M>)],
    induct_addr: &Address,
  ) -> TcResult<Option<Val<M>>, M> {
    let major_idx = num_params + num_motives + num_minors + num_indices;
    if spine.len() <= major_idx {
      return Ok(None);
    }

    let major_thunk = &spine[major_idx];
    let major_val = self.force_thunk(major_thunk)?;
    let major_whnf = self.whnf_val(&major_val, 0)?;

    // Convert nat literal 0 to Nat.zero ctor form (only for the real Nat type)
    let major_whnf = match major_whnf.inner() {
      ValInner::Lit(Literal::NatVal(n))
        if n.0 == BigUint::ZERO
          && self.prims.nat.as_ref() == Some(induct_addr) =>
      {
        if let Some(ctor_val) = nat_lit_to_ctor_val(n, self.prims) {
          ctor_val
        } else {
          major_whnf
        }
      }
      _ => major_whnf,
    };

    match major_whnf.inner() {
      ValInner::Ctor {
        cidx,
        spine: ctor_spine,
        ..
      } => {
        // Find the matching rule
        if *cidx >= rules.len() {
          return Ok(None);
        }
        let (nfields, rule_rhs) = &rules[*cidx];

        // Evaluate the RHS with substituted levels
        let rhs_expr = &rule_rhs.body;
        let rhs_instantiated = self.instantiate_levels(rhs_expr, levels);
        let mut rhs_val = self.eval_in_ctx(&rhs_instantiated)?;

        // Apply: params, motives, minors from the spine
        let params_motives_minors =
          &spine[..num_params + num_motives + num_minors];
        for thunk in params_motives_minors {
          rhs_val = self.apply_val_thunk(rhs_val, thunk.clone())?;
        }

        // Apply: constructor fields from the ctor spine
        let field_start = ctor_spine.len() - nfields;
        for i in 0..*nfields {
          let field_thunk = &ctor_spine[field_start + i];
          rhs_val =
            self.apply_val_thunk(rhs_val, field_thunk.clone())?;
        }

        // Apply: remaining spine arguments after major
        for thunk in &spine[major_idx + 1..] {
          rhs_val = self.apply_val_thunk(rhs_val, thunk.clone())?;
        }

        Ok(Some(rhs_val))
      }
      _ => Ok(None),
    }
  }

  /// Try K-reduction for Prop inductives with single zero-field ctor.
  fn try_k_reduction(
    &mut self,
    _levels: &[KLevel<M>],
    spine: &[Thunk<M>],
    num_params: usize,
    num_motives: usize,
    num_minors: usize,
    num_indices: usize,
    _induct_addr: &Address,
    _rules: &[(usize, TypedExpr<M>)],
  ) -> TcResult<Option<Val<M>>, M> {
    // K-reduction: for Prop inductives with single zero-field ctor,
    // the minor premise is returned directly
    if num_minors != 1 {
      return Ok(None);
    }

    let major_idx = num_params + num_motives + num_minors + num_indices;
    if spine.len() <= major_idx {
      return Ok(None);
    }

    // The minor premise is at index num_params + num_motives
    let minor_idx = num_params + num_motives;
    if minor_idx >= spine.len() {
      return Ok(None);
    }

    let minor_val = self.force_thunk(&spine[minor_idx])?;

    // Apply remaining spine args after major
    let mut result = minor_val;
    for thunk in &spine[major_idx + 1..] {
      result = self.apply_val_thunk(result, thunk.clone())?;
    }

    Ok(Some(result))
  }

  /// Try struct eta for iota: expand major premise via projections.
  fn try_struct_eta_iota(
    &mut self,
    levels: &[KLevel<M>],
    spine: &[Thunk<M>],
    num_params: usize,
    num_motives: usize,
    num_minors: usize,
    num_indices: usize,
    induct_addr: &Address,
    rules: &[(usize, TypedExpr<M>)],
  ) -> TcResult<Option<Val<M>>, M> {
    // Ensure the inductive is in typed_consts (needed for is_struct check)
    let _ = self.ensure_typed_const(induct_addr);
    if !is_struct_like_app_by_addr(induct_addr, &self.typed_consts) {
      return Ok(None);
    }

    // Skip Prop structures (proof irrelevance handles them)
    let major_idx = num_params + num_motives + num_minors + num_indices;
    if major_idx >= spine.len() {
      return Ok(None);
    }
    let major = self.force_thunk(&spine[major_idx])?;
    let is_prop = self.is_prop_val(&major).unwrap_or(false);
    if is_prop {
      return Ok(None);
    }

    let (nfields, rhs) = match rules.first() {
      Some(r) => r,
      None => return Ok(None),
    };

    // Instantiate RHS with levels
    let rhs_body = inst_levels_expr(&rhs.body, levels);
    let mut result = self.eval(&rhs_body, &Vec::new())?;

    // Phase 1: apply params + motives + minors
    let pmm_end = num_params + num_motives + num_minors;
    for i in 0..pmm_end {
      if i < spine.len() {
        result = self.apply_val_thunk(result, spine[i].clone())?;
      }
    }

    // Phase 2: projections as fields
    let major_thunk = mk_thunk_val(major);
    for i in 0..*nfields {
      let proj_val = Val::mk_proj(
        induct_addr.clone(),
        i,
        major_thunk.clone(),
        M::Field::<Name>::default(),
        Vec::new(),
      );
      let proj_thunk = mk_thunk_val(proj_val);
      result = self.apply_val_thunk(result, proj_thunk)?;
    }

    // Phase 3: extra args after major
    if major_idx + 1 < spine.len() {
      for i in (major_idx + 1)..spine.len() {
        result = self.apply_val_thunk(result, spine[i].clone())?;
      }
    }

    Ok(Some(result))
  }

  /// Try quotient reduction (Quot.lift, Quot.ind).
  fn try_quot_reduction(
    &mut self,
    spine: &[Thunk<M>],
    reduce_size: usize,
    f_pos: usize,
  ) -> TcResult<Option<Val<M>>, M> {
    // Force the last argument (should be Quot.mk applied to a value)
    let last_idx = reduce_size - 1;
    if last_idx >= spine.len() {
      return Ok(None);
    }
    let last_val = self.force_thunk(&spine[last_idx])?;
    let last_whnf = self.whnf_val(&last_val, 0)?;

    // Check if the last arg is a Quot.mk application
    // Extract the Quot.mk spine (works for both Ctor and Neutral Quot.mk)
    let mk_spine_opt = match last_whnf.inner() {
      ValInner::Ctor { spine: mk_spine, .. } => Some(mk_spine.clone()),
      ValInner::Neutral {
        head: Head::Const { addr, .. },
        spine: mk_spine,
      } => {
        // Check if this is a Quot.mk (QuotKind::Ctor)
        let _ = self.ensure_typed_const(addr);
        if matches!(
          self.typed_consts.get(addr),
          Some(TypedConst::Quotient {
            kind: crate::ix::env::QuotKind::Ctor,
            ..
          })
        ) {
          Some(mk_spine.clone())
        } else {
          None
        }
      }
      _ => None,
    };

    match mk_spine_opt {
      Some(mk_spine) if !mk_spine.is_empty() => {
        // The quotient value is the last field of Quot.mk
        let quot_val = &mk_spine[mk_spine.len() - 1];

        // Apply the function (at f_pos) to the quotient value
        let f_val = self.force_thunk(&spine[f_pos])?;
        let mut result =
          self.apply_val_thunk(f_val, quot_val.clone())?;

        // Apply remaining spine
        for thunk in &spine[reduce_size..] {
          result = self.apply_val_thunk(result, thunk.clone())?;
        }

        Ok(Some(result))
      }
      _ => Ok(None),
    }
  }

  /// Single delta unfolding step: unfold one definition.
  pub fn delta_step_val(
    &mut self,
    v: &Val<M>,
  ) -> TcResult<Option<Val<M>>, M> {
    match v.inner() {
      ValInner::Neutral {
        head: Head::Const { addr, levels, .. },
        spine,
      } => {
        // Check if this constant should be unfolded
        let ci = match self.env.get(addr) {
          Some(ci) => ci.clone(),
          None => return Ok(None),
        };

        let body = match &ci {
          KConstantInfo::Definition(d) => {
            // Don't unfold if it's the current recursive def
            if self.rec_addr.as_ref() == Some(addr) {
              return Ok(None);
            }
            &d.value
          }
          KConstantInfo::Theorem(t) => &t.value,
          _ => return Ok(None),
        };

        // Instantiate universe levels in the body
        let body_inst = self.instantiate_levels(body, levels);

        // Evaluate the body
        let mut val = self.eval_in_ctx(&body_inst)?;

        // Apply all spine thunks
        for thunk in spine {
          val = self.apply_val_thunk(val, thunk.clone())?;
        }

        Ok(Some(val))
      }
      _ => Ok(None),
    }
  }

  /// Try to reduce nat primitives.
  pub fn try_reduce_nat_val(
    &mut self,
    v: &Val<M>,
  ) -> TcResult<Option<Val<M>>, M> {
    match v.inner() {
      ValInner::Neutral {
        head: Head::Const { addr, .. },
        spine,
      } => {
        // Nat.zero with 0 args → nat literal 0
        if self.prims.nat_zero.as_ref() == Some(addr)
          && spine.is_empty()
        {
          return Ok(Some(Val::mk_lit(Literal::NatVal(
            Nat::from(0u64),
          ))));
        }

        // Nat.succ with 1 arg
        if is_nat_succ(addr, self.prims) && spine.len() == 1 {
          let arg = self.force_thunk(&spine[0])?;
          let arg = self.whnf_val(&arg, 0)?;
          if let Some(n) = extract_nat_val(&arg, self.prims) {
            return Ok(Some(Val::mk_lit(Literal::NatVal(Nat(&n.0 + 1u64)))));
          }
        }

        // Binary nat ops with 2 args
        if is_nat_bin_op(addr, self.prims) && spine.len() == 2 {
          let a = self.force_thunk(&spine[0])?;
          let a = self.whnf_val(&a, 0)?;
          let b = self.force_thunk(&spine[1])?;
          let b = self.whnf_val(&b, 0)?;
          if let (Some(na), Some(nb)) = (
            extract_nat_val(&a, self.prims),
            extract_nat_val(&b, self.prims),
          ) {
            if let Some(result) =
              compute_nat_prim(addr, &na, &nb, self.prims)
            {
              return Ok(Some(result));
            }
          }
        }

        Ok(None)
      }
      _ => Ok(None),
    }
  }

  /// Try to reduce native reduction markers (reduceBool, reduceNat).
  pub fn reduce_native_val(
    &mut self,
    v: &Val<M>,
  ) -> TcResult<Option<Val<M>>, M> {
    match v.inner() {
      ValInner::Neutral {
        head: Head::Const { addr, .. },
        spine,
      } => {
        let is_reduce_bool =
          self.prims.reduce_bool.as_ref() == Some(addr);
        let is_reduce_nat =
          self.prims.reduce_nat.as_ref() == Some(addr);

        if !is_reduce_bool && !is_reduce_nat {
          return Ok(None);
        }

        if spine.len() != 1 {
          return Ok(None);
        }

        let arg = self.force_thunk(&spine[0])?;
        // The argument should be a constant whose definition we fully
        // evaluate
        let arg_addr = match arg.const_addr() {
          Some(a) => a.clone(),
          None => return Ok(None),
        };

        // Look up the definition
        let body = match self.env.get(&arg_addr) {
          Some(KConstantInfo::Definition(d)) => d.value.clone(),
          _ => return Ok(None),
        };

        // Fully evaluate
        let result = self.eval_in_ctx(&body)?;
        let result = self.whnf_val(&result, 0)?;

        Ok(Some(result))
      }
      _ => Ok(None),
    }
  }

  /// Full WHNF: structural reduction + delta unfolding + nat/native, with
  /// caching.
  pub fn whnf_val(
    &mut self,
    v: &Val<M>,
    delta_steps: usize,
  ) -> TcResult<Val<M>, M> {
    let max_steps = if self.eager_reduce {
      MAX_DELTA_STEPS_EAGER
    } else {
      MAX_DELTA_STEPS
    };

    // Check cache on first entry
    if delta_steps == 0 {
      let key = v.ptr_id();
      if let Some((_, cached)) = self.whnf_cache.get(&key) {
        self.stats.cache_hits += 1;
        return Ok(cached.clone());
      }
    }

    if delta_steps >= max_steps {
      return Err(TcError::KernelException {
        msg: format!("delta step limit exceeded ({max_steps})"),
      });
    }

    // Step 1: Structural WHNF
    let v1 = self.whnf_core_val(v, false, false)?;
    if !v1.ptr_eq(v) {
      // Structural reduction happened, recurse
      return self.whnf_val(&v1, delta_steps + 1);
    }

    // Step 2: Delta unfolding
    if let Some(v2) = self.delta_step_val(&v1)? {
      return self.whnf_val(&v2, delta_steps + 1);
    }

    // Step 3: Native reduction
    if let Some(v3) = self.reduce_native_val(&v1)? {
      return self.whnf_val(&v3, delta_steps + 1);
    }

    // Step 4: Nat primitive reduction
    if let Some(v4) = self.try_reduce_nat_val(&v1)? {
      return self.whnf_val(&v4, delta_steps + 1);
    }

    // No reduction possible — cache and return
    if delta_steps == 0 || !v1.ptr_eq(v) {
      let key = v.ptr_id();
      self.whnf_cache.insert(key, (v.clone(), v1.clone()));
    }

    Ok(v1)
  }

  /// Instantiate universe level parameters in an expression.
  pub fn instantiate_levels(
    &self,
    expr: &KExpr<M>,
    levels: &[KLevel<M>],
  ) -> KExpr<M> {
    if levels.is_empty() {
      return expr.clone();
    }
    inst_levels_expr(expr, levels)
  }
}

/// Recursively instantiate level parameters in an expression.
pub fn inst_levels_expr<M: MetaMode>(expr: &KExpr<M>, levels: &[KLevel<M>]) -> KExpr<M> {
  match expr.data() {
    KExprData::BVar(..) | KExprData::Lit(_) => expr.clone(),
    KExprData::Sort(l) => KExpr::sort(inst_bulk_reduce(levels, l)),
    KExprData::Const(addr, ls, name) => {
      let new_ls: Vec<_> =
        ls.iter().map(|l| inst_bulk_reduce(levels, l)).collect();
      KExpr::cnst(addr.clone(), new_ls, name.clone())
    }
    KExprData::App(f, a) => {
      KExpr::app(inst_levels_expr(f, levels), inst_levels_expr(a, levels))
    }
    KExprData::Lam(ty, body, name, bi) => KExpr::lam(
      inst_levels_expr(ty, levels),
      inst_levels_expr(body, levels),
      name.clone(),
      bi.clone(),
    ),
    KExprData::ForallE(ty, body, name, bi) => KExpr::forall_e(
      inst_levels_expr(ty, levels),
      inst_levels_expr(body, levels),
      name.clone(),
      bi.clone(),
    ),
    KExprData::LetE(ty, val, body, name) => KExpr::let_e(
      inst_levels_expr(ty, levels),
      inst_levels_expr(val, levels),
      inst_levels_expr(body, levels),
      name.clone(),
    ),
    KExprData::Proj(addr, idx, s, name) => {
      KExpr::proj(addr.clone(), *idx, inst_levels_expr(s, levels), name.clone())
    }
  }
}
