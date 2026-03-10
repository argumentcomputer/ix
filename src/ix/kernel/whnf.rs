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
    cheap_rec: bool,
    cheap_proj: bool,
  ) -> TcResult<Val<M>, M> {
    self.heartbeat()?;

    // Check cache (only when not cheap_rec and not cheap_proj)
    if !cheap_rec && !cheap_proj {
      let key = v.ptr_id();
      if let Some(cached) = self.whnf_core_cache.get(&key).cloned() {
        return Ok(cached);
      }
    }

    let result = self.whnf_core_val_inner(v, cheap_rec, cheap_proj)?;

    // Cache result
    if !cheap_rec && !cheap_proj && !result.ptr_eq(v) {
      self.whnf_core_cache.insert(v.ptr_id(), result.clone());
    }

    Ok(result)
  }

  fn whnf_core_val_inner(
    &mut self,
    v: &Val<M>,
    cheap_rec: bool,
    cheap_proj: bool,
  ) -> TcResult<Val<M>, M> {
    match v.inner() {
      // Projection reduction with chain flattening
      ValInner::Proj {
        type_addr,
        idx,
        strct,
        type_name,
        spine,
      } => {
        // Collect nested projection chain (outside-in)
        let mut proj_stack: Vec<(
          Address,
          usize,
          M::Field<Name>,
          Vec<Thunk<M>>,
        )> = vec![(
          type_addr.clone(),
          *idx,
          type_name.clone(),
          spine.clone(),
        )];
        let mut inner_thunk = strct.clone();
        loop {
          let inner_v = self.force_thunk(&inner_thunk)?;
          match inner_v.inner() {
            ValInner::Proj {
              type_addr: ta,
              idx: i,
              strct: st,
              type_name: tn,
              spine: sp,
            } => {
              proj_stack.push((
                ta.clone(),
                *i,
                tn.clone(),
                sp.clone(),
              ));
              inner_thunk = st.clone();
            }
            _ => break,
          }
        }

        // Reduce the innermost struct once
        let inner_v = self.force_thunk(&inner_thunk)?;
        let inner_v = if cheap_proj {
          self.whnf_core_val(&inner_v, cheap_rec, cheap_proj)?
        } else {
          self.whnf_val(&inner_v, 0)?
        };

        // Resolve projections from inside out (last pushed = innermost)
        let mut current = inner_v;
        let mut any_resolved = false;
        let mut i = proj_stack.len();
        while i > 0 {
          i -= 1;
          let (ta, ix, _tn, sp) = &proj_stack[i];
          if let Some(field_thunk) =
            reduce_val_proj_forced(&current, *ix, ta)
          {
            any_resolved = true;
            current = self.force_thunk(&field_thunk)?;
            current =
              self.whnf_core_val(&current, cheap_rec, cheap_proj)?;
            // Apply accumulated spine args after reducing each projection
            for tid in sp {
              current =
                self.apply_val_thunk(current, tid.clone())?;
              current =
                self.whnf_core_val(&current, cheap_rec, cheap_proj)?;
            }
          } else {
            if !any_resolved {
              // No projection was resolved at all — preserve pointer identity
              return Ok(v.clone());
            }
            // Some inner projections resolved but this one didn't.
            // Reconstruct remaining chain.
            let mut st_thunk = mk_thunk_val(current);
            current = Val::mk_proj(
              ta.clone(),
              *ix,
              st_thunk.clone(),
              proj_stack[i].2.clone(),
              sp.clone(),
            );
            while i > 0 {
              i -= 1;
              let (ta2, ix2, tn2, sp2) = &proj_stack[i];
              st_thunk = mk_thunk_val(current);
              current = Val::mk_proj(
                ta2.clone(),
                *ix2,
                st_thunk,
                tn2.clone(),
                sp2.clone(),
              );
            }
            return Ok(current);
          }
        }
        Ok(current)
      }

      // Recursor (iota) reduction
      ValInner::Neutral {
        head: Head::Const { addr, levels, .. },
        spine,
      } => {
        // Skip iota/recursor reduction when cheap_rec is set
        if cheap_rec {
          return Ok(v.clone());
        }

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

  /// Helper: apply params+motives+minors from rec spine, ctor fields, and extra args after major.
  fn apply_pmm_and_extra(
    &mut self,
    mut result: Val<M>,
    levels: &[KLevel<M>],
    spine: &[Thunk<M>],
    num_params: usize,
    num_motives: usize,
    num_minors: usize,
    major_idx: usize,
    ctor_field_thunks: &[Thunk<M>],
  ) -> TcResult<Val<M>, M> {
    let _ = levels; // already used for RHS instantiation by caller
    let pmm_end = num_params + num_motives + num_minors;
    for i in 0..pmm_end {
      if i < spine.len() {
        result = self.apply_val_thunk(result, spine[i].clone())?;
      }
    }
    for thunk in ctor_field_thunks {
      result = self.apply_val_thunk(result, thunk.clone())?;
    }
    for thunk in &spine[major_idx + 1..] {
      result = self.apply_val_thunk(result, thunk.clone())?;
    }
    Ok(result)
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

    // Handle nat literals directly (O(1) instead of O(n) via nat_lit_to_ctor_thunked)
    match major_whnf.inner() {
      ValInner::Lit(Literal::NatVal(n))
        if self.prims.nat.as_ref() == Some(induct_addr) =>
      {
        if n.0 == BigUint::ZERO {
          // Lit(0) → fire rule[0] (zero) with no ctor fields
          if let Some((_, rule_rhs)) = rules.first() {
            let rhs_inst = self.instantiate_levels(&rule_rhs.body, levels);
            let result = self.eval_in_ctx(&rhs_inst)?;
            return Ok(Some(self.apply_pmm_and_extra(
              result, levels, spine, num_params, num_motives, num_minors,
              major_idx, &[],
            )?));
          }
          return Ok(None);
        } else {
          // Lit(n+1) → fire rule[1] (succ) with one field = Lit(n)
          if rules.len() > 1 {
            let (_, rule_rhs) = &rules[1];
            let rhs_inst = self.instantiate_levels(&rule_rhs.body, levels);
            let result = self.eval_in_ctx(&rhs_inst)?;
            let pred_val = Val::mk_lit(Literal::NatVal(Nat(&n.0 - 1u64)));
            let pred_thunk = mk_thunk_val(pred_val);
            return Ok(Some(self.apply_pmm_and_extra(
              result, levels, spine, num_params, num_motives, num_minors,
              major_idx, &[pred_thunk],
            )?));
          }
          return Ok(None);
        }
      }
      _ => {}
    }

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
        let rhs_inst = self.instantiate_levels(&rule_rhs.body, levels);
        let result = self.eval_in_ctx(&rhs_inst)?;

        // Collect constructor fields (skip constructor params)
        let field_start = ctor_spine.len() - nfields;
        let ctor_fields: Vec<_> =
          ctor_spine[field_start..].to_vec();

        Ok(Some(self.apply_pmm_and_extra(
          result, levels, spine, num_params, num_motives, num_minors,
          major_idx, &ctor_fields,
        )?))
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
    induct_addr: &Address,
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

    // Force and WHNF the major premise
    let major = self.force_thunk(&spine[major_idx])?;
    let major_whnf = self.whnf_val(&major, 0)?;

    // If major is not already a constructor, validate its type matches
    // the K-inductive
    let is_ctor = matches!(major_whnf.inner(), ValInner::Ctor { .. });
    if !is_ctor {
      if self.to_ctor_when_k_val(&major_whnf, induct_addr)?.is_none() {
        return Ok(None);
      }
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

  /// For K-like inductives, verify the major's type matches the inductive.
  /// Returns Some(ctor) if valid, None if type doesn't match.
  fn to_ctor_when_k_val(
    &mut self,
    major: &Val<M>,
    ind_addr: &Address,
  ) -> TcResult<Option<Val<M>>, M> {
    let ci = match self.env.get(ind_addr) {
      Some(KConstantInfo::Inductive(iv)) => iv.clone(),
      _ => return Ok(None),
    };
    if ci.ctors.is_empty() {
      return Ok(None);
    }
    let ctor_addr = &ci.ctors[0];

    // Infer major's type; bail if inference fails
    let major_type = match self.infer_type_of_val(major) {
      Ok(ty) => ty,
      Err(_) => return Ok(None),
    };
    let major_type_whnf = self.whnf_val(&major_type, 0)?;

    // Check if major's type is headed by the inductive
    match major_type_whnf.inner() {
      ValInner::Neutral {
        head: Head::Const { addr: head_addr, levels: univs, .. },
        spine: type_spine,
      } if head_addr == ind_addr => {
        // Build the nullary ctor applied to params from the type
        let cv = match self.env.get(ctor_addr) {
          Some(KConstantInfo::Constructor(cv)) => cv.clone(),
          _ => return Ok(None),
        };
        let mut ctor_args = Vec::new();
        for i in 0..ci.num_params {
          if i < type_spine.len() {
            ctor_args.push(type_spine[i].clone());
          }
        }
        let ctor_val = Val::mk_ctor(
          ctor_addr.clone(),
          univs.clone(),
          M::Field::<Name>::default(),
          cv.cidx,
          cv.num_params,
          cv.num_fields,
          cv.induct.clone(),
          ctor_args,
        );

        // Verify ctor type matches major type
        let ctor_type = match self.infer_type_of_val(&ctor_val) {
          Ok(ty) => ty,
          Err(_) => return Ok(None),
        };
        if !self.is_def_eq(&major_type, &ctor_type)? {
          return Ok(None);
        }
        Ok(Some(ctor_val))
      }
      _ => Ok(None),
    }
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
    self.heartbeat()?;
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
          // Both args are concrete nat values → compute directly
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
          // Partial reduction: base cases (second arg is 0)
          if is_nat_zero_val(&b, self.prims) {
            if self.prims.nat_add.as_ref() == Some(addr) {
              return Ok(Some(a)); // n + 0 = n
            } else if self.prims.nat_sub.as_ref() == Some(addr) {
              return Ok(Some(a)); // n - 0 = n
            } else if self.prims.nat_mul.as_ref() == Some(addr) {
              return Ok(Some(Val::mk_lit(Literal::NatVal(Nat::from(0u64))))); // n * 0 = 0
            } else if self.prims.nat_pow.as_ref() == Some(addr) {
              return Ok(Some(Val::mk_lit(Literal::NatVal(Nat::from(1u64))))); // n ^ 0 = 1
            } else if self.prims.nat_ble.as_ref() == Some(addr) {
              // n ≤ 0 = (n == 0)
              if is_nat_zero_val(&a, self.prims) {
                if let Some(t) = &self.prims.bool_true {
                  if let Some(bt) = &self.prims.bool_type {
                    return Ok(Some(Val::mk_ctor(t.clone(), Vec::new(), M::Field::<Name>::default(), 1, 0, 0, bt.clone(), Vec::new())));
                  }
                }
              }
              // else need to know if a is succ to return false
            }
          }
          // Partial reduction: base cases (first arg is 0)
          else if is_nat_zero_val(&a, self.prims) {
            if self.prims.nat_add.as_ref() == Some(addr) {
              return Ok(Some(b)); // 0 + n = n
            } else if self.prims.nat_sub.as_ref() == Some(addr) {
              return Ok(Some(Val::mk_lit(Literal::NatVal(Nat::from(0u64))))); // 0 - n = 0
            } else if self.prims.nat_mul.as_ref() == Some(addr) {
              return Ok(Some(Val::mk_lit(Literal::NatVal(Nat::from(0u64))))); // 0 * n = 0
            } else if self.prims.nat_ble.as_ref() == Some(addr) {
              // 0 ≤ n = true
              if let Some(t) = &self.prims.bool_true {
                if let Some(bt) = &self.prims.bool_type {
                  return Ok(Some(Val::mk_ctor(t.clone(), Vec::new(), M::Field::<Name>::default(), 1, 0, 0, bt.clone(), Vec::new())));
                }
              }
            }
          }
          // Step-case reductions (second arg is succ)
          if let Some(pred_ref) = extract_succ_pred(&b, self.prims) {
            let pred_thunk = match pred_ref {
              PredRef::Thunk(t) => t,
              PredRef::Lit(n) => mk_thunk_val(Val::mk_lit(Literal::NatVal(n))),
            };
            let addr = addr.clone();
            if self.prims.nat_add.as_ref() == Some(&addr) {
              // add x (succ y) = succ (add x y)
              let inner = mk_thunk_val(Val::mk_neutral(
                Head::Const { addr: addr.clone(), levels: Vec::new(), name: M::Field::<Name>::default() },
                vec![spine[0].clone(), pred_thunk],
              ));
              let succ_addr = self.prims.nat_succ.as_ref().unwrap().clone();
              return Ok(Some(Val::mk_neutral(
                Head::Const { addr: succ_addr, levels: Vec::new(), name: M::Field::<Name>::default() },
                vec![inner],
              )));
            } else if self.prims.nat_sub.as_ref() == Some(&addr) {
              // sub x (succ y) = pred (sub x y)
              let inner = mk_thunk_val(Val::mk_neutral(
                Head::Const { addr: addr.clone(), levels: Vec::new(), name: M::Field::<Name>::default() },
                vec![spine[0].clone(), pred_thunk],
              ));
              let pred_addr = self.prims.nat_pred.as_ref().unwrap().clone();
              return Ok(Some(Val::mk_neutral(
                Head::Const { addr: pred_addr, levels: Vec::new(), name: M::Field::<Name>::default() },
                vec![inner],
              )));
            } else if self.prims.nat_mul.as_ref() == Some(&addr) {
              // mul x (succ y) = add (mul x y) x
              let inner = mk_thunk_val(Val::mk_neutral(
                Head::Const { addr: addr.clone(), levels: Vec::new(), name: M::Field::<Name>::default() },
                vec![spine[0].clone(), pred_thunk],
              ));
              let add_addr = self.prims.nat_add.as_ref().unwrap().clone();
              return Ok(Some(Val::mk_neutral(
                Head::Const { addr: add_addr, levels: Vec::new(), name: M::Field::<Name>::default() },
                vec![inner, spine[0].clone()],
              )));
            } else if self.prims.nat_pow.as_ref() == Some(&addr) {
              // pow x (succ y) = mul (pow x y) x
              let inner = mk_thunk_val(Val::mk_neutral(
                Head::Const { addr: addr.clone(), levels: Vec::new(), name: M::Field::<Name>::default() },
                vec![spine[0].clone(), pred_thunk],
              ));
              let mul_addr = self.prims.nat_mul.as_ref().unwrap().clone();
              return Ok(Some(Val::mk_neutral(
                Head::Const { addr: mul_addr, levels: Vec::new(), name: M::Field::<Name>::default() },
                vec![inner, spine[0].clone()],
              )));
            } else if self.prims.nat_beq.as_ref() == Some(&addr) {
              // beq (succ x) (succ y) = beq x y
              if let Some(pred_ref_a) = extract_succ_pred(&a, self.prims) {
                let pred_thunk_a = match pred_ref_a {
                  PredRef::Thunk(t) => t,
                  PredRef::Lit(n) => mk_thunk_val(Val::mk_lit(Literal::NatVal(n))),
                };
                return Ok(Some(Val::mk_neutral(
                  Head::Const { addr: addr.clone(), levels: Vec::new(), name: M::Field::<Name>::default() },
                  vec![pred_thunk_a, pred_thunk],
                )));
              } else if is_nat_zero_val(&a, self.prims) {
                // beq 0 (succ y) = false
                if let Some(f) = &self.prims.bool_false {
                  if let Some(bt) = &self.prims.bool_type {
                    return Ok(Some(Val::mk_ctor(f.clone(), Vec::new(), M::Field::<Name>::default(), 0, 0, 0, bt.clone(), Vec::new())));
                  }
                }
              }
            } else if self.prims.nat_ble.as_ref() == Some(&addr) {
              // ble (succ x) (succ y) = ble x y
              if let Some(pred_ref_a) = extract_succ_pred(&a, self.prims) {
                let pred_thunk_a = match pred_ref_a {
                  PredRef::Thunk(t) => t,
                  PredRef::Lit(n) => mk_thunk_val(Val::mk_lit(Literal::NatVal(n))),
                };
                return Ok(Some(Val::mk_neutral(
                  Head::Const { addr: addr.clone(), levels: Vec::new(), name: M::Field::<Name>::default() },
                  vec![pred_thunk_a, pred_thunk],
                )));
              } else if is_nat_zero_val(&a, self.prims) {
                // ble 0 (succ y) = true
                if let Some(t) = &self.prims.bool_true {
                  if let Some(bt) = &self.prims.bool_type {
                    return Ok(Some(Val::mk_ctor(t.clone(), Vec::new(), M::Field::<Name>::default(), 1, 0, 0, bt.clone(), Vec::new())));
                  }
                }
              }
            }
          } else {
            // Second arg is not succ — check if first arg is succ for beq/ble edge cases
            if let Some(_) = extract_succ_pred(&a, self.prims) {
              if self.prims.nat_beq.as_ref() == Some(addr) && is_nat_zero_val(&b, self.prims) {
                // beq (succ x) 0 = false
                if let Some(f) = &self.prims.bool_false {
                  if let Some(bt) = &self.prims.bool_type {
                    return Ok(Some(Val::mk_ctor(f.clone(), Vec::new(), M::Field::<Name>::default(), 0, 0, 0, bt.clone(), Vec::new())));
                  }
                }
              } else if self.prims.nat_ble.as_ref() == Some(addr) && is_nat_zero_val(&b, self.prims) {
                // ble (succ x) 0 = false
                if let Some(f) = &self.prims.bool_false {
                  if let Some(bt) = &self.prims.bool_type {
                    return Ok(Some(Val::mk_ctor(f.clone(), Vec::new(), M::Field::<Name>::default(), 0, 0, 0, bt.clone(), Vec::new())));
                  }
                }
              }
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
  /// caching. Matches the Lean kernel's whnfVal loop:
  /// whnfCoreVal → tryReduceNatVal → deltaStepVal → reduceNativeVal.
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
      self.heartbeat()?;
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

    // Step 1: Structural WHNF (projection, iota, K, quotient)
    let v1 = self.whnf_core_val(v, false, false)?;

    // Step 2: Nat primitive reduction
    let result = if let Some(v2) = self.try_reduce_nat_val(&v1)? {
      self.whnf_val(&v2, delta_steps + 1)?
    // Step 3: Delta unfolding (single step)
    } else if let Some(v2) = self.delta_step_val(&v1)? {
      self.whnf_val(&v2, delta_steps + 1)?
    // Step 4: Native reduction (structural WHNF only to prevent re-entry)
    } else if let Some(v2) = self.reduce_native_val(&v1)? {
      self.whnf_core_val(&v2, false, false)?
    } else {
      v1
    };

    // Cache the final result (only at top-level entry)
    if delta_steps == 0 {
      let key = v.ptr_id();
      self.whnf_cache.insert(key, (v.clone(), result.clone()));
    }

    Ok(result)
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
