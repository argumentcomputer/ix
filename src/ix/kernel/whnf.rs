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
      if let Some((orig, cached)) = self.whnf_core_cache.get(&key) {
        if orig.ptr_eq(v) {
          self.stats.whnf_core_cache_hits += 1;
          return Ok(cached.clone());
        }
      }
      // Second-chance lookup via equiv root
      if let Some(root_ptr) = self.equiv_manager.find_root_ptr(key) {
        if root_ptr != key {
          if let Some((_, cached)) = self.whnf_core_cache.get(&root_ptr) {
            self.stats.whnf_core_cache_hits += 1;
            return Ok(cached.clone());
          }
        }
      }
      self.stats.whnf_core_cache_misses += 1;
    }

    let result = self.whnf_core_val_inner(v, cheap_rec, cheap_proj)?;

    // Cache result
    if !cheap_rec && !cheap_proj {
      let key = v.ptr_id();
      self.whnf_core_cache.insert(key, (v.clone(), result.clone()));
      // Also insert under root
      if let Some(root_ptr) = self.equiv_manager.find_root_ptr(key) {
        if root_ptr != key {
          self.whnf_core_cache.insert(root_ptr, (v.clone(), result.clone()));
        }
      }
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
        let inner_v_before_whnf = inner_v.clone();
        let inner_v = if cheap_proj {
          self.whnf_core_val(&inner_v, cheap_rec, cheap_proj)?
        } else {
          self.whnf_val(&inner_v, 0)?
        };

        if self.trace && proj_stack.len() > 0 {
          let (_ta, ix, tn, _) = &proj_stack[0];
          let tn_str = format!("{tn:?}");
          if tn_str.contains("Fin") || tn_str.contains("BitVec") {
            self.trace_msg(&format!("[PROJ CHAIN] depth={} outermost=proj[{ix}] {tn:?}  inner_whnf={inner_v}", proj_stack.len()));
          }
        }

        // Resolve projections from inside out (last pushed = innermost)
        let mut current = inner_v;
        let mut i = proj_stack.len();
        while i > 0 {
          i -= 1;
          let (ta, ix, _tn, sp) = &proj_stack[i];
          if let Some(field_thunk) =
            reduce_val_proj_forced(&current, *ix, ta)
          {
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
            if self.trace {
              self.trace_msg(&format!(
                "[PROJ STUCK] proj[{ix}]  inner_whnf={current}  cheap_proj={cheap_proj}  cheap_rec={cheap_rec}"
              ));
            }
            if current.ptr_eq(&inner_v_before_whnf) {
              // WHNF was no-op and no projection resolved — preserve pointer identity
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
        head: Head::Const { id, levels },
        spine,
      } => {
        let addr = &id.addr;
        // Skip iota/recursor reduction when cheap_rec is set
        if cheap_rec {
          return Ok(v.clone());
        }

        // Check if this is a recursor (look up directly in env, not via ensure_typed_const)
        if let Some(KConstantInfo::Recursor(rv)) = self.env.find_by_addr(addr) {
          let num_params = rv.num_params;
          let num_motives = rv.num_motives;
          let num_minors = rv.num_minors;
          let num_indices = rv.num_indices;
          let k = rv.k;
          let induct_addr = get_major_induct(
            &rv.cv.typ, num_params, num_motives, num_minors, num_indices,
          ).map(|id| id.addr);
          let rules: Vec<(usize, TypedExpr<M>)> = rv.rules.iter().map(|r| {
            (r.nfields, TypedExpr { info: TypeInfo::None, body: r.rhs.clone() })
          }).collect();
          let total_before_major =
            num_params + num_motives + num_minors;
          let major_idx = total_before_major + num_indices;

          if spine.len() <= major_idx {
            return Ok(v.clone());
          }

          if let Some(induct_addr) = &induct_addr {
            // K-reduction
            if k {
              if let Some(result) = self.try_k_reduction(
                levels,
                spine,
                num_params,
                num_motives,
                num_minors,
                num_indices,
                induct_addr,
                &rules,
              )? {
                return self.whnf_core_val(&result, cheap_rec, cheap_proj);
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
              induct_addr,
            )? {
              return self.whnf_core_val(&result, cheap_rec, cheap_proj);
            }

            // Struct eta fallback
            if let Some(result) = self.try_struct_eta_iota(
              levels,
              spine,
              num_params,
              num_motives,
              num_minors,
              num_indices,
              induct_addr,
              &rules,
            )? {
              return self.whnf_core_val(&result, cheap_rec, cheap_proj);
            }
          }
        }

        // Quotient reduction (look up directly in env)
        if let Some(KConstantInfo::Quotient(qv)) = self.env.find_by_addr(addr) {
          use crate::ix::env::QuotKind;
          let kind = qv.kind;
          match kind {
            QuotKind::Lift if spine.len() >= 6 => {
              if let Some(result) =
                self.try_quot_reduction(spine, 6, 3)?
              {
                return self.whnf_core_val(&result, cheap_rec, cheap_proj);
              }
            }
            QuotKind::Ind if spine.len() >= 5 => {
              if let Some(result) =
                self.try_quot_reduction(spine, 5, 3)?
              {
                return self.whnf_core_val(&result, cheap_rec, cheap_proj);
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
    if self.trace {
      // Show the major premise before and after whnf for stuck cases
      let is_ctor = matches!(major_whnf.inner(), ValInner::Ctor { .. });
      let is_lit = matches!(major_whnf.inner(), ValInner::Lit(_));
      if !is_ctor && !is_lit {
        self.trace_msg(&format!(
          "[IOTA major] idx={major_idx}  before={major_val}  after={major_whnf}"
        ));
      }
    }

    // Handle nat literals directly (O(1) instead of O(n) via nat_lit_to_ctor_thunked)
    match major_whnf.inner() {
      ValInner::Lit(Literal::NatVal(n))
        if Primitives::<M>::addr_matches(&self.prims.nat, induct_addr) =>
      {
        if n.0 == BigUint::ZERO {
          // Lit(0) → fire rule[0] (zero) with no ctor fields
          if let Some((_, rule_rhs)) = rules.first() {
            let rhs_inst = self.instantiate_levels(&rule_rhs.body, levels);
            let result = self.eval(&rhs_inst, &empty_env())?;
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
            let result = self.eval(&rhs_inst, &empty_env())?;
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

        // Evaluate the RHS with substituted levels (empty env — RHS is closed)
        let rhs_inst = self.instantiate_levels(&rule_rhs.body, levels);
        let result = self.eval(&rhs_inst, &empty_env())?;

        // Collect constructor fields (skip constructor params)
        if *nfields > ctor_spine.len() {
          return Ok(None);
        }
        let field_start = ctor_spine.len() - nfields;
        let ctor_fields: Vec<_> =
          ctor_spine[field_start..].to_vec();

        Ok(Some(self.apply_pmm_and_extra(
          result, levels, spine, num_params, num_motives, num_minors,
          major_idx, &ctor_fields,
        )?))
      }
      _ => {
        if self.trace {
          let kind = match major_whnf.inner() {
            ValInner::Neutral { head: Head::Const { .. }, .. } => "Neutral(Const)",
            ValInner::Neutral { head: Head::FVar { .. }, .. } => "Neutral(FVar)",
            ValInner::Lit(_) => "Lit",
            ValInner::Pi { .. } => "Pi",
            ValInner::Lam { .. } => "Lam",
            ValInner::Sort(_) => "Sort",
            ValInner::Proj { idx, strct, .. } => {
              // Show what the stuck projection is trying to project from
              if let Ok(inner) = self.force_thunk(strct) {
                self.trace_msg(&format!(
                  "[IOTA STUCK] major_idx={major_idx}  spine_len={}  major=proj[{idx}]  strct={inner}",
                  spine.len()
                ));
              }
              "Proj"
            }
            _ => "Other",
          };
          if kind != "Proj" {
            // For stuck neutrals, show what the head's spine args are
            let extra = if let ValInner::Neutral { head: Head::Const { .. }, spine: nspine } = major_whnf.inner() {
              let mut parts = Vec::new();
              for (i, thunk) in nspine.iter().enumerate() {
                if let Ok(val) = self.force_thunk(thunk) {
                  parts.push(format!("  arg[{i}]={val}"));
                }
              }
              parts.join("")
            } else {
              String::new()
            };
            self.trace_msg(&format!(
              "[IOTA STUCK] major_idx={major_idx}  spine_len={}  major_whnf={major_whnf}  kind={kind}{extra}",
              spine.len()
            ));
          }
        }
        Ok(None)
      }
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
    let ci = match self.env.find_by_addr(ind_addr) {
      Some(KConstantInfo::Inductive(iv)) => iv.clone(),
      _ => return Ok(None),
    };
    if ci.ctors.is_empty() {
      return Ok(None);
    }
    let ctor_id = &ci.ctors[0];

    // Infer major's type; bail if inference fails
    let major_type = match self.infer_type_of_val(major) {
      Ok(ty) => ty,
      Err(_) => return Ok(None),
    };
    let major_type_whnf = self.whnf_val(&major_type, 0)?;

    // Check if major's type is headed by the inductive
    match major_type_whnf.inner() {
      ValInner::Neutral {
        head: Head::Const { id: head_id, levels: univs },
        spine: type_spine,
      } if &head_id.addr == ind_addr => {
        // Build the nullary ctor applied to params from the type
        let cv = match self.env.get(ctor_id) {
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
          ctor_id.clone(),
          univs.clone(),
          cv.cidx,
          cv.num_params,
          cv.num_fields,
          cv.induct.addr.clone(),
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
    if !is_struct_like_raw(induct_addr, self.env) {
      return Ok(None);
    }

    // Skip Prop structures (proof irrelevance handles them)
    let major_idx = num_params + num_motives + num_minors + num_indices;
    if major_idx >= spine.len() {
      return Ok(None);
    }
    let major = self.force_thunk(&spine[major_idx])?;
    let major = self.whnf_val(&major, 0)?;
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
    let mut result = self.eval(&rhs_body, &empty_env())?;

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
    let mk_spine_opt = match last_whnf.inner() {
      ValInner::Neutral {
        head: Head::Const { id, .. },
        spine: mk_spine,
      } => {
        // Check if this is a Quot.mk (QuotKind::Ctor)
        if matches!(
          self.env.find_by_addr(&id.addr),
          Some(KConstantInfo::Quotient(qv)) if qv.kind == crate::ix::env::QuotKind::Ctor
        ) {
          Some(mk_spine.clone())
        } else {
          None
        }
      }
      _ => None,
    };

    match mk_spine_opt {
      Some(mk_spine) if mk_spine.len() >= 3 => {
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

  /// Check if a value is a fully-applied nat primitive (unary with ≥1 arg, binary with ≥2 args).
  /// Used to block delta-unfolding when tryReduceNatVal fails on symbolic args.
  fn is_fully_applied_nat_prim(&self, v: &Val<M>) -> bool {
    match v.inner() {
      ValInner::Neutral {
        head: Head::Const { id, .. },
        spine,
      } => {
        if (is_nat_succ(&id.addr, self.prims) || is_nat_pred(&id.addr, self.prims))
          && spine.len() >= 1
        {
          return true;
        }
        is_nat_bin_op(&id.addr, self.prims) && spine.len() >= 2
      }
      _ => false,
    }
  }

  /// Check if a fully-applied nat primitive has any spine arg that contains
  /// a free variable (after whnf). When fvars are present, the recursor form
  /// can still make progress by pattern-matching on constructor args even
  /// with symbolic subterms (e.g. Nat.ble (succ n) m), so we allow delta.
  /// We DON'T allow delta for stuck-but-ground terms (no fvars) because
  /// that causes infinite recursion.
  fn nat_prim_has_fvar_arg(&mut self, v: &Val<M>) -> TcResult<bool, M> {
    let spine = match v.spine() {
      Some(s) => s.to_vec(),
      None => return Ok(false),
    };
    for thunk in &spine {
      let val = self.force_thunk(thunk)?;
      let val = self.whnf_val(&val, 0)?;
      if Self::val_contains_fvar(&val) {
        return Ok(true);
      }
    }
    Ok(false)
  }

  /// Shallow check if a value contains a free variable.
  /// Checks the head and one level of spine args.
  fn val_contains_fvar(v: &Val<M>) -> bool {
    match v.inner() {
      ValInner::Neutral { head: Head::FVar { .. }, .. } => true,
      ValInner::Neutral { head: Head::Const { .. }, spine } => {
        // Check if any already-evaluated spine arg is an fvar
        for thunk in spine {
          if let ThunkEntry::Evaluated(val) = &*thunk.borrow() {
            if matches!(val.inner(), ValInner::Neutral { head: Head::FVar { .. }, .. }) {
              return true;
            }
          }
        }
        false
      }
      _ => false,
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
        head: Head::Const { id, levels },
        spine,
      } => {
        let addr = &id.addr;
        // Platform-dependent reduction: System.Platform.numBits → word size
        if Primitives::<M>::addr_matches(&self.prims.system_platform_num_bits, addr)
          && spine.is_empty()
        {
          return Ok(Some(Val::mk_lit(Literal::NatVal(
            Nat::from(self.word_size.num_bits()),
          ))));
        }

        // Check if this constant should be unfolded
        let ci = match self.env.find_by_addr(addr) {
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

        // Evaluate the body (empty env — definition bodies are closed)
        let mut val = self.eval(&body_inst, &empty_env())?;

        // Apply all spine thunks
        for thunk in spine {
          val = self.apply_val_thunk(val, thunk.clone())?;
        }

        self.stats.delta_steps += 1;
        Ok(Some(val))
      }
      _ => Ok(None),
    }
  }

  /// Extract a nat value from a Val, forcing thunks and peeling Nat.succ
  /// constructors as needed. Handles Lit, Ctor(zero), Ctor(succ), and
  /// Neutral(Nat.zero).
  fn force_extract_nat(&mut self, v: &Val<M>) -> TcResult<Option<Nat>, M> {
    // Try the cheap non-forcing check first
    if let Some(n) = extract_nat_val(v, self.prims) {
      return Ok(Some(n));
    }
    // Handle Ctor(Nat.succ, cidx=1) by forcing the inner thunk
    if let ValInner::Ctor {
      cidx: 1,
      induct_addr,
      num_params,
      spine,
      ..
    } = v.inner()
    {
      if Primitives::<M>::addr_matches(&self.prims.nat, induct_addr)
        && spine.len() == num_params + 1
      {
        let inner = self.force_thunk(&spine[spine.len() - 1])?;
        let inner = self.whnf_val(&inner, 0)?;
        if let Some(n) = self.force_extract_nat(&inner)? {
          return Ok(Some(Nat(&n.0 + 1u64)));
        }
      }
    }
    Ok(None)
  }

  /// Try to reduce nat primitives.
  pub fn try_reduce_nat_val(
    &mut self,
    v: &Val<M>,
  ) -> TcResult<Option<Val<M>>, M> {
    match v.inner() {
      ValInner::Neutral {
        head: Head::Const { id, .. },
        spine,
      } => {
        let addr = &id.addr;
        // Nat.zero with 0 args → nat literal 0
        if Primitives::<M>::addr_matches(&self.prims.nat_zero, addr)
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
          if let Some(n) = self.force_extract_nat(&arg)? {
            return Ok(Some(Val::mk_lit(Literal::NatVal(Nat(&n.0 + 1u64)))));
          }
        }

        // Nat.pred with 1 arg
        if is_nat_pred(addr, self.prims) && spine.len() == 1 {
          let arg = self.force_thunk(&spine[0])?;
          let arg = self.whnf_val(&arg, 0)?;
          if let Some(n) = self.force_extract_nat(&arg)? {
            let result = if n.0 == BigUint::ZERO {
              Nat::from(0u64)
            } else {
              Nat(&n.0 - 1u64)
            };
            return Ok(Some(Val::mk_lit(Literal::NatVal(result))));
          }
        }

        // Binary nat ops with 2 args
        if is_nat_bin_op(addr, self.prims) && spine.len() == 2 {
          let a = self.force_thunk(&spine[0])?;
          let a = self.whnf_val(&a, 0)?;
          let b = self.force_thunk(&spine[1])?;
          let b = self.whnf_val(&b, 0)?;
          // Both args are concrete nat values → compute directly
          let na = self.force_extract_nat(&a)?;
          let nb = self.force_extract_nat(&b)?;
          if let (Some(na), Some(nb)) = (&na, &nb) {
            if let Some(result) =
              compute_nat_prim(addr, na, nb, self.prims)
            {
              return Ok(Some(result));
            }
          }
          if self.trace && (na.is_none() || nb.is_none()) {
            self.trace_msg(&format!(
              "[NAT BIN STUCK] op={id}  a={a} (is_nat={})  b={b} (is_nat={})",
              na.is_some(), nb.is_some()
            ));
          }
          // Partial reduction: base cases (second arg is 0)
          if is_nat_zero_val(&b, self.prims) {
            if Primitives::<M>::addr_matches(&self.prims.nat_add, addr) {
              return Ok(Some(a)); // n + 0 = n
            } else if Primitives::<M>::addr_matches(&self.prims.nat_sub, addr) {
              return Ok(Some(a)); // n - 0 = n
            } else if Primitives::<M>::addr_matches(&self.prims.nat_mul, addr) {
              return Ok(Some(Val::mk_lit(Literal::NatVal(Nat::from(0u64))))); // n * 0 = 0
            } else if Primitives::<M>::addr_matches(&self.prims.nat_pow, addr) {
              return Ok(Some(Val::mk_lit(Literal::NatVal(Nat::from(1u64))))); // n ^ 0 = 1
            } else if Primitives::<M>::addr_matches(&self.prims.nat_ble, addr) {
              // n ≤ 0 = (n == 0)
              if is_nat_zero_val(&a, self.prims) {
                if let Some(t) = &self.prims.bool_true {
                  if let Some(bt) = &self.prims.bool_type {
                    return Ok(Some(Val::mk_ctor(t.clone(), Vec::new(), 1, 0, 0, bt.addr.clone(), Vec::new())));
                  }
                }
              }
              // else need to know if a is succ to return false
            }
          }
          // Partial reduction: base cases (first arg is 0)
          else if is_nat_zero_val(&a, self.prims) {
            if Primitives::<M>::addr_matches(&self.prims.nat_add, addr) {
              return Ok(Some(b)); // 0 + n = n
            } else if Primitives::<M>::addr_matches(&self.prims.nat_sub, addr) {
              return Ok(Some(Val::mk_lit(Literal::NatVal(Nat::from(0u64))))); // 0 - n = 0
            } else if Primitives::<M>::addr_matches(&self.prims.nat_mul, addr) {
              return Ok(Some(Val::mk_lit(Literal::NatVal(Nat::from(0u64))))); // 0 * n = 0
            } else if Primitives::<M>::addr_matches(&self.prims.nat_ble, addr) {
              // 0 ≤ n = true
              if let Some(t) = &self.prims.bool_true {
                if let Some(bt) = &self.prims.bool_type {
                  return Ok(Some(Val::mk_ctor(t.clone(), Vec::new(), 1, 0, 0, bt.addr.clone(), Vec::new())));
                }
              }
            }
          }
          // Step-case reductions (second arg is succ)
          if let Some(pred_thunk) = extract_succ_pred(&b, self.prims) {
            let addr = addr.clone();
            if Primitives::<M>::addr_matches(&self.prims.nat_add, &addr) {
              // add x (succ y) = succ (add x y)
              let add_id = self.prims.nat_add.as_ref().unwrap().clone();
              let inner = mk_thunk_val(Val::mk_neutral(
                Head::Const { id: add_id, levels: Vec::new() },
                vec![spine[0].clone(), pred_thunk],
              ));
              let succ_id = self.prims.nat_succ.as_ref().unwrap().clone();
              return Ok(Some(Val::mk_neutral(
                Head::Const { id: succ_id, levels: Vec::new() },
                vec![inner],
              )));
            } else if Primitives::<M>::addr_matches(&self.prims.nat_sub, &addr) {
              // sub x (succ y) = pred (sub x y)
              let sub_id = self.prims.nat_sub.as_ref().unwrap().clone();
              let inner = mk_thunk_val(Val::mk_neutral(
                Head::Const { id: sub_id, levels: Vec::new() },
                vec![spine[0].clone(), pred_thunk],
              ));
              let pred_id = self.prims.nat_pred.as_ref().unwrap().clone();
              return Ok(Some(Val::mk_neutral(
                Head::Const { id: pred_id, levels: Vec::new() },
                vec![inner],
              )));
            } else if Primitives::<M>::addr_matches(&self.prims.nat_mul, &addr) {
              // mul x (succ y) = add (mul x y) x
              let mul_id = self.prims.nat_mul.as_ref().unwrap().clone();
              let inner = mk_thunk_val(Val::mk_neutral(
                Head::Const { id: mul_id, levels: Vec::new() },
                vec![spine[0].clone(), pred_thunk],
              ));
              let add_id = self.prims.nat_add.as_ref().unwrap().clone();
              return Ok(Some(Val::mk_neutral(
                Head::Const { id: add_id, levels: Vec::new() },
                vec![inner, spine[0].clone()],
              )));
            } else if Primitives::<M>::addr_matches(&self.prims.nat_pow, &addr) {
              // pow x (succ y) = mul (pow x y) x
              let pow_id = self.prims.nat_pow.as_ref().unwrap().clone();
              let inner = mk_thunk_val(Val::mk_neutral(
                Head::Const { id: pow_id, levels: Vec::new() },
                vec![spine[0].clone(), pred_thunk],
              ));
              let mul_id = self.prims.nat_mul.as_ref().unwrap().clone();
              return Ok(Some(Val::mk_neutral(
                Head::Const { id: mul_id, levels: Vec::new() },
                vec![inner, spine[0].clone()],
              )));
            } else if Primitives::<M>::addr_matches(&self.prims.nat_shift_left, &addr) {
              // shiftLeft x (succ y) = shiftLeft (2 * x) y
              if let Some(mul_id) = self.prims.nat_mul.as_ref().cloned() {
                let two = mk_thunk_val(Val::mk_lit(Literal::NatVal(Nat::from(2u64))));
                let two_x = mk_thunk_val(Val::mk_neutral(
                  Head::Const { id: mul_id, levels: Vec::new() },
                  vec![two, spine[0].clone()],
                ));
                let shift_left_id = self.prims.nat_shift_left.as_ref().unwrap().clone();
                return Ok(Some(Val::mk_neutral(
                  Head::Const { id: shift_left_id, levels: Vec::new() },
                  vec![two_x, pred_thunk],
                )));
              }
            } else if Primitives::<M>::addr_matches(&self.prims.nat_shift_right, &addr) {
              // shiftRight x (succ y) = (shiftRight x y) / 2
              if let Some(div_id) = self.prims.nat_div.as_ref().cloned() {
                let shift_right_id = self.prims.nat_shift_right.as_ref().unwrap().clone();
                let inner = mk_thunk_val(Val::mk_neutral(
                  Head::Const { id: shift_right_id, levels: Vec::new() },
                  vec![spine[0].clone(), pred_thunk],
                ));
                let two = mk_thunk_val(Val::mk_lit(Literal::NatVal(Nat::from(2u64))));
                return Ok(Some(Val::mk_neutral(
                  Head::Const { id: div_id, levels: Vec::new() },
                  vec![inner, two],
                )));
              }
            } else if Primitives::<M>::addr_matches(&self.prims.nat_beq, &addr) {
              // beq (succ x) (succ y) = beq x y
              if let Some(pred_thunk_a) = extract_succ_pred(&a, self.prims) {
                let beq_id = self.prims.nat_beq.as_ref().unwrap().clone();
                return Ok(Some(Val::mk_neutral(
                  Head::Const { id: beq_id, levels: Vec::new() },
                  vec![pred_thunk_a, pred_thunk],
                )));
              } else if is_nat_zero_val(&a, self.prims) {
                // beq 0 (succ y) = false
                if let Some(f) = &self.prims.bool_false {
                  if let Some(bt) = &self.prims.bool_type {
                    return Ok(Some(Val::mk_ctor(f.clone(), Vec::new(), 0, 0, 0, bt.addr.clone(), Vec::new())));
                  }
                }
              }
            } else if Primitives::<M>::addr_matches(&self.prims.nat_ble, &addr) {
              // ble (succ x) (succ y) = ble x y
              if let Some(pred_thunk_a) = extract_succ_pred(&a, self.prims) {
                let ble_id = self.prims.nat_ble.as_ref().unwrap().clone();
                return Ok(Some(Val::mk_neutral(
                  Head::Const { id: ble_id, levels: Vec::new() },
                  vec![pred_thunk_a, pred_thunk],
                )));
              } else if is_nat_zero_val(&a, self.prims) {
                // ble 0 (succ y) = true
                if let Some(t) = &self.prims.bool_true {
                  if let Some(bt) = &self.prims.bool_type {
                    return Ok(Some(Val::mk_ctor(t.clone(), Vec::new(), 1, 0, 0, bt.addr.clone(), Vec::new())));
                  }
                }
              }
            }
          } else {
            // Second arg is not succ — check if first arg is succ for beq/ble edge cases
            if let Some(_) = extract_succ_pred(&a, self.prims) {
              if Primitives::<M>::addr_matches(&self.prims.nat_beq, addr) && is_nat_zero_val(&b, self.prims) {
                // beq (succ x) 0 = false
                if let Some(f) = &self.prims.bool_false {
                  if let Some(bt) = &self.prims.bool_type {
                    return Ok(Some(Val::mk_ctor(f.clone(), Vec::new(), 0, 0, 0, bt.addr.clone(), Vec::new())));
                  }
                }
              } else if Primitives::<M>::addr_matches(&self.prims.nat_ble, addr) && is_nat_zero_val(&b, self.prims) {
                // ble (succ x) 0 = false
                if let Some(f) = &self.prims.bool_false {
                  if let Some(bt) = &self.prims.bool_type {
                    return Ok(Some(Val::mk_ctor(f.clone(), Vec::new(), 0, 0, 0, bt.addr.clone(), Vec::new())));
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
        head: Head::Const { id, .. },
        spine,
      } => {
        let addr = &id.addr;
        let is_reduce_bool =
          Primitives::<M>::addr_matches(&self.prims.reduce_bool, addr);
        let is_reduce_nat =
          Primitives::<M>::addr_matches(&self.prims.reduce_nat, addr);

        if !is_reduce_bool && !is_reduce_nat {
          return Ok(None);
        }

        if spine.is_empty() {
          return Ok(None);
        }

        let arg = self.force_thunk(&spine[0])?;
        // The argument should be a constant whose definition we fully
        // evaluate
        let (arg_addr, arg_levels) = match arg.inner() {
          ValInner::Neutral {
            head: Head::Const { id, levels },
            ..
          } => (id.addr.clone(), levels.clone()),
          _ => return Ok(None),
        };

        // Look up the definition
        let (body, num_levels) = match self.env.find_by_addr(&arg_addr) {
          Some(KConstantInfo::Definition(d)) => {
            (d.value.clone(), d.cv.num_levels)
          }
          _ => return Ok(None),
        };

        // Instantiate universe levels if needed
        let body = if num_levels == 0 {
          body
        } else {
          self.instantiate_levels(&body, &arg_levels)
        };

        // Fully evaluate (empty env — definition bodies are closed)
        let result = self.eval(&body, &empty_env())?;
        let result = self.whnf_val(&result, 0)?;

        // Validate the result is a concrete value, matching the Lean kernel
        // (Infer.lean:644-658). Without this, non-concrete terms could
        // propagate through native_decide, creating a soundness gap.
        if is_reduce_bool {
          // Check both Ctor and Neutral forms (the Lean kernel does too,
          // via isBoolTrue which matches both .neutral and .ctor).
          let is_bool = |addr: &Address, spine_empty: bool| -> bool {
            spine_empty
              && (Primitives::<M>::addr_matches(&self.prims.bool_true, addr)
                || Primitives::<M>::addr_matches(&self.prims.bool_false, addr))
          };
          let ok = match result.inner() {
            ValInner::Ctor { id, spine, .. } => is_bool(&id.addr, spine.is_empty()),
            ValInner::Neutral {
              head: Head::Const { id, .. },
              spine,
            } => is_bool(&id.addr, spine.is_empty()),
            _ => false,
          };
          if !ok {
            return Err(TcError::KernelException {
              msg: "reduceBool: constant did not reduce to Bool.true or Bool.false".into(),
            });
          }
        } else {
          // is_reduce_nat: accept Lit(NatVal), Ctor(nat_zero), or
          // Neutral(nat_zero) — same as extract_nat_val.
          if extract_nat_val(&result, self.prims).is_none() {
            return Err(TcError::KernelException {
              msg: "reduceNat: constant did not reduce to a Nat literal".into(),
            });
          }
        }

        self.stats.native_reduces += 1;

        // Canonicalize the result to match the lean4 reference kernel:
        // reduceBool → mk_bool_true()/mk_bool_false() (canonical Ctor)
        // reduceNat  → mk_lit(literal(nat(...))) (canonical Lit)
        if is_reduce_bool {
          let is_true = match result.inner() {
            ValInner::Ctor { id, .. } => Primitives::<M>::addr_matches(&self.prims.bool_true, &id.addr),
            ValInner::Neutral { head: Head::Const { id, .. }, .. } => {
              Primitives::<M>::addr_matches(&self.prims.bool_true, &id.addr)
            }
            _ => false,
          };
          let (ctor_id, cidx) = if is_true {
            (self.prims.bool_true.as_ref().unwrap().clone(), 1usize)
          } else {
            (self.prims.bool_false.as_ref().unwrap().clone(), 0usize)
          };
          let induct_addr = self.prims.bool_type.as_ref().unwrap().addr.clone();
          Ok(Some(Val::mk_ctor(
            ctor_id, Vec::new(),
            cidx, 0, 0, induct_addr, Vec::new(),
          )))
        } else {
          // reduceNat: extract and rewrap as canonical Lit
          let n = extract_nat_val(&result, self.prims).unwrap();
          Ok(Some(Val::mk_lit(Literal::NatVal(n))))
        }
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
      // Direct lookup
      if let Some((orig, cached)) = self.whnf_cache.get(&key) {
        if orig.ptr_eq(v) {
          self.stats.cache_hits += 1;
          self.stats.whnf_cache_hits += 1;
          return Ok(cached.clone());
        }
      }
      // Second-chance lookup via equiv root
      if let Some(root_ptr) = self.equiv_manager.find_root_ptr(key) {
        if root_ptr != key {
          if let Some((orig_root, cached)) = self.whnf_cache.get(&root_ptr) {
            if self.trace {
              self.trace_msg(&format!("[whnf_val EQUIV-HIT] v={v}  root_orig={orig_root}  cached={cached}"));
            }
            self.stats.cache_hits += 1;
            self.stats.whnf_equiv_hits += 1;
            return Ok(cached.clone());
          }
        }
      }
      self.stats.whnf_cache_misses += 1;
    }

    if delta_steps > max_steps {
      return Err(TcError::KernelException {
        msg: format!("delta step limit exceeded ({max_steps})"),
      });
    }

    // Step 1: Structural WHNF (projection, iota, K, quotient)
    let v1 = self.whnf_core_val(v, false, false)?;

    // Step 2: Nat primitive reduction
    let result = if let Some(v2) = self.try_reduce_nat_val(&v1)? {
      self.whnf_val(&v2, delta_steps + 1)?
    // Step 2b: Block delta-unfolding of fully-applied nat primitives when
    // all args are ground (no fvars). When args contain fvars, the recursor
    // definition can still make progress by pattern-matching on constructors
    // (e.g. Nat.ble (succ n) m), so we must allow delta unfolding.
    } else if self.is_fully_applied_nat_prim(&v1) && !self.nat_prim_has_fvar_arg(&v1)? {
      v1
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
      // Register v ≡ whnf(v) in equiv manager
      if !v.ptr_eq(&result) {
        self.add_equiv_val(v, &result);
      }
      // Also insert under root for equiv-class sharing
      if let Some(root_ptr) = self.equiv_manager.find_root_ptr(key) {
        if root_ptr != key {
          self.whnf_cache.insert(root_ptr, (v.clone(), result.clone()));
        }
      }
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
    KExprData::Const(id, ls) => {
      let new_ls: Vec<_> =
        ls.iter().map(|l| inst_bulk_reduce(levels, l)).collect();
      KExpr::cnst(id.clone(), new_ls)
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
    KExprData::Proj(type_id, idx, s) => {
      KExpr::proj(type_id.clone(), *idx, inst_levels_expr(s, levels))
    }
  }
}
