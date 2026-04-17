//! `.casesOn` generation: per-inductive eliminator without inductive hypotheses.
//!
//! `.casesOn` is a **definition** (not a recursor) whose value calls `.rec` with:
//! - Non-target motives replaced by `λ _ ... _, PUnit`
//! - Non-target minors replaced by `λ _ ... _, PUnit.unit`
//! - Target minors rebuilt to strip IH fields (keep only non-recursive params)
//!
//! casesOn binder order: params, target_motive, indices, major, target_minors
//! (same reordering as recOn: indices+major before minors)
//!
//! Follows `refs/lean4/src/library/constructions/cases_on.cpp`.

use crate::ix::compile::aux_gen::AuxDef;
use crate::ix::env::{
  BinderInfo, ConstantInfo, Env as LeanEnv, Expr as LeanExpr, ExprData, Level,
  Name, RecursorVal,
};

use super::below::{mk_punit_unit, punit_const};
use super::expr_utils::{
  LocalDecl, count_foralls, find_motive_fvar, forall_telescope, fresh_fvar,
  instantiate1, mk_app_n, mk_const, mk_forall, mk_lambda, subst_fvar,
};

/// Replace the innermost return type of a forall chain with `unit`.
///
/// Matches Lean's `mk_pi_unit` in `cases_on.cpp`:
/// `∀ (x : A) (y : B), C x y` → `∀ (x : A) (y : B), unit`
fn mk_pi_unit(e: &LeanExpr, unit: &LeanExpr) -> LeanExpr {
  match e.as_data() {
    ExprData::ForallE(name, dom, body, bi, _) => LeanExpr::all(
      name.clone(),
      dom.clone(),
      mk_pi_unit(body, unit),
      bi.clone(),
    ),
    _ => unit.clone(),
  }
}

// NOTE: `_mk_unit_type` / `_mk_unit_val` (Prop-case helpers that would
// use `True` / `True.intro` when `elim_to_prop` holds) were removed in
// Round 4 of the adversarial review cleanup. They were documentation of
// how a branching `mk_unit` *could* be written, but the live pipeline
// always uses `PUnit.{l}` and `PUnit.unit.{l}` via `punit_const` /
// `mk_punit_unit` — matching Lean's actual `cases_on.cpp:378`. If a Prop
// branching helper is ever needed, resurrect from git history.

/// Generate a `.casesOn` definition from a canonical `.rec`.
///
/// Returns `None` if the recursor type cannot be decomposed.
///
/// Uses FVar-based construction: opens the rec type into FVars, builds
/// casesOn type and value using FVar references, then abstracts with
/// mk_forall/mk_lambda.
pub(crate) fn generate_cases_on(
  name: &Name,
  rec_val: &RecursorVal,
  lean_env: &LeanEnv,
) -> Option<AuxDef> {
  let n_params = rec_val.num_params.to_u64()? as usize;
  let n_motives = rec_val.num_motives.to_u64()? as usize;
  let n_minors = rec_val.num_minors.to_u64()? as usize;
  let n_indices = rec_val.num_indices.to_u64()? as usize;

  // Extract target inductive name from "A.casesOn" → "A"
  let target_ind = match name.as_data() {
    crate::ix::env::NameData::Str(parent, s, _) if s == "casesOn" => {
      parent.clone()
    },
    _ => return None,
  };

  // Find target index in rec_val.all
  let target_idx = rec_val.all.iter().position(|n| *n == target_ind)?;

  // Determine elimination level
  let ind_n_lparams = match lean_env.get(&target_ind).as_deref() {
    Some(ConstantInfo::InductInfo(v)) => v.cnst.level_params.len(),
    _ => return None,
  };
  let elim_to_prop = rec_val.cnst.level_params.len() == ind_n_lparams;
  let elim_lvl = if elim_to_prop {
    Level::zero()
  } else {
    Level::param(rec_val.cnst.level_params[0].clone())
  };

  // Count constructors per inductive
  let ctor_counts: Vec<usize> = rec_val
    .all
    .iter()
    .map(|ind_name| match lean_env.get(ind_name).as_deref() {
      Some(ConstantInfo::InductInfo(v)) => v.ctors.len(),
      _ => 0,
    })
    .collect();

  // Universe levels for the rec application
  let rec_univs: Vec<Level> = rec_val
    .cnst
    .level_params
    .iter()
    .map(|lp| Level::param(lp.clone()))
    .collect();

  // === Step 1: Open rec type into FVars ===

  let (param_fvars, param_decls, after_params) =
    forall_telescope(&rec_val.cnst.typ, n_params, "cop", 0);

  // Open ALL motives as FVars (needed for IH detection in minor fields).
  // Only the target motive becomes a casesOn binder; non-target FVars will
  // be replaced in the final value by PUnit functions.
  let mut motive_fvars: Vec<LeanExpr> = Vec::new();
  let mut all_motive_decls: Vec<LocalDecl> = Vec::new();
  let mut after_motives = after_params;
  for mi in 0..n_motives {
    if let ExprData::ForallE(bname, dom, body, bi, _) = after_motives.as_data()
    {
      let (fv_name, fv) = fresh_fvar("com", mi);
      all_motive_decls.push(LocalDecl {
        fvar_name: fv_name,
        binder_name: bname.clone(),
        domain: dom.clone(),
        info: bi.clone(),
      });
      motive_fvars.push(fv.clone());
      after_motives = instantiate1(body, &fv);
    }
  }
  let target_motive_decl = all_motive_decls[target_idx].clone();

  // Open minors (keep FVar-based domains; dummy FVars for instantiation)
  let mut minor_doms: Vec<LeanExpr> = Vec::new();
  let mut after_minors = after_motives;
  for mi in 0..n_minors {
    if let ExprData::ForallE(_, dom, body, _, _) = after_minors.as_data() {
      minor_doms.push(dom.clone());
      let (_, dummy) = fresh_fvar("cox", mi);
      after_minors = instantiate1(body, &dummy);
    }
  }

  // Open indices and major
  let (index_fvars, index_decls, after_indices) =
    forall_telescope(&after_minors, n_indices, "coi", 0);
  let (major_fvars, major_decls, rec_return_type) =
    forall_telescope(&after_indices, 1, "coj", 0);

  // === Step 2: Build casesOn binder list ===

  let mut co_decls: Vec<LocalDecl> = Vec::new();
  co_decls.extend(param_decls.iter().cloned()); // params
  co_decls.push(target_motive_decl); // target motive only
  co_decls.extend(index_decls.iter().cloned()); // indices
  co_decls.extend(major_decls.iter().cloned()); // major

  // === Step 3: Build stripped target minors + minor wrappers for rec ===

  // Track which minors belong to target inductive
  let mut minor_offset = 0usize;
  let mut target_minor_range = 0..0usize;
  for (j, &count) in ctor_counts.iter().enumerate() {
    if j == target_idx {
      target_minor_range = minor_offset..(minor_offset + count);
    }
    minor_offset += count;
  }

  // For each minor, build:
  // - If target: casesOn minor binder (stripped of IH) + rec arg wrapper
  // - If non-target: rec arg = λ (all_fields), PUnit.unit
  struct MinorInfo {
    rec_arg: LeanExpr,
  }

  let mut minor_infos: Vec<MinorInfo> = Vec::new();

  for (mi, minor_dom) in minor_doms.iter().enumerate() {
    let is_target = target_minor_range.contains(&mi);

    if is_target {
      // Open minor fields
      let n_fields = count_foralls(minor_dom);
      let (field_fvars, field_decls, minor_ret) =
        forall_telescope(minor_dom, n_fields, &format!("cof{mi}"), 0);

      // Classify fields: non-IH go into casesOn minor, IH fields are dropped
      let mut non_ih_decls: Vec<LocalDecl> = Vec::new();
      let mut non_ih_fvars: Vec<LeanExpr> = Vec::new();
      let mut wrapper_decls: Vec<LocalDecl> = Vec::new(); // all fields for the rec lambda

      for (decl, fvar) in field_decls.into_iter().zip(field_fvars.into_iter()) {
        let motive_idx = find_motive_fvar(&decl.domain, &motive_fvars);
        if let Some(idx) = motive_idx {
          if idx == target_idx {
            // Target-motive IH: keep original domain in wrapper.
            wrapper_decls.push(decl);
          } else {
            // Non-target-motive IH: wrap domain with mk_pi_unit.
            // Matches C++ lines 134-140: replace type with `∀ args, PUnit`.
            let wrapped_domain =
              mk_pi_unit(&decl.domain, &punit_const(&elim_lvl));
            wrapper_decls.push(LocalDecl { domain: wrapped_domain, ..decl });
          }
        } else {
          // Non-IH field: appears in both wrapper and casesOn minor
          non_ih_decls.push(decl.clone());
          non_ih_fvars.push(fvar.clone());
          wrapper_decls.push(decl);
        }
      }

      // Build casesOn minor type: ∀ (non_ih_fields...), minor_ret
      let co_minor_type = mk_forall(minor_ret.clone(), &non_ih_decls);

      // Get original minor name from rec type for the casesOn binder name
      // (use rec_val's constructor name suffix as binder name)
      let co_minor_binder_name =
        get_minor_name(mi, &target_minor_range, &target_ind, lean_env);
      let (co_fv_name, co_fv) = fresh_fvar("coq", mi);
      co_decls.push(LocalDecl {
        fvar_name: co_fv_name,
        binder_name: co_minor_binder_name,
        domain: co_minor_type,
        info: BinderInfo::Default,
      });

      // Build rec arg wrapper: λ (all_fields), co_minor_fvar(non_ih_fvars)
      let wrapper_body = mk_app_n(co_fv.clone(), &non_ih_fvars);
      let rec_arg = mk_lambda(wrapper_body, &wrapper_decls);

      minor_infos.push(MinorInfo { rec_arg });
    } else {
      // Non-target minor: rec arg = λ (all_fields), PUnit.unit
      // IH fields targeting non-target motives need mk_pi_unit wrapping
      // (matching Lean's process_minor which applies mk_pi_unit for all
      // non-main IH fields, regardless of whether the minor itself is main).
      let n_fields = count_foralls(minor_dom);
      let (_, field_decls, _) =
        forall_telescope(minor_dom, n_fields, &format!("con{mi}"), 0);
      let wrapped_decls: Vec<LocalDecl> = field_decls
        .into_iter()
        .map(|decl| {
          if let Some(idx) = find_motive_fvar(&decl.domain, &motive_fvars)
            && idx != target_idx
          {
            // Non-target-motive IH: wrap domain
            return LocalDecl {
              domain: mk_pi_unit(&decl.domain, &punit_const(&elim_lvl)),
              ..decl
            };
          }
          decl
        })
        .collect();
      let rec_arg = mk_lambda(mk_punit_unit(&elim_lvl), &wrapped_decls);
      minor_infos.push(MinorInfo { rec_arg });
    }
  }

  // === Step 4: Substitute non-target motive FVars ===
  // Non-target motive FVars may appear in index/major/minor domains.
  // Replace them with PUnit functions before building final type and value.
  let mut non_target_substs: Vec<(Name, LeanExpr)> = Vec::new();
  for (j, decl) in all_motive_decls.iter().enumerate() {
    if j == target_idx {
      continue;
    }
    let motive_type = &decl.domain;
    let n_motive_args = count_foralls(motive_type);
    let (_, motive_arg_decls, _) =
      forall_telescope(motive_type, n_motive_args, &format!("cos{j}"), 0);
    let fun_unit = mk_lambda(punit_const(&elim_lvl), &motive_arg_decls);
    non_target_substs.push((decl.fvar_name.clone(), fun_unit));
  }

  // Apply substitutions to co_decls domains and rec_return_type
  let mut co_ret = rec_return_type.clone();
  for (fv_name, replacement) in &non_target_substs {
    co_ret = subst_fvar(&co_ret, fv_name, replacement);
  }
  let co_decls: Vec<LocalDecl> = co_decls
    .into_iter()
    .map(|mut d| {
      for (fv_name, replacement) in &non_target_substs {
        d.domain = subst_fvar(&d.domain, fv_name, replacement);
      }
      d
    })
    .collect();

  // === Step 5: Build casesOn type ===

  let co_type = mk_forall(co_ret, &co_decls);

  // === Step 5: Build casesOn value ===

  let mut val = mk_const(&rec_val.cnst.name, &rec_univs);

  // Apply params
  val = mk_app_n(val, &param_fvars);

  // Apply motives: target motive directly, others as λ targs, unit_type
  for (j, motive_decl) in all_motive_decls.iter().enumerate().take(n_motives) {
    if j == target_idx {
      val = LeanExpr::app(val, motive_fvars[target_idx].clone());
    } else {
      // Build λ (motive_args...), unit_type
      let motive_type = &motive_decl.domain;
      let n_motive_args = count_foralls(motive_type);
      let (_, motive_arg_decls, _) =
        forall_telescope(motive_type, n_motive_args, &format!("cou{j}"), 0);
      let fun_unit = mk_lambda(punit_const(&elim_lvl), &motive_arg_decls);
      val = LeanExpr::app(val, fun_unit);
    }
  }

  // Apply minors
  for info in &minor_infos {
    val = LeanExpr::app(val, info.rec_arg.clone());
  }

  // Apply indices and major
  val = mk_app_n(val, &index_fvars);
  val = mk_app_n(val, &major_fvars);

  // Replace non-target motive FVars in the value (same substitutions as type).
  for (fv_name, replacement) in &non_target_substs {
    val = subst_fvar(&val, fv_name, replacement);
  }

  let co_value = mk_lambda(val, &co_decls);

  Some(AuxDef {
    name: name.clone(),
    level_params: rec_val.cnst.level_params.clone(),
    typ: co_type,
    value: co_value,
  })
}

/// Extract a minor premise name for the casesOn binder.
///
/// Uses the constructor name suffix (e.g., "A.mk" → "mk").
fn get_minor_name(
  minor_idx: usize,
  target_range: &std::ops::Range<usize>,
  target_ind: &Name,
  lean_env: &LeanEnv,
) -> Name {
  let ctor_idx = minor_idx - target_range.start;
  if let Some(ConstantInfo::InductInfo(v)) = lean_env.get(target_ind).as_deref()
    && let Some(ctor_name) = v.ctors.get(ctor_idx)
  {
    // Strip prefix to get suffix (e.g., "A.mk" → "mk")
    if let Some(suffix) = ctor_name.strip_prefix(target_ind) {
      return Name::anon().append_components(&suffix);
    }
    return ctor_name.clone();
  }
  Name::str(Name::anon(), format!("minor_{}", ctor_idx))
}
