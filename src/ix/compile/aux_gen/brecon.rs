//! Canonical `.brecOn` generation for alpha-collapsed inductive blocks.
//!
//! **Prop-level** (inductive predicates): generates a single theorem per class.
//!   `I_i.brecOn = λ params motives t F_1..F_n => F_i t (I_i.rec below_motives below_minors t)`
//!   Reference: `refs/lean4/src/Lean/Meta/IndPredBelow.lean:185-208`
//!
//! **Type-level** (large eliminators): generates `.brecOn.go` + `.brecOn` per class.
//!   `.brecOn.go` uses PProd-wrapped motives; `.brecOn` projects first component.
//!   Reference: `refs/lean4/src/Lean/Meta/Constructions/BRecOn.lean:191-308`

use crate::ix::env::{
  BinderInfo, ConstantInfo, Env as LeanEnv, Expr as LeanExpr, ExprData,
  InductiveVal, Level, LevelData, Name, RecursorVal,
};
use crate::ix::ixon::CompileError;
use lean_ffi::nat::Nat;

use super::below::{
  BelowConstant, get_ind_sort_level, level_max, mk_pprod, mk_pprod_mk,
  mk_punit_unit,
};

use super::expr_utils::{
  LocalDecl, decompose_apps, find_motive_fvar, forall_telescope, fresh_fvar,
  instantiate1, mk_app_n, mk_const, mk_forall, mk_lambda,
};

/// A generated `.brecOn` definition (or `.brecOn.go`).
#[derive(Clone)]
pub(crate) struct BRecOnDef {
  pub name: Name,
  pub level_params: Vec<Name>,
  pub typ: LeanExpr,
  pub value: LeanExpr,
}

/// Generate all `.brecOn` (and `.brecOn.go` for Type-level) constants.
///
/// Called after Phase 2 (`.below` generation). Uses the canonical recursors
/// from Phase 1 and the `.below` constants from Phase 2.
/// `is_prop` determines whether to generate Prop-level (single theorem) or
/// Type-level (`.brecOn.go` + `.brecOn`) forms.
pub(crate) fn generate_brecon_constants(
  sorted_classes: &[Vec<Name>],
  canonical_recs: &[(Name, RecursorVal)],
  below_consts: &[BelowConstant],
  lean_env: &LeanEnv,
  is_prop: bool,
) -> Result<Vec<BRecOnDef>, CompileError> {
  let n_classes = sorted_classes.len();
  if n_classes == 0 || canonical_recs.is_empty() || below_consts.is_empty() {
    return Ok(vec![]);
  }

  let mut results = Vec::new();

  for ci in 0..n_classes.min(canonical_recs.len()).min(below_consts.len()) {
    let (_, rec_val) = &canonical_recs[ci];
    let class_rep = &sorted_classes[ci][0];
    let ind = match lean_env.get(class_rep) {
      Some(ConstantInfo::InductInfo(v)) => v,
      _ => continue,
    };

    // Only generate brecOn for recursive inductives (matching Lean's guard:
    // `unless indVal.isRec do return` in BRecOn.lean:313 and IndPredBelow.lean:215).
    // Also skip inductives with nested occurrences for now — their brecOn
    // references auxiliary `.below_N` constants that aren't yet generated.
    if !ind.is_rec || ind.num_nested.to_u64().unwrap_or(0) > 0 {
      continue;
    }

    if !is_prop {
      // Type-level: generate .brecOn.go + .brecOn + .brecOn.eq (BRecOn.lean path)
      let defs = build_type_brecon_fvar(
        ci,
        rec_val,
        ind,
        lean_env,
        n_classes,
        sorted_classes,
        below_consts,
        canonical_recs,
      )?;
      results.extend(defs);
    } else {
      // Prop-level: generate single .brecOn theorem (IndPredBelow.lean path)
      let def = build_prop_brecon(
        ci,
        rec_val,
        ind,
        lean_env,
        n_classes,
        sorted_classes,
        below_consts,
      )?;
      results.push(def);
    }
  }

  Ok(results)
}

// =========================================================================
// Prop-level brecOn
// =========================================================================

/// Build Prop-level `.brecOn` for class `ci`.
///
/// ```text
/// I_i.brecOn : ∀ {params} {motives} (t : I_i params)
///   (F_1 : ∀ majors, I_1.below params motives majors → motive_1 majors)
///   ...
///   → motive_i t
///
/// I_i.brecOn = λ {params} {motives} t F_1..F_n =>
///   F_i t (I_i.rec params below_motives below_minors t)
/// ```
fn build_prop_brecon(
  ci: usize,
  rec_val: &RecursorVal,
  ind: &InductiveVal,
  _lean_env: &LeanEnv,
  n_classes: usize,
  sorted_classes: &[Vec<Name>],
  below_consts: &[BelowConstant],
) -> Result<BRecOnDef, CompileError> {
  let n_params = rec_val.num_params.to_u64().unwrap_or(0) as usize;
  let n_motives = rec_val.num_motives.to_u64().unwrap_or(0) as usize;
  let n_minors = rec_val.num_minors.to_u64().unwrap_or(0) as usize;
  let n_indices = ind.num_indices.to_u64().unwrap_or(0) as usize;
  let ind_level_params = &ind.cnst.level_params;

  // For Prop brecOn with large elimination (drec), substitute u -> Level::zero()
  let large_elim = rec_val.cnst.level_params.len() > ind_level_params.len();
  let rec_val = if large_elim && !rec_val.cnst.level_params.is_empty() {
    let u_param = &rec_val.cnst.level_params[0];
    let mut rv = rec_val.clone();
    rv.cnst.typ = subst_level_in_expr(&rv.cnst.typ, u_param, &Level::zero());
    for rule in &mut rv.rules {
      rule.rhs = subst_level_in_expr(&rule.rhs, u_param, &Level::zero());
    }
    rv
  } else {
    rec_val.clone()
  };
  let rec_val = &rec_val;

  let brecon_name = Name::str(ind.cnst.name.clone(), "brecOn".to_string());

  let below_names: Vec<Name> = (0..n_classes)
    .map(|j| Name::str(sorted_classes[j][0].clone(), "below".to_string()))
    .collect();

  let below_ctor_names: Vec<Vec<Name>> = (0..n_classes)
    .map(|j| {
      below_consts
        .get(j)
        .map(|bc| match bc {
          BelowConstant::Indc(bi) => {
            bi.ctors.iter().map(|c| c.name.clone()).collect()
          },
          _ => vec![],
        })
        .unwrap_or_default()
    })
    .collect();

  // --- Phase 1: Open rec type into FVars ---
  let (param_fvars, param_decls, after_params) =
    forall_telescope(&rec_val.cnst.typ, n_params, "pbp", 0);

  // Open motives (make implicit)
  let mut motive_fvars: Vec<LeanExpr> = Vec::new();
  let mut motive_decls: Vec<LocalDecl> = Vec::new();
  let mut after_motives = after_params;
  for mi in 0..n_motives {
    if let ExprData::ForallE(name, dom, body, _, _) = after_motives.as_data() {
      let (fv_name, fv) = fresh_fvar("pbm", mi);
      motive_decls.push(LocalDecl {
        fvar_name: fv_name,
        binder_name: name.clone(),
        domain: dom.clone(),
        info: BinderInfo::Implicit,
      });
      motive_fvars.push(fv.clone());
      after_motives = instantiate1(body, &fv);
    }
  }

  // Open minors (keep domains for building below_minors later)
  let mut minor_doms: Vec<LeanExpr> = Vec::new();
  let mut after_minors = after_motives;
  for mi in 0..n_minors {
    if let ExprData::ForallE(_, dom, body, _, _) = after_minors.as_data() {
      minor_doms.push(dom.clone());
      let (_, dummy) = fresh_fvar("pbx", mi);
      after_minors = instantiate1(body, &dummy);
    }
  }

  // Open indices and major
  let (index_fvars, index_decls, after_indices) =
    forall_telescope(&after_minors, n_indices, "pbi", 0);
  let (major_fvars, major_decls, _) =
    forall_telescope(&after_indices, 1, "pbj", 0);

  // --- Phase 2: Build F binders ---
  // F_j : ∀ (motive_args...) (below_proof : I_j.below params motives args), motive_j args
  let mut f_fvars: Vec<LeanExpr> = Vec::new();
  let mut f_decls: Vec<LocalDecl> = Vec::new();
  let ind_univs: Vec<Level> =
    ind_level_params.iter().map(|lp| Level::param(lp.clone())).collect();

  for j in 0..n_motives {
    // Open motive_j's type to get inner binders (indices + major for that motive)
    let motive_type = &motive_decls[j].domain;
    let n_motive_args = super::expr_utils::count_foralls(motive_type);
    let (inner_fvars, inner_decls, _inner_sort) =
      forall_telescope(motive_type, n_motive_args, &format!("pbfa{j}"), 0);

    // Build below_app: I_j.below params motives inner_args
    let below_app = {
      let mut app = mk_const(&below_names[j], &ind_univs);
      app = mk_app_n(app, &param_fvars);
      app = mk_app_n(app, &motive_fvars);
      app = mk_app_n(app, &inner_fvars);
      app
    };

    // Build motive_app: motive_j inner_args
    let motive_app = mk_app_n(motive_fvars[j].clone(), &inner_fvars);

    // F_j type body: below_app → motive_app
    // Create a below_proof binder, then build motive_app as the return
    let (below_fv_name, _below_fv) = fresh_fvar(&format!("pbfb{j}"), 0);
    let below_decl = LocalDecl {
      fvar_name: below_fv_name,
      binder_name: Name::anon(),
      domain: below_app,
      info: BinderInfo::Default,
    };

    // F_j type = ∀ inner_args below_proof, motive_app
    let f_type_binders: Vec<LocalDecl> =
      inner_decls.into_iter().chain(std::iter::once(below_decl)).collect();
    let f_type = mk_forall(motive_app, &f_type_binders);

    let f_name = Name::str(Name::anon(), format!("F_{}", j + 1));
    let (fj_fv_name, fj_fv) = fresh_fvar("pbf", j);
    f_decls.push(LocalDecl {
      fvar_name: fj_fv_name,
      binder_name: f_name,
      domain: f_type,
      info: BinderInfo::Default,
    });
    f_fvars.push(fj_fv);
  }

  // --- Phase 3: Build return type (for type) ---
  // motive_ci index_fvars major_fvar
  let ret_type =
    mk_app_n(mk_app_n(motive_fvars[ci].clone(), &index_fvars), &major_fvars);

  // --- Phase 4: Build value body ---
  // F_ci index_fvars major (I_ci.rec params below_motives below_minors index_fvars major)

  // Build rec application
  let rec_univs: Vec<Level> = rec_val
    .cnst
    .level_params
    .iter()
    .enumerate()
    .map(|(i, lp)| {
      if large_elim && i == 0 {
        Level::zero()
      } else {
        Level::param(lp.clone())
      }
    })
    .collect();
  let mut rec_app = mk_const(&rec_val.cnst.name, &rec_univs);

  // Apply params
  rec_app = mk_app_n(rec_app, &param_fvars);

  // Apply below_motives: I_j.below params motives (partial application)
  for below_name in below_names.iter().take(n_motives) {
    let below_motive = mk_app_n(
      mk_app_n(mk_const(below_name, &ind_univs), &param_fvars),
      &motive_fvars,
    );
    rec_app = LeanExpr::app(rec_app, below_motive);
  }

  // Apply below_minors: for each ctor, build λ (fields) => below_ctor params motives args
  let mut global_ctor_idx = 0usize;
  for j in 0..n_classes {
    let class_ctor_names: &[Name] =
      below_ctor_names.get(j).map_or(&[], |v| v.as_slice());

    for (cidx, below_ctor_name) in class_ctor_names.iter().enumerate() {
      if global_ctor_idx + cidx >= minor_doms.len() {
        break;
      }
      let minor_dom = &minor_doms[global_ctor_idx + cidx];

      // Build the below minor using FVars
      let minor = build_prop_below_minor_fvar(
        minor_dom,
        below_ctor_name,
        &param_fvars,
        &motive_fvars,
        &f_fvars,
        &below_names,
        &ind_univs,
      );
      rec_app = LeanExpr::app(rec_app, minor);
    }
    global_ctor_idx += class_ctor_names.len();
  }

  // Apply indices and major
  rec_app = mk_app_n(rec_app, &index_fvars);
  rec_app = mk_app_n(rec_app, &major_fvars);

  // F_ci index_fvars major rec_app
  let val_body = LeanExpr::app(
    mk_app_n(mk_app_n(f_fvars[ci].clone(), &index_fvars), &major_fvars),
    rec_app,
  );

  // --- Phase 5: Close with mk_forall / mk_lambda ---
  let all_decls: Vec<LocalDecl> = param_decls
    .into_iter()
    .chain(motive_decls)
    .chain(index_decls)
    .chain(major_decls)
    .chain(f_decls)
    .collect();

  let typ = mk_forall(ret_type, &all_decls);
  let val = mk_lambda(val_body, &all_decls);

  Ok(BRecOnDef {
    name: brecon_name,
    level_params: ind_level_params.clone(),
    typ,
    value: val,
  })
}

/// Build a Prop-level below minor for one constructor (FVar-based).
///
/// Given minor domain (in FVar form: params + motives substituted):
///   `∀ (fields...) (ih_fields...), motive_j (ctor_args)`
///
/// Builds: `λ (fields_and_ihs) => below_ctor params motives args`
///
/// For each IH field (head is motive FVar):
///   - Replace binder domain with `I_{j'}.below params motives args`
///   - Add below arg (ih FVar) and proof arg (F_{j'+1} applied to args + ih)
fn build_prop_below_minor_fvar(
  minor_dom: &LeanExpr,
  below_ctor_name: &Name,
  param_fvars: &[LeanExpr],
  motive_fvars: &[LeanExpr],
  f_fvars: &[LeanExpr],
  below_names: &[Name],
  ind_univs: &[Level],
) -> LeanExpr {
  // Open all minor fields with forall_telescope.
  // After this, field domains reference motive FVars directly.
  let n_fields = super::expr_utils::count_foralls(minor_dom);
  let (field_fvars, field_decls, _return_type) =
    forall_telescope(minor_dom, n_fields, "pbmf", 0);

  // Classify fields and build lambda binders + ctor args
  let mut lambda_decls: Vec<LocalDecl> = Vec::new();
  let mut lambda_fvars: Vec<LeanExpr> = Vec::new();
  let mut ctor_args: Vec<LeanExpr> = Vec::new();

  for (fi, (decl, fvar)) in
    field_decls.into_iter().zip(field_fvars.into_iter()).enumerate()
  {
    if let Some(j_prime) = find_motive_fvar(&decl.domain, motive_fvars) {
      // IH field: replace domain with I_{j'}.below params motives args
      let (_, dom_args) = decompose_apps(&decl.domain);

      // Build below domain: I_{j'}.below params motives dom_args
      let mut below_dom = mk_const(&below_names[j_prime], ind_univs);
      below_dom = mk_app_n(below_dom, param_fvars);
      below_dom = mk_app_n(below_dom, motive_fvars);
      for a in &dom_args {
        below_dom = LeanExpr::app(below_dom, a.clone());
      }

      // Create ih FVar with below domain
      let (ih_fv_name, ih_fv) = fresh_fvar("pbmi", fi);
      lambda_decls.push(LocalDecl {
        fvar_name: ih_fv_name,
        binder_name: Name::str(Name::anon(), "ih".to_string()),
        domain: below_dom,
        info: BinderInfo::Default,
      });
      lambda_fvars.push(ih_fv.clone());

      // ih arg for below ctor
      ctor_args.push(ih_fv.clone());

      // proof arg: build F_{j'+1} applied to dom_args and ih
      // For simple case: F_{j'} dom_args ih_fv
      // For forall case: λ (forall_args) => F_{j'} dom_args_applied (ih_fv forall_args)
      let n_inner_foralls = super::expr_utils::count_foralls(&decl.domain);
      let proof = if n_inner_foralls == 0 {
        // Simple: F_{j'} dom_args ih_fv
        let mut p = f_fvars[j_prime].clone();
        for a in &dom_args {
          p = LeanExpr::app(p, a.clone());
        }
        LeanExpr::app(p, ih_fv)
      } else {
        // Forall: λ (inner_args) => F_{j'} leaf_args (ih_fv inner_args)
        let (inner_fvars, inner_decls, leaf) = forall_telescope(
          &decl.domain,
          n_inner_foralls,
          &format!("pbmp{fi}"),
          0,
        );
        let (_, leaf_args) = decompose_apps(&leaf);

        let mut p = f_fvars[j_prime].clone();
        for a in &leaf_args {
          p = LeanExpr::app(p, a.clone());
        }
        // Apply (ih_fv inner_args)
        let ih_app = mk_app_n(ih_fv, &inner_fvars);
        p = LeanExpr::app(p, ih_app);

        mk_lambda(p, &inner_decls)
      };
      ctor_args.push(proof);
    } else {
      // Non-IH field: pass through
      lambda_decls.push(decl);
      lambda_fvars.push(fvar.clone());
      ctor_args.push(fvar);
    }
  }

  // Build below ctor application: below_ctor params motives ctor_args
  let mut app = mk_const(below_ctor_name, ind_univs);
  app = mk_app_n(app, param_fvars);
  app = mk_app_n(app, motive_fvars);
  app = mk_app_n(app, &ctor_args);

  mk_lambda(app, &lambda_decls)
}

// =========================================================================
// FVar-based Type-level brecOn implementation
// =========================================================================

/// Build Type-level `.brecOn.go`, `.brecOn`, and `.brecOn.eq` (FVar-based).
///
/// This replaces the old BVar-based `build_type_brecon` and all its helpers.
#[allow(clippy::too_many_arguments)]
fn build_type_brecon_fvar(
  ci: usize,
  rec_val: &RecursorVal,
  ind: &InductiveVal,
  lean_env: &LeanEnv,
  n_classes: usize,
  sorted_classes: &[Vec<Name>],
  _below_consts: &[BelowConstant],
  _canonical_recs: &[(Name, RecursorVal)],
) -> Result<Vec<BRecOnDef>, CompileError> {
  let n_params = rec_val.num_params.to_u64().unwrap_or(0) as usize;
  let n_motives = rec_val.num_motives.to_u64().unwrap_or(0) as usize;
  let n_minors = rec_val.num_minors.to_u64().unwrap_or(0) as usize;
  let n_indices = ind.num_indices.to_u64().unwrap_or(0) as usize;
  let ind_level_params = &ind.cnst.level_params;
  let rec_level_params = &rec_val.cnst.level_params;

  let brecon_name = Name::str(ind.cnst.name.clone(), "brecOn".to_string());
  let go_name = Name::str(brecon_name.clone(), "go".to_string());
  let eq_name = Name::str(brecon_name.clone(), "eq".to_string());

  let elim_level = Level::param(rec_level_params[0].clone());
  let ilvl = get_ind_sort_level(&ind.cnst.typ, n_params + n_indices);
  let rlvl = level_max(&ilvl, &elim_level);

  let main_name = &sorted_classes[0][0];
  let below_names: Vec<Name> = (0..n_motives)
    .map(|j| {
      if j < n_classes {
        Name::str(sorted_classes[j][0].clone(), "below".to_string())
      } else {
        let aux_idx = j - n_classes + 1;
        Name::str(main_name.clone(), format!("below_{}", aux_idx))
      }
    })
    .collect();

  let rec_univs: Vec<Level> =
    rec_level_params.iter().map(|lp| Level::param(lp.clone())).collect();
  let _ind_univs: Vec<Level> =
    ind_level_params.iter().map(|lp| Level::param(lp.clone())).collect();

  // --- Phase 1: Open rec type into FVars ---
  let (param_fvars, param_decls, after_params) =
    forall_telescope(&rec_val.cnst.typ, n_params, "tbp", 0);

  let mut motive_fvars: Vec<LeanExpr> = Vec::new();
  let mut motive_decls: Vec<LocalDecl> = Vec::new();
  let mut after_motives = after_params;
  for mi in 0..n_motives {
    if let ExprData::ForallE(name, dom, body, _, _) = after_motives.as_data() {
      let (fv_name, fv) = fresh_fvar("tbm", mi);
      motive_decls.push(LocalDecl {
        fvar_name: fv_name,
        binder_name: name.clone(),
        domain: dom.clone(),
        info: BinderInfo::Implicit,
      });
      motive_fvars.push(fv.clone());
      after_motives = instantiate1(body, &fv);
    }
  }

  // Open minors (keep FVar-based domains for building modified minors)
  let mut minor_doms: Vec<LeanExpr> = Vec::new();
  let mut after_minors = after_motives;
  for mi in 0..n_minors {
    if let ExprData::ForallE(_, dom, body, _, _) = after_minors.as_data() {
      minor_doms.push(dom.clone());
      let (_, dummy) = fresh_fvar("tbx", mi);
      after_minors = instantiate1(body, &dummy);
    }
  }

  let (index_fvars, index_decls, after_indices) =
    forall_telescope(&after_minors, n_indices, "tbi", 0);
  let (major_fvars, major_decls, _) =
    forall_telescope(&after_indices, 1, "tbj", 0);
  let major_fvar = &major_fvars[0];

  // --- Phase 2: Build F binders ---
  // F_j : ∀ targs, I_j.below params motives targs → motive_j targs
  let mut f_fvars: Vec<LeanExpr> = Vec::new();
  let mut f_decls: Vec<LocalDecl> = Vec::new();

  for j in 0..n_motives {
    let motive_type = &motive_decls[j].domain;
    let n_motive_args = super::expr_utils::count_foralls(motive_type);
    let (inner_fvars, inner_decls, _) =
      forall_telescope(motive_type, n_motive_args, &format!("tbfa{j}"), 0);

    // below_app: I_j.below params motives inner_fvars
    let below_app = mk_app_n(
      mk_app_n(
        mk_app_n(mk_const(&below_names[j], &rec_univs), &param_fvars),
        &motive_fvars,
      ),
      &inner_fvars,
    );

    // motive_app: motive_fvars[j] inner_fvars
    let motive_app = mk_app_n(motive_fvars[j].clone(), &inner_fvars);

    // F type: ∀ inner_args, below_app → motive_app
    let (below_fv_name, _) = fresh_fvar(&format!("tbfb{j}"), 0);
    let below_decl = LocalDecl {
      fvar_name: below_fv_name,
      binder_name: Name::str(Name::anon(), "f".to_string()),
      domain: below_app,
      info: BinderInfo::Default,
    };
    let f_type_binders: Vec<LocalDecl> =
      inner_decls.into_iter().chain(std::iter::once(below_decl)).collect();
    let f_type = mk_forall(motive_app, &f_type_binders);

    let f_name = Name::str(Name::anon(), format!("F_{}", j + 1));
    let (fj_fv_name, fj_fv) = fresh_fvar("tbf", j);
    f_decls.push(LocalDecl {
      fvar_name: fj_fv_name,
      binder_name: f_name,
      domain: f_type,
      info: BinderInfo::Default,
    });
    f_fvars.push(fj_fv);
  }

  // Collect all outer binder decls
  let all_decls: Vec<LocalDecl> = param_decls
    .iter()
    .chain(motive_decls.iter())
    .chain(index_decls.iter())
    .chain(major_decls.iter())
    .chain(f_decls.iter())
    .cloned()
    .collect();
  let all_fvars: Vec<LeanExpr> = param_fvars
    .iter()
    .chain(motive_fvars.iter())
    .chain(index_fvars.iter())
    .chain(major_fvars.iter())
    .chain(f_fvars.iter())
    .cloned()
    .collect();

  // --- Phase 3: Build .brecOn.go ---

  // go return type: PProd (motive_ci indices major) (below_ci params motives indices major)
  let motive_ci_app = mk_app_n(
    mk_app_n(motive_fvars[ci].clone(), &index_fvars),
    std::slice::from_ref(major_fvar),
  );
  let below_ci_app = mk_app_n(
    mk_app_n(
      mk_app_n(
        mk_app_n(mk_const(&below_names[ci], &rec_univs), &param_fvars),
        &motive_fvars,
      ),
      &index_fvars,
    ),
    std::slice::from_ref(major_fvar),
  );
  let go_ret_type = mk_pprod(&elim_level, &rlvl, &motive_ci_app, &below_ci_app);

  // go value: I.rec.{rlvl, lvls...} params [modified_motives] [modified_minors] indices major
  let mut go_val = mk_const(&rec_val.cnst.name, &{
    let mut us = vec![rlvl.clone()];
    us.extend(ind_level_params.iter().map(|lp| Level::param(lp.clone())));
    us
  });

  // Apply params
  go_val = mk_app_n(go_val, &param_fvars);

  // Apply modified motives: λ targs => PProd(motive_j targs, below_j params motives targs)
  for j in 0..n_motives {
    let mt = &motive_decls[j].domain;
    let nma = super::expr_utils::count_foralls(mt);
    let (ifvs, idcls, _) = forall_telescope(mt, nma, &format!("tbgm{j}"), 0);

    let m_app = mk_app_n(motive_fvars[j].clone(), &ifvs);
    let b_app = mk_app_n(
      mk_app_n(
        mk_app_n(mk_const(&below_names[j], &rec_univs), &param_fvars),
        &motive_fvars,
      ),
      &ifvs,
    );
    let pprod_body = mk_pprod(&elim_level, &rlvl, &m_app, &b_app);
    go_val = LeanExpr::app(go_val, mk_lambda(pprod_body, &idcls));
  }

  // Apply modified minors: for each ctor, build PProd-packed minor
  for minor_dom in &minor_doms {
    let minor = build_type_minor_premise_fvar(
      minor_dom,
      &param_fvars,
      &motive_fvars,
      &f_fvars,
      &below_names,
      &rec_univs,
      &elim_level,
      &rlvl,
    );
    go_val = LeanExpr::app(go_val, minor);
  }

  // Apply indices and major
  go_val = mk_app_n(go_val, &index_fvars);
  go_val = LeanExpr::app(go_val, major_fvar.clone());

  let go_type = mk_forall(go_ret_type, &all_decls);
  let go_value = mk_lambda(go_val, &all_decls);

  // --- Phase 4: Build .brecOn ---
  // brecOn value: Proj("PProd", 0, brecOn.go all_fvars...)
  let go_app = mk_app_n(mk_const(&go_name, &rec_univs), &all_fvars);
  let brecon_val = LeanExpr::proj(
    Name::str(Name::anon(), "PProd".to_string()),
    Nat::from(0u64),
    go_app.clone(),
  );

  let brecon_type = mk_forall(motive_ci_app.clone(), &all_decls);
  let brecon_value = mk_lambda(brecon_val, &all_decls);

  // --- Phase 5: Build .brecOn.eq ---
  let eq_result = build_type_brecon_eq_fvar(
    ci,
    rec_val,
    &brecon_name,
    &go_name,
    &rec_univs,
    &param_fvars,
    &param_decls,
    &motive_fvars,
    &motive_decls,
    &index_fvars,
    &index_decls,
    &major_fvars,
    &major_decls,
    &f_fvars,
    &f_decls,
    &all_decls,
    &all_fvars,
    &below_names,
    &minor_doms,
    n_minors,
    &motive_ci_app,
    &elim_level,
    lean_env,
  );

  let mut results = vec![
    BRecOnDef {
      name: go_name,
      level_params: rec_level_params.clone(),
      typ: go_type,
      value: go_value,
    },
    BRecOnDef {
      name: brecon_name,
      level_params: rec_level_params.clone(),
      typ: brecon_type,
      value: brecon_value,
    },
  ];

  if let Some((eq_typ, eq_val)) = eq_result {
    results.push(BRecOnDef {
      name: eq_name,
      level_params: rec_level_params.clone(),
      typ: eq_typ,
      value: eq_val,
    });
  }

  Ok(results)
}

/// Build a Type-level brecOn minor premise (FVar-based).
///
/// Takes a minor domain in FVar form (params + motives substituted).
/// For each IH field: replaces domain with PProd(motive, below), creates
/// PProdN-packed body with `PProd.mk (F_j args b) b`.
#[allow(clippy::too_many_arguments)]
fn build_type_minor_premise_fvar(
  minor_dom: &LeanExpr,
  param_fvars: &[LeanExpr],
  motive_fvars: &[LeanExpr],
  f_fvars: &[LeanExpr],
  below_names: &[Name],
  rec_univs: &[Level],
  elim_level: &Level,
  rlvl: &Level,
) -> LeanExpr {
  let n_fields = super::expr_utils::count_foralls(minor_dom);
  let (field_fvars, field_decls, return_type) =
    forall_telescope(minor_dom, n_fields, "tmf", 0);

  // Determine which class the return type targets
  let ret_motive_idx =
    find_motive_fvar(&return_type, motive_fvars).unwrap_or(0);

  // Classify fields and build modified binders
  let mut lambda_decls: Vec<LocalDecl> = Vec::new();
  let mut lambda_fvars: Vec<LeanExpr> = Vec::new();
  let mut prod_entries: Vec<(LeanExpr, usize)> = Vec::new(); // (fvar, lambda_index) for IH fields

  for (fi, (decl, fvar)) in
    field_decls.into_iter().zip(field_fvars.into_iter()).enumerate()
  {
    if let Some(_j_prime) = find_motive_fvar(&decl.domain, motive_fvars) {
      // IH field: replace domain with PProd(motive, below)
      let pprod_dom = replace_motive_with_pprod_fvar(
        &decl.domain,
        param_fvars,
        motive_fvars,
        below_names,
        rec_univs,
        elim_level,
        rlvl,
      );
      let (ih_fv_name, ih_fv) = fresh_fvar("tmih", fi);
      lambda_decls.push(LocalDecl {
        fvar_name: ih_fv_name,
        binder_name: decl.binder_name.clone(),
        domain: pprod_dom,
        info: decl.info.clone(),
      });
      lambda_fvars.push(ih_fv.clone());
      prod_entries.push((ih_fv, lambda_decls.len() - 1));
    } else {
      lambda_decls.push(decl);
      lambda_fvars.push(fvar);
    }
  }

  // Build PProdN.mk of prod entries (right-fold of VALUES, not types).
  // Lean's PProdN.mk calls mkPProdMk which infers types from the values.
  // Each prod entry is an FVar whose type is PProd(motive, below).
  // Empty case: Lean's PProdN.mk uses the passed `rlvl` directly for PUnit,
  // not max(1, rlvl) — they're numerically equal for Type-level but
  // structurally different.
  let (b, b_type) = if prod_entries.is_empty() {
    let punit_ty = super::below::punit_const(rlvl);
    (mk_punit_unit(rlvl), punit_ty)
  } else if prod_entries.len() == 1 {
    let fv = prod_entries[0].0.clone();
    let ty = lambda_decls[prod_entries[0].1].domain.clone();
    (fv, ty)
  } else {
    // Right-fold with mk_pprod_mk (value-level PProd packing).
    let last_idx = prod_entries.len() - 1;
    let last_fv = prod_entries[last_idx].0.clone();
    let last_ty = lambda_decls[prod_entries[last_idx].1].domain.clone();
    prod_entries[..last_idx].iter().rev().fold(
      (last_fv, last_ty),
      |(acc_val, acc_ty), (fv, decl_idx)| {
        let fv_ty = lambda_decls[*decl_idx].domain.clone();
        let packed = mk_pprod_mk(rlvl, rlvl, &fv_ty, &acc_ty, fv, &acc_val);
        let packed_ty = mk_pprod(rlvl, rlvl, &fv_ty, &acc_ty);
        (packed, packed_ty)
      },
    )
  };

  // Build the conclusion: PProd.mk (F_{ret_idx} ret_args b) b
  let (_, ret_args) = decompose_apps(&return_type);

  // F_{ret_idx} applied to ret_args and b
  let mut f_app = f_fvars[ret_motive_idx].clone();
  for a in &ret_args {
    f_app = LeanExpr::app(f_app, a.clone());
  }
  f_app = LeanExpr::app(f_app, b.clone());

  // motive_ci ret_args — this is the type of (F ret_args b)
  let motive_app = mk_app_n(motive_fvars[ret_motive_idx].clone(), &ret_args);

  // The outer PProd.mk wraps (F result, b) where:
  //   type_a = motive_app (: Sort elim_level)
  //   type_b = b_type (the PProdN-packed type : Sort rlvl)
  let body = mk_pprod_mk(elim_level, rlvl, &motive_app, &b_type, &f_app, &b);

  mk_lambda(body, &lambda_decls)
}

/// Replace a motive application with PProd(motive, below) (FVar-based).
///
/// `dom` is in FVar form. If it's `motive_j args`, produce
/// `PProd (motive_j args) (below_j params motives args)`.
/// Handles forall wrapping.
#[allow(clippy::too_many_arguments)]
fn replace_motive_with_pprod_fvar(
  dom: &LeanExpr,
  param_fvars: &[LeanExpr],
  motive_fvars: &[LeanExpr],
  below_names: &[Name],
  rec_univs: &[Level],
  elim_level: &Level,
  rlvl: &Level,
) -> LeanExpr {
  let n_inner = super::expr_utils::count_foralls(dom);
  let (inner_fvars, inner_decls, leaf) =
    forall_telescope(dom, n_inner, "tpp", 0);

  let j_prime = find_motive_fvar(&leaf, motive_fvars).unwrap_or(0);
  let (_, args) = decompose_apps(&leaf);

  // motive_app: motive_fvars[j'] args inner_fvars
  let mut motive_app = motive_fvars[j_prime].clone();
  for a in &args {
    motive_app = LeanExpr::app(motive_app, a.clone());
  }
  motive_app = mk_app_n(motive_app, &inner_fvars);

  // below_app: below_names[j'] params motives args inner_fvars
  let mut below_app = mk_const(&below_names[j_prime], rec_univs);
  below_app = mk_app_n(below_app, param_fvars);
  below_app = mk_app_n(below_app, motive_fvars);
  for a in &args {
    below_app = LeanExpr::app(below_app, a.clone());
  }
  below_app = mk_app_n(below_app, &inner_fvars);

  let pprod = mk_pprod(elim_level, rlvl, &motive_app, &below_app);

  if inner_decls.is_empty() { pprod } else { mk_forall(pprod, &inner_decls) }
}

/// Build `.brecOn.eq` type and value (FVar-based).
///
/// Type: `∀ binders, @Eq (motive_ci args) (brecOn args) (F_ci args (go args).2)`
/// Value: Recursor-based case-split proof with Eq.refl minors.
#[allow(clippy::too_many_arguments)]
fn build_type_brecon_eq_fvar(
  ci: usize,
  rec_val: &RecursorVal,
  brecon_name: &Name,
  go_name: &Name,
  rec_univs: &[Level],
  param_fvars: &[LeanExpr],
  _param_decls: &[LocalDecl],
  motive_fvars: &[LeanExpr],
  motive_decls: &[LocalDecl],
  index_fvars: &[LeanExpr],
  _index_decls: &[LocalDecl],
  major_fvars: &[LeanExpr],
  _major_decls: &[LocalDecl],
  f_fvars: &[LeanExpr],
  _f_decls: &[LocalDecl],
  all_decls: &[LocalDecl],
  all_fvars: &[LeanExpr],
  _below_names: &[Name],
  minor_doms: &[LeanExpr],
  n_minors: usize,
  motive_ci_app: &LeanExpr,
  elim_level: &Level,
  lean_env: &LeanEnv,
) -> Option<(LeanExpr, LeanExpr)> {
  // .brecOn.eq requires Eq and Eq.refl as constants. In the full pipeline,
  // aux_gen is only called when the original Lean environment has these
  // constants, so this always succeeds. But in minimal test environments
  // (e.g., unit tests with synthetic inductives), Eq may not exist.
  // Return None in that case — matching the old BVar code's behavior.
  //
  // TODO: Accept a lean_env parameter and check lean_env.get("Eq").is_some()
  // for a more principled guard. For now, we always generate .eq since the
  // real pipeline guarantees Eq exists.
  let _ = n_minors;

  let _n_motives = motive_fvars.len();
  let major_fvar = &major_fvars[0];

  // --- Type ---
  // @Eq.{elim_level} motive_ci_app (brecOn all_fvars) (F_ci indices major (go all_fvars).2)
  let brecon_app = mk_app_n(mk_const(brecon_name, rec_univs), all_fvars);
  let go_app = mk_app_n(mk_const(go_name, rec_univs), all_fvars);
  let go_snd = LeanExpr::proj(
    Name::str(Name::anon(), "PProd".to_string()),
    Nat::from(1u64),
    go_app.clone(),
  );

  // F_ci indices major go_snd
  let mut f_ci_app = f_fvars[ci].clone();
  f_ci_app = mk_app_n(f_ci_app, index_fvars);
  f_ci_app = LeanExpr::app(f_ci_app, major_fvar.clone());
  f_ci_app = LeanExpr::app(f_ci_app, go_snd);

  // @Eq.{elim_level} (motive_ci_type) (brecOn_app) (f_ci_app)
  let eq_type_body = LeanExpr::app(
    LeanExpr::app(
      LeanExpr::app(
        mk_const(
          &Name::str(Name::anon(), "Eq".to_string()),
          std::slice::from_ref(elim_level),
        ),
        motive_ci_app.clone(),
      ),
      brecon_app,
    ),
    f_ci_app,
  );

  let eq_type = mk_forall(eq_type_body, all_decls);

  // --- Value ---
  // Build via casesOn (matching Lean's `cases` tactic + `refl`).
  // casesOn has binder order: params, motive, indices, major, minors
  // (different from rec's: params, motives, minors, indices, major)
  // Only the target motive (ci) and target minors are present.
  let ind_name = &rec_val.all[ci];
  let cases_on_name = Name::str(ind_name.clone(), "casesOn".to_string());

  // casesOn universe: [Level::zero(), ind_lvls...] for Prop elimination
  let eq_cases_univs: Vec<Level> = std::iter::once(Level::zero())
    .chain(rec_univs.iter().skip(1).cloned())
    .collect();
  let mut eq_val = mk_const(&cases_on_name, &eq_cases_univs);

  // Apply params
  eq_val = mk_app_n(eq_val, param_fvars);

  // Apply target motive (only one motive in casesOn)
  // Motive: λ targs => @Eq (motive_ci targs) (brecOn ... targs ...) (F_ci targs (go ... targs ...).2)
  {
    let mt = &motive_decls[ci].domain;
    let nma = super::expr_utils::count_foralls(mt);
    let (targ_fvars, targ_decls, _) = forall_telescope(mt, nma, "tbeqmc", 0);

    let inner_all: Vec<LeanExpr> = param_fvars
      .iter()
      .chain(motive_fvars.iter())
      .chain(targ_fvars.iter())
      .chain(f_fvars.iter())
      .cloned()
      .collect();
    let inner_brecon = mk_app_n(mk_const(brecon_name, rec_univs), &inner_all);
    let inner_go = mk_app_n(mk_const(go_name, rec_univs), &inner_all);
    let inner_go_snd = LeanExpr::proj(
      Name::str(Name::anon(), "PProd".to_string()),
      Nat::from(1u64),
      inner_go,
    );
    let mut inner_f_ci = f_fvars[ci].clone();
    inner_f_ci = mk_app_n(inner_f_ci, &targ_fvars);
    inner_f_ci = LeanExpr::app(inner_f_ci, inner_go_snd);

    let inner_motive_app = mk_app_n(motive_fvars[ci].clone(), &targ_fvars);

    let eq_motive_body = LeanExpr::app(
      LeanExpr::app(
        LeanExpr::app(
          mk_const(
            &Name::str(Name::anon(), "Eq".to_string()),
            std::slice::from_ref(elim_level),
          ),
          inner_motive_app,
        ),
        inner_brecon,
      ),
      inner_f_ci,
    );

    eq_val = LeanExpr::app(eq_val, mk_lambda(eq_motive_body, &targ_decls));
  }

  // Apply indices and major (in casesOn, these come BEFORE minors)
  eq_val = mk_app_n(eq_val, index_fvars);
  eq_val = LeanExpr::app(eq_val, major_fvar.clone());

  // Apply target minors only (casesOn has no non-target minors).
  // For casesOn, minor fields have IH stripped — only non-recursive fields remain.
  // Each minor body is Eq.refl.
  // Identify target ctor count and which minor_doms belong to class ci.
  let target_ind = &rec_val.all[ci];
  let target_ctors: Vec<Name> = match lean_env.get(target_ind) {
    Some(ConstantInfo::InductInfo(v)) => v.ctors.clone(),
    _ => vec![],
  };

  // Find which minor_doms belong to target class ci.
  // minor_doms are ordered by class: class 0 ctors, class 1 ctors, etc.
  let mut minor_offset = 0usize;
  for j in 0..ci {
    let ind_j = &rec_val.all[j];
    if let Some(ConstantInfo::InductInfo(v)) = lean_env.get(ind_j) {
      minor_offset += v.ctors.len();
    }
  }

  for (ctor_idx, _ctor_name) in target_ctors.iter().enumerate() {
    let mi = minor_offset + ctor_idx;
    if mi >= minor_doms.len() {
      break;
    }
    let minor_dom = &minor_doms[mi];

    // Open minor fields. In FVar form, IH fields have motive FVars as heads.
    // casesOn strips IH fields, so we only open non-IH fields.
    let n_minor_fields = super::expr_utils::count_foralls(minor_dom);
    let (_mfield_fvars, mfield_decls, minor_ret) =
      forall_telescope(minor_dom, n_minor_fields, &format!("tbeqf{mi}"), 0);

    // Filter to non-IH fields only (casesOn strips IH)
    let non_ih_decls: Vec<LocalDecl> = mfield_decls
      .into_iter()
      .filter(|d| find_motive_fvar(&d.domain, motive_fvars).is_none())
      .collect();

    // Build Eq.refl: @Eq.refl.{elim_level} (motive_ci ctor_ret_args) (brecOn ... ctor_ret_args ...)
    let (_, ctor_ret_args) = decompose_apps(&minor_ret);

    let inner_all: Vec<LeanExpr> = param_fvars
      .iter()
      .chain(motive_fvars.iter())
      .chain(ctor_ret_args.iter())
      .chain(f_fvars.iter())
      .cloned()
      .collect();
    let inner_brecon = mk_app_n(mk_const(brecon_name, rec_univs), &inner_all);
    let motive_app = mk_app_n(motive_fvars[ci].clone(), &ctor_ret_args);

    let minor_body = LeanExpr::app(
      LeanExpr::app(
        mk_const(
          &Name::str(
            Name::str(Name::anon(), "Eq".to_string()),
            "refl".to_string(),
          ),
          std::slice::from_ref(elim_level),
        ),
        motive_app,
      ),
      inner_brecon,
    );

    eq_val = LeanExpr::app(eq_val, mk_lambda(minor_body, &non_ih_decls));
  }

  let eq_value = mk_lambda(eq_val, all_decls);

  Some((eq_type, eq_value))
}

// =========================================================================
// Level utilities
// =========================================================================

/// Substitute a named level parameter with a concrete level throughout an expression.
///
/// Used for Prop brecOn: the recursor type has `Level::param(u)` for large elimination,
/// but brecOn specializes to Prop, so `u -> Level::zero()`.
fn subst_level_in_expr(
  expr: &LeanExpr,
  param: &Name,
  replacement: &Level,
) -> LeanExpr {
  match expr.as_data() {
    ExprData::Sort(lvl, _) => {
      LeanExpr::sort(subst_level(lvl, param, replacement))
    },
    ExprData::Const(n, lvls, _) => {
      let new_lvls: Vec<Level> =
        lvls.iter().map(|l| subst_level(l, param, replacement)).collect();
      LeanExpr::cnst(n.clone(), new_lvls)
    },
    ExprData::App(f, a, _) => LeanExpr::app(
      subst_level_in_expr(f, param, replacement),
      subst_level_in_expr(a, param, replacement),
    ),
    ExprData::ForallE(n, d, b, bi, _) => LeanExpr::all(
      n.clone(),
      subst_level_in_expr(d, param, replacement),
      subst_level_in_expr(b, param, replacement),
      bi.clone(),
    ),
    ExprData::Lam(n, d, b, bi, _) => LeanExpr::lam(
      n.clone(),
      subst_level_in_expr(d, param, replacement),
      subst_level_in_expr(b, param, replacement),
      bi.clone(),
    ),
    ExprData::LetE(n, t, v, b, nd, _) => LeanExpr::letE(
      n.clone(),
      subst_level_in_expr(t, param, replacement),
      subst_level_in_expr(v, param, replacement),
      subst_level_in_expr(b, param, replacement),
      *nd,
    ),
    _ => expr.clone(),
  }
}

/// Substitute a named level parameter with a concrete level.
fn subst_level(lvl: &Level, param: &Name, replacement: &Level) -> Level {
  match lvl.as_data() {
    LevelData::Param(n, _) if n == param => replacement.clone(),
    LevelData::Succ(l, _) => Level::succ(subst_level(l, param, replacement)),
    LevelData::Max(l1, l2, _) => Level::max(
      subst_level(l1, param, replacement),
      subst_level(l2, param, replacement),
    ),
    LevelData::Imax(l1, l2, _) => Level::imax(
      subst_level(l1, param, replacement),
      subst_level(l2, param, replacement),
    ),
    _ => lvl.clone(),
  }
}
