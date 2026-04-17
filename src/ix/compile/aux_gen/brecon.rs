//! Canonical `.brecOn` generation for alpha-collapsed inductive blocks.
//!
//! **Prop-level** (inductive predicates): generates a single theorem per class.
//!   `I_i.brecOn = λ params motives t F_1..F_n => F_i t (I_i.rec below_motives below_minors t)`
//!   Reference: `refs/lean4/src/Lean/Meta/IndPredBelow.lean:185-208`
//!
//! **Type-level** (large eliminators): generates `.brecOn.go` + `.brecOn` per class.
//!   `.brecOn.go` uses PProd-wrapped motives; `.brecOn` projects first component.
//!   Reference: `refs/lean4/src/Lean/Meta/Constructions/BRecOn.lean:191-308`

use crate::ix::compile::nat_conv::try_nat_to_usize;
use crate::ix::env::{
  BinderInfo, ConstantInfo, Env as LeanEnv, Expr as LeanExpr, ExprData,
  InductiveVal, Level, LevelData, Name, RecursorVal,
};
use crate::ix::ixon::CompileError;
use lean_ffi::nat::Nat;

use super::below::{
  BelowConstant, mk_level_succ, mk_pprod, mk_pprod_mk, mk_punit_unit,
};

use super::expr_utils::{
  LocalDecl, abstract_fvar, decompose_apps, find_motive_fvar, forall_telescope,
  fresh_fvar, instantiate1, mk_app_n, mk_const, mk_forall, mk_lambda,
  subst_fvar,
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
  stt: &crate::ix::compile::CompileState,
  kctx: &crate::ix::compile::KernelCtx,
) -> Result<Vec<BRecOnDef>, CompileError> {
  let n_classes = sorted_classes.len();
  if n_classes == 0 || canonical_recs.is_empty() || below_consts.is_empty() {
    return Ok(vec![]);
  }

  let mut results = Vec::new();

  for ci in 0..n_classes.min(canonical_recs.len()).min(below_consts.len()) {
    let (_, rec_val) = &canonical_recs[ci];
    let class_rep = &sorted_classes[ci][0];
    let ind_ref = lean_env.get(class_rep);
    let ind = match ind_ref.as_deref() {
      Some(ConstantInfo::InductInfo(v)) => v,
      _ => {
        return Err(CompileError::MissingConstant {
          name: class_rep.pretty(),
          caller: "generate_brecon_constants: class rep not an inductive"
            .into(),
        });
      },
    };

    // Only generate brecOn for recursive inductives (matching Lean's guard:
    // `unless indVal.isRec do return` in BRecOn.lean:313 and IndPredBelow.lean:215).
    if !ind.is_rec {
      continue;
    }

    if !is_prop {
      // Type-level: generate .brecOn.go + .brecOn + .brecOn.eq (BRecOn.lean path)
      let brecon_name =
        Name::str(sorted_classes[ci][0].clone(), "brecOn".to_string());
      let all0 = &ind.all[0];
      let defs = build_type_brecon_fvar(
        ci,
        rec_val,
        &brecon_name,
        all0,
        lean_env,
        n_classes,
        sorted_classes,
        stt,
        kctx,
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

  // Generate .brecOn_N for nested auxiliary members (Type-level only).
  // Lean (BRecOn.lean:320-326): for each nested auxiliary recursor rec_N,
  // generate brecOn_N.go + brecOn_N + brecOn_N.eq using the same
  // mkBRecOnFromRec function as the main brecOn.
  if !is_prop {
    let n_aux = canonical_recs.len().saturating_sub(n_classes);
    if n_aux > 0 {
      // all[0] from the first class's inductive — Lean hangs _N names here.
      let first_class_name = &sorted_classes[0][0];
      let all0 = match lean_env.get(first_class_name).as_deref() {
        Some(ConstantInfo::InductInfo(v)) => v.all[0].clone(),
        _ => first_class_name.clone(),
      };

      for j in 0..n_aux {
        let idx = j + 1; // 1-based Lean convention
        let (_, aux_rec_val) = &canonical_recs[n_classes + j];
        let brecon_name = Name::str(all0.clone(), format!("brecOn_{idx}"));

        // Only generate if this constant exists in the source environment.
        // Check lean_env (original Lean env during compilation) OR
        // stt.env.named (Ixon compile state — has all constants during
        // decompilation where lean_env is the incrementally-built work_env
        // and won't contain the constant we're about to generate).
        let exists = lean_env.contains_key(&brecon_name)
          || stt.env.named.contains_key(&brecon_name);
        if !exists {
          continue;
        }

        let ci = n_classes + j; // target motive index in the flat block
        let defs = build_type_brecon_fvar(
          ci,
          aux_rec_val,
          &brecon_name,
          &all0,
          lean_env,
          n_classes,
          sorted_classes,
          stt,
          kctx,
        )?;
        results.extend(defs);
      }
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
  let n_params = try_nat_to_usize(&rec_val.num_params)?;
  let n_motives = try_nat_to_usize(&rec_val.num_motives)?;
  let n_minors = try_nat_to_usize(&rec_val.num_minors)?;
  let n_indices = try_nat_to_usize(&ind.num_indices)?;
  let ind_level_params = &ind.cnst.level_params;

  // For Prop brecOn with large elimination (drec), substitute u -> Level::zero().
  // Invariant: generate_canonical_recursors always prepends the elimination level
  // as level_params[0] for large recursors (recursor.rs:192-194), so [0] is correct.
  let large_elim = rec_val.cnst.level_params.len() > ind_level_params.len();
  let rec_val = if large_elim && !rec_val.cnst.level_params.is_empty() {
    let u_param = &rec_val.cnst.level_params[0];
    debug_assert!(
      !ind_level_params.contains(u_param),
      "elimination level param {:?} should not be in the inductive's own level params",
      u_param.pretty(),
    );
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
      let bc =
        below_consts.get(j).ok_or_else(|| CompileError::UnsupportedExpr {
          desc: format!("prop brecOn: missing below constant for class {j}"),
        })?;
      Ok(match bc {
        BelowConstant::Indc(bi) => {
          bi.ctors.iter().map(|c| c.name.clone()).collect()
        },
        _ => vec![],
      })
    })
    .collect::<Result<Vec<_>, CompileError>>()?;

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
    let class_ctor_names: &[Name] = below_ctor_names
      .get(j)
      .ok_or_else(|| CompileError::UnsupportedExpr {
        desc: format!("prop brecOn: missing below ctor names for class {j}"),
      })?
      .as_slice();

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
      // IH field. For a non-reflexive IH `motive args`, the new binder is
      // just `I_{j'}.below params motives args`. For a reflexive IH
      // `∀(inner), motive args`, the new binder preserves the forall
      // structure: `∀(inner), I_{j'}.below params motives args`.
      //
      // This matches Lean's `ihTypeToBelowType` (IndPredBelow.lean:71-75),
      // which walks the expression and replaces only the motive head.
      let n_inner_foralls = super::expr_utils::count_foralls(&decl.domain);
      let (inner_fvars, inner_decls, leaf) = forall_telescope(
        &decl.domain,
        n_inner_foralls,
        &format!("pbmp{fi}"),
        0,
      );
      let (_, leaf_args) = decompose_apps(&leaf);

      // Build the leaf below application: I_{j'}.below params motives leaf_args
      let mut below_leaf = mk_const(&below_names[j_prime], ind_univs);
      below_leaf = mk_app_n(below_leaf, param_fvars);
      below_leaf = mk_app_n(below_leaf, motive_fvars);
      for a in &leaf_args {
        below_leaf = LeanExpr::app(below_leaf, a.clone());
      }
      // Re-wrap with the original foralls (empty for non-reflexive).
      let below_dom = mk_forall(below_leaf, &inner_decls);

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

      // proof arg: `F_{j'}` applied to leaf_args and `ih_fv applied to inner`.
      //   non-reflexive: F_{j'} leaf_args ih_fv
      //   reflexive:     λ inner, F_{j'} leaf_args (ih_fv inner)
      let proof = if n_inner_foralls == 0 {
        let mut p = f_fvars[j_prime].clone();
        for a in &leaf_args {
          p = LeanExpr::app(p, a.clone());
        }
        LeanExpr::app(p, ih_fv)
      } else {
        let mut p = f_fvars[j_prime].clone();
        for a in &leaf_args {
          p = LeanExpr::app(p, a.clone());
        }
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

/// Infer the inductive sort level from the major premise domain.
///
/// Matches Lean's `typeFormerTypeLevel (← inferType (← inferType major))`:
/// finds the head constant of the major's type, looks it up in the
/// environment, and peels foralls to get the resulting Sort level.
///
// NOTE: the previous fallback helpers `infer_ilvl_from_motive_domain`,
// `infer_ilvl_from_major`, and `get_ind_sort_level` (formerly in below.rs)
// were removed when we switched to propagating TcScope::get_level errors
// unconditionally — see the comment above `rlvls` in `build_type_brecon_fvar`
// for the rationale.

/// Build Type-level `.brecOn.go`, `.brecOn`, and `.brecOn.eq` (FVar-based).
///
/// Generic over any recursor in the flat block: works for both original
/// class recursors (ci < n_classes) and nested auxiliary recursors
/// (ci >= n_classes).
///
/// `brecon_name`: the output name (e.g., `I.brecOn` or `I.brecOn_1`)
/// `ci`: the target motive index in the flat block
/// `all0`: `all[0]` from the first inductive, used for `below_N` naming
#[allow(clippy::too_many_arguments)]
fn build_type_brecon_fvar(
  ci: usize,
  rec_val: &RecursorVal,
  brecon_name: &Name,
  all0: &Name,
  lean_env: &LeanEnv,
  n_classes: usize,
  sorted_classes: &[Vec<Name>],
  stt: &crate::ix::compile::CompileState,
  kctx: &crate::ix::compile::KernelCtx,
) -> Result<Vec<BRecOnDef>, CompileError> {
  // canon_kenv is populated by `populate_canon_kenv_with_below` in
  // aux_gen.rs between Phase 2 and Phase 3. It contains PUnit, PProd,
  // parent inductives, and canonical .below types.

  let n_params = try_nat_to_usize(&rec_val.num_params)?;
  let n_motives = try_nat_to_usize(&rec_val.num_motives)?;
  let n_minors = try_nat_to_usize(&rec_val.num_minors)?;
  let n_indices = try_nat_to_usize(&rec_val.num_indices)?;
  let rec_level_params = &rec_val.cnst.level_params;
  // Inductive-only level params (rec has [elim_level, ind_levels...]).
  let ind_level_params = &rec_level_params[1..];

  let brecon_name = brecon_name.clone();
  let go_name = Name::str(brecon_name.clone(), "go".to_string());
  let eq_name = Name::str(brecon_name.clone(), "eq".to_string());

  let elim_level = Level::param(rec_level_params[0].clone());

  let below_names: Vec<Name> = (0..n_motives)
    .map(|j| {
      if j < n_classes {
        Name::str(sorted_classes[j][0].clone(), "below".to_string())
      } else {
        let aux_idx = j - n_classes + 1;
        Name::str(all0.clone(), format!("below_{}", aux_idx))
      }
    })
    .collect();

  let rec_univs: Vec<Level> =
    rec_level_params.iter().map(|lp| Level::param(lp.clone())).collect();

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

  // Compute per-motive rlvl: each member of the flat block may live in a
  // different universe. Lean (BRecOn.lean:215-220) computes ilvl via
  // `inferType (← inferType major)` then `rlvl = mkLevelMax ilvl lvl`.
  // We use TcScope::get_level on the major domain from each motive's type,
  // which performs the same inferType + ensure_sort sequence.
  //
  // If `get_level` fails, we propagate the error rather than silently
  // falling back to `infer_ilvl_from_motive_domain`. The fallback uses a
  // different universe-construction path than Lean and can produce
  // structurally-different Level trees; silently masking a TC failure
  // here leads to `PProd` universe mismatches later that are
  // hard-to-diagnose. A TC failure here is almost always a sign that
  // `canon_kenv` is missing a dependency — fix the root cause, don't
  // paper over it.
  let rlvls: Vec<Level> = {
    // Create a temporary TcScope with params + motives context for ilvl inference.
    let ilvl_ctx: Vec<LocalDecl> =
      param_decls.iter().chain(motive_decls.iter()).cloned().collect();
    let mut ilvl_tc =
      super::expr_utils::TcScope::new(&ilvl_ctx, rec_level_params, stt, kctx);

    motive_decls
      .iter()
      .map(|md| -> Result<Level, CompileError> {
        // Peel foralls from the motive type to find the major domain,
        // then infer its sort level via TC.
        let n_motive_args = super::expr_utils::count_foralls(&md.domain);
        let (_ifvs, idcls, _) =
          forall_telescope(&md.domain, n_motive_args, "ilvl_m", 0);
        // The major domain is the last binder's domain.
        let major_dom = if let Some(last) = idcls.last() {
          &last.domain
        } else {
          &md.domain
        };

        ilvl_tc.push_locals(&idcls);
        let ilvl_j = ilvl_tc.get_level(major_dom).map_err(|e| {
          CompileError::UnsupportedExpr {
            desc: format!(
              "brecOn ilvl inference failed for motive at class {ci}: \
               TcScope::get_level on major domain returned {e:?}. \
               This typically means `canon_kenv` is missing a \
               required inductive — check that Phase 2 (populate_canon_kenv_with_below) \
               ran before brecOn generation",
            ),
          }
        })?;
        ilvl_tc.pop_locals(&idcls);

        // Match Lean's BRecOn.lean:220: `mkLevelMax ilvl lvl` — raw Level.max
        // with only zero elimination.
        Ok(if matches!(ilvl_j.as_data(), LevelData::Zero(_)) {
          elim_level.clone()
        } else if matches!(elim_level.as_data(), LevelData::Zero(_)) {
          ilvl_j
        } else {
          Level::max(ilvl_j, elim_level.clone())
        })
      })
      .collect::<Result<Vec<_>, _>>()?
  };
  // The target's rlvl is used for the rec universe arg and go return type.
  let rlvl = &rlvls[ci];

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

  // Create ONE TcScope for the entire .go construction. Start with
  // params + motives; push/pop indices/major/F-binders as needed.
  // This matches Lean's mkPProd/mkPProdMk which infer levels via getLevel.
  let base_ctx: Vec<LocalDecl> =
    param_decls.iter().chain(motive_decls.iter()).cloned().collect();
  let mut rtc =
    super::expr_utils::TcScope::new(&base_ctx, rec_level_params, stt, kctx);

  // go return type: PProd (motive_ci indices major) (below_ci params motives indices major)
  // Infer levels via TC with indices + major in scope.
  rtc.push_locals(&index_decls);
  rtc.push_locals(&major_decls);

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
  let go_ret_lvl1 = rtc.get_level(&motive_ci_app)?;
  let go_ret_lvl2 = rtc.get_level(&below_ci_app)?;
  let go_ret_type =
    mk_pprod(&go_ret_lvl1, &go_ret_lvl2, &motive_ci_app, &below_ci_app);

  rtc.pop_locals(&major_decls);
  rtc.pop_locals(&index_decls);

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

    rtc.push_locals(&idcls);

    let m_app = mk_app_n(motive_fvars[j].clone(), &ifvs);
    let b_app = mk_app_n(
      mk_app_n(
        mk_app_n(mk_const(&below_names[j], &rec_univs), &param_fvars),
        &motive_fvars,
      ),
      &ifvs,
    );
    let mm_lvl1 = rtc.get_level(&m_app)?;
    let mm_lvl2 = rtc.get_level(&b_app)?;
    let pprod_body = mk_pprod(&mm_lvl1, &mm_lvl2, &m_app, &b_app);

    rtc.pop_locals(&idcls);

    go_val = LeanExpr::app(go_val, mk_lambda(pprod_body, &idcls));
  }

  // Push remaining context (indices, major, F-binders) for minor premises.
  rtc.push_locals(&index_decls);
  rtc.push_locals(&major_decls);
  rtc.push_locals(&f_decls);

  // Apply modified minors: for each ctor, build PProd-packed minor.
  //
  // All minors share a single `rlvl` — the one derived from the recursor's
  // single major premise. This matches Lean's BRecOn.lean where `rlvl` is
  // computed once outside the per-minor loop and threaded through
  // `buildBRecOnMinorPremise`. Using per-motive rlvls here (via
  // `rlvls[ret_motive_idx]`) would produce syntactically different (but
  // semantically equal) universe levels for `PUnit.unit` in nil-type
  // minors, breaking alpha-congruence with Lean's original.
  for minor_dom in &minor_doms {
    let minor = build_type_minor_premise_fvar(
      minor_dom,
      &param_fvars,
      &motive_fvars,
      &f_fvars,
      &below_names,
      &rec_univs,
      rlvl,
      &mut rtc,
    )?;
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
  // Derive the target inductive name from the major premise domain head.
  // For main inductives this is the block member (rec_val.all[ci]); for
  // nested auxiliaries it's the external inductive (e.g., List).
  let target_ind_name = {
    let (head, _) = decompose_apps(&major_decls[0].domain);
    match head.as_data() {
      ExprData::Const(name, _, _) => name.clone(),
      _ => Name::anon(), // will cause eq generation to gracefully skip
    }
  };
  // For nested auxiliaries, casesOn needs the ext inductive's own params
  // (spec_params) applied before the block params. E.g., for
  // NestedSimple.Tree: List.casesOn needs (α := Tree); for
  // NestedParam.RoseA α: List.casesOn needs (α := RoseA α).
  let cases_on_spec: Vec<LeanExpr> = if ci >= n_classes {
    let (_, major_args) = decompose_apps(&major_decls[0].domain);
    let ext_n_params = match lean_env.get(&target_ind_name).as_deref() {
      Some(ConstantInfo::InductInfo(v)) => try_nat_to_usize(&v.num_params)?,
      _ => 0,
    };
    major_args.into_iter().take(ext_n_params).collect()
  } else {
    vec![]
  };
  let eq_result = build_type_brecon_eq_fvar(
    ci,
    &target_ind_name,
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
    &cases_on_spec,
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
  // The single `rlvl` derived from the recursor's single major premise.
  // Lean's `buildBRecOnMinorPremise` threads this one value through all
  // minors — it is NOT specialised per motive.
  rlvl: &Level,
  rtc: &mut super::expr_utils::TcScope<'_>,
) -> Result<LeanExpr, CompileError> {
  let n_fields = super::expr_utils::count_foralls(minor_dom);
  let (field_fvars, mut field_decls, return_type) =
    forall_telescope(minor_dom, n_fields, "tmf", 0);

  // Head-reduce field domains to match Lean's stored .brecOn.go shape.
  // Same rationale as `build_below_minor`: Lean's `mkBRecOnFromRec` goes
  // through `mkLambdaFVars` which effectively normalises lambda-application
  // redexes in field binder types, even though the underlying recursor
  // stores them unreduced. Without this reduction, a field like
  // `v : (λ_:α. Json) k` would be rendered `λ v:(λ_.Json) k. …` in our
  // generated .brecOn.go, while Lean stores `λ v:Json. …`.
  for decl in &mut field_decls {
    decl.domain = super::expr_utils::beta_reduce(&decl.domain);
  }

  // Determine which class the return type targets
  let ret_motive_idx = find_motive_fvar(&return_type, motive_fvars)
    .ok_or_else(|| CompileError::UnsupportedExpr {
      desc: "brecOn minor: return type has no motive fvar head".into(),
    })?;

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
        rtc,
      )?;
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
  //
  // Lean's mkPProdMk (PProdN.lean:44-53) infers universe levels from the
  // types via getLevel. We use the TcScope to do the same. Push the lambda
  // decls (with replaced IH domains) into the TC so FVars resolve correctly.

  rtc.push_locals(&lambda_decls);

  let (b, b_type) = if prod_entries.is_empty() {
    // PUnit.{rlvl} : Sort rlvl
    let punit_ty = super::below::punit_const(rlvl);
    (mk_punit_unit(rlvl), punit_ty)
  } else if prod_entries.len() == 1 {
    let fv = prod_entries[0].0.clone();
    let ty = lambda_decls[prod_entries[0].1].domain.clone();
    (fv, ty)
  } else {
    // Right-fold with mk_pprod_mk (value-level PProd packing).
    // Infer levels per-pair via TC, matching Lean's mkPProdMk.
    let last_idx = prod_entries.len() - 1;
    let last_fv = prod_entries[last_idx].0.clone();
    let last_ty = lambda_decls[prod_entries[last_idx].1].domain.clone();
    let mut fold_val = last_fv;
    let mut fold_ty = last_ty;
    for (fv, decl_idx) in prod_entries[..last_idx].iter().rev() {
      let fv_ty = lambda_decls[*decl_idx].domain.clone();
      let fv_sort = rtc.get_level(&fv_ty)?;
      let fold_sort = rtc.get_level(&fold_ty)?;
      let packed =
        mk_pprod_mk(&fv_sort, &fold_sort, &fv_ty, &fold_ty, fv, &fold_val);
      let packed_ty = mk_pprod(&fv_sort, &fold_sort, &fv_ty, &fold_ty);
      fold_val = packed;
      fold_ty = packed_ty;
    }
    (fold_val, fold_ty)
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

  // The outer PProd.mk wraps (F result, b).
  // Infer levels via TC, matching Lean's mkPProdMk (PProdN.lean:44-53).
  let lvl_a = rtc.get_level(&motive_app)?;
  let lvl_b = rtc.get_level(&b_type)?;
  let body = mk_pprod_mk(&lvl_a, &lvl_b, &motive_app, &b_type, &f_app, &b);

  rtc.pop_locals(&lambda_decls);

  Ok(mk_lambda(body, &lambda_decls))
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
  rtc: &mut super::expr_utils::TcScope<'_>,
) -> Result<LeanExpr, CompileError> {
  let n_inner = super::expr_utils::count_foralls(dom);
  let (_inner_fvars, inner_decls, leaf) =
    forall_telescope(dom, n_inner, "tpp", 0);

  let j_prime = find_motive_fvar(&leaf, motive_fvars).ok_or_else(|| {
    CompileError::UnsupportedExpr {
      desc: "brecOn pprod: leaf expression has no motive fvar head".into(),
    }
  })?;
  let (_, args) = decompose_apps(&leaf);

  // motive_app: motive_fvars[j'] args
  let mut motive_app = motive_fvars[j_prime].clone();
  for a in &args {
    motive_app = LeanExpr::app(motive_app, a.clone());
  }

  // below_app: below_names[j'] params motives args
  let mut below_app = mk_const(&below_names[j_prime], rec_univs);
  below_app = mk_app_n(below_app, param_fvars);
  below_app = mk_app_n(below_app, motive_fvars);
  for a in &args {
    below_app = LeanExpr::app(below_app, a.clone());
  }

  // Infer PProd levels via TC, matching Lean's mkPProd (PProdN.lean:37-38).
  if !inner_decls.is_empty() {
    rtc.push_locals(&inner_decls);
  }
  let lvl1 = rtc.get_level(&motive_app)?;
  let lvl2 = rtc.get_level(&below_app)?;
  if !inner_decls.is_empty() {
    rtc.pop_locals(&inner_decls);
  }

  let pprod = mk_pprod(&lvl1, &lvl2, &motive_app, &below_app);

  Ok(if inner_decls.is_empty() {
    pprod
  } else {
    mk_forall(pprod, &inner_decls)
  })
}

/// Build `@Eq.{u} α a b`.
fn mk_eq(u: &Level, alpha: &LeanExpr, a: &LeanExpr, b: &LeanExpr) -> LeanExpr {
  let eq = mk_const(
    &Name::str(Name::anon(), "Eq".to_string()),
    std::slice::from_ref(u),
  );
  LeanExpr::app(
    LeanExpr::app(LeanExpr::app(eq, alpha.clone()), a.clone()),
    b.clone(),
  )
}

/// Build `@Eq.refl.{u} α a : Eq.{u} α a a`.
fn mk_eq_refl(u: &Level, alpha: &LeanExpr, a: &LeanExpr) -> LeanExpr {
  let eq_refl = mk_const(
    &Name::str(Name::str(Name::anon(), "Eq".to_string()), "refl".to_string()),
    std::slice::from_ref(u),
  );
  LeanExpr::app(LeanExpr::app(eq_refl, alpha.clone()), a.clone())
}

/// Build `@Eq.symm.{u} α a b h : Eq b a` given `h : Eq a b`.
fn mk_eq_symm(
  u: &Level,
  alpha: &LeanExpr,
  a: &LeanExpr,
  b: &LeanExpr,
  h: &LeanExpr,
) -> LeanExpr {
  let eq_symm = mk_const(
    &Name::str(Name::str(Name::anon(), "Eq".to_string()), "symm".to_string()),
    std::slice::from_ref(u),
  );
  LeanExpr::app(
    LeanExpr::app(
      LeanExpr::app(LeanExpr::app(eq_symm, alpha.clone()), a.clone()),
      b.clone(),
    ),
    h.clone(),
  )
}

/// Build `@Eq.ndrec.{u_1, u_2} α a motive prf b h : motive b`.
///
/// `u_1` is the motive's result universe, `u_2` is the type `α`'s universe.
#[allow(clippy::too_many_arguments)]
fn mk_eq_ndrec(
  u1: &Level,
  u2: &Level,
  alpha: &LeanExpr,
  a: &LeanExpr,
  motive: &LeanExpr,
  prf: &LeanExpr,
  b: &LeanExpr,
  h: &LeanExpr,
) -> LeanExpr {
  let ndrec = mk_const(
    &Name::str(Name::str(Name::anon(), "Eq".to_string()), "ndrec".to_string()),
    &[u1.clone(), u2.clone()],
  );
  mk_app_n(
    ndrec,
    &[
      alpha.clone(),
      a.clone(),
      motive.clone(),
      prf.clone(),
      b.clone(),
      h.clone(),
    ],
  )
}

/// Build `@HEq.{u} α a β b`.
fn mk_heq(
  u: &Level,
  alpha: &LeanExpr,
  a: &LeanExpr,
  beta: &LeanExpr,
  b: &LeanExpr,
) -> LeanExpr {
  let heq = mk_const(
    &Name::str(Name::anon(), "HEq".to_string()),
    std::slice::from_ref(u),
  );
  mk_app_n(heq, &[alpha.clone(), a.clone(), beta.clone(), b.clone()])
}

/// Build `@HEq.refl.{u} α a : HEq a a`.
fn mk_heq_refl(u: &Level, alpha: &LeanExpr, a: &LeanExpr) -> LeanExpr {
  let heq_refl = mk_const(
    &Name::str(Name::str(Name::anon(), "HEq".to_string()), "refl".to_string()),
    std::slice::from_ref(u),
  );
  LeanExpr::app(LeanExpr::app(heq_refl, alpha.clone()), a.clone())
}

/// Build `@eq_of_heq.{u} α a b h : Eq a b` given `h : HEq a b`.
fn mk_eq_of_heq(
  u: &Level,
  alpha: &LeanExpr,
  a: &LeanExpr,
  b: &LeanExpr,
  h: &LeanExpr,
) -> LeanExpr {
  let eq_of_heq = mk_const(
    &Name::str(Name::anon(), "eq_of_heq".to_string()),
    std::slice::from_ref(u),
  );
  mk_app_n(eq_of_heq, &[alpha.clone(), a.clone(), b.clone(), h.clone()])
}

/// Build `.brecOn.eq` type and value (FVar-based).
///
/// Type: `∀ binders, @Eq (motive_ci args) (brecOn args) (F_ci args (go args).2)`
/// Value: Recursor-based case-split proof with Eq.refl minors.
#[allow(clippy::too_many_arguments)]
fn build_type_brecon_eq_fvar(
  ci: usize,
  target_ind_name: &Name,
  _rec_val: &RecursorVal,
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
  // Specialization params for nested auxiliaries (e.g., [Tree] for List
  // specialized to Tree). Empty for non-nested members.
  cases_on_spec_params: &[LeanExpr],
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

  // Target constructor list and counts, needed by both the simple and
  // generalized value paths.
  let ctor_counts: Vec<usize> = motive_decls
    .iter()
    .map(|md| {
      let mut ty = md.domain.clone();
      let mut last_dom = ty.clone();
      loop {
        match ty.as_data() {
          ExprData::ForallE(_, dom, body, _, _) => {
            last_dom = dom.clone();
            ty = body.clone();
          },
          _ => break,
        }
      }
      let (head, _) = decompose_apps(&last_dom);
      match head.as_data() {
        ExprData::Const(name, _, _) | ExprData::Fvar(name, _) => {
          match lean_env.get(name).as_deref() {
            Some(ConstantInfo::InductInfo(v)) => v.ctors.len(),
            _ => 0,
          }
        },
        _ => 0,
      }
    })
    .collect();
  let target_ctors: Vec<Name> = match lean_env.get(target_ind_name).as_deref() {
    Some(ConstantInfo::InductInfo(v)) => v.ctors.clone(),
    _ => vec![],
  };
  let minor_offset: usize = ctor_counts[..ci].iter().sum();

  // casesOn universe args (shared between simple and indexed paths).
  let eq_cases_univs: Vec<Level> = {
    let (head, _) = decompose_apps(&_major_decls[0].domain);
    if let ExprData::Const(_, lvls, _) = head.as_data() {
      std::iter::once(Level::zero()).chain(lvls.iter().cloned()).collect()
    } else {
      std::iter::once(Level::zero())
        .chain(rec_univs.iter().skip(1).cloned())
        .collect()
    }
  };
  let cases_on_name = Name::str(target_ind_name.clone(), "casesOn".to_string());

  // --- Indexed path ---
  //
  // When the target inductive has indices, Lean's `cases` tactic
  // generalizes them with `Eq` proofs and the major with an `HEq` proof
  // before applying `casesOn`. Each minor then proves the original goal
  // via a chain of `Eq.ndrec` applications that rewrite the outer indices
  // into the constructor's return indices, and one final `Eq.ndrec` that
  // rewrites the outer major into the constructor-applied value via
  // `Eq.symm ∘ eq_of_heq`.
  //
  // See `refs/lean4/src/Lean/Meta/Tactic/Cases.lean::generalizeIndices'`
  // and `refs/lean4/src/Lean/Meta/Tactic/Induction.lean` for Lean's
  // construction.
  let n_indices = _index_decls.len();
  if n_indices > 0 {
    let eq_value_opt = build_indexed_eq_value(
      ci,
      &target_ctors,
      brecon_name,
      go_name,
      rec_univs,
      param_fvars,
      motive_fvars,
      motive_decls,
      index_fvars,
      _index_decls,
      major_fvars,
      _major_decls,
      f_fvars,
      all_decls,
      minor_doms,
      &ctor_counts,
      minor_offset,
      elim_level,
      &cases_on_name,
      &eq_cases_univs,
      cases_on_spec_params,
    );
    if let Some(eq_value) = eq_value_opt {
      return Some((eq_type, eq_value));
    }
    // Fall through to the simple path if the indexed construction
    // couldn't be completed (e.g., missing ctor info).
  }

  // --- Simple value path (non-indexed) ---
  // Build via casesOn (matching Lean's `cases` tactic + `refl`).
  // casesOn has binder order: params, motive, indices, major, minors
  // (different from rec's: params, motives, minors, indices, major)
  // Only the target motive (ci) and target minors are present.

  let mut eq_val = mk_const(&cases_on_name, &eq_cases_univs);

  if !cases_on_spec_params.is_empty() {
    // Nested auxiliary: apply the casesOn's own params (spec_params).
    // These replace the ext inductive's params (e.g., List's α := Tree
    // or List's α := RoseA α). Block params are NOT applied separately —
    // the spec params already cover the casesOn's param slots.
    eq_val = mk_app_n(eq_val, cases_on_spec_params);
  } else {
    // Original member: apply block params as casesOn params.
    eq_val = mk_app_n(eq_val, param_fvars);
  }

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
  //
  // `ctor_counts`, `target_ctors`, and `minor_offset` were computed before
  // branching into the indexed path.

  for (ctor_idx, _ctor_name) in target_ctors.iter().enumerate() {
    let mi = minor_offset + ctor_idx;
    if mi >= minor_doms.len() {
      break;
    }
    let minor_dom = &minor_doms[mi];

    // Open minor fields. In FVar form, IH fields have motive FVars as heads.
    // casesOn strips IH fields, so we only open non-IH fields.
    let n_minor_fields = super::expr_utils::count_foralls(minor_dom);
    let (_mfield_fvars, mut mfield_decls, minor_ret) =
      forall_telescope(minor_dom, n_minor_fields, &format!("tbeqf{mi}"), 0);

    // Head-reduce field domains — same rationale as `build_below_minor` and
    // `build_type_minor_premise_fvar`. Lean's stored .brecOn.eq value reduces
    // lambda-application redexes in field binder types (e.g. `v : (λ_:α. Json) k`
    // becomes `v : Json`). Without this we end up with a structural mismatch
    // on the binder types of minors for nested auxiliaries.
    for decl in &mut mfield_decls {
      decl.domain = super::expr_utils::beta_reduce(&decl.domain);
    }

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
// Indexed-inductive `.brecOn.eq` value construction
// =========================================================================

/// Build the value of `.brecOn.eq` for an indexed inductive.
///
/// Replicates the output of Lean's `cases` tactic applied to an indexed
/// inductive: `generalizeIndices` followed by `casesOn` with one `refl`
/// per case. See `refs/lean4/src/Lean/Meta/Tactic/Cases.lean`.
///
/// ```text
/// casesOn.{0} (spec_params | params)
///   (λ new_idxs new_major.
///      ∀h_0:Eq _ outer_idx_0 new_idx_0. …
///      ∀h_major:HEq (I outer_idxs) outer_major (I new_idxs) new_major.
///      Eq (motive outer_idxs outer_major)
///         (brecOn motive outer_idxs outer_major F_1)
///         (F_1 outer_idxs outer_major (go … F_1).2))
///   outer_idxs… outer_major
///   minor_1 … minor_N
///   (Eq.refl outer_idx_0) … (HEq.refl outer_major)
/// ```
///
/// Each minor's body chains `Eq.ndrec` over each index, then one final
/// `Eq.ndrec` for the major discharged via `Eq.symm ∘ eq_of_heq`. When
/// `ret_args[i]` is an expression (not a bound fvar), the intermediate
/// motive adds an extra major binder that is consumed by applying the
/// `Eq.ndrec` result to the outer major.
#[allow(clippy::too_many_arguments)]
fn build_indexed_eq_value(
  ci: usize,
  target_ctors: &[Name],
  brecon_name: &Name,
  go_name: &Name,
  rec_univs: &[Level],
  param_fvars: &[LeanExpr],
  motive_fvars: &[LeanExpr],
  _motive_decls: &[LocalDecl],
  index_fvars: &[LeanExpr],
  index_decls: &[LocalDecl],
  major_fvars: &[LeanExpr],
  major_decls: &[LocalDecl],
  f_fvars: &[LeanExpr],
  all_decls: &[LocalDecl],
  minor_doms: &[LeanExpr],
  _ctor_counts: &[usize],
  minor_offset: usize,
  elim_level: &Level,
  cases_on_name: &Name,
  cases_on_univs: &[Level],
  cases_on_spec_params: &[LeanExpr],
) -> Option<LeanExpr> {
  let n_indices = index_decls.len();
  let outer_major = &major_fvars[0];
  let major_type = &major_decls[0].domain;

  // Use level 1 for generalization Eq/HEq types. All inductives with
  // indices generating `.brecOn.eq` live in `Type` (Sort 1); if we ever
  // encounter `Sort 0` indices we will need per-index precomputed levels.
  let one = Level::succ(Level::zero());

  // Extract the FVar names for outer indices and major so we can abstract
  // them into new-index / new-major binders.
  let index_fvar_names: Vec<Name> = index_fvars
    .iter()
    .filter_map(|e| match e.as_data() {
      ExprData::Fvar(n, _) => Some(n.clone()),
      _ => None,
    })
    .collect();
  if index_fvar_names.len() != n_indices {
    return None;
  }
  let major_fvar_name = match outer_major.as_data() {
    ExprData::Fvar(n, _) => n.clone(),
    _ => return None,
  };

  // OUTER_Eq_body: `Eq (motive outer_idxs outer_major) (brecOn …) (F_1 …)`
  let outer_eq_body = {
    let all_fvars_outer: Vec<LeanExpr> = param_fvars
      .iter()
      .chain(motive_fvars.iter())
      .chain(index_fvars.iter())
      .chain(std::iter::once(outer_major))
      .chain(f_fvars.iter())
      .cloned()
      .collect();
    let brecon_app =
      mk_app_n(mk_const(brecon_name, rec_univs), &all_fvars_outer);
    let go_app = mk_app_n(mk_const(go_name, rec_univs), &all_fvars_outer);
    let go_snd = LeanExpr::proj(
      Name::str(Name::anon(), "PProd".to_string()),
      Nat::from(1u64),
      go_app,
    );
    let motive_ci_app = mk_app_n(
      mk_app_n(motive_fvars[ci].clone(), index_fvars),
      std::slice::from_ref(outer_major),
    );
    let mut f_ci_app = f_fvars[ci].clone();
    f_ci_app = mk_app_n(f_ci_app, index_fvars);
    f_ci_app = LeanExpr::app(f_ci_app, outer_major.clone());
    f_ci_app = LeanExpr::app(f_ci_app, go_snd);
    mk_eq(elim_level, &motive_ci_app, &brecon_app, &f_ci_app)
  };

  // --- Build motive_wrapped: λ new_idxs new_major. ∀h_i. ∀h_major. OUTER_Eq_body ---
  let mut new_idx_decls: Vec<LocalDecl> = Vec::with_capacity(n_indices);
  let mut new_idx_fvars: Vec<LeanExpr> = Vec::with_capacity(n_indices);
  for (i, idx_decl) in index_decls.iter().enumerate() {
    let (fv_name, fv) = fresh_fvar("ieq_ni", i);
    new_idx_decls.push(LocalDecl {
      fvar_name: fv_name,
      binder_name: idx_decl.binder_name.clone(),
      domain: idx_decl.domain.clone(),
      info: idx_decl.info.clone(),
    });
    new_idx_fvars.push(fv);
  }
  let new_major_type =
    build_specialized_major_type(major_type, index_fvars, &new_idx_fvars);
  let (new_major_name, new_major_fvar) = fresh_fvar("ieq_nm", 0);
  let new_major_decl = LocalDecl {
    fvar_name: new_major_name,
    binder_name: Name::str(Name::anon(), "x".to_string()),
    domain: new_major_type.clone(),
    info: BinderInfo::Default,
  };
  let mut mw_decls: Vec<LocalDecl> = Vec::new();
  for (i, idx_decl) in index_decls.iter().enumerate() {
    let eq_ty =
      mk_eq(&one, &idx_decl.domain, &index_fvars[i], &new_idx_fvars[i]);
    let (h_name, _) = fresh_fvar("ieq_h", i);
    mw_decls.push(LocalDecl {
      fvar_name: h_name,
      binder_name: Name::str(Name::anon(), "h".to_string()),
      domain: eq_ty,
      info: BinderInfo::Default,
    });
  }
  let heq_ty =
    mk_heq(&one, major_type, outer_major, &new_major_type, &new_major_fvar);
  let (hm_name, _) = fresh_fvar("ieq_hm", 0);
  mw_decls.push(LocalDecl {
    fvar_name: hm_name,
    binder_name: Name::str(Name::anon(), "h".to_string()),
    domain: heq_ty,
    info: BinderInfo::Default,
  });
  let mw_body = mk_forall(outer_eq_body.clone(), &mw_decls);
  let mut motive_binders: Vec<LocalDecl> = new_idx_decls.clone();
  motive_binders.push(new_major_decl.clone());
  let motive_wrapped = mk_lambda(mw_body, &motive_binders);

  // --- casesOn head with params + motive + outer indices + outer major ---
  let mut eq_val = mk_const(cases_on_name, cases_on_univs);
  if !cases_on_spec_params.is_empty() {
    eq_val = mk_app_n(eq_val, cases_on_spec_params);
  } else {
    eq_val = mk_app_n(eq_val, param_fvars);
  }
  eq_val = LeanExpr::app(eq_val, motive_wrapped);
  eq_val = mk_app_n(eq_val, index_fvars);
  eq_val = LeanExpr::app(eq_val, outer_major.clone());

  // --- Build each minor ---
  for (ctor_idx, _ctor_name) in target_ctors.iter().enumerate() {
    let mi = minor_offset + ctor_idx;
    if mi >= minor_doms.len() {
      break;
    }
    let minor_dom = &minor_doms[mi];

    let n_minor_fields = super::expr_utils::count_foralls(minor_dom);
    let (_mfield_fvars, mut mfield_decls, minor_ret) =
      forall_telescope(minor_dom, n_minor_fields, &format!("ieqf{mi}"), 0);
    for decl in &mut mfield_decls {
      decl.domain = super::expr_utils::beta_reduce(&decl.domain);
    }
    let non_ih_decls: Vec<LocalDecl> = mfield_decls
      .into_iter()
      .filter(|d| find_motive_fvar(&d.domain, motive_fvars).is_none())
      .collect();

    // minor_ret has shape `motive_ci <ret_idxs> <major>`, so the first
    // `n_indices` arguments after the motive head are the ret_idxs. The
    // last argument (the major) is a full ctor-applied term, constructed
    // by us separately as `ctor_applied` — we don't read it here.
    let (_, minor_ret_args) = decompose_apps(&minor_ret);
    if minor_ret_args.len() < n_indices {
      return None;
    }
    let ret_args: Vec<LeanExpr> = minor_ret_args[..n_indices].to_vec();

    // Build `C (spec_params|params) non_ih_fields`.
    let ctor_name = &target_ctors[ctor_idx];
    let ctor_univs: Vec<Level> = if !cases_on_spec_params.is_empty() {
      cases_on_univs.iter().skip(1).cloned().collect()
    } else {
      rec_univs.iter().skip(1).cloned().collect()
    };
    let mut ctor_applied = mk_const(ctor_name, &ctor_univs);
    if !cases_on_spec_params.is_empty() {
      ctor_applied = mk_app_n(ctor_applied, cases_on_spec_params);
    } else {
      ctor_applied = mk_app_n(ctor_applied, param_fvars);
    }
    for decl in &non_ih_decls {
      ctor_applied =
        LeanExpr::app(ctor_applied, LeanExpr::fvar(decl.fvar_name.clone()));
    }

    // Base (major) continuation: `λ h_major. Eq.ndrec … (Eq.refl …) outer_major (Eq.symm (eq_of_heq h_major))`.
    let (t_name, t_fvar) = fresh_fvar("ieq_mt", ctor_idx);
    let major_motive_body =
      subst_fvar(&outer_eq_body, &major_fvar_name, &t_fvar);
    let major_motive = LeanExpr::lam(
      Name::str(Name::anon(), "t".to_string()),
      major_type.clone(),
      abstract_fvar(&major_motive_body, &t_name, 0),
      BinderInfo::Default,
    );
    let inner_eq_refl = {
      let motive_ci_ctor = mk_app_n(
        mk_app_n(motive_fvars[ci].clone(), index_fvars),
        std::slice::from_ref(&ctor_applied),
      );
      let inner_brecon_all: Vec<LeanExpr> = param_fvars
        .iter()
        .chain(motive_fvars.iter())
        .chain(index_fvars.iter())
        .chain(std::iter::once(&ctor_applied))
        .chain(f_fvars.iter())
        .cloned()
        .collect();
      let inner_brecon =
        mk_app_n(mk_const(brecon_name, rec_univs), &inner_brecon_all);
      mk_app_n(
        mk_const(
          &Name::str(
            Name::str(Name::anon(), "Eq".to_string()),
            "refl".to_string(),
          ),
          std::slice::from_ref(elim_level),
        ),
        &[motive_ci_ctor, inner_brecon],
      )
    };
    let specialized_major_type =
      build_specialized_major_type(major_type, index_fvars, &ret_args);
    let heq_for_minor = mk_heq(
      &one,
      major_type,
      outer_major,
      &specialized_major_type,
      &ctor_applied,
    );
    let (hm_name, hm_fvar) = fresh_fvar("ieq_hm_min", ctor_idx);
    let hm_decl = LocalDecl {
      fvar_name: hm_name.clone(),
      binder_name: Name::str(Name::anon(), "h".to_string()),
      domain: heq_for_minor,
      info: BinderInfo::Default,
    };
    let eq_of_heq_val =
      mk_eq_of_heq(&one, major_type, outer_major, &ctor_applied, &hm_fvar);
    let eq_symm_val =
      mk_eq_symm(&one, major_type, outer_major, &ctor_applied, &eq_of_heq_val);
    // Inner Eq.ndrec's motive returns `Eq.{elim_level} …` which is in
    // `Prop` (Sort 0). Hence its u_1 is 0, not `elim_level`.
    let ndrec_major = mk_eq_ndrec(
      &Level::zero(),
      &one,
      major_type,
      &ctor_applied,
      &major_motive,
      &inner_eq_refl,
      outer_major,
      &eq_symm_val,
    );
    let mut proof = mk_lambda(ndrec_major, std::slice::from_ref(&hm_decl));

    // Chain Eq.ndrec for each index, inside-out (i = n-1 .. 0).
    for i in (0..n_indices).rev() {
      let ret_arg = &ret_args[i];
      let outer_idx = &index_fvars[i];
      let idx_type = &index_decls[i].domain;

      let simple_fvar_opt = match ret_arg.as_data() {
        ExprData::Fvar(name, _) => {
          if non_ih_decls.iter().any(|d| &d.fvar_name == name) {
            Some(name.clone())
          } else {
            None
          }
        },
        _ => None,
      };

      if let Some(ret_fvar_name) = simple_fvar_opt {
        let (x_name, x_fvar) = fresh_fvar("ieq_x", i);

        // Collect dependent fields — those declared AFTER `ret_fvar_name`
        // whose types reference it. Lean rebinds these in the motive
        // lambda and the `Eq.ndrec` is applied to the original fvars
        // after the transport. E.g. `BVExpr.const {n} (v:BitVec n)`
        // rebinds `v` when generalizing `n`.
        let ret_field_pos =
          non_ih_decls.iter().position(|d| &d.fvar_name == &ret_fvar_name);
        let dep_fields: Vec<LocalDecl> = match ret_field_pos {
          Some(idx) => non_ih_decls
            .iter()
            .enumerate()
            .skip(idx + 1)
            .filter(|(_, d)| expr_contains_fvar(&d.domain, &ret_fvar_name))
            .map(|(_, d)| d.clone())
            .collect(),
          None => Vec::new(),
        };

        // Fresh renamed fvars for dep fields in the motive-lambda's body
        // (the view at generalized x_i).
        let dep_renamed: Vec<(Name, LeanExpr)> = (0..dep_fields.len())
          .map(|k| fresh_fvar(&format!("ieq_df{i}"), k))
          .collect();

        let motive_lam = build_index_motive_simple(
          i,
          &ret_args,
          &ret_fvar_name,
          &dep_fields,
          &dep_renamed,
          index_fvars,
          index_decls,
          major_type,
          outer_major,
          &ctor_applied,
          &outer_eq_body,
          &one,
          &x_name,
          &x_fvar,
          idx_type,
        );

        // Lift the inner proof:
        //   1. Substitute ret_fvar → outer_idx_i  (outer-side view).
        //   2. Substitute each dep_field's fvar → its renamed fvar (new
        //      binders at the outer_idx_i view have the outer-side type).
        //   3. Wrap with `λ renamed_dep_fields`.
        let mut lifted_proof = subst_fvar(&proof, &ret_fvar_name, outer_idx);
        for (orig, (_, renamed)) in dep_fields.iter().zip(dep_renamed.iter()) {
          lifted_proof = subst_fvar(&lifted_proof, &orig.fvar_name, renamed);
        }
        // Build λ-decls for the renamed dep fields. Their types come
        // from the original dep_fields' domains with ret_fvar_name
        // replaced by outer_idx_i (the outer-side view).
        let renamed_decls: Vec<LocalDecl> = dep_fields
          .iter()
          .zip(dep_renamed.iter())
          .map(|(orig, (rn_name, _))| LocalDecl {
            fvar_name: rn_name.clone(),
            binder_name: orig.binder_name.clone(),
            domain: subst_fvar(&orig.domain, &ret_fvar_name, outer_idx),
            info: orig.info.clone(),
          })
          .collect();
        if !renamed_decls.is_empty() {
          lifted_proof = mk_lambda(lifted_proof, &renamed_decls);
        }

        let (h_name, h_fvar) = fresh_fvar("ieq_hs", i);
        let h_decl = LocalDecl {
          fvar_name: h_name.clone(),
          binder_name: Name::str(Name::anon(), "h".to_string()),
          domain: mk_eq(&one, idx_type, outer_idx, ret_arg),
          info: BinderInfo::Default,
        };
        let mut ndrec_i = mk_eq_ndrec(
          &Level::zero(),
          &one,
          idx_type,
          outer_idx,
          &motive_lam,
          &lifted_proof,
          ret_arg,
          &h_fvar,
        );
        // Apply the Eq.ndrec result to each dep-field's original fvar
        // to consume the ∀-binders added to motive_lambda_i.
        for orig in &dep_fields {
          ndrec_i =
            LeanExpr::app(ndrec_i, LeanExpr::fvar(orig.fvar_name.clone()));
        }
        proof = mk_lambda(ndrec_i, std::slice::from_ref(&h_decl));
      } else {
        let (x_name, x_fvar) = fresh_fvar("ieq_x", i);
        let (t_inner_name, t_inner_fvar) = fresh_fvar("ieq_ti", i);
        let motive_lam = build_index_motive_complex(
          i,
          &ret_args,
          &index_fvar_names,
          &major_fvar_name,
          index_fvars,
          index_decls,
          major_type,
          &ctor_applied,
          &outer_eq_body,
          &one,
          &x_name,
          &x_fvar,
          &t_inner_name,
          &t_inner_fvar,
          idx_type,
        );

        // For the complex case, `motive_lambda_i ret_arg_i` has shape
        //   ∀t:(I ret_args[0..=i] outer_later_idxs). … body …
        // so the `proof_at_a` must bind `t` and substitute
        // `outer_major → t` in the inner proof.
        //
        // Outer indices j < i have already been rewritten to `ret_args[j]`
        // by outer Eq.ndrecs, so we use `ret_args[j]` for positions j ≤ i
        // and the outer `index_fvars[j]` for positions j > i. This matches
        // what Lean's `cases` tactic produces.
        let partial_major_ty_at_ret =
          build_major_type_with_partial_specialization(
            major_type,
            index_fvars,
            &ret_args,
            i,
          );
        // Substitute outer indices j ≤ i to their constructor-specialized
        // values `ret_args[j]` in the inner proof before wrapping. This
        // bakes in the rewrites that the outer Eq.ndrecs (for j < i) and
        // the current Eq.ndrec (for j == i) perform conceptually, matching
        // the shape Lean's `cases` tactic produces for complex-index cases.
        // Without this, the `h_m` binder's HEq type (inside the stored
        // `proof` from the major Eq.ndrec construction) still references
        // outer index fvars, producing a term that is definitionally but
        // not alpha-equal to Lean's.
        let proof_specialized =
          subst_outer_indices_upto(&proof, &index_fvar_names, &ret_args, i + 1);
        let proof_with_t =
          subst_fvar(&proof_specialized, &major_fvar_name, &t_inner_fvar);
        let t_decl = LocalDecl {
          fvar_name: t_inner_name.clone(),
          binder_name: Name::str(Name::anon(), "t".to_string()),
          domain: partial_major_ty_at_ret,
          info: BinderInfo::Default,
        };
        let proof_t = mk_lambda(proof_with_t, std::slice::from_ref(&t_decl));

        let (h_name, h_fvar) = fresh_fvar("ieq_hc", i);
        let h_decl = LocalDecl {
          fvar_name: h_name.clone(),
          binder_name: Name::str(Name::anon(), "h".to_string()),
          domain: mk_eq(&one, idx_type, outer_idx, ret_arg),
          info: BinderInfo::Default,
        };
        let symm_h = mk_eq_symm(&one, idx_type, outer_idx, ret_arg, &h_fvar);
        let ndrec_i = mk_eq_ndrec(
          &Level::zero(),
          &one,
          idx_type,
          ret_arg,
          &motive_lam,
          &proof_t,
          outer_idx,
          &symm_h,
        );
        // Consume the extra ∀t by applying the Eq.ndrec result to the
        // outer major.
        let ndrec_applied = LeanExpr::app(ndrec_i, outer_major.clone());
        proof = mk_lambda(ndrec_applied, std::slice::from_ref(&h_decl));
      }
    }

    let minor_value = mk_lambda(proof, &non_ih_decls);
    eq_val = LeanExpr::app(eq_val, minor_value);
  }

  // --- Discharge Eq/HEq generalizations with refl ---
  for (idx_decl, idx_fv) in index_decls.iter().zip(index_fvars.iter()) {
    eq_val = LeanExpr::app(eq_val, mk_eq_refl(&one, &idx_decl.domain, idx_fv));
  }
  eq_val = LeanExpr::app(eq_val, mk_heq_refl(&one, major_type, outer_major));

  Some(mk_lambda(eq_val, all_decls))
}

/// Build the motive-lambda for `Eq.ndrec` at index `i` in the simple case
/// (where `ret_args[i]` is a field FVar). The motive has shape
///
///     λ x_i. ∀(dep_fields). ∀h_{i+1}…h_major. OUTER_Eq_body
///
/// where `dep_fields` are any fields declared after `ret_fvar_name` in
/// the constructor whose type references it. Lean rebinds them with the
/// index generalized to `x_i`. The ret-arg FVar is substituted by `x_i`
/// throughout the body.
#[allow(clippy::too_many_arguments)]
fn build_index_motive_simple(
  i: usize,
  ret_args: &[LeanExpr],
  ret_fvar_name: &Name,
  dep_fields: &[LocalDecl],
  dep_renamed: &[(Name, LeanExpr)],
  index_fvars: &[LeanExpr],
  index_decls: &[LocalDecl],
  major_type: &LeanExpr,
  outer_major: &LeanExpr,
  ctor_applied: &LeanExpr,
  outer_eq_body: &LeanExpr,
  one: &Level,
  x_name: &Name,
  x_fvar: &LeanExpr,
  idx_type: &LeanExpr,
) -> LeanExpr {
  let n_indices = index_decls.len();
  // Substitution to apply to every expression inside the motive body:
  //   - `ret_fvar_name → x_fvar`  (generalize the index)
  //   - `orig_dep.fvar_name → renamed_dep_fvar`  (point at the new binders)
  let apply_subst = |e: &LeanExpr| -> LeanExpr {
    let mut out = subst_fvar(e, ret_fvar_name, x_fvar);
    for (orig, (_, renamed)) in dep_fields.iter().zip(dep_renamed.iter()) {
      out = subst_fvar(&out, &orig.fvar_name, renamed);
    }
    out
  };

  let mut decls: Vec<LocalDecl> = Vec::new();

  // Dep-field ∀ binders first, with substituted domains.
  for (orig, (rn_name, _)) in dep_fields.iter().zip(dep_renamed.iter()) {
    decls.push(LocalDecl {
      fvar_name: rn_name.clone(),
      binder_name: orig.binder_name.clone(),
      domain: apply_subst(&orig.domain),
      info: orig.info.clone(),
    });
  }

  // Eq binders for later indices.
  for j in (i + 1)..n_indices {
    let eq_ty =
      mk_eq(one, &index_decls[j].domain, &index_fvars[j], &ret_args[j]);
    let (h_name, _) = fresh_fvar("ieq_h_lam", j);
    decls.push(LocalDecl {
      fvar_name: h_name,
      binder_name: Name::str(Name::anon(), "h".to_string()),
      domain: apply_subst(&eq_ty),
      info: BinderInfo::Default,
    });
  }

  // HEq major binder, with the specialized major type and ctor_applied
  // substituted so `ret_fvar_name` points at `x_fvar` and the dep fields
  // point at the renamed binders.
  let spec_major_ty =
    build_specialized_major_type(major_type, index_fvars, ret_args);
  let heq_ty = mk_heq(
    one,
    major_type,
    outer_major,
    &apply_subst(&spec_major_ty),
    &apply_subst(ctor_applied),
  );
  let (hm_name, _) = fresh_fvar("ieq_hm_lam", i);
  decls.push(LocalDecl {
    fvar_name: hm_name,
    binder_name: Name::str(Name::anon(), "h".to_string()),
    domain: heq_ty,
    info: BinderInfo::Default,
  });

  // `outer_eq_body` doesn't reference field fvars, but `apply_subst` is
  // a no-op on such expressions, so applying it uniformly is safe.
  let body_inner = apply_subst(outer_eq_body);
  let body = mk_forall(body_inner, &decls);

  LeanExpr::lam(
    Name::str(Name::anon(), "x".to_string()),
    idx_type.clone(),
    abstract_fvar(&body, x_name, 0),
    BinderInfo::Implicit,
  )
}

/// Substitute outer index FVars in `expr`, replacing
/// `outer_idx_fvar_names[j]` with `replacements[j]` for `j in 0..up_to`.
///
/// This is used by the indexed `.brecOn.eq` construction: at each Eq.ndrec
/// level in the chain, outer indices j below the current level have already
/// been rewritten to their constructor-specialized values, and Lean's
/// `cases` tactic bakes these rewrites into inner motive bodies. Keeping
/// the outer fvars unsubstituted produces terms that are definitionally
/// equal to Lean's but not alpha-equal, which the aux_gen congruence check
/// rejects.
fn subst_outer_indices_upto(
  expr: &LeanExpr,
  outer_idx_fvar_names: &[Name],
  replacements: &[LeanExpr],
  up_to: usize,
) -> LeanExpr {
  let limit = up_to.min(outer_idx_fvar_names.len()).min(replacements.len());
  let mut out = expr.clone();
  for j in 0..limit {
    out = subst_fvar(&out, &outer_idx_fvar_names[j], &replacements[j]);
  }
  out
}

/// Whether an expression contains a free variable with the given name.
fn expr_contains_fvar(expr: &LeanExpr, fvar_name: &Name) -> bool {
  match expr.as_data() {
    ExprData::Fvar(n, _) => n == fvar_name,
    ExprData::App(f, a, _) => {
      expr_contains_fvar(f, fvar_name) || expr_contains_fvar(a, fvar_name)
    },
    ExprData::Lam(_, t, b, _, _) | ExprData::ForallE(_, t, b, _, _) => {
      expr_contains_fvar(t, fvar_name) || expr_contains_fvar(b, fvar_name)
    },
    ExprData::LetE(_, t, v, b, _, _) => {
      expr_contains_fvar(t, fvar_name)
        || expr_contains_fvar(v, fvar_name)
        || expr_contains_fvar(b, fvar_name)
    },
    ExprData::Proj(_, _, e, _) | ExprData::Mdata(_, e, _) => {
      expr_contains_fvar(e, fvar_name)
    },
    _ => false,
  }
}

/// Build the motive-lambda for `Eq.ndrec` at index `i` in the complex case
/// (where `ret_args[i]` is an expression). The motive has shape
///
///     λ x_i. ∀t:I <ret_args[<i]…, x_i, outer_{i+1..n-1}>.
///            ∀h_{i+1}…h_major. OUTER_Eq_body[outer_j → ret_args[j] for j<i,
///                                             outer_i → x_i, major → t]
///
/// with the extra `t` binder rebinding the major along the generalized
/// index. The `t` binder is consumed by applying the `Eq.ndrec` result to
/// `outer_major` at the call site.
///
/// Note on the `j < i` substitution: this matches what Lean's `cases`
/// tactic produces for the complex (non-fvar ret_args) path. Each outer
/// Eq.ndrec at level `j < i` has already rewritten `outer_j → ret_args[j]`
/// by the time this inner motive is evaluated, and Lean bakes those
/// rewrites into the motive body rather than leaving them as free
/// references to the outer index fvars. Without this substitution, the
/// motive's `∀t` type and body use `outer_j` where Lean uses the
/// constructor-specialized expression (see `Omega.Justification.brecOn.eq`:
/// the `tidy` branch generalizes both `s` and `c` to computed expressions,
/// and the inner motive at i=1 needs `tidyConstraint field_s field_c` as
/// the first index of the major type rather than the outer `s`).
#[allow(clippy::too_many_arguments)]
fn build_index_motive_complex(
  i: usize,
  ret_args: &[LeanExpr],
  outer_idx_fvar_names: &[Name],
  major_fvar_name: &Name,
  index_fvars: &[LeanExpr],
  index_decls: &[LocalDecl],
  major_type: &LeanExpr,
  ctor_applied: &LeanExpr,
  outer_eq_body: &LeanExpr,
  one: &Level,
  x_name: &Name,
  x_fvar: &LeanExpr,
  t_name: &Name,
  t_fvar: &LeanExpr,
  idx_type: &LeanExpr,
) -> LeanExpr {
  let n_indices = index_decls.len();
  // Partial major type: I params (ret_args[0..i]) x_i (outer_{i+1}..outer_{n-1}).
  // Outer indices `j < i` have already been rewritten to `ret_args[j]` by
  // the outer Eq.ndrec chain at this point.
  let partial_major_type = {
    let (head, args) = decompose_apps(major_type);
    let n_param_args = args.len().saturating_sub(n_indices);
    let mut spec = head;
    for p in &args[..n_param_args] {
      spec = LeanExpr::app(spec, p.clone());
    }
    for j in 0..n_indices {
      if j < i {
        spec = LeanExpr::app(spec, ret_args[j].clone());
      } else if j == i {
        spec = LeanExpr::app(spec, x_fvar.clone());
      } else {
        spec = LeanExpr::app(spec, index_fvars[j].clone());
      }
    }
    spec
  };

  // The motive body in the complex case substitutes outer indices j < i
  // to `ret_args[j]` (already rewritten by outer Eq.ndrecs), the outer
  // index at position `i` to `x_fvar`, and the outer major to `t_fvar`
  // inside `outer_eq_body`. Lean's `cases` tactic produces this shape for
  // indexed inductives with non-fvar return args: the inner `∀t` binder
  // rebinds the major at the partially-generalized type, and the Eq body
  // uses the new `t` in place of the outer major, with earlier indices
  // baked in at their constructor-specialized values.
  let apply_subst = |e: &LeanExpr| -> LeanExpr {
    let mut out =
      subst_outer_indices_upto(e, outer_idx_fvar_names, ret_args, i);
    if i < outer_idx_fvar_names.len() {
      out = subst_fvar(&out, &outer_idx_fvar_names[i], x_fvar);
    }
    out = subst_fvar(&out, major_fvar_name, t_fvar);
    out
  };

  let mut decls: Vec<LocalDecl> = Vec::new();
  for j in (i + 1)..n_indices {
    let eq_ty =
      mk_eq(one, &index_decls[j].domain, &index_fvars[j], &ret_args[j]);
    let (h_name, _) = fresh_fvar("ieq_h_lam_c", j);
    decls.push(LocalDecl {
      fvar_name: h_name,
      binder_name: Name::str(Name::anon(), "h".to_string()),
      domain: apply_subst(&eq_ty),
      info: BinderInfo::Default,
    });
  }
  let spec_major_ty =
    build_specialized_major_type(major_type, index_fvars, ret_args);
  let heq_ty = mk_heq(
    one,
    &partial_major_type,
    t_fvar,
    &apply_subst(&spec_major_ty),
    &apply_subst(ctor_applied),
  );
  let (hm_name, _) = fresh_fvar("ieq_hm_lam_c", i);
  decls.push(LocalDecl {
    fvar_name: hm_name,
    binder_name: Name::str(Name::anon(), "h".to_string()),
    domain: heq_ty,
    info: BinderInfo::Default,
  });

  let body_inner = apply_subst(outer_eq_body);
  let body = mk_forall(body_inner, &decls);
  let t_decl = LocalDecl {
    fvar_name: t_name.clone(),
    binder_name: Name::str(Name::anon(), "t".to_string()),
    domain: partial_major_type.clone(),
    info: BinderInfo::Default,
  };
  let body_with_t = mk_forall(body, std::slice::from_ref(&t_decl));
  LeanExpr::lam(
    Name::str(Name::anon(), "x".to_string()),
    idx_type.clone(),
    abstract_fvar(&body_with_t, x_name, 0),
    BinderInfo::Implicit,
  )
}

/// Build `I <params> <args>` — the major type with the given index args.
fn build_specialized_major_type(
  major_type: &LeanExpr,
  index_fvars: &[LeanExpr],
  ret_args: &[LeanExpr],
) -> LeanExpr {
  let (head, args) = decompose_apps(major_type);
  let n_indices = index_fvars.len();
  let n_param_args = args.len().saturating_sub(n_indices);
  let mut spec = head;
  for p in &args[..n_param_args] {
    spec = LeanExpr::app(spec, p.clone());
  }
  for r in ret_args {
    spec = LeanExpr::app(spec, r.clone());
  }
  spec
}

/// Build `I <params> <ret_args[0..=pos]> <index_fvars[pos+1..]>` — the
/// major type with indices 0..=pos specialized to their constructor-view
/// values (`ret_args[j]`) and indices j > pos left as outer FVars.
///
/// This is the "partially specialized" major type used at level `pos` of
/// the Eq.ndrec chain for complex indexed `.brecOn.eq`: at this level,
/// outer indices j < pos have been rewritten by outer Eq.ndrecs (hence
/// `ret_args[j]`), index `pos` is being rewritten by the current Eq.ndrec
/// (also at the base case value `ret_args[pos]`), and indices j > pos are
/// still outer fvars.
fn build_major_type_with_partial_specialization(
  major_type: &LeanExpr,
  index_fvars: &[LeanExpr],
  ret_args: &[LeanExpr],
  pos: usize,
) -> LeanExpr {
  let (head, args) = decompose_apps(major_type);
  let n_indices = index_fvars.len();
  let n_param_args = args.len().saturating_sub(n_indices);
  let mut spec = head;
  for p in &args[..n_param_args] {
    spec = LeanExpr::app(spec, p.clone());
  }
  for j in 0..n_indices {
    if j <= pos {
      spec = LeanExpr::app(spec, ret_args[j].clone());
    } else {
      spec = LeanExpr::app(spec, index_fvars[j].clone());
    }
  }
  spec
}

// =========================================================================
// Sort-level inference
// =========================================================================

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
    LevelData::Succ(l, _) => mk_level_succ(&subst_level(l, param, replacement)),
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
