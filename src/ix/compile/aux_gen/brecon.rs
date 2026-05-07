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

use rustc_hash::FxHashMap;

/// A generated `.brecOn` definition (or `.brecOn.go`, `.brecOn.eq`).
///
/// `is_unsafe` mirrors the parent inductive's `is_unsafe` flag. Lean's
/// `mkThmOrUnsafeDef` (`refs/lean4/src/Lean/Environment.lean:2797`) emits
/// `.brecOn.eq` as an unsafe `Defn` with `hints := .opaque` (instead of the
/// usual `Thm`) whenever the type or value references an unsafe constant —
/// for unsafe inductives this always triggers. `.brecOn` and `.brecOn.go`
/// likewise flip to `safety := .unsafe` via `mkDefinitionValInferringUnsafe`.
///
/// `is_prop` distinguishes the two generation paths:
/// - **Prop-level** (`IndPredBelow.lean`): a single `.brecOn` theorem per class;
///   never emits `.go` or `.eq`. Emitted as `Thm` (safe) or unsafe `Defn`.
/// - **Type-level** (`BRecOn.lean`): emits `.brecOn.go`, `.brecOn`, and
///   `.brecOn.eq`. `.go` and `.brecOn` are always `Defn`; `.eq` is `Thm`
///   (safe) or unsafe `Defn` with `hints := .opaque`.
#[derive(Clone)]
pub(crate) struct BRecOnDef {
  pub name: Name,
  pub level_params: Vec<Name>,
  pub typ: LeanExpr,
  pub value: LeanExpr,
  pub is_unsafe: bool,
  pub is_prop: bool,
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
  kctx: &mut crate::ix::compile::KernelCtx,
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
    let ind = match ind_ref {
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
      // Derive below names from below_consts (source-indexed, matching
      // canon_kenv's content hashes). Positions align with the canonical
      // flat block: 0..n_classes = primary belows, n_classes.. = aux belows.
      let below_names: Vec<Name> = below_consts
        .iter()
        .map(|bc| match bc {
          BelowConstant::Def(d) => d.name.clone(),
          BelowConstant::Indc(i) => i.name.clone(),
        })
        .collect();
      let defs = build_type_brecon_fvar(
        ci,
        rec_val,
        &brecon_name,
        all0,
        &below_names,
        lean_env,
        n_classes,
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
      let all0 = match lean_env.get(first_class_name) {
        Some(ConstantInfo::InductInfo(v)) => v.all[0].clone(),
        _ => first_class_name.clone(),
      };

      for j in 0..n_aux {
        let (aux_rec_name, aux_rec_val) = &canonical_recs[n_classes + j];
        // Derive source-indexed suffix from the aux rec's name
        // (aux_gen already names it `<all0>.rec_{source_j+1}`).
        let idx = super::below::aux_rec_suffix_idx(aux_rec_name).ok_or_else(|| {
          CompileError::InvalidMutualBlock {
            reason: format!(
              "brecOn aux recursor '{}' is not source-indexed; refusing to synthesize brecOn_{}",
              aux_rec_name.pretty(),
              j + 1,
            ),
          }
        })?;
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
        let below_names: Vec<Name> = below_consts
          .iter()
          .map(|bc| match bc {
            BelowConstant::Def(d) => d.name.clone(),
            BelowConstant::Indc(i) => i.name.clone(),
          })
          .collect();
        let defs = build_type_brecon_fvar(
          ci,
          aux_rec_val,
          &brecon_name,
          &all0,
          &below_names,
          lean_env,
          n_classes,
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
    if std::env::var("IX_BRECON_DEBUG").is_ok() {
      eprintln!(
        "[brecon-build] j={}, below_names[{}]={}, f_type={}",
        j,
        j,
        below_names[j].pretty(),
        f_type.pretty(),
      );
    }
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
    // Prop-level `.brecOn` references the parent `.rec` and mentions the
    // inductive; Lean's `mkThmOrUnsafeDef` flips to `Unsafe`+`Opaque` when
    // the inductive is unsafe.
    is_unsafe: ind.is_unsafe,
    is_prop: true,
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

// Infer the inductive sort level from the major premise domain.
//
// Matches Lean's `typeFormerTypeLevel (← inferType (← inferType major))`:
// finds the head constant of the major's type, looks it up in the
// environment, and peels foralls to get the resulting Sort level.
//
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
  below_names: &[Name],
  lean_env: &LeanEnv,
  n_classes: usize,
  stt: &crate::ix::compile::CompileState,
  kctx: &mut crate::ix::compile::KernelCtx,
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

  // below_names for each motive position in the canonical flat block.
  // Supplied by the caller (from `below_consts`), not locally constructed:
  // the aux suffixes are Lean-source-indexed (via `aux_rec_suffix_idx` on
  // the renamed aux_rec_name in `below::generate_below_constants`), so
  // these names match what `populate_canon_kenv_with_below` inserts
  // into `canon_kenv`. Building them here from `n_classes + canonical_i`
  // produces canonical-indexed names that the kernel can't resolve when
  // `perm` is non-identity, causing TcScope failures on
  // `mk_const(below_names[j], ...)` applications below.
  if below_names.len() != n_motives {
    return Err(CompileError::InvalidMutualBlock {
      reason: format!(
        "build_type_brecon_fvar({}): {} below constants for {} recursor motives",
        brecon_name.pretty(),
        below_names.len(),
        n_motives,
      ),
    });
  }
  let _ = all0;
  if std::env::var("IX_BRECON_DEBUG").is_ok() {
    eprintln!(
      "[brecon] building {} (ci={}): below_names={:?}",
      brecon_name.pretty(),
      ci,
      below_names.iter().map(|n| n.pretty()).collect::<Vec<_>>(),
    );
  }

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
  // Per-motive ilvl (major's sort level) and rlvl (= max ilvl elim_level).
  //
  // `ilvls` are also needed by `.brecOn.eq`: the HEq/Eq.ndrec/Eq.symm/
  // eq_of_heq applied to the major premise are parameterized by the
  // major's sort level, not a hardcoded `1`. A polymorphic indexed
  // inductive like `TRBTree α : TColor → TN2 → Type u` has major sort
  // level `u+1`, so HEq must be `HEq.{u+1}` — cf. `TRBTree.brecOn.eq`.
  let ilvls: Vec<Level> = {
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
        Ok(ilvl_j)
      })
      .collect::<Result<Vec<_>, _>>()?
  };
  // Match Lean's BRecOn.lean:220: `mkLevelMax ilvl lvl` — raw Level.max
  // with only zero elimination.
  let rlvls: Vec<Level> = ilvls
    .iter()
    .map(|ilvl_j| {
      if matches!(ilvl_j.as_data(), LevelData::Zero(_)) {
        elim_level.clone()
      } else if matches!(elim_level.as_data(), LevelData::Zero(_)) {
        ilvl_j.clone()
      } else {
        Level::max(ilvl_j.clone(), elim_level.clone())
      }
    })
    .collect();
  // The target's rlvl is used for the rec universe arg and go return type.
  let rlvl = &rlvls[ci];
  let ilvl = &ilvls[ci];

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
      below_names,
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
    let ext_n_params = match lean_env.get(&target_ind_name) {
      Some(ConstantInfo::InductInfo(v)) => try_nat_to_usize(&v.num_params)?,
      _ => 0,
    };
    major_args.into_iter().take(ext_n_params).collect()
  } else {
    vec![]
  };
  // Per-index sort levels — Lean's `mkEq` calls `getLevel idx_type` per
  // index. Without per-index inference we hard-coded `Sort 1`, which only
  // happened to be right for monomorphic-Type indices and broke the
  // `Eq.lvl[0]` check for indexed inductives whose index types live at
  // `Param u` / `Succ u` / `Type u+1` etc. (e.g. `PGame.Relabelling`,
  // `Monoid.CoprodI.NeWord`, `NFA.Path`, `Quiver.Path`, …).
  //
  // Compute the levels here while the index decls are still pushed into
  // the live `rtc` scope so `get_level` resolves any FVar references to
  // earlier indices/params correctly. Then pop them back to the state the
  // existing code below expects.
  let index_sort_levels: Vec<Level> = {
    rtc.push_locals(&index_decls);
    let mut out = Vec::with_capacity(index_decls.len());
    for d in &index_decls {
      out.push(rtc.get_level(&d.domain)?);
    }
    rtc.pop_locals(&index_decls);
    out
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
    &index_sort_levels,
    &major_fvars,
    &major_decls,
    &f_fvars,
    &f_decls,
    &all_decls,
    &all_fvars,
    below_names,
    &minor_doms,
    n_minors,
    &motive_ci_app,
    &elim_level,
    ilvl,
    lean_env,
    &cases_on_spec,
    rec_level_params,
    stt,
    kctx,
  );

  // Type-level `.brecOn.go` / `.brecOn` / `.brecOn.eq` all reference the
  // parent inductive's `.rec`, so Lean's `mkDefinitionValInferringUnsafe` /
  // `mkThmOrUnsafeDef` consistently propagate the recursor's `is_unsafe`.
  let is_unsafe = rec_val.is_unsafe;

  let mut results = vec![
    BRecOnDef {
      name: go_name,
      level_params: rec_level_params.clone(),
      typ: go_type,
      value: go_value,
      is_unsafe,
      is_prop: false,
    },
    BRecOnDef {
      name: brecon_name,
      level_params: rec_level_params.clone(),
      typ: brecon_type,
      value: brecon_value,
      is_unsafe,
      is_prop: false,
    },
  ];

  if let Some((eq_typ, eq_val)) = eq_result {
    results.push(BRecOnDef {
      name: eq_name,
      level_params: rec_level_params.clone(),
      typ: eq_typ,
      value: eq_val,
      is_unsafe,
      is_prop: false,
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
  // One sort level per index, computed by the caller via `TcScope::get_level`
  // on each `index_decls[i].domain` (matching Lean's `mkEq`, which calls
  // `getLevel idx_type`). Used as the universe arg of every `Eq.{·}` /
  // `Eq.refl.{·}` / `Eq.symm.{·}` / `Eq.ndrec.{_, ·}` that generalizes an
  // index in the indexed-eq construction.
  index_sort_levels: &[Level],
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
  // Major's sort level — the `u` in `HEq.{u}` / `Eq.ndrec.{_, u}` etc.
  // that generalize the major premise. For an inductive `I : ... → Sort v`,
  // this is `v`; e.g., for `TRBTree α : TColor → TN2 → Type u` it is `u+1`.
  major_level: &Level,
  lean_env: &LeanEnv,
  // Specialization params for nested auxiliaries (e.g., [Tree] for List
  // specialized to Tree). Empty for non-nested members.
  cases_on_spec_params: &[LeanExpr],
  // Threaded for `TcScope::is_def_eq` checks when deciding between
  // `Eq` and `HEq` binders in `motive_wrapped` and
  // `build_minor_via_cases_sim`'s remaining list.
  rec_level_params: &[Name],
  stt: &crate::ix::compile::CompileState,
  kctx: &mut crate::ix::compile::KernelCtx,
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
      while let ExprData::ForallE(_, dom, body, _, _) = ty.as_data() {
        last_dom = dom.clone();
        ty = body.clone();
      }
      let (head, _) = decompose_apps(&last_dom);
      match head.as_data() {
        ExprData::Const(name, _, _) | ExprData::Fvar(name, _) => {
          match lean_env.get(name) {
            Some(ConstantInfo::InductInfo(v)) => v.ctors.len(),
            _ => 0,
          }
        },
        _ => 0,
      }
    })
    .collect();
  let target_ctors: Vec<Name> = match lean_env.get(target_ind_name) {
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
      index_sort_levels,
      major_fvars,
      _major_decls,
      f_fvars,
      all_decls,
      minor_doms,
      &ctor_counts,
      minor_offset,
      elim_level,
      major_level,
      &cases_on_name,
      &eq_cases_univs,
      cases_on_spec_params,
      rec_level_params,
      stt,
      kctx,
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
  // One sort level per index (parallel to `index_decls`), pre-computed by
  // the caller via `TcScope::get_level` on each `idx_decl.domain`. Used
  // wherever we build an `Eq.{·}` that generalizes the i-th index, so the
  // resulting `Eq` constants live in the same universe Lean's `mkEq`
  // produces (level of `inferType idx`).
  index_sort_levels: &[Level],
  major_fvars: &[LeanExpr],
  major_decls: &[LocalDecl],
  f_fvars: &[LeanExpr],
  all_decls: &[LocalDecl],
  minor_doms: &[LeanExpr],
  _ctor_counts: &[usize],
  minor_offset: usize,
  elim_level: &Level,
  // Major's sort level (see `build_type_brecon_eq_fvar`). Applied to
  // HEq / HEq.refl / eq_of_heq / Eq.symm-on-major / the `u_2` of the
  // major-generalizing Eq.ndrec.
  major_level: &Level,
  cases_on_name: &Name,
  cases_on_univs: &[Level],
  cases_on_spec_params: &[LeanExpr],
  // Threaded to enable `TcScope::is_def_eq` checks for deciding between
  // `Eq` and `HEq` binders (matching Lean's `mkEqAndProof` in
  // `refs/lean4/src/Lean/Meta/Tactic/Cases.lean:30-37`).
  rec_level_params: &[Name],
  stt: &crate::ix::compile::CompileState,
  kctx: &mut crate::ix::compile::KernelCtx,
) -> Option<LeanExpr> {
  let n_indices = index_decls.len();
  let outer_major = &major_fvars[0];
  let major_type = &major_decls[0].domain;
  // Defensive sanity check — caller is supposed to provide one level per
  // index decl. If the parallel arrays disagree, fall back to `Sort 1`
  // (the historical hard-coded value) rather than panicking; that's
  // strictly no-worse than the pre-fix behavior for the affected index.
  let idx_sort = |i: usize| -> Level {
    index_sort_levels
      .get(i)
      .cloned()
      .unwrap_or_else(|| Level::succ(Level::zero()))
  };

  // Validate that `index_fvars` are all FVars — required for `fvar_order`
  // tracking in `build_minor_via_cases_sim`'s symm determination.
  let n_fvar_indices = index_fvars
    .iter()
    .filter(|e| matches!(e.as_data(), ExprData::Fvar(..)))
    .count();
  if n_fvar_indices != n_indices {
    return None;
  }
  // Validate that `outer_major` is a FVar (mirrors the same requirement).
  if !matches!(outer_major.as_data(), ExprData::Fvar(..)) {
    return None;
  }

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
  //
  // For dependently-indexed inductives (e.g. `ExBase : ∀ {u} {α : Q(Type u)}
  // (sα : Q(CommSemiring α)) (e : Q(α)), Type`), the TYPE of a later index
  // depends on EARLIER indices. In Lean's cases tactic, when generalizing,
  // the new indices are introduced with types that reference each other
  // (via inner-scope `bvar`s/fvars), NOT the outer fvars.
  //
  // We achieve this by substituting `outer_idx_j → new_idx_fvar_j` for
  // `j < i` when building each `new_idx_i`'s domain. Without this, a
  // later new_idx's domain would reference the OUTER index fvar,
  // producing a motive with incorrect bvar indices relative to what
  // Lean's `generalizeIndices` produces.
  let mut new_idx_decls: Vec<LocalDecl> = Vec::with_capacity(n_indices);
  let mut new_idx_fvars: Vec<LeanExpr> = Vec::with_capacity(n_indices);
  for (i, idx_decl) in index_decls.iter().enumerate() {
    let (fv_name, fv) = fresh_fvar("ieq_ni", i);
    // Substitute outer_idx_j → new_idx_fvar_j for j < i in the domain.
    // This matches what Lean's cases tactic produces for dependently-
    // indexed inductives.
    let mut fresh_domain = idx_decl.domain.clone();
    for j in 0..i {
      if let ExprData::Fvar(outer_name, _) = index_fvars[j].as_data() {
        fresh_domain = subst_fvar(&fresh_domain, outer_name, &new_idx_fvars[j]);
      }
    }
    new_idx_decls.push(LocalDecl {
      fvar_name: fv_name,
      binder_name: idx_decl.binder_name.clone(),
      domain: fresh_domain,
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
  // Decide between `Eq` and `HEq` for each index's equality binder,
  // matching Lean's `mkEqAndProof` in
  // `refs/lean4/src/Lean/Meta/Tactic/Cases.lean:30-37`. Lean uses
  // `isDefEq` on the outer and new index types:
  //   - `Eq α outer_idx new_idx`       if types defEq
  //   - `HEq α_outer outer_idx α_new new_idx`  otherwise
  //
  // Example of why defEq matters (not just syntactic match):
  //   - `Qq.Quoted α` is defined as `def Quoted (α : Expr) := Expr`,
  //     so it's a NON-DEPENDENT alias. `Q(Type u)` and `Q(Type u_1)`
  //     both unfold to `Expr` — defEq — so Lean uses `Eq`.
  //   - For `Quiver.Hom ... a b`, the signature IS dependent on a, b.
  //     With a ≠ a_1, it's NOT defEq — Lean uses `HEq`.
  //
  // We use `TcScope::is_def_eq` for the decision.
  let mut eq_tc =
    super::expr_utils::TcScope::new(all_decls, rec_level_params, stt, kctx);
  // Track which index binders are HEq (for the remaining-list construction
  // below in `build_minor_via_cases_sim`).
  let mut idx_is_heq: Vec<bool> = Vec::with_capacity(n_indices);
  let mut idx_new_types: Vec<LeanExpr> = Vec::with_capacity(n_indices);
  let mut mw_decls: Vec<LocalDecl> = Vec::new();
  for (i, idx_decl) in index_decls.iter().enumerate() {
    let outer_type = &idx_decl.domain;
    let new_type = &new_idx_decls[i].domain;
    let types_defeq = eq_tc.is_def_eq(outer_type, new_type);
    let eq_ty = if types_defeq {
      mk_eq(&idx_sort(i), outer_type, &index_fvars[i], &new_idx_fvars[i])
    } else {
      mk_heq(
        &idx_sort(i),
        outer_type,
        &index_fvars[i],
        new_type,
        &new_idx_fvars[i],
      )
    };
    let (h_name, _) = fresh_fvar("ieq_h", i);
    mw_decls.push(LocalDecl {
      fvar_name: h_name,
      binder_name: Name::str(Name::anon(), "h".to_string()),
      domain: eq_ty,
      info: BinderInfo::Default,
    });
    idx_is_heq.push(!types_defeq);
    idx_new_types.push(new_type.clone());
  }
  drop(eq_tc); // release the TC before building the rest of the term
  let heq_ty = mk_heq(
    major_level,
    major_type,
    outer_major,
    &new_major_type,
    &new_major_fvar,
  );
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
  //
  // Each minor's body is constructed via `build_minor_via_cases_sim`,
  // which simulates Lean's `cases + refl` tactic flow from
  // `refs/lean4/src/Lean/Meta/Constructions/BRecOn.lean:288-300` —
  // producing a proof term byte-equivalent to Lean's stored
  // `.brecOn.eq` value.
  for (ctor_idx, _ctor_name) in target_ctors.iter().enumerate() {
    let mi = minor_offset + ctor_idx;
    if mi >= minor_doms.len() {
      break;
    }
    let minor_dom = &minor_doms[mi];

    // Open the minor's field binders via `forall_telescope`, then
    // filter to non-IH fields (casesOn strips IH).
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

    // Extract the ctor's return-indices from `minor_ret`. Shape:
    // `motive_ci <ret_idxs> <major>` — the first `n_indices` args after
    // the motive head are the ret_idxs. The major arg is built
    // separately as `ctor_applied` below.
    let (_, minor_ret_args) = decompose_apps(&minor_ret);
    if minor_ret_args.len() < n_indices {
      return None;
    }
    let ret_args: Vec<LeanExpr> = minor_ret_args[..n_indices].to_vec();

    // Build `C (spec_params|params) non_ih_fields` — the ctor applied
    // to params and fields. Nested auxiliaries use `cases_on_spec_params`
    // in place of the block's `param_fvars`.
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

    // Build the minor body by simulating `cases + refl`.
    let minor_value = build_minor_via_cases_sim(
      ctor_idx,
      &non_ih_decls,
      &ret_args,
      &ctor_applied,
      &outer_eq_body,
      index_fvars,
      index_decls,
      index_sort_levels,
      outer_major,
      major_type,
      major_level,
      param_fvars,
      motive_fvars,
      f_fvars,
      &idx_is_heq,
    )?;

    eq_val = LeanExpr::app(eq_val, minor_value);
  }

  // --- Discharge Eq/HEq generalizations with refl ---
  //
  // For each index binder in motive_wrapped, we apply the matching refl:
  //   - `Eq.refl` if the binder was `Eq` (idx_is_heq[i] = false)
  //   - `HEq.refl` if the binder was `HEq` (idx_is_heq[i] = true)
  // This matches Lean's cases-tactic behavior where `generalizeIndices'`
  // supplies `eqRefls` of the matching kind (Eq/HEq) per
  // `refs/lean4/src/Lean/Meta/Tactic/Cases.lean:30-47`.
  for (i, (idx_decl, idx_fv)) in
    index_decls.iter().zip(index_fvars.iter()).enumerate()
  {
    let refl = if idx_is_heq[i] {
      mk_heq_refl(&idx_sort(i), &idx_decl.domain, idx_fv)
    } else {
      mk_eq_refl(&idx_sort(i), &idx_decl.domain, idx_fv)
    };
    eq_val = LeanExpr::app(eq_val, refl);
  }
  eq_val =
    LeanExpr::app(eq_val, mk_heq_refl(major_level, major_type, outer_major));

  Some(mk_lambda(eq_val, all_decls))
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

// =========================================================================
// Cases-tactic simulation for indexed `.brecOn.eq` minor-body construction
// =========================================================================
//
// To match Lean's stored `.brecOn.eq` byte-for-byte, each indexed minor's
// body is built by replicating the exact output of Lean's `cases + refl`
// tactic — see `refs/lean4/src/Lean/Meta/Constructions/BRecOn.lean:288-300`.
// For indexed inductives, `cases` runs `generalizeIndices` →
// `inductionCasesOn` → `unifyCasesEqs`, and each `unifyCasesEqs` iteration
// introduces one hypothesis (via `intro1`) and either applies `substCore`
// (emitting a 6-arg `Eq.ndrec`) or, for the `HEq` case, applies
// `heqToEq'` (producing an unreduced beta-redex
// `(λ eq_major. …) (eq_of_heq heq)`) and iterates.
//
// The resulting proof-term shape is a deep chain of `λ`-intros and 6-arg
// `Eq.ndrec`s, interleaved, with each `Eq.ndrec`'s motive being
// `λ abstracted_fvar. current_remaining_goal`, where `abstracted_fvar`
// is whichever side of the equation `substCore` abstracts (per its
// symm-direction rule in
// `refs/lean4/src/Lean/Meta/Tactic/UnifyEq.lean:127-134`).

/// Classified shape of an `Eq` or `HEq` binder's domain.
#[derive(Clone)]
enum EqBinderKind {
  /// `@Eq.{u} α lhs rhs`.
  Eq { alpha: LeanExpr, lhs: LeanExpr, rhs: LeanExpr, level: Level },
  /// `@HEq.{u} α a β b`.
  HEq {
    alpha: LeanExpr,
    a: LeanExpr,
    beta: LeanExpr,
    b: LeanExpr,
    level: Level,
  },
}

/// Apply a FVar → expression substitution across an `EqBinderKind`.
fn subst_in_eq_binder_kind(
  kind: &EqBinderKind,
  fvar_name: &Name,
  replacement: &LeanExpr,
) -> EqBinderKind {
  match kind {
    EqBinderKind::Eq { alpha, lhs, rhs, level } => EqBinderKind::Eq {
      alpha: subst_fvar(alpha, fvar_name, replacement),
      lhs: subst_fvar(lhs, fvar_name, replacement),
      rhs: subst_fvar(rhs, fvar_name, replacement),
      level: level.clone(),
    },
    EqBinderKind::HEq { alpha, a, beta, b, level } => EqBinderKind::HEq {
      alpha: subst_fvar(alpha, fvar_name, replacement),
      a: subst_fvar(a, fvar_name, replacement),
      beta: subst_fvar(beta, fvar_name, replacement),
      b: subst_fvar(b, fvar_name, replacement),
      level: level.clone(),
    },
  }
}

/// Build `@Eq.refl.{u} α lhs` for a goal `@Eq.{u} α lhs rhs`.
///
/// Mirrors `MVarId.refl` in
/// `refs/lean4/src/Lean/Meta/Tactic/Refl.lean:25-39`, which always uses
/// the LHS of the equation (even with `check := false`).
fn build_refl_proof(goal_eq: &LeanExpr) -> Option<LeanExpr> {
  let (head, args) = decompose_apps(goal_eq);
  if args.len() != 3 {
    return None;
  }
  let level = match head.as_data() {
    ExprData::Const(name, lvls, _)
      if *name == Name::str(Name::anon(), "Eq".to_string())
        && lvls.len() == 1 =>
    {
      lvls[0].clone()
    },
    _ => return None,
  };
  let alpha = &args[0];
  let lhs = &args[1];
  // rhs is args[2] — not used because Eq.refl uses LHS.
  Some(mk_eq_refl(&level, alpha, lhs))
}

/// Determine `substCore`'s `symm` direction for an `Eq` binder.
///
/// Mirrors `substEq` in
/// `refs/lean4/src/Lean/Meta/Tactic/UnifyEq.lean:127-134`:
/// - both fvars → `symm = aDecl.index < bDecl.index`
/// - `(fvar, _)` → `symm = false`
/// - `(_, fvar)` → `symm = true`
/// - `(expr, expr)` → unreachable in the `.brecOn.eq` cases flow
///
/// Returns `(symm, abstracted_fvar_name, replacement)` where
/// `abstracted_fvar_name` is the FVar substituted out by `substCore`
/// (and thus the variable abstracted in the motive), and `replacement`
/// is what replaces it in the continuation's goal.
fn determine_symm(
  lhs: &LeanExpr,
  rhs: &LeanExpr,
  fvar_order: &FxHashMap<Name, usize>,
) -> Option<(bool, Name, LeanExpr)> {
  match (lhs.as_data(), rhs.as_data()) {
    (ExprData::Fvar(lname, _), ExprData::Fvar(rname, _)) => {
      let lorder = fvar_order.get(lname).copied().unwrap_or(usize::MAX);
      let rorder = fvar_order.get(rname).copied().unwrap_or(usize::MAX);
      if lorder < rorder {
        // symm=true: abstract rhs (the later-intro'd fvar), replace with lhs
        Some((true, rname.clone(), lhs.clone()))
      } else {
        // symm=false: abstract lhs, replace with rhs
        Some((false, lname.clone(), rhs.clone()))
      }
    },
    (ExprData::Fvar(lname, _), _) => {
      // (fvar, expr) → symm=false: abstract lhs, replace with rhs
      Some((false, lname.clone(), rhs.clone()))
    },
    (_, ExprData::Fvar(rname, _)) => {
      // (expr, fvar) → symm=true: abstract rhs, replace with lhs
      Some((true, rname.clone(), lhs.clone()))
    },
    _ => None,
  }
}

/// Compute forward dependencies of `abstracted_fvar` in `local_context`.
///
/// Mirrors Lean's `collectForwardDeps` at
/// `refs/lean4/src/Lean/MetavarContext.lean:1372`. A fvar is a forward
/// dependency if its type references `abstracted_fvar` (directly) or a
/// previously-collected forward dependency (transitively). Returns the
/// dependencies in their `local_context` order (matching Lean's
/// `preserveOrder := true` behavior).
///
/// In Lean's `substCore` (`refs/lean4/src/Lean/Meta/Tactic/Subst.lean:34`),
/// `revert` pulls these in automatically. After `revert+intro+assign`,
/// their types get `abstracted_fvar := replacement` substituted (via
/// `type.replaceFVar`), and Lean's `instantiateMVars` beta-reduces the
/// revert-introduced redex, producing extra args on `Eq.ndrec`.
fn collect_forward_deps<'a>(
  abstracted_fvar_name: &Name,
  local_context: &'a [LocalDecl],
) -> Vec<&'a LocalDecl> {
  let mut deps: Vec<&LocalDecl> = Vec::new();
  let mut dep_names: rustc_hash::FxHashSet<Name> =
    rustc_hash::FxHashSet::default();
  dep_names.insert(abstracted_fvar_name.clone());
  for d in local_context {
    if d.fvar_name == *abstracted_fvar_name {
      continue;
    }
    let depends = dep_names.iter().any(|n| expr_contains_fvar(&d.domain, n));
    if depends {
      deps.push(d);
      dep_names.insert(d.fvar_name.clone());
    }
  }
  deps
}

/// Build the proof term for the "remaining" `∀`-chain `∀ rest. body`.
///
/// Outside-in recursive construction. Peels one binder at a time,
/// emitting a 6-arg `Eq.ndrec` (for `Eq` binders) or the beta-reduced
/// form `Eq.ndrec_major ... (Eq.symm (eq_of_heq heq))` (for `HEq`
/// binders). Each `Eq.ndrec` result may be followed by *extra* args
/// that consume `∀`-binders introduced for forward-dep context fvars
/// (matching Lean's beta-reduced revert+intro redex).
///
/// Simulates Lean's `unifyEqs?` loop from
/// `refs/lean4/src/Lean/Meta/Tactic/Cases.lean:231-239`.
#[allow(clippy::too_many_arguments)]
fn build_proof_for_remaining(
  remaining: &[(EqBinderKind, LocalDecl)],
  body: &LeanExpr,
  local_context: &[LocalDecl],
  fvar_order: &FxHashMap<Name, usize>,
  ctor_idx: usize,
  depth: usize,
) -> Option<LeanExpr> {
  if remaining.is_empty() {
    return build_refl_proof(body);
  }
  let (kind, decl) = &remaining[0];
  let rest = &remaining[1..];
  match kind {
    EqBinderKind::Eq { alpha, lhs, rhs, level } => handle_substcore_step(
      decl,
      rest,
      body,
      alpha,
      lhs,
      rhs,
      level,
      /* h_arg_source = */ HArgSource::EqFvar,
      local_context,
      fvar_order,
      ctor_idx,
      depth,
    ),
    EqBinderKind::HEq { alpha, a, beta: _, b, level } => {
      // For HEq binders, Lean's `heqToEq'` converts to an `Eq` via
      // `eq_of_heq`, and the ensuing `substCore` uses `eq_of_heq heq`
      // inline (not an intermediate `eq_major` fvar). This is because
      // `instantiateMVars` beta-reduces the revert+intro redex produced
      // by `heqToEq'`'s `assert` — see `Lean.MetavarContext:1473`
      // (`(← visitApp v args).headBeta`).
      //
      // We match Lean's post-beta form by calling `handle_substcore_step`
      // with `HArgSource::EqOfHeq` — it substitutes `eq_of_heq heq_fvar`
      // wherever an eq fvar would appear.
      handle_substcore_step(
        decl,
        rest,
        body,
        alpha,
        a,
        b,
        level,
        /* h_arg_source = */ HArgSource::EqOfHeq,
        local_context,
        fvar_order,
        ctor_idx,
        depth,
      )
    },
  }
}

/// Describes how the `h_arg` (eq proof) of `Eq.ndrec` is constructed
/// from the binder fvar.
#[derive(Copy, Clone)]
enum HArgSource {
  /// The binder is an `Eq` fvar — use it directly (possibly `Eq.symm`-ed).
  EqFvar,
  /// The binder is an `HEq` fvar — wrap with `eq_of_heq` inline (matching
  /// Lean's beta-reduced `heqToEq'` form).
  EqOfHeq,
}

/// Handle a single substCore step — either for an `Eq` binder (using the
/// fvar directly) or a converted `HEq` binder (using `eq_of_heq heq`
/// inline).
///
/// The output shape is:
///
/// ```text
/// λ binder_decl.
///   (@Eq.ndrec.{0, level} α a_ndrec motive continuation b_ndrec h_arg)
///     orig_forward_dep_1 orig_forward_dep_2 ...
/// ```
///
/// where `forward_deps` are context fvars depending (transitively) on
/// `abstracted_fvar`, included in the motive as `∀` binders and consumed
/// via extra args. Motive is `λ x. ∀ forward_deps. ∀ rest. body` with
/// `abstracted_fvar` abstracted throughout. The continuation uses fresh
/// fvars for the forward deps (with `abstracted_fvar := replacement`
/// substitution applied to their types).
#[allow(clippy::too_many_arguments)]
fn handle_substcore_step(
  decl: &LocalDecl,
  rest: &[(EqBinderKind, LocalDecl)],
  body: &LeanExpr,
  alpha: &LeanExpr,
  lhs: &LeanExpr,
  rhs: &LeanExpr,
  level: &Level,
  h_arg_source: HArgSource,
  local_context: &[LocalDecl],
  fvar_order: &FxHashMap<Name, usize>,
  ctor_idx: usize,
  depth: usize,
) -> Option<LeanExpr> {
  let (symm, abstracted_fvar_name, replacement) =
    determine_symm(lhs, rhs, fvar_order)?;

  // Defensive invariant: for `.brecOn.eq`, we expect `depElim = false`
  // (the goal doesn't depend on the eq-fvar itself). Lean's substCore
  // would branch to `mkEqRec` (7 args, 2-binder motive) if it did.
  let eq_fvar_used_in_rest_or_body = expr_contains_fvar(body, &decl.fvar_name)
    || rest.iter().any(|(_, d)| expr_contains_fvar(&d.domain, &decl.fvar_name));
  if eq_fvar_used_in_rest_or_body {
    return None;
  }

  // Collect forward dependencies — context fvars depending transitively
  // on `abstracted_fvar`. Lean's `revert` pulls these in automatically
  // via `collectForwardDeps` (MetavarContext.lean:1372).
  let forward_deps_refs =
    collect_forward_deps(&abstracted_fvar_name, local_context);
  let forward_deps: Vec<LocalDecl> =
    forward_deps_refs.iter().map(|d| (*d).clone()).collect();

  // Build the motive. The motive body is the FULL current goal
  // (`∀ forward_deps. ∀ rest. body`) with `abstracted_fvar` abstracted.
  // The forward_deps appear as ∀-binders inside the motive.
  let mut motive_binders: Vec<LocalDecl> = forward_deps.clone();
  motive_binders.extend(rest.iter().map(|(_, d)| d.clone()));
  let current_goal_type = mk_forall(body.clone(), &motive_binders);
  let motive_body = abstract_fvar(&current_goal_type, &abstracted_fvar_name, 0);

  // The motive's λ binder TYPE is the abstracted fvar's *actual stored
  // type* from the local context — not the `α` passed in (which is the
  // Eq/HEq's `α` arg, i.e., the outer-side type).
  //
  // These can differ syntactically even when def-equal. For example, in
  // `CategoryTheory.FreeBicategory.Hom₂`, `outer_g` has type
  // `Quiver.Hom ... (FreeBicategory.quiver ...) a b`, but the abstracted
  // ctor field `ctor_f` has type `Quiver.Hom ... (CategoryStruct.toQuiver (FreeBicategory.categoryStruct ...)) a b`
  // (the un-reduced form from casesOn's stored minor). Both forms are
  // definitionally equal (via projection reduction on the CategoryStruct
  // instance), but Lean's cases tactic preserves the un-reduced form
  // because the motive's λ binder type in `substCore` comes from
  // `mkLambdaFVars #[a] type` where `a` is the abstracted fvar —
  // whose type is exactly what's stored for it in the LCtx.
  //
  // Look up the abstracted fvar's stored type in `local_context`. For
  // the common case (it's an outer index), this is the same as `alpha`.
  // For ctor fields (which can have un-reduced forms), this differs.
  let binder_type = local_context
    .iter()
    .find(|d| d.fvar_name == abstracted_fvar_name)
    .map_or_else(|| alpha.clone(), |d| d.domain.clone());
  let motive = LeanExpr::lam(
    Name::str(Name::anon(), "x".to_string()),
    binder_type,
    motive_body,
    BinderInfo::Default,
  );

  // Build the substituted continuation state. Substitute
  // `abstracted_fvar := replacement` in forward_deps' domains,
  // rest binders' domains, and body. The forward_deps become fresh
  // λ-bindings at the front of the continuation (matching Lean's
  // `introNP (vars.size - 2)` after substCore's `mvarId.assign`).
  let new_forward_deps: Vec<LocalDecl> = forward_deps
    .iter()
    .map(|d| LocalDecl {
      fvar_name: d.fvar_name.clone(),
      binder_name: d.binder_name.clone(),
      domain: subst_fvar(&d.domain, &abstracted_fvar_name, &replacement),
      info: d.info.clone(),
    })
    .collect();
  let new_body = subst_fvar(body, &abstracted_fvar_name, &replacement);
  let new_rest: Vec<(EqBinderKind, LocalDecl)> = rest
    .iter()
    .map(|(k, d)| {
      let new_domain =
        subst_fvar(&d.domain, &abstracted_fvar_name, &replacement);
      let new_decl = LocalDecl {
        fvar_name: d.fvar_name.clone(),
        binder_name: d.binder_name.clone(),
        domain: new_domain,
        info: d.info.clone(),
      };
      let new_kind =
        subst_in_eq_binder_kind(k, &abstracted_fvar_name, &replacement);
      (new_kind, new_decl)
    })
    .collect();

  // Build the new local_context for the continuation: replace the
  // original forward_deps with their substituted versions (same fvar
  // names, substituted domains). Non-dep entries are unchanged. The
  // abstracted_fvar is removed (Lean's `clearH := true` clears it).
  let new_local_context: Vec<LocalDecl> = local_context
    .iter()
    .filter_map(|d| {
      if d.fvar_name == abstracted_fvar_name {
        None
      } else if let Some(new_d) =
        new_forward_deps.iter().find(|nd| nd.fvar_name == d.fvar_name)
      {
        Some(new_d.clone())
      } else {
        Some(d.clone())
      }
    })
    .collect();

  let inner_proof = build_proof_for_remaining(
    &new_rest,
    &new_body,
    &new_local_context,
    fvar_order,
    ctor_idx,
    depth + 1,
  )?;

  // Wrap inner_proof with `λ forward_deps` — these λ-binders match
  // motive(a_ndrec)'s ∀-binders (with `abstracted := replacement` subst
  // applied to their types). Internally the inner_proof uses the SAME
  // fvar names for forward_deps, so no renaming is needed.
  let continuation = mk_lambda(inner_proof, &new_forward_deps);

  // Build the h_arg per the binder's source.
  let binder_as_expr: LeanExpr = match h_arg_source {
    HArgSource::EqFvar => LeanExpr::fvar(decl.fvar_name.clone()),
    HArgSource::EqOfHeq => {
      // Build `eq_of_heq.{level} α a b heq`. This is the inlined form
      // Lean produces after `instantiateMVars` beta-reduces the
      // `heqToEq'` redex. Note: `a` and `b` are `lhs` and `rhs` of the
      // eq we're constructing — which for HEq correspond to the HEq's
      // `a` and `b` (homogeneous at this point).
      mk_eq_of_heq(
        level,
        alpha,
        lhs,
        rhs,
        &LeanExpr::fvar(decl.fvar_name.clone()),
      )
    },
  };

  // Per substCore's symm convention:
  //   symm=false → a_ndrec = rhs, b_ndrec = lhs, h_arg = Eq.symm _
  //   symm=true  → a_ndrec = lhs, b_ndrec = rhs, h_arg = _
  let (a_ndrec, b_ndrec, h_arg) = if symm {
    (lhs.clone(), rhs.clone(), binder_as_expr)
  } else {
    let symm_h = mk_eq_symm(level, alpha, lhs, rhs, &binder_as_expr);
    (rhs.clone(), lhs.clone(), symm_h)
  };

  // Build the 6-arg Eq.ndrec. Then apply the ORIGINAL forward_dep fvars
  // as extra args — this consumes the ∀-binders that motive(b_ndrec)
  // has for them. Their types in motive(b_ndrec) are
  // `orig_type[abstracted := b_ndrec]`; for `b_ndrec = abstracted_fvar`
  // (which is the case per the symm convention above), this is a
  // no-op substitution, so the original fvars type-check as extras.
  let mut ndrec = mk_eq_ndrec(
    &Level::zero(),
    level,
    alpha,
    &a_ndrec,
    &motive,
    &continuation,
    &b_ndrec,
    &h_arg,
  );
  for fd in &forward_deps {
    ndrec = LeanExpr::app(ndrec, LeanExpr::fvar(fd.fvar_name.clone()));
  }

  Some(mk_lambda(ndrec, std::slice::from_ref(decl)))
}

/// Build a single indexed `.brecOn.eq` minor's body by simulating Lean's
/// `cases + refl` tactic flow.
///
/// Returns `λ non_ih_fields. proof` where `proof` has type
/// `∀ eq_0 ... eq_{n-1} ∀ heq. outer_eq_body`.
///
/// Returns `None` on any structural precondition violation (e.g.
/// dependent elimination, or a fvar missing from `fvar_order`), which
/// propagates as the overall indexed-eq construction falling back to
/// the non-indexed path (matching existing behavior).
#[allow(clippy::too_many_arguments)]
fn build_minor_via_cases_sim(
  ctor_idx: usize,
  non_ih_decls: &[LocalDecl],
  ret_args: &[LeanExpr],
  ctor_applied: &LeanExpr,
  outer_eq_body: &LeanExpr,
  index_fvars: &[LeanExpr],
  index_decls: &[LocalDecl],
  index_sort_levels: &[Level],
  outer_major: &LeanExpr,
  major_type: &LeanExpr,
  major_level: &Level,
  param_fvars: &[LeanExpr],
  motive_fvars: &[LeanExpr],
  f_fvars: &[LeanExpr],
  // Parallel to `index_decls`: `idx_is_heq[i] = true` means the motive's
  // `h_i` binder was built as `HEq` (because the types aren't defEq),
  // and the cases-sim's `remaining` list should match.
  idx_is_heq: &[bool],
) -> Option<LeanExpr> {
  let n_indices = index_decls.len();

  // Extract fvar names for outer indices and major.
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
  let outer_major_name = match outer_major.as_data() {
    ExprData::Fvar(n, _) => n.clone(),
    _ => return None,
  };

  let idx_sort = |i: usize| -> Level {
    index_sort_levels
      .get(i)
      .cloned()
      .unwrap_or_else(|| Level::succ(Level::zero()))
  };

  // Build eq/heq binder decls for each index, mirroring `mw_decls`'s
  // per-index choice (via `idx_is_heq`). When the motive used `HEq`
  // (types not defEq), the casesOn-applied position specializes the
  // ret-side type by substituting `outer_idx[j] → ret[j]` for `j < i`.
  let mut eq_decls: Vec<LocalDecl> = Vec::with_capacity(n_indices);
  let mut eq_ret_types: Vec<LeanExpr> = Vec::with_capacity(n_indices);
  for i in 0..n_indices {
    let eq_ty = if idx_is_heq[i] {
      // Build the ret-side type with outer_idx[j] → ret[j] for j < i.
      let mut ret_type = index_decls[i].domain.clone();
      for j in 0..i {
        if let ExprData::Fvar(outer_name, _) = index_fvars[j].as_data() {
          ret_type = subst_fvar(&ret_type, outer_name, &ret_args[j]);
        }
      }
      eq_ret_types.push(ret_type.clone());
      mk_heq(
        &idx_sort(i),
        &index_decls[i].domain,
        &index_fvars[i],
        &ret_type,
        &ret_args[i],
      )
    } else {
      eq_ret_types.push(index_decls[i].domain.clone());
      mk_eq(&idx_sort(i), &index_decls[i].domain, &index_fvars[i], &ret_args[i])
    };
    let (fv_name, _) = fresh_fvar(&format!("ieq_eq_c{ctor_idx}"), i);
    eq_decls.push(LocalDecl {
      fvar_name: fv_name,
      binder_name: Name::str(Name::anon(), "h".to_string()),
      domain: eq_ty,
      info: BinderInfo::Default,
    });
  }

  // Build the heq binder decl.
  let ctor_ret_type =
    build_specialized_major_type(major_type, index_fvars, ret_args);
  let heq_ty =
    mk_heq(major_level, major_type, outer_major, &ctor_ret_type, ctor_applied);
  let (heq_name, _) = fresh_fvar(&format!("ieq_heq_c{ctor_idx}"), 0);
  let heq_decl = LocalDecl {
    fvar_name: heq_name,
    binder_name: Name::str(Name::anon(), "h_m".to_string()),
    domain: heq_ty,
    info: BinderInfo::Default,
  };

  // Build fvar_order for symm determination. Canonical introduction
  // order: params < motives < F's < outer_idxs < outer_major < non_ih.
  // (Eqs and heq come later via `unifyEqs?`'s intros, but they never
  // appear on both sides of an eq-binder, so we don't need them here.)
  let mut fvar_order: FxHashMap<Name, usize> = FxHashMap::default();
  let mut order_counter = 0usize;
  for fv in param_fvars.iter().chain(motive_fvars.iter()).chain(f_fvars.iter())
  {
    if let ExprData::Fvar(name, _) = fv.as_data() {
      fvar_order.insert(name.clone(), order_counter);
      order_counter += 1;
    }
  }
  for name in &index_fvar_names {
    fvar_order.insert(name.clone(), order_counter);
    order_counter += 1;
  }
  fvar_order.insert(outer_major_name, order_counter);
  order_counter += 1;
  for d in non_ih_decls {
    fvar_order.insert(d.fvar_name.clone(), order_counter);
    order_counter += 1;
  }

  // Build the full remaining-binder list: eq_0 ... eq_{n-1}, heq.
  // Each binder is Eq or HEq per `idx_is_heq[i]` (must match `eq_decls`).
  let mut remaining: Vec<(EqBinderKind, LocalDecl)> =
    Vec::with_capacity(n_indices + 1);
  for (i, decl) in eq_decls.iter().enumerate() {
    let kind = if idx_is_heq[i] {
      EqBinderKind::HEq {
        alpha: index_decls[i].domain.clone(),
        a: index_fvars[i].clone(),
        beta: eq_ret_types[i].clone(),
        b: ret_args[i].clone(),
        level: idx_sort(i),
      }
    } else {
      EqBinderKind::Eq {
        alpha: index_decls[i].domain.clone(),
        lhs: index_fvars[i].clone(),
        rhs: ret_args[i].clone(),
        level: idx_sort(i),
      }
    };
    remaining.push((kind, decl.clone()));
  }
  let heq_kind = EqBinderKind::HEq {
    alpha: major_type.clone(),
    a: outer_major.clone(),
    beta: ctor_ret_type,
    b: ctor_applied.clone(),
    level: major_level.clone(),
  };
  remaining.push((heq_kind, heq_decl));

  // Build the local_context — the list of outer fvars visible at the
  // start of the minor, ordered by introduction. `collect_forward_deps`
  // uses this to find context fvars depending on each `abstracted_fvar`
  // at each substCore step. Only fvar-typed entries with extractable
  // names are included.
  let mut local_context: Vec<LocalDecl> = Vec::new();
  // Params, motives, F's: extract from their fvar exprs. These are
  // outer context fvars from `all_decls`. We use their domain types
  // (taken from their fvar exprs — but we only have the fvars, not
  // their decls, at this layer). The caller passes `index_decls`,
  // `_major_decls`, etc. — we reuse their domains for the context.
  //
  // For simplicity, we only include outer_indices, outer_major, and
  // non_ih fields — the fvars most likely to be forward-dep sources
  // for the substCore steps. Params / motives / F don't typically
  // have types that depend on the abstracted eq-fvar.
  for (i, idx_decl) in index_decls.iter().enumerate() {
    // Rebuild a LocalDecl for each outer index using its fvar name
    // (extracted from index_fvars) and the domain from index_decls.
    if let ExprData::Fvar(fname, _) = index_fvars[i].as_data() {
      local_context.push(LocalDecl {
        fvar_name: fname.clone(),
        binder_name: idx_decl.binder_name.clone(),
        domain: idx_decl.domain.clone(),
        info: idx_decl.info.clone(),
      });
    }
  }
  // Major — type is `major_type` (= I outer_idxs).
  if let ExprData::Fvar(maj_name, _) = outer_major.as_data() {
    local_context.push(LocalDecl {
      fvar_name: maj_name.clone(),
      binder_name: Name::str(Name::anon(), "t".to_string()),
      domain: major_type.clone(),
      info: BinderInfo::Default,
    });
  }
  // Non-IH ctor fields.
  for d in non_ih_decls {
    local_context.push(d.clone());
  }

  // Recursively build the proof term.
  let proof = build_proof_for_remaining(
    &remaining,
    outer_eq_body,
    &local_context,
    &fvar_order,
    ctor_idx,
    0,
  )?;

  // Wrap with `λ non_ih_fields` — the outer intros that `inductionCasesOn`
  // does before `unifyCasesEqs` is invoked.
  Some(mk_lambda(proof, non_ih_decls))
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
