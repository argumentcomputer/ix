//! Canonical `.below` generation for inductive blocks.
//!
//! For Type-level inductives, `.below` is a reducible definition:
//!   `A.below {motives} t := A.rec (λ _, Sort rlvl) (λ fields ih, motive x ×' ih) t`
//!
//! For Prop-level inductives, `.below` is an inductive type with constructors
//! mirroring the parent's structure (see `IndPredBelow.lean`).
//!
//! Follows `refs/lean4/src/Lean/Meta/Constructions/BRecOn.lean:59-108`.

use crate::ix::env::{
  BinderInfo, ConstantInfo, ConstructorVal, Env as LeanEnv, Expr as LeanExpr,
  ExprData, InductiveVal, Level, LevelData, Name, RecursorVal,
};
use crate::ix::ixon::CompileError;

use super::expr_utils::{
  LocalDecl, decompose_apps, find_motive_fvar, forall_telescope, fresh_fvar,
  instantiate1, mk_app_n, mk_const, mk_forall, mk_lambda, replace_const_names,
};

/// A generated `.below` constant — either a definition (Type-level)
/// or an inductive (Prop-level).
#[derive(Clone)]
pub(crate) enum BelowConstant {
  /// Type-level `.below`: a reducible definition using `.rec` + PProd.
  Def(BelowDef),
  /// Prop-level `.below`: an inductive type with constructors.
  Indc(BelowIndc),
}

/// A generated `.below` definition (Type-level case).
#[derive(Clone)]
pub(crate) struct BelowDef {
  pub name: Name,
  pub level_params: Vec<Name>,
  pub typ: LeanExpr,
  pub value: LeanExpr,
}

/// A generated `.below` inductive (Prop-level case).
#[derive(Clone)]
pub(crate) struct BelowIndc {
  pub name: Name,
  pub level_params: Vec<Name>,
  pub n_params: usize,
  pub typ: LeanExpr,
  pub ctors: Vec<BelowCtor>,
}

/// A constructor for a Prop-level `.below` inductive.
#[derive(Clone)]
pub(crate) struct BelowCtor {
  pub name: Name,
  pub typ: LeanExpr,
  pub n_params: usize,
  pub n_fields: usize,
}

/// Rename a `BelowIndc` to match a different parent inductive name.
///
/// Given a canonical `BLE.below` with constructors named after `BLE`'s ctors,
/// produces `BLI.below` with constructors named after `BLI`'s ctors.
/// Uses positional mapping: canonical parent's ctor[i] → target parent's ctor[i].
///
/// `canonical_parent`: the representative inductive name (e.g., `BLE`)
/// `lean_env`: to look up constructor names for both parent inductives
pub(crate) fn rename_below_indc(
  canonical: &BelowIndc,
  new_parent: &Name,
  canonical_parent: &Name,
  lean_env: &LeanEnv,
) -> BelowIndc {
  let new_below_name = Name::str(new_parent.clone(), "below".to_string());

  // Build a positional map from canonical parent ctor suffix → target parent ctor suffix.
  // e.g., BLE.ble → BLI.bli (both at position 0)
  let canon_ctors = match lean_env.get(canonical_parent) {
    Some(ConstantInfo::InductInfo(v)) => &v.ctors,
    _ => &vec![],
  };
  let target_ctors = match lean_env.get(new_parent) {
    Some(ConstantInfo::InductInfo(v)) => &v.ctors,
    _ => &vec![],
  };

  // Build a complete name replacement map for expressions.
  //
  // The canonical `.below` constructor types contain Const references to:
  //   1. The canonical parent inductive (e.g., `BLE` in motive/major domains)
  //   2. The canonical `.below` inductive (e.g., `BLE.below` in return type and IH fields)
  //   3. The canonical parent's constructors (e.g., `BLE.ble` in the return type)
  //
  // All three categories must be rewritten to reference the alias target.
  let mut name_map = std::collections::HashMap::new();
  name_map.insert(canonical_parent.clone(), new_parent.clone());
  name_map.insert(canonical.name.clone(), new_below_name.clone());
  for (canon_ctor, target_ctor) in canon_ctors.iter().zip(target_ctors.iter()) {
    name_map.insert(canon_ctor.clone(), target_ctor.clone());
  }

  // Build suffix map for renaming .below constructor names (structural, not expression-level).
  use crate::ix::env::NameComponent;
  let suffix_map: Vec<(Vec<NameComponent>, Vec<NameComponent>)> = canon_ctors
    .iter()
    .zip(target_ctors.iter())
    .map(|(c, t)| {
      let c_suffix =
        c.strip_prefix(canonical_parent).unwrap_or_else(|| c.components());
      let t_suffix =
        t.strip_prefix(new_parent).unwrap_or_else(|| t.components());
      (c_suffix, t_suffix)
    })
    .collect();

  let renamed_ctors = canonical
    .ctors
    .iter()
    .map(|ctor| {
      // Strip the canonical .below prefix to get the ctor suffix components.
      let ctor_suffix = ctor
        .name
        .strip_prefix(&canonical.name)
        .unwrap_or_else(|| ctor.name.components());

      // Look up the positional rename: find which canonical ctor suffix matches.
      let new_suffix = suffix_map
        .iter()
        .find(|(cs, _)| *cs == ctor_suffix)
        .map(|(_, ts)| ts.clone())
        .unwrap_or(ctor_suffix);

      BelowCtor {
        name: new_below_name.append_components(&new_suffix),
        typ: replace_const_names(&ctor.typ, &name_map),
        n_params: ctor.n_params,
        n_fields: ctor.n_fields,
      }
    })
    .collect();

  BelowIndc {
    name: new_below_name,
    level_params: canonical.level_params.clone(),
    n_params: canonical.n_params,
    typ: replace_const_names(&canonical.typ, &name_map),
    ctors: renamed_ctors,
  }
}

/// Generate `.below` constants for all classes in a block.
///
/// For Type-level inductives: generates a `BelowDef` (reducible definition).
/// For Prop-level inductives: generates a `BelowIndc` (inductive type).
///
/// `canonical_recs` are the recursors generated by Phase 1.
/// `is_prop` indicates whether the inductive block is in Prop (Sort 0).
/// This determines the generation strategy — matching Lean's split between
/// `BRecOn.lean` (Type-level → definition) and `IndPredBelow.lean` (Prop → inductive).
///
/// Note: `is_prop` is distinct from `is_large`. A Prop inductive with single
/// constructors and all-Prop fields gets large elimination (`drec`), but Lean
/// still generates `.below` as an inductive via `IndPredBelow`.
pub(crate) fn generate_below_constants(
  sorted_classes: &[Vec<Name>],
  canonical_recs: &[(Name, RecursorVal)],
  lean_env: &LeanEnv,
  is_prop: bool,
  stt: Option<&crate::ix::compile::CompileState>,
) -> Result<Vec<BelowConstant>, CompileError> {
  let n_classes = sorted_classes.len();
  if n_classes == 0 || canonical_recs.is_empty() {
    return Ok(vec![]);
  }

  let mut results = Vec::new();

  for ci in 0..n_classes.min(canonical_recs.len()) {
    let (_, rec_val) = &canonical_recs[ci];
    let class_rep = &sorted_classes[ci][0];

    let ind = match lean_env.get(class_rep) {
      Some(ConstantInfo::InductInfo(v)) => v,
      _ => continue,
    };

    let below_name = Name::str(ind.cnst.name.clone(), "below".to_string());

    if !is_prop {
      // Type-level: generate definition (BRecOn.lean path)
      let def = build_below_def(
        &below_name,
        rec_val,
        ind,
        lean_env,
        n_classes,
        canonical_recs,
        stt,
      )?;
      results.push(BelowConstant::Def(def));
    } else {
      // Prop-level: generate .below inductive (IndPredBelow.lean path)
      let indc = build_below_indc(
        ci,
        &below_name,
        rec_val,
        ind,
        lean_env,
        n_classes,
        sorted_classes,
        canonical_recs,
      )?;
      results.push(BelowConstant::Indc(indc));
    }
  }

  Ok(results)
}

/// Build a single `.below` definition for a Type-level inductive.
///
/// The `.below` definition's value is:
/// ```
/// λ {params} {motives} (indices) (major),
///   I.rec.{succ(rlvl), lvls...} params
///     (λ (indices) (major), Sort rlvl)     -- for each motive
///     (buildMinor rlvl motives minorType)  -- for each minor
///     indices major
/// ```
fn build_below_def(
  below_name: &Name,
  rec_val: &RecursorVal,
  ind: &InductiveVal,
  lean_env: &LeanEnv,
  n_classes: usize,
  canonical_recs: &[(Name, RecursorVal)],
  stt: Option<&crate::ix::compile::CompileState>,
) -> Result<BelowDef, CompileError> {
  let n_params = rec_val.num_params.to_u64().unwrap_or(0) as usize;
  let n_motives = rec_val.num_motives.to_u64().unwrap_or(0) as usize;
  let n_minors = rec_val.num_minors.to_u64().unwrap_or(0) as usize;
  let n_indices = rec_val.num_indices.to_u64().unwrap_or(0) as usize;
  let rec_level_params = &rec_val.cnst.level_params;
  let _ind_level_params = &ind.cnst.level_params;

  // The elimination level is the first level param (for large eliminators).
  let elim_level = Level::param(rec_level_params[0].clone());

  // ilvl: the universe level of the inductive's type former.
  //
  // Lean (BRecOn.lean:78-80) computes this from the major premise:
  //   `typeFormerTypeLevel (← inferType (← inferType major))`
  // "to be more robust when facing nested induction" — because nested
  // inductives specialize universe params, the inductive's raw type
  // may not reflect the actual sort level seen through the recursor.
  //
  // When the kernel type checker is available (stt), extract the major
  // premise's type from the recursor and infer its sort level semantically.
  // Fall back to the syntactic approach otherwise.
  let syntactic_ilvl = get_ind_sort_level(&ind.cnst.typ, n_params + n_indices);
  let ilvl = if let Some(stt) = stt {
    // Build the major premise's type by walking the recursor telescope.
    // The major is the last binder: peel params + motives + minors + indices.
    let total_before_major = n_params + n_motives + n_minors + n_indices;
    let mut cur = rec_val.cnst.typ.clone();
    let mut major_type = None;
    for i in 0..=total_before_major {
      match cur.as_data() {
        ExprData::ForallE(_, dom, body, _, _) => {
          if i == total_before_major {
            // dom is the major premise's type (under total_before_major binders)
            major_type = Some(dom.clone());
          }
          cur = body.clone();
        },
        _ => break,
      }
    }
    if let Some(major_ty) = major_type {
      // Infer the sort level of the major premise's type.
      // major_ty lives under n_params + n_motives + n_minors + n_indices
      // binders in the recursor type. We need it as a closed expression
      // for the type checker, so we use the recursor's level params.
      infer_sort_level(&major_ty, rec_level_params, stt, &syntactic_ilvl)
    } else {
      syntactic_ilvl
    }
  } else {
    syntactic_ilvl
  };

  // rlvl = max(ilvl, elim_level), normalized to avoid structural mismatch.
  let rlvl = level_max(&ilvl, &elim_level);

  // .below level params = same as .rec level params
  let below_level_params = rec_level_params.clone();

  // Build the type: ∀ {params} {motives} (indices) (major : I params indices), Sort rlvl
  // This is the recursor type WITHOUT minors and with Sort rlvl as return.
  let below_type = build_below_type(rec_val, &rlvl);

  // Build the value: λ {params} {motives} (indices) (major),
  //   I.rec.{succ(rlvl), lvls...} params motives' minors' indices major
  let below_value = build_below_value(
    rec_val,
    ind,
    lean_env,
    &rlvl,
    &elim_level,
    n_classes,
    canonical_recs,
  );

  Ok(BelowDef {
    name: below_name.clone(),
    level_params: below_level_params,
    typ: below_type,
    value: below_value,
  })
}

/// Extract the sort level from an inductive's type by peeling n foralls.
pub(super) fn get_ind_sort_level(typ: &LeanExpr, n: usize) -> Level {
  let mut cur = typ.clone();
  for _ in 0..n {
    if let ExprData::ForallE(_, _, body, _, _) = cur.as_data() {
      cur = body.clone();
    }
  }
  match cur.as_data() {
    ExprData::Sort(lvl, _) => lvl.clone(),
    _ => Level::zero(),
  }
}

/// Build the `.below` type from the recursor type.
///
/// Takes the recursor type `∀ params motives minors indices major, motive major`
/// and produces `∀ params motives indices major, Sort rlvl` (drops minors,
/// replaces return with Sort rlvl).
///
/// Uses FVar-based construction: opens all rec type binders into FVars,
/// discards minor FVars, and re-closes with `mk_forall` which handles
/// all BVar computation automatically.
fn build_below_type(rec_val: &RecursorVal, rlvl: &Level) -> LeanExpr {
  let n_params = rec_val.num_params.to_u64().unwrap_or(0) as usize;
  let n_motives = rec_val.num_motives.to_u64().unwrap_or(0) as usize;
  let n_minors = rec_val.num_minors.to_u64().unwrap_or(0) as usize;
  let n_indices = rec_val.num_indices.to_u64().unwrap_or(0) as usize;

  // Open all rec type binders into FVars.
  let (_, param_decls, after_params) =
    forall_telescope(&rec_val.cnst.typ, n_params, "btp", 0);
  let (_, motive_decls, after_motives) =
    forall_telescope(&after_params, n_motives, "btm", 0);
  // Open minors (we'll discard these decls)
  let (_, _minor_decls, after_minors) =
    forall_telescope(&after_motives, n_minors, "btx", 0);
  let (_, index_decls, after_indices) =
    forall_telescope(&after_minors, n_indices, "bti", 0);
  // Open major
  let (_, major_decl, _after_major) =
    forall_telescope(&after_indices, 1, "btj", 0);

  // Build: ∀ params motives indices major, Sort rlvl
  // The decls already have correct FVar-based domains (instantiate1 resolved
  // cross-references). mk_forall abstracts all FVars into BVars.
  let all_decls: Vec<LocalDecl> = param_decls
    .into_iter()
    .chain(motive_decls)
    .chain(index_decls)
    .chain(major_decl)
    .collect();

  mk_forall(LeanExpr::sort(rlvl.clone()), &all_decls)
}

/// Build the `.below` value (lambda body).
///
/// Uses FVar-based construction: opens the rec type into FVars, builds
/// the rec application with motive/minor replacements using FVar references,
/// then closes with `mk_lambda` over the non-minor binders.
fn build_below_value(
  rec_val: &RecursorVal,
  ind: &InductiveVal,
  _lean_env: &LeanEnv,
  rlvl: &Level,
  elim_level: &Level,
  _n_classes: usize,
  _canonical_recs: &[(Name, RecursorVal)],
) -> LeanExpr {
  let n_params = rec_val.num_params.to_u64().unwrap_or(0) as usize;
  let n_motives = rec_val.num_motives.to_u64().unwrap_or(0) as usize;
  let n_minors = rec_val.num_minors.to_u64().unwrap_or(0) as usize;
  let n_indices = rec_val.num_indices.to_u64().unwrap_or(0) as usize;

  // Open all rec type binders into FVars.
  let (param_fvars, param_decls, after_params) =
    forall_telescope(&rec_val.cnst.typ, n_params, "bvp", 0);
  let (motive_fvars, motive_decls, after_motives) =
    forall_telescope(&after_params, n_motives, "bvm", 0);
  // Open minors — we need their domains (now FVar-based) for building
  // the minor replacement args, but we discard the minor decls from
  // the output binder list.
  let mut minor_doms: Vec<LeanExpr> = Vec::with_capacity(n_minors);
  let mut after_minors = after_motives.clone();
  for _ in 0..n_minors {
    if let ExprData::ForallE(_, dom, body, _, _) = after_minors.as_data() {
      minor_doms.push(dom.clone());
      // Instantiate with a dummy FVar so subsequent minors see correct context
      let (_, dummy_fv) = fresh_fvar("bvx", minor_doms.len());
      after_minors = instantiate1(body, &dummy_fv);
    }
  }
  let (index_fvars, index_decls, after_indices) =
    forall_telescope(&after_minors, n_indices, "bvi", 0);
  let (major_fvars, major_decls, _) =
    forall_telescope(&after_indices, 1, "bvj", 0);

  // Universe args for the rec application: [succ(rlvl), ind_lvls...]
  let ind_level_params = &ind.cnst.level_params;
  let mut rec_univs: Vec<Level> = vec![Level::succ(rlvl.clone())];
  for lp in ind_level_params {
    rec_univs.push(Level::param(lp.clone()));
  }

  // Build rec application using FVars:
  //   I.rec.{succ(rlvl), lvls...} params motives' minors' indices major
  let mut app = mk_const(&rec_val.cnst.name, &rec_univs);

  // Apply params (FVars)
  app = mk_app_n(app, &param_fvars);

  // Apply modified motives: for each motive, build λ (motive_args...), Sort rlvl
  // The motive domains are in FVar form (param FVars already substituted),
  // so we can use forall_telescope on them directly.
  for decl in &motive_decls {
    let motive_type = &decl.domain; // ∀ (indices) (major), Sort u
    let n_motive_args = count_foralls_expr(motive_type);
    let (_, motive_arg_decls, _) =
      forall_telescope(motive_type, n_motive_args, "bvma", 0);
    let motive_replacement =
      mk_lambda(LeanExpr::sort(rlvl.clone()), &motive_arg_decls);
    app = LeanExpr::app(app, motive_replacement);
  }

  // Apply modified minors: for each minor, build the PProd chain.
  // The minor domains are in FVar form (params + motives substituted),
  // so field IH detection uses find_motive_fvar instead of BVar range checks.
  for minor_dom in &minor_doms {
    let minor_arg =
      build_below_minor(minor_dom, rlvl, elim_level, &motive_fvars);
    app = LeanExpr::app(app, minor_arg);
  }

  // Apply indices and major (FVars)
  app = mk_app_n(app, &index_fvars);
  app = mk_app_n(app, &major_fvars);

  // Wrap in lambdas over [params, motives, indices, major] (no minors)
  let all_decls: Vec<LocalDecl> = param_decls
    .into_iter()
    .chain(motive_decls)
    .chain(index_decls)
    .chain(major_decls)
    .collect();

  mk_lambda(app, &all_decls)
}

/// Count leading foralls (local helper to avoid name collision with
/// the pub(super) count_foralls in below.rs).
fn count_foralls_expr(expr: &LeanExpr) -> usize {
  let mut n = 0;
  let mut cur = expr.clone();
  loop {
    match cur.as_data() {
      ExprData::ForallE(_, _, body, _, _) => {
        n += 1;
        cur = body.clone();
      },
      _ => return n,
    }
  }
}

/// Build a Prop-level `.below` inductive.
///
/// For a Prop inductive `I_i` with constructor `C : ∀ params fields, I_i params`,
/// the `.below` inductive has:
/// - Type: `∀ {params} {motives} (major : I_i params), Prop`
/// - One ctor per parent ctor, with IH fields expanded to include `.below` proofs.
///
/// Follows `IndPredBelow.lean:83-120`.
#[allow(clippy::too_many_arguments)]
fn build_below_indc(
  ci: usize,
  below_name: &Name,
  rec_val: &RecursorVal,
  ind: &InductiveVal,
  lean_env: &LeanEnv,
  n_classes: usize,
  sorted_classes: &[Vec<Name>],
  _canonical_recs: &[(Name, RecursorVal)],
) -> Result<BelowIndc, CompileError> {
  let n_params = rec_val.num_params.to_u64().unwrap_or(0) as usize;
  let n_motives = rec_val.num_motives.to_u64().unwrap_or(0) as usize;
  let _n_minors = rec_val.num_minors.to_u64().unwrap_or(0) as usize;
  let _n_indices = ind.num_indices.to_u64().unwrap_or(0) as usize;
  let below_n_params = n_params + n_motives;
  let ind_level_params = &ind.cnst.level_params;

  // Build .below names for all classes (needed for ihTypeToBelowType)
  let below_names: Vec<Name> = (0..n_classes)
    .map(|j| {
      let rep = &sorted_classes[j][0];
      Name::str(rep.clone(), "below".to_string())
    })
    .collect();

  // .below type: ∀ {params} {motives} (major : I_i params indices), Prop
  // Build from the recursor type: take params + motives, skip minors,
  // take indices + major, return Prop.
  let below_type = build_below_indc_type(rec_val, ind);

  // Build constructors: one per parent ctor for class ci
  let mut ctors = Vec::new();

  // Walk rec type to find the minors for this class.
  // The minors in the rec type correspond to constructors.
  // We need to identify which minors belong to class ci.
  let mut _global_minor_idx = 0usize;
  for class_idx in 0..n_classes {
    let class_rep = &sorted_classes[class_idx][0];
    let class_ind = match lean_env.get(class_rep) {
      Some(ConstantInfo::InductInfo(v)) => v,
      _ => {
        _global_minor_idx += 1;
        continue;
      },
    };

    for ctor_name in &class_ind.ctors {
      if class_idx == ci {
        // This ctor belongs to our class — build a .below ctor for it
        let ctor = match lean_env.get(ctor_name) {
          Some(ConstantInfo::CtorInfo(c)) => c,
          _ => {
            _global_minor_idx += 1;
            continue;
          },
        };

        let below_ctor = build_below_indc_ctor(
          below_name,
          ctor_name,
          ctor,
          rec_val,
          ind,
          ci,
          n_params,
          n_motives,
          n_classes,
          &below_names,
          sorted_classes,
          lean_env,
        );
        ctors.push(below_ctor);
      }
      _global_minor_idx += 1;
    }
  }

  Ok(BelowIndc {
    name: below_name.clone(),
    level_params: ind_level_params.clone(), // .below has same level params as parent (no elim level for Prop)
    n_params: below_n_params,
    typ: below_type,
    ctors,
  })
}

/// Build the type of a Prop-level `.below` inductive.
///
/// Type: `∀ {params} {motives} (indices) (major : I params indices), Prop`
///
/// Uses FVar-based construction: opens all rec type binders, skips minors,
/// adjusts motive domains to target Prop, re-closes with `mk_forall`.
fn build_below_indc_type(
  rec_val: &RecursorVal,
  ind: &InductiveVal,
) -> LeanExpr {
  let n_params = rec_val.num_params.to_u64().unwrap_or(0) as usize;
  let n_motives = rec_val.num_motives.to_u64().unwrap_or(0) as usize;
  let n_minors = rec_val.num_minors.to_u64().unwrap_or(0) as usize;
  let n_indices = ind.num_indices.to_u64().unwrap_or(0) as usize;

  // Open all rec type binders into FVars.
  let (_, param_decls, after_params) =
    forall_telescope(&rec_val.cnst.typ, n_params, "bitp", 0);
  let (_, motive_decls, after_motives) =
    forall_telescope(&after_params, n_motives, "bitm", 0);
  let (_, _minor_decls, after_minors) =
    forall_telescope(&after_motives, n_minors, "bitx", 0);
  let (_, index_decls, after_indices) =
    forall_telescope(&after_minors, n_indices, "biti", 0);
  let (_, major_decls, _) = forall_telescope(&after_indices, 1, "bitj", 0);

  // Adjust motive domains: replace result Sort with Prop, make implicit.
  // Prop .below motives always target Prop, even with large elimination (drec).
  let motive_decls: Vec<LocalDecl> = motive_decls
    .into_iter()
    .map(|mut d| {
      d.domain = replace_result_sort_with_prop(&d.domain);
      d.info = BinderInfo::Implicit;
      d
    })
    .collect();

  let all_decls: Vec<LocalDecl> = param_decls
    .into_iter()
    .chain(motive_decls)
    .chain(index_decls)
    .chain(major_decls)
    .collect();

  mk_forall(LeanExpr::sort(Level::zero()), &all_decls)
}

/// Build a constructor for a Prop-level `.below` inductive.
///
/// For parent ctor `C : ∀ params fields, I params`:
/// The `.below` ctor has: `∀ params motives (expanded_fields), I.below motives (C params orig_fields)`
///
/// For each field in the parent ctor:
/// - Non-recursive field: keep as-is
/// - Recursive field (head is inductive in block): expand to TWO extra fields:
///   1. `ih : Target_j.below motives args` (below proof)
///   2. `f_ih : motive_j args` (motive proof)
///
/// Uses FVar-based construction: opens all binders into FVars, builds
/// domains using FVar references, closes with `mk_forall`.
#[allow(clippy::too_many_arguments)]
fn build_below_indc_ctor(
  below_name: &Name,
  ctor_name: &Name,
  ctor: &ConstructorVal,
  rec_val: &RecursorVal,
  ind: &InductiveVal,
  _ci: usize,
  n_params: usize,
  n_motives: usize,
  n_classes: usize,
  below_names: &[Name],
  sorted_classes: &[Vec<Name>],
  lean_env: &LeanEnv,
) -> BelowCtor {
  let ctor_suffix = ctor_name
    .strip_prefix(&ind.cnst.name)
    .unwrap_or_else(|| ctor_name.components());
  let below_ctor_name = below_name.append_components(&ctor_suffix);

  let n_ctor_params = ctor.num_params.to_u64().unwrap_or(0) as usize;
  let n_ctor_fields = ctor.num_fields.to_u64().unwrap_or(0) as usize;
  let ind_level_params = &ind.cnst.level_params;

  // Extract original field binder names from the Lean-generated `.below` ctor
  // for faithful roundtrip of hygiene names.
  let orig_below_ctor_name = below_name.append_components(&ctor_suffix);
  let orig_field_names: Vec<Name> = lean_env
    .get(&orig_below_ctor_name)
    .and_then(|ci| match ci {
      ConstantInfo::CtorInfo(cv) => {
        let mut names = Vec::new();
        let mut ty = cv.cnst.typ.clone();
        let skip = cv.num_params.to_u64().unwrap_or(0) as usize;
        for _ in 0..skip {
          if let ExprData::ForallE(_, _, body, _, _) = ty.as_data() {
            ty = body.clone();
          }
        }
        while let ExprData::ForallE(name, _, body, _, _) = ty.as_data() {
          names.push(name.clone());
          ty = body.clone();
        }
        Some(names)
      },
      _ => None,
    })
    .unwrap_or_default();
  let mut orig_name_iter = orig_field_names.into_iter();

  // --- Phase 1: Open ctor type into FVars ---

  // Open params from ctor type
  let (param_fvars, param_decls, after_params) =
    forall_telescope(&ctor.cnst.typ, n_ctor_params, "bicp", 0);

  // Open fields from ctor type (after params). Domains now reference param FVars.
  let (field_fvars, field_decls, _ctor_return) =
    forall_telescope(&after_params, n_ctor_fields, "bicf", 0);

  // --- Phase 2: Create motive FVars from rec type ---
  // Open rec type past params (using our param FVars for substitution),
  // then extract motive domains. Replace result Sort with Prop.
  let (_, _rec_param_decls, rec_after_params) =
    forall_telescope(&rec_val.cnst.typ, n_params, "bicrp", 0);
  // The motive domains in the rec type reference rec param FVars, but we need
  // them to reference our ctor param FVars. Since both have the same structure,
  // we open the rec type motives with forall_telescope and then substitute
  // the rec param FVars with our ctor param FVars.
  // Actually, simpler: open rec motives independently, then in the final
  // mk_forall, the motive domains will be abstracted correctly since they
  // don't reference the ctor's param FVars. But we need motive FVars that
  // we can use in field domains. Let's create them with adjusted domains.
  let mut motive_fvars: Vec<LeanExpr> = Vec::new();
  let mut motive_decls: Vec<LocalDecl> = Vec::new();
  {
    let mut rec_cur = rec_after_params.clone();
    for mi in 0..n_motives {
      if let ExprData::ForallE(name, dom, body, _, _) = rec_cur.as_data() {
        let dom = replace_result_sort_with_prop(dom);
        let (fv_name, fv) = fresh_fvar("bicm", mi);
        motive_decls.push(LocalDecl {
          fvar_name: fv_name,
          binder_name: name.clone(),
          domain: dom,
          info: BinderInfo::Implicit,
        });
        motive_fvars.push(fv.clone());
        rec_cur = instantiate1(body, &fv);
      }
    }
  }

  // --- Phase 3: Detect recursive fields and build expanded binders ---

  // Maps from inductive name → class index for recursive field detection.
  let all_ind_names: Vec<(Name, usize)> = (0..n_classes)
    .flat_map(|j| {
      sorted_classes[j].iter().filter_map(move |name| {
        lean_env.get(name).map(|ci| match ci {
          ConstantInfo::InductInfo(v) => (v.cnst.name.clone(), j),
          _ => (name.clone(), j),
        })
      })
    })
    .collect();

  // Classify fields as recursive or not. Field domains are in FVar form
  // (param FVars substituted), so detect_rec_target_class works on Const heads.
  struct FieldEntry {
    decl: LocalDecl,
    fvar: LeanExpr,
    rec_target: Option<usize>,
  }

  let fields: Vec<FieldEntry> = field_decls
    .into_iter()
    .zip(field_fvars.iter().cloned())
    .map(|(decl, fvar)| {
      let rec_target = detect_rec_target_class(&decl.domain, &all_ind_names);
      FieldEntry { decl, fvar, rec_target }
    })
    .collect();

  // Build the expanded binder list following Lean's IndPredBelow ordering:
  // Pass 1: All original fields (non-rec and rec alike)
  // Pass 2: For each recursive field, add (ih_below, motive_proof) pairs
  let mut expanded_decls: Vec<LocalDecl> = Vec::new();
  let mut orig_field_fvars: Vec<LeanExpr> = Vec::new(); // FVars for original fields

  // Pass 1: Push all original fields
  for field in &fields {
    let orig_name =
      orig_name_iter.next().unwrap_or_else(|| field.decl.binder_name.clone());
    expanded_decls
      .push(LocalDecl { binder_name: orig_name, ..field.decl.clone() });
    orig_field_fvars.push(field.fvar.clone());
  }

  // Pass 2: For each recursive field, push ih_below + motive_proof
  for field in &fields {
    if let Some(target_j) = field.rec_target {
      // ih: Target_j.below params motives field_fvar
      // The field domain is `I_j args` in FVar form. We need to build
      // `I_j.below params motives args field_fvar`.
      let ih_dom = transform_to_below_fvar(
        &field.decl.domain,
        target_j,
        &param_fvars,
        &motive_fvars,
        below_names,
        ind_level_params,
        &field.fvar,
      );
      let ih_name = orig_name_iter
        .next()
        .unwrap_or_else(|| Name::str(Name::anon(), "ih".to_string()));
      let (ih_fv_name, ih_fv) = fresh_fvar("bici", expanded_decls.len());
      expanded_decls.push(LocalDecl {
        fvar_name: ih_fv_name,
        binder_name: ih_name,
        domain: ih_dom,
        info: BinderInfo::Default,
      });

      // f_ih: motive_j field_fvar
      // Replace inductive head with motive FVar, apply to same args + field_fvar
      let fih_dom = replace_head_with_fvar(
        &field.decl.domain,
        &motive_fvars[target_j],
        &field.fvar,
      );
      let fih_name =
        orig_name_iter.next().unwrap_or_else(|| field.decl.binder_name.clone());
      let (fih_fv_name, _fih_fv) = fresh_fvar("bicih", expanded_decls.len());
      expanded_decls.push(LocalDecl {
        fvar_name: fih_fv_name,
        binder_name: fih_name,
        domain: fih_dom,
        info: BinderInfo::Default,
      });

      let _ = ih_fv; // used only for its FVar name in mk_forall
    }
  }

  // --- Phase 4: Build return type using FVars ---
  // Return type: below_name params motives (ctor params orig_fields)
  let ctor_app = mk_app_n(
    mk_const(
      ctor_name,
      &ind_level_params
        .iter()
        .map(|lp| Level::param(lp.clone()))
        .collect::<Vec<_>>(),
    ),
    &[&param_fvars[..], &orig_field_fvars[..]].concat(),
  );

  let mut ret = mk_const(
    below_name,
    &ind_level_params
      .iter()
      .map(|lp| Level::param(lp.clone()))
      .collect::<Vec<_>>(),
  );
  ret = mk_app_n(ret, &param_fvars);
  ret = mk_app_n(ret, &motive_fvars);
  ret = LeanExpr::app(ret, ctor_app);

  // --- Phase 5: Close with mk_forall ---
  let all_decls: Vec<LocalDecl> =
    param_decls.into_iter().chain(motive_decls).chain(expanded_decls).collect();

  let n_fields_total = all_decls.len() - n_params - n_motives;
  let typ = mk_forall(ret, &all_decls);

  BelowCtor {
    name: below_ctor_name,
    typ,
    n_params: n_params + n_motives,
    n_fields: n_fields_total,
  }
}

/// Transform `I_j args` (FVar-based) to `I_j.below params motives args major`.
///
/// Handles forall wrapping: opens inner foralls, replaces head, adds
/// params + motives, re-closes.
fn transform_to_below_fvar(
  field_dom: &LeanExpr,
  target_j: usize,
  param_fvars: &[LeanExpr],
  motive_fvars: &[LeanExpr],
  below_names: &[Name],
  level_params: &[Name],
  major_fvar: &LeanExpr,
) -> LeanExpr {
  // Open any inner foralls (for higher-order recursive fields like `∀ a, I_j (f a)`)
  let n_inner = count_foralls_expr(field_dom);
  let (inner_fvars, inner_decls, leaf) =
    forall_telescope(field_dom, n_inner, "bict", 0);

  // Decompose leaf: should be `I_j args...` (Const or FVar head)
  let (_head, args) = decompose_apps(&leaf);

  // Build: I_j.below params motives args major_applied
  let below_const = mk_const(
    &below_names[target_j],
    &level_params.iter().map(|lp| Level::param(lp.clone())).collect::<Vec<_>>(),
  );
  let mut result = below_const;
  result = mk_app_n(result, param_fvars);
  result = mk_app_n(result, motive_fvars);
  // Apply original args (skip first n_params, those are already in param_fvars)
  let n_params = param_fvars.len();
  for a in args.iter().skip(n_params) {
    result = LeanExpr::app(result, a.clone());
  }
  // Apply inner forall args if present
  if !inner_fvars.is_empty() {
    result = mk_app_n(result, &inner_fvars);
  }
  // Apply the major (the field value itself)
  if n_inner == 0 {
    result = LeanExpr::app(result, major_fvar.clone());
  }

  // Re-close inner foralls if present
  if !inner_decls.is_empty() {
    result = mk_forall(result, &inner_decls);
  }
  result
}

/// Replace the head constant in a field domain with a motive FVar.
///
/// `I_j args` → `motive_fvar args major_fvar`
/// Handles forall wrapping.
fn replace_head_with_fvar(
  field_dom: &LeanExpr,
  motive_fvar: &LeanExpr,
  major_fvar: &LeanExpr,
) -> LeanExpr {
  let n_inner = count_foralls_expr(field_dom);
  let (inner_fvars, inner_decls, leaf) =
    forall_telescope(field_dom, n_inner, "bicr", 0);

  let (_head, args) = decompose_apps(&leaf);

  // Build: motive_fvar args inner_fvars major_fvar
  let _n_params = args.len();
  let mut result = motive_fvar.clone();
  // Skip param args (the motive doesn't take params)
  // The args from the field domain are: params... indices...
  // The motive takes: indices... major
  // So skip the first n_param args
  // Actually, the field domain in FVar form has param FVars as args.
  // The motive FVar already has the right type (∀ indices major, Prop).
  // So we need to skip the param-level args and pass only index-level + major.
  // For Prop mutual cycles with 0 params, all args are indices.
  // For the general case: the ctor field's I_j application has all args
  // (params included as FVars). The motive takes only indices + major.
  // We don't know how many are params here, so we skip none and let
  // the type checker sort it out — the args after the head should match
  // what the motive expects.
  for a in &args {
    result = LeanExpr::app(result, a.clone());
  }
  if !inner_fvars.is_empty() {
    result = mk_app_n(result, &inner_fvars);
  }
  if n_inner == 0 {
    result = LeanExpr::app(result, major_fvar.clone());
  }

  if !inner_decls.is_empty() {
    result = mk_forall(result, &inner_decls);
  }
  result
}

/// Detect if a field domain targets an inductive in the block.
/// Returns the class index if found.
///
/// Works on both BVar-based and FVar-based domains — checks for Const heads.
fn detect_rec_target_class(
  dom: &LeanExpr,
  all_ind_names: &[(Name, usize)],
) -> Option<usize> {
  let mut ty = dom.clone();
  loop {
    match ty.as_data() {
      ExprData::ForallE(_, _, body, _, _) => ty = body.clone(),
      _ => {
        let (head, _) = decompose_apps(&ty);
        if let ExprData::Const(name, _, _) = head.as_data() {
          for (ind_name, class_idx) in all_ind_names {
            if name == ind_name {
              return Some(*class_idx);
            }
          }
        }
        return None;
      },
    }
  }
}

/// Build a minor premise argument for `.below`.
///
/// `minor_dom` is the minor's type from the rec type, in FVar form (params
/// and motives already substituted with FVars). e.g.:
///   `∀ (x : B) (x_ih : _bvm_1 x), _bvm_0 (A.a x)`
/// where `_bvm_0`, `_bvm_1` are motive FVars.
///
/// For each field:
/// - Non-IH field (head is NOT a motive FVar) → keep as lambda param
/// - IH field (head IS a motive FVar) → replace domain with `Sort rlvl`,
///   collect PProd entry: `motive_app ×' ih_field`
///
/// The result is a lambda taking all fields (with IH types replaced by Sort rlvl),
/// returning a PProd chain of entries, ending with PUnit.
fn build_below_minor(
  minor_dom: &LeanExpr,
  rlvl: &Level,
  elim_level: &Level,
  motive_fvars: &[LeanExpr],
) -> LeanExpr {
  // Open all field binders with forall_telescope. After this, field
  // domains reference motive FVars directly (no BVar arithmetic needed).
  let n_fields = count_foralls_expr(minor_dom);
  let (field_fvars, field_decls, _return_type) =
    forall_telescope(minor_dom, n_fields, "bwf", 0);

  // Classify fields: IH (head is motive FVar) vs non-IH.
  struct FieldInfo {
    decl: LocalDecl,
    fvar: LeanExpr,
    is_ih: bool,
    /// For IH fields: the original domain expression (motive_fvar args)
    motive_app: Option<LeanExpr>,
  }

  let fields: Vec<FieldInfo> = field_decls
    .into_iter()
    .zip(field_fvars)
    .map(|(decl, fvar)| {
      let is_ih = find_motive_fvar(&decl.domain, motive_fvars).is_some();
      let motive_app = if is_ih { Some(decl.domain.clone()) } else { None };
      FieldInfo { decl, fvar, is_ih, motive_app }
    })
    .collect();

  // Build PProd entries from IH fields.
  // Each entry is PProd(motive_app, ih_field_fvar) — both in FVar form.
  // No manual BVar arithmetic or shift_vars needed.
  let mut ih_entries: Vec<LeanExpr> = Vec::new();
  for field in &fields {
    if field.is_ih
      && let Some(motive_app) = &field.motive_app
    {
      let pprod = mk_pprod(elim_level, rlvl, motive_app, &field.fvar);
      ih_entries.push(pprod);
    }
  }

  // Pack IH entries following Lean's PProdN.pack convention:
  //   []       -> PUnit.{rlvl}
  //   [a]      -> a
  //   [a,b]    -> PProd a b
  //   [a,b,c]  -> PProd a (PProd b c)
  let body = if ih_entries.is_empty() {
    punit_const(rlvl)
  } else {
    let last = ih_entries.pop().unwrap();
    ih_entries
      .iter()
      .rev()
      .fold(last, |acc, entry| mk_pprod(rlvl, rlvl, entry, &acc))
  };

  // Build lambda binders: for IH fields, replace domain with Sort rlvl.
  let lam_decls: Vec<LocalDecl> = fields
    .into_iter()
    .map(|f| {
      if f.is_ih {
        LocalDecl { domain: LeanExpr::sort(rlvl.clone()), ..f.decl }
      } else {
        f.decl
      }
    })
    .collect();

  mk_lambda(body, &lam_decls)
}

/// Normalizing `max` for universe levels, matching Lean's `mkLevelMax'`.
///
/// Simplifies: `max(0, u) = u`, `max(u, 0) = u`, `max(u, u) = u`.
/// This avoids structural mismatches like `Max(Zero, Param(u))` vs `Param(u)`.
pub(super) fn level_max(a: &Level, b: &Level) -> Level {
  let a_zero = matches!(a.as_data(), LevelData::Zero(_));
  let b_zero = matches!(b.as_data(), LevelData::Zero(_));
  if a_zero {
    return b.clone();
  }
  if b_zero {
    return a.clone();
  }
  if a == b {
    return a.clone();
  }
  Level::max(a.clone(), b.clone())
}

/// Convert a `KUniv<Anon>` back to a `Level`, using `param_names` to recover
/// `Param` names from de Bruijn indices.
pub(super) fn kuniv_to_level(
  u: &crate::ix::kernel::level::KUniv<crate::ix::kernel::mode::Anon>,
  param_names: &[Name],
) -> Level {
  use crate::ix::kernel::level::UnivData;
  match u.data() {
    UnivData::Zero(_) => Level::zero(),
    UnivData::Succ(inner, _) => Level::succ(kuniv_to_level(inner, param_names)),
    UnivData::Max(a, b, _) => {
      let la = kuniv_to_level(a, param_names);
      let lb = kuniv_to_level(b, param_names);
      level_max(&la, &lb)
    },
    UnivData::IMax(a, b, _) => Level::imax(
      kuniv_to_level(a, param_names),
      kuniv_to_level(b, param_names),
    ),
    UnivData::Param(idx, _, _) => {
      let name = param_names
        .get(*idx as usize)
        .cloned()
        .unwrap_or_else(|| Name::str(Name::anon(), format!("u_{idx}")));
      Level::param(name)
    },
  }
}

/// Infer the universe level of a type expression using the kernel type checker.
///
/// Converts `expr` to a KExpr, runs `tc.infer` to get its type (a Sort),
/// then extracts the level and converts back to a `Level`.
/// Falls back to `fallback` if inference fails.
pub(super) fn infer_sort_level(
  expr: &LeanExpr,
  param_names: &[Name],
  stt: &crate::ix::compile::CompileState,
  fallback: &Level,
) -> Level {
  use crate::ix::kernel::ingress::lean_expr_to_zexpr;
  use crate::ix::kernel::mode::Anon;
  use crate::ix::kernel::tc::TypeChecker;

  let n2a = Some(&stt.name_to_addr);
  let aux_n2a = Some(&stt.aux_name_to_addr);
  let kexpr = lean_expr_to_zexpr(expr, param_names, &stt.kintern, n2a, aux_n2a);

  let tc_intern = crate::ix::kernel::env::InternTable::<Anon>::new();
  let mut tc = TypeChecker::<Anon>::new(&stt.kenv, tc_intern);

  match tc.infer(&kexpr) {
    Ok(ty) => match tc.ensure_sort(&ty) {
      Ok(ku) => kuniv_to_level(&ku, param_names),
      Err(_) => fallback.clone(),
    },
    Err(_) => fallback.clone(),
  }
}

/// Build `PProd.{u, v} a b` with separate universe levels for each component.
///
/// Matches Lean's `mkPProd` which infers levels from the actual types.
/// Callers should compute `lvl1` from `a`'s sort level and `lvl2` from `b`'s sort level.
pub(super) fn mk_pprod(
  lvl1: &Level,
  lvl2: &Level,
  a: &LeanExpr,
  b: &LeanExpr,
) -> LeanExpr {
  let pprod = LeanExpr::cnst(
    Name::str(Name::anon(), "PProd".to_string()),
    vec![lvl1.clone(), lvl2.clone()],
  );
  LeanExpr::app(LeanExpr::app(pprod, a.clone()), b.clone())
}

/// Build `PUnit.{u}` (the type, at `Sort (u+1)`)
pub(super) fn punit_const(lvl: &Level) -> LeanExpr {
  LeanExpr::cnst(
    Name::str(Name::anon(), "PUnit".to_string()),
    vec![lvl.clone()],
  )
}

/// Build `PProd.mk.{u, v} type_a type_b val_a val_b`
pub(super) fn mk_pprod_mk(
  lvl_u: &Level,
  lvl_v: &Level,
  type_a: &LeanExpr,
  type_b: &LeanExpr,
  val_a: &LeanExpr,
  val_b: &LeanExpr,
) -> LeanExpr {
  let pprod_mk = LeanExpr::cnst(
    Name::str(Name::str(Name::anon(), "PProd".to_string()), "mk".to_string()),
    vec![lvl_u.clone(), lvl_v.clone()],
  );
  LeanExpr::app(
    LeanExpr::app(
      LeanExpr::app(LeanExpr::app(pprod_mk, type_a.clone()), type_b.clone()),
      val_a.clone(),
    ),
    val_b.clone(),
  )
}

/// Build `PUnit.unit.{u}` (the term, not the type)
pub(super) fn mk_punit_unit(lvl: &Level) -> LeanExpr {
  LeanExpr::cnst(
    Name::str(Name::str(Name::anon(), "PUnit".to_string()), "unit".to_string()),
    vec![lvl.clone()],
  )
}

/// Replace the result sort of a forall chain with `Sort 0` (Prop).
///
/// Given `∀ (x1 : A1) ... (xn : An), Sort u`, returns
/// `∀ (x1 : A1) ... (xn : An), Prop`.
///
/// Used when extracting motive domains from the recursor type for Prop-level
/// `.below` inductives. The recursor may have large elimination (extra `u`
/// param), but `.below` motives always target Prop.
pub(crate) fn replace_result_sort_with_prop(expr: &LeanExpr) -> LeanExpr {
  match expr.as_data() {
    ExprData::ForallE(name, dom, body, bi, _) => LeanExpr::all(
      name.clone(),
      dom.clone(),
      replace_result_sort_with_prop(body),
      bi.clone(),
    ),
    ExprData::Sort(_, _) => LeanExpr::sort(Level::zero()),
    _ => expr.clone(),
  }
}
