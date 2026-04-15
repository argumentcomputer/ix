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
  /// Number of indices: original inductive's indices + 1 (major premise).
  pub n_indices: usize,
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
    n_indices: canonical.n_indices,
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

  // Generate .below_N for nested auxiliary members (Type-level only).
  // Lean generates these via mkBelowFromRec for each nested auxiliary
  // recursor (BRecOn.lean:125-129). They're always definitions, even for
  // Prop-level blocks, but we only implement Type-level for now.
  //
  // The auxiliary recursors are at canonical_recs[n_classes..]. Each gets
  // a 1-based suffix: .below_1, .below_2, etc., hanging off the first
  // inductive in the block.
  if !is_prop {
    let n_aux = canonical_recs.len().saturating_sub(n_classes);
    if n_aux > 0 {
      let first_class_name = &sorted_classes[0][0];
      let first_ind = match lean_env.get(first_class_name) {
        Some(ConstantInfo::InductInfo(v)) => v,
        _ => return Ok(results),
      };
      // Lean hangs _N suffixed names off all[0] (first in source order),
      // not the canonical class representative.
      let all0 = &first_ind.all[0];
      for j in 0..n_aux {
        let idx = j + 1; // 1-based Lean convention
        let (_, aux_rec_val) = &canonical_recs[n_classes + j];
        let below_name = Name::str(all0.clone(), format!("below_{idx}"));

        // Only generate if this constant exists in the source environment.
        // Check lean_env (original Lean env during compilation) OR
        // stt.env.named (Ixon compile state — has all constants during
        // decompilation where lean_env is the incrementally-built work_env
        // and won't contain the constant we're about to generate).
        let exists = lean_env.contains_key(&below_name)
          || stt.is_some_and(|s| s.env.named.contains_key(&below_name));
        if !exists {
          continue;
        }

        // Extract the actual external inductive from the auxiliary
        // recursor's major premise. The major is the last binder in the
        // rec type: `∀ ... (t : ExtInd spec_params indices), ...`.
        // We need the external ind for the ilvl fallback path in
        // build_below_def, which uses ind.cnst.typ to extract the sort.
        let ext_ind =
          extract_major_head_ind(aux_rec_val, lean_env).unwrap_or(first_ind);

        let def = build_below_def(
          &below_name,
          aux_rec_val,
          ext_ind,
          lean_env,
          n_classes,
          canonical_recs,
          stt,
        )?;
        results.push(BelowConstant::Def(def));
      }
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
  _stt: Option<&crate::ix::compile::CompileState>,
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
  // Lean (BRecOn.lean:78-80):
  //   let majorTypeType ← inferType (← inferType major)
  //   let ilvl ← typeFormerTypeLevel majorTypeType
  //
  // We replicate this by opening the recursor type into FVars, getting the
  // major's type (an applied inductive), decomposing to get the head
  // inductive, looking up its sort, and substituting the occurrence levels.
  // This preserves Lean's level tree structure (no kernel normalization).
  let ilvl = {
    let total = n_params + n_motives + n_minors + n_indices + 1;
    let (_fvars, decls, _) =
      forall_telescope(&rec_val.cnst.typ, total, "blv", 0);

    // major's type in FVar form: e.g. `List(Doc.Part FVar_α FVar_β FVar_γ)`
    // or `Doc.Part FVar_α FVar_β FVar_γ` for original below.
    let major_type_fvar = &decls[total - 1].domain;

    // Decompose to get the head inductive and its level args.
    let (head, _args) = super::expr_utils::decompose_apps(major_type_fvar);

    if let ExprData::Const(head_name, head_levels, _) = head.as_data()
      && let Some(ConstantInfo::InductInfo(head_ind)) = lean_env.get(head_name)
    {
      // Get the inductive's sort: peel params + indices from the type.
      let head_n_params = head_ind.num_params.to_u64().unwrap_or(0) as usize;
      let head_n_indices = head_ind.num_indices.to_u64().unwrap_or(0) as usize;
      let raw_sort =
        get_ind_sort_level(&head_ind.cnst.typ, head_n_params + head_n_indices);
      // Substitute the inductive's level params with the occurrence levels,
      // then normalize to right-associated form to match Lean's inferType.
      let result = normalize_level(&super::expr_utils::subst_level(
        &raw_sort,
        &head_ind.cnst.level_params,
        head_levels,
      ));
      result
    } else {
      // Fallback: use parent inductive's sort level directly.
      get_ind_sort_level(&ind.cnst.typ, n_params + n_indices)
    }
  };

  // rlvl = max(ilvl, elim_level), normalized to match Lean's canonical form.
  let rlvl = normalize_level(&level_max(&ilvl, &elim_level));

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

/// Extract the `InductiveVal` from a recursor's major premise.
///
/// The major premise is the last binder in the recursor type:
/// `∀ params motives minors indices (t : ExtInd ...), motive ...`
/// Returns the `InductiveVal` for the head constant of the major's domain.
fn extract_major_head_ind<'a>(
  rec_val: &RecursorVal,
  lean_env: &'a LeanEnv,
) -> Option<&'a InductiveVal> {
  let n_params = rec_val.num_params.to_u64().unwrap_or(0) as usize;
  let n_motives = rec_val.num_motives.to_u64().unwrap_or(0) as usize;
  let n_minors = rec_val.num_minors.to_u64().unwrap_or(0) as usize;
  let n_indices = rec_val.num_indices.to_u64().unwrap_or(0) as usize;
  let total = n_params + n_motives + n_minors + n_indices + 1;

  // Peel all binders to get the major premise's domain.
  let mut cur = rec_val.cnst.typ.clone();
  for _ in 0..total - 1 {
    if let ExprData::ForallE(_, _, body, _, _) = cur.as_data() {
      cur = body.clone();
    }
  }
  // cur is now `∀ (t : MajorDom), ReturnType`
  let major_dom = match cur.as_data() {
    ExprData::ForallE(_, dom, _, _, _) => dom,
    _ => return None,
  };
  let (head, _) = decompose_apps(major_dom);
  match head.as_data() {
    ExprData::Const(name, _, _) => match lean_env.get(name) {
      Some(ConstantInfo::InductInfo(v)) => Some(v),
      _ => None,
    },
    _ => None,
  }
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
  _ind: &InductiveVal,
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
  // Use Level::succ directly (not mk_level_succ) to match Lean's elaborator,
  // which does NOT distribute Succ over Max for recursor elimination levels.
  //
  // Derive the inductive-level params from the recursor's own level params,
  // not from `ind`. The recursor's level params are [elim_level, ind_params...],
  // so [1..] gives the inductive-level params. This is correct for both the
  // main .below (where ind = block inductive) and below_N (where ind = external
  // inductive, whose level params may differ from the auxiliary recursor's).
  let mut rec_univs: Vec<Level> = vec![Level::succ(rlvl.clone())];
  for lp in &rec_val.cnst.level_params[1..] {
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
  let n_indices = ind.num_indices.to_u64().unwrap_or(0) as usize;
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
    n_indices: n_indices + 1, // original indices + major premise
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

  // Match Lean's `toImplicit` (IndPredBelow.lean:77-80): make index binders
  // implicit while keeping the major (last binder) explicit.
  let index_decls: Vec<LocalDecl> = index_decls
    .into_iter()
    .map(|mut d| {
      d.info = BinderInfo::Implicit;
      d
    })
    .collect();

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
  // ctor_return is the constructor's return type (e.g., `I params indices`) in FVar form.
  let (field_fvars, field_decls, ctor_return) =
    forall_telescope(&after_params, n_ctor_fields, "bicf", 0);

  // --- Phase 2: Create motive FVars from rec type ---
  // Peel rec type params by substituting with the ctor's param FVars (bicp_*).
  // This ensures motive domains reference the same FVars as param_decls,
  // so mk_forall can abstract them correctly.
  let mut rec_after_params = rec_val.cnst.typ.clone();
  for pf in &param_fvars {
    if let ExprData::ForallE(_, _, body, _, _) = rec_after_params.as_data() {
      rec_after_params = instantiate1(body, pf);
    }
  }
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

  // Build the expanded binder list following Lean's IndPredBelow ordering
  // (IndPredBelow.lean:99-113).
  //
  // Lean processes the recursor MINOR premise, which places ALL constructor
  // fields first, then ALL IH fields. IndPredBelow iterates the minor args
  // in order: non-IH args (constructor fields) are pushed as-is, then IH
  // args (motive-typed) get (below, motive) pairs inserted.
  //
  // Since we work from the constructor (not the minor), we replicate this
  // with two passes:
  //   Pass 1: push ALL original fields
  //   Pass 2: for each recursive field, push (ih_below, motive_proof)
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

  // Pass 2: For each recursive field, push (ih_below, motive_proof)
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

      // f_ih: motive_j indices... field_fvar
      // Replace inductive head with motive FVar, skip params, apply indices + field_fvar
      let fih_dom = replace_head_with_fvar(
        &field.decl.domain,
        &motive_fvars[target_j],
        &field.fvar,
        n_params,
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
  // Return type: below_name params motives indices... (ctor params orig_fields)
  // where indices are extracted from the constructor's return type `I params indices`.
  let univs: Vec<Level> =
    ind_level_params.iter().map(|lp| Level::param(lp.clone())).collect();
  let ctor_app = mk_app_n(
    mk_const(ctor_name, &univs),
    &[&param_fvars[..], &orig_field_fvars[..]].concat(),
  );

  // Extract index arguments from the ctor's return type.
  // _ctor_return is e.g. `Nat.le n (Nat.succ m)` in FVar form;
  // args after n_params are the index expressions.
  let (_ret_head, ret_args) = decompose_apps(&ctor_return);
  let index_args: Vec<&LeanExpr> = ret_args.iter().skip(n_params).collect();

  let mut ret = mk_const(below_name, &univs);
  ret = mk_app_n(ret, &param_fvars);
  ret = mk_app_n(ret, &motive_fvars);
  for idx_arg in &index_args {
    ret = LeanExpr::app(ret, (*idx_arg).clone());
  }
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
/// Given a field domain `I_j params... indices...`, build
/// `motive_fvar indices... major_fvar`. The motive does not take
/// parameters (they are global to the block), so the first
/// `num_params` arguments from the domain's application spine are
/// skipped.
///
/// Handles forall wrapping for higher-order fields.
fn replace_head_with_fvar(
  field_dom: &LeanExpr,
  motive_fvar: &LeanExpr,
  major_fvar: &LeanExpr,
  num_params: usize,
) -> LeanExpr {
  let n_inner = count_foralls_expr(field_dom);
  let (inner_fvars, inner_decls, leaf) =
    forall_telescope(field_dom, n_inner, "bicr", 0);

  let (_head, args) = decompose_apps(&leaf);

  // Build: motive_fvar indices... inner_fvars major_fvar
  // The args from the field domain are: [params..., indices...].
  // The motive takes only (indices, major), so skip the first num_params.
  let mut result = motive_fvar.clone();
  for a in args.iter().skip(num_params) {
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
/// - Simple IH field (domain = `motive args`) → replace domain with
///   `Sort rlvl`, collect PProd entry: `motive_app ×' ih_field`
/// - Higher-order IH field (domain = `∀ a₁..aₙ, motive args`) → replace
///   domain with `∀ a₁..aₙ, Sort rlvl`, collect PProd entry:
///   `∀ a₁..aₙ, PProd (motive args) (ih_field a₁..aₙ)`
///
/// The result is a lambda taking all fields (with IH types replaced),
/// returning a PProd chain of entries, ending with PUnit.
///
/// Matches Lean's `buildBelowMinorPremise` in
/// `refs/lean4/src/Lean/Meta/Constructions/BRecOn.lean:33-48`.
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
  // For IH fields, also open inner foralls to detect higher-order pattern.
  struct FieldInfo {
    decl: LocalDecl,
    fvar: LeanExpr,
    is_ih: bool,
    /// For higher-order IH: inner forall binders and leaf motive application.
    /// Empty for simple IH or non-IH fields.
    inner_decls: Vec<LocalDecl>,
    inner_fvars: Vec<LeanExpr>,
    /// The leaf motive application (after peeling inner foralls).
    /// For simple IH: same as `decl.domain`. For higher-order IH: the
    /// innermost `motive_fvar args` after stripping foralls.
    leaf_motive_app: Option<LeanExpr>,
  }

  let fields: Vec<FieldInfo> = field_decls
    .into_iter()
    .zip(field_fvars)
    .map(|(decl, fvar)| {
      let is_ih = find_motive_fvar(&decl.domain, motive_fvars).is_some();
      if is_ih {
        // Open inner foralls in the domain to distinguish simple vs
        // higher-order IH. For `motive x` → n_inner=0, leaf=motive x.
        // For `∀ (a : Nat), motive (f a)` → n_inner=1, leaf=motive (f a).
        let n_inner = count_foralls_expr(&decl.domain);
        let (inner_fvars, inner_decls, leaf) =
          forall_telescope(&decl.domain, n_inner, "bwi", 0);
        FieldInfo {
          decl,
          fvar,
          is_ih,
          inner_decls,
          inner_fvars,
          leaf_motive_app: Some(leaf),
        }
      } else {
        FieldInfo {
          decl,
          fvar,
          is_ih,
          inner_decls: vec![],
          inner_fvars: vec![],
          leaf_motive_app: None,
        }
      }
    })
    .collect();

  // Build PProd entries from IH fields.
  // Simple IH: PProd(motive_app, ih_fvar)
  // Higher-order IH: ∀ (a₁..aₙ), PProd(motive_app_leaf, ih_fvar a₁..aₙ)
  let mut ih_entries: Vec<LeanExpr> = Vec::new();
  for field in &fields {
    if field.is_ih
      && let Some(leaf) = &field.leaf_motive_app
    {
      if field.inner_decls.is_empty() {
        // Simple IH: no inner foralls.
        let pprod = mk_pprod(elim_level, rlvl, leaf, &field.fvar);
        ih_entries.push(pprod);
      } else {
        // Higher-order IH: distribute PProd inside the foralls.
        // Entry: ∀ (a₁..aₙ), PProd(leaf, ih_fvar a₁..aₙ)
        let ih_applied = mk_app_n(field.fvar.clone(), &field.inner_fvars);
        let pprod = mk_pprod(elim_level, rlvl, leaf, &ih_applied);
        let entry = mk_forall(pprod, &field.inner_decls);
        ih_entries.push(entry);
      }
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

  // Build lambda binders: for IH fields, replace domain with the
  // appropriate below-data type.
  // Simple IH: Sort rlvl
  // Higher-order IH: ∀ (a₁..aₙ), Sort rlvl
  let lam_decls: Vec<LocalDecl> = fields
    .into_iter()
    .map(|f| {
      if f.is_ih {
        let new_domain = if f.inner_decls.is_empty() {
          LeanExpr::sort(rlvl.clone())
        } else {
          mk_forall(LeanExpr::sort(rlvl.clone()), &f.inner_decls)
        };
        LocalDecl { domain: new_domain, ..f.decl }
      } else {
        f.decl
      }
    })
    .collect();

  mk_lambda(body, &lam_decls)
}

/// Compute the sort level of `PProd.{u, v}`, which is `Sort (max 1 u v)`.
///
/// Matches the structural level tree that Lean's `getLevel` produces when
/// inferring the type of a PProd application: `inferType(PProd.{u,v} X Y)`
/// returns `Sort (max 1 u v)`, where `max 1 u v` is built by two nested
/// `mkLevelMax` calls: `mkLevelMax(mkLevelMax(succ(0), u), v)`.
///
/// Construct `Succ(l)`, distributing over `Max`/`IMax` to match Lean's
/// `mkLevelSucc`:
///
///   `mkLevelSucc(Max(a, b))  = Max(mkLevelSucc(a), mkLevelSucc(b))`
///   `mkLevelSucc(IMax(a, b)) = Max(mkLevelSucc(a), mkLevelSucc(b))`
///   `mkLevelSucc(l)          = Succ(l)`  (otherwise)
///
/// Normalized successor: distributes `Succ` over `Max`/`Imax` to match
/// Lean's kernel normalization of universe levels in PProd.mk and similar
/// contexts.
///
/// Note: for recursor elimination levels (e.g., `.below` value's
/// `I.rec.{succ(rlvl)}`), use `Level::succ` directly instead — Lean's
/// elaborator does NOT distribute there.
pub(super) fn mk_level_succ(l: &Level) -> Level {
  match l.as_data() {
    LevelData::Max(a, b, _) => level_max(&mk_level_succ(a), &mk_level_succ(b)),
    LevelData::Imax(a, b, _) => level_max(&mk_level_succ(a), &mk_level_succ(b)),
    _ => Level::succ(l.clone()),
  }
}

/// Whether a level is an explicit numeric constant (a Succ-chain over Zero).
/// Matches Lean's `Level.isExplicit`.
fn is_explicit(l: &Level) -> bool {
  match l.as_data() {
    LevelData::Zero(_) => true,
    LevelData::Succ(inner, _) => is_explicit(inner),
    _ => false,
  }
}

/// Count the outermost Succ wrappers. Matches Lean's `Level.getOffset`.
fn get_offset(l: &Level) -> u64 {
  match l.as_data() {
    LevelData::Succ(inner, _) => 1 + get_offset(inner),
    _ => 0,
  }
}

/// Strip all outermost Succ wrappers. Matches Lean's `Level.getLevelOffset`.
fn get_level_offset(l: &Level) -> &Level {
  match l.as_data() {
    LevelData::Succ(inner, _) => get_level_offset(inner),
    _ => l,
  }
}

/// Check whether `u` subsumes `v` (i.e., `u >= v` for all parameter
/// assignments). Matches the `subsumes` local in Lean's `mkLevelMaxCore`.
///
/// Two cases:
/// 1. `v` is an explicit numeric (Succ-chain over Zero) and `u` has at
///    least as many Succ wrappers — the base of `u` is always >= 0.
/// 2. `u = max(u1, u2)` and `v` equals one of the direct children.
fn level_subsumes(u: &Level, v: &Level) -> bool {
  if is_explicit(v) && get_offset(u) >= get_offset(v) {
    return true;
  }
  if let LevelData::Max(u1, u2, _) = u.as_data() {
    return v == u1 || v == u2;
  }
  false
}

/// Normalizing `max` for universe levels, matching Lean's `mkLevelMaxCore`
/// / `mkLevelMax'` (`refs/lean4/src/Lean/Level.lean:516-534`).
///
/// Applies cheap simplifications beyond zero-elimination and equality:
/// - Subsumption: `max(max(a, b), a) = max(a, b)` (one-level subtree check)
/// - Explicit absorption: `max(succ(u), 1) = succ(u)` when offset(succ(u)) >= 1
/// - Same-base offset: `max(succ(succ(u)), succ(u)) = succ(succ(u))`
pub(super) fn level_max(a: &Level, b: &Level) -> Level {
  if a == b {
    return a.clone();
  }
  if matches!(a.as_data(), LevelData::Zero(_)) {
    return b.clone();
  }
  if matches!(b.as_data(), LevelData::Zero(_)) {
    return a.clone();
  }
  if level_subsumes(a, b) {
    return a.clone();
  }
  if level_subsumes(b, a) {
    return b.clone();
  }
  // Same base (after stripping Succs), different offsets: keep the larger.
  if get_level_offset(a) == get_level_offset(b) {
    return if get_offset(a) >= get_offset(b) { a.clone() } else { b.clone() };
  }
  Level::max(a.clone(), b.clone())
}

/// Normalize a level to Lean's canonical right-associated form.
/// - `max(max(a, b), c)` → `max(a, max(b, c))`
/// - Applied recursively to fully flatten and right-associate.
pub(super) fn normalize_level(lvl: &Level) -> Level {
  match lvl.as_data() {
    LevelData::Zero(_) | LevelData::Param(_, _) | LevelData::Mvar(_, _) => {
      lvl.clone()
    },
    LevelData::Succ(inner, _) => mk_level_succ(&normalize_level(inner)),
    LevelData::Max(a, b, _) => {
      let a = normalize_level(a);
      let b = normalize_level(b);
      // Right-associate: if a = max(a1, a2), flatten to max(a1, max(a2, b))
      if let LevelData::Max(a1, a2, _) = a.as_data() {
        let inner = level_max(&normalize_level(a2), &b);
        level_max(&normalize_level(a1), &normalize_level(&inner))
      } else {
        level_max(&a, &b)
      }
    },
    LevelData::Imax(a, b, _) => {
      Level::imax(normalize_level(a), normalize_level(b))
    },
  }
}

/// Convert a `KUniv<Meta>` back to a `Level`, using `param_names` to recover
/// `Param` names from de Bruijn indices.
pub(super) fn kuniv_to_level(
  u: &crate::ix::kernel::level::KUniv<crate::ix::kernel::mode::Meta>,
  param_names: &[Name],
) -> Level {
  use crate::ix::kernel::level::UnivData;
  match u.data() {
    UnivData::Zero(_) => Level::zero(),
    UnivData::Succ(inner, _) => {
      mk_level_succ(&kuniv_to_level(inner, param_names))
    },
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
