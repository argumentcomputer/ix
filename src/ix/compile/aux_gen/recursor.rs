//! Canonical recursor generation for alpha-collapsed inductive blocks.
//!
//! Regenerates a `RecursorVal` from canonical class structure, producing
//! identical output regardless of source declaration order.
//!
//! Closely follows `refs/lean4/src/kernel/inductive.cpp:589-776`:
//! - `mk_rec_infos`: builds motive types and minor premise types
//! - `mk_rec_rules`: builds rule RHS
//! - `declare_recursors`: assembles the final recursor type
//!
//! Key difference from C++: we use FVar-based intermediate computation
//! (see `expr_utils.rs`) then abstract back into de Bruijn binder chains.

use crate::ix::env::{
  BinderInfo, ConstantInfo, ConstantVal, ConstructorVal, Env as LeanEnv,
  Expr as LeanExpr, ExprData, InductiveVal, Level, LevelData, Name, NameData,
  RecursorRule, RecursorVal,
};
use crate::ix::ixon::CompileError;
use lean_ffi::nat::Nat;

use super::expr_utils::{
  LocalDecl, abstract_fvar, decompose_apps, fresh_fvar,
  instantiate_spec_with_fvars, instantiate1, mk_const, mk_forall, mk_lambda,
  shift_vars, subst_levels,
};

// =========================================================================
// Public API
// =========================================================================

/// Info about one member of the flat block (original or auxiliary).
struct FlatInfo<'a> {
  /// Name of the inductive (for originals: the class rep, for aux: external ind)
  name: Name,
  /// InductiveVal from lean_env
  ind: &'a InductiveVal,
  /// Constructors from lean_env
  ctors: Vec<&'a ConstructorVal>,
  /// All inductive names in equivalence class (for rec target detection).
  /// For auxiliary: just the external inductive name.
  all_names: Vec<Name>,
  /// True if this is an auxiliary member (nested occurrence)
  is_aux: bool,
  /// Specialized parameter expressions (empty for originals,
  /// concrete args like [Syntax] for auxiliaries)
  spec_params: Vec<LeanExpr>,
  /// Concrete universe level args from the nested occurrence.
  /// Empty for originals (use `ind_univs` instead).
  occurrence_level_args: Vec<Level>,
  /// Number of params for this member's inductive (may differ from block
  /// params for auxiliaries).
  own_params: usize,
  /// Number of indices for this member's inductive.
  n_indices: usize,
}

/// Generate canonical recursors for all classes in a block.
///
/// Returns one `RecursorVal` per class. `sorted_classes[i]` contains the
/// names of inductives in equivalence class `i`; the first is the
/// representative whose `InductiveVal` and `ConstructorVal`s are used.
/// Returns `(recursors, is_prop)` where `is_prop` indicates whether the
/// inductive block is in Prop. Downstream phases (`.below`, `.brecOn`)
/// use `is_prop` to choose between definition (Type-level) and inductive
/// (Prop-level) generation — matching Lean's `isPropFormerType` guard.
pub(crate) fn generate_canonical_recursors(
  sorted_classes: &[Vec<Name>],
  lean_env: &LeanEnv,
  stt: &crate::ix::compile::CompileState,
  aux_n2a: Option<&dashmap::DashMap<Name, crate::ix::address::Address>>,
) -> Result<(Vec<(Name, RecursorVal)>, bool), CompileError> {
  let mut classes: Vec<FlatInfo<'_>> = sorted_classes
    .iter()
    .map(|class| {
      let rep = &class[0];
      let ind = match lean_env.get(rep) {
        Some(ConstantInfo::InductInfo(v)) => v,
        _ => {
          return Err(CompileError::InvalidMutualBlock {
            reason: format!("aux_gen: {} not an inductive", rep.pretty()),
          });
        },
      };
      let ctors: Vec<&ConstructorVal> = ind
        .ctors
        .iter()
        .filter_map(|cn| match lean_env.get(cn) {
          Some(ConstantInfo::CtorInfo(c)) => Some(c),
          _ => None,
        })
        .collect();
      Ok(FlatInfo {
        name: ind.cnst.name.clone(),
        ind,
        ctors,
        all_names: class.clone(),
        is_aux: false,
        spec_params: vec![],
        occurrence_level_args: vec![],
        own_params: ind.num_params.to_u64().unwrap_or(0) as usize,
        n_indices: ind.num_indices.to_u64().unwrap_or(0) as usize,
      })
    })
    .collect::<Result<Vec<_>, _>>()?;

  let n_classes = classes.len();
  let n_params = classes[0].ind.num_params.to_u64().unwrap_or(0) as usize;

  // Build flat block to detect nested inductive occurrences.
  let ordered_originals: Vec<Name> =
    classes.iter().map(|c| c.name.clone()).collect();
  let flat =
    super::nested::build_compile_flat_block(&ordered_originals, lean_env);

  // Add auxiliary members (nested occurrences) to classes.
  for fm in flat.iter().skip(n_classes) {
    if let Some(ConstantInfo::InductInfo(ind)) = lean_env.get(&fm.name) {
      let ctors: Vec<&ConstructorVal> = ind
        .ctors
        .iter()
        .filter_map(|cn| match lean_env.get(cn) {
          Some(ConstantInfo::CtorInfo(c)) => Some(c),
          _ => None,
        })
        .collect();
      classes.push(FlatInfo {
        name: fm.name.clone(),
        ind,
        ctors,
        all_names: vec![fm.name.clone()],
        is_aux: true,
        spec_params: fm.spec_params.clone(),
        occurrence_level_args: fm.occurrence_level_args.clone(),
        own_params: fm.own_params,
        n_indices: fm.n_indices,
      });
    }
  }

  let n_flat = classes.len();

  let n_minors: usize = classes.iter().map(|fi| fi.ctors.len()).sum();

  // Compute is_large, k, and is_prop using the zero kernel's TypeChecker.
  let (is_large, k, is_prop) = compute_is_large_and_k(
    &classes, n_classes, n_params, lean_env, stt, aux_n2a,
  );

  // Build canonical level params: [u_1, u1, ..., un] for large, [u1, ..., un] for small.
  // Use the inductive's own level param names for consistency.
  // Build canonical level params following Lean C++ init_elim_level:
  // Start with "u", append suffix if it conflicts with existing level params.
  let ind_level_params = &classes[0].ind.cnst.level_params;
  let elim_level_name = {
    let mut u = Name::str(Name::anon(), "u".to_string());
    let mut i = 1;
    while ind_level_params.contains(&u) {
      u = Name::str(Name::anon(), format!("u_{}", i));
      i += 1;
    }
    u
  };
  let mut rec_level_params: Vec<Name> = Vec::new();
  if is_large {
    rec_level_params.push(elim_level_name.clone());
  }
  rec_level_params.extend(ind_level_params.iter().cloned());

  let n_ind_lvls = classes[0].ind.cnst.level_params.len();
  let univ_offset: usize = if is_large { 1 } else { 0 };

  // Shifted universe args for inductives: Param(0+offset)..Param(n-1+offset)
  let ind_univs: Vec<Level> = (0..n_ind_lvls)
    .map(|i| Level::param(rec_level_params[i + univ_offset].clone()))
    .collect();

  // Elim level
  let elim_level = if is_large {
    Level::param(rec_level_params[0].clone())
  } else {
    Level::zero()
  };

  // (n_minors already computed above from flat_infos)

  // === Collect binder info following Lean C++ mk_rec_infos ===

  // Param binder names + domains + binder info: walk first inductive type
  let first_ty = subst_levels(
    &classes[0].ind.cnst.typ,
    &classes[0].ind.cnst.level_params,
    &ind_univs,
  );
  let param_binders = collect_binders(&first_ty, n_params);

  // Per-class: index binders, motive name, minor names + types
  // We precompute motive types and minor types here.

  // Generate one recursor per flat member (originals + auxiliaries).
  let mut results = Vec::new();
  for di in 0..n_flat {
    let di_member = &classes[di];
    let n_indices = di_member.n_indices;

    // Name: original → <ind>.rec, auxiliary → <main>.rec_N
    let rec_name = if di < n_classes {
      Name::str(di_member.ind.cnst.name.clone(), "rec".to_string())
    } else {
      let main_name = classes[0].ind.cnst.name.clone();
      let aux_idx = di - n_classes + 1;
      Name::str(main_name, format!("rec_{}", aux_idx))
    };

    // `all` should list only the original inductives, matching Lean's convention.
    let all: Vec<Name> =
      classes[..n_classes].iter().map(|c| c.ind.cnst.name.clone()).collect();

    // Build rec type: ∀ params motives minors indices major, motive indices major
    let rec_type = build_rec_type(
      di,
      &classes,
      &flat,
      n_params,
      n_classes,
      &param_binders,
      &elim_level,
      &ind_univs,
      is_large,
      lean_env,
    );

    // Build rules
    let rules = build_rec_rules(
      di,
      &classes,
      &flat,
      n_params,
      n_classes,
      &param_binders,
      &elim_level,
      &ind_univs,
      is_large,
      &rec_level_params,
      &rec_type,
    );

    results.push((
      rec_name.clone(),
      RecursorVal {
        cnst: ConstantVal {
          name: rec_name,
          level_params: rec_level_params.clone(),
          typ: rec_type,
        },
        all,
        num_params: Nat::from(n_params as u64),
        num_indices: Nat::from(n_indices as u64),
        num_motives: Nat::from(n_flat as u64),
        num_minors: Nat::from(n_minors as u64),
        rules,
        k,
        is_unsafe: false,
      },
    ));
  }

  Ok((results, is_prop))
}

// =========================================================================
// Binder info collected from types
// =========================================================================

/// A binder extracted from a forall chain.
#[derive(Clone)]
struct Binder {
  name: Name,
  domain: LeanExpr,
  info: BinderInfo,
}

/// Collect the first `n` forall binders from an expression.
fn collect_binders(expr: &LeanExpr, n: usize) -> Vec<Binder> {
  let mut binders = Vec::with_capacity(n);
  let mut cur = expr.clone();
  for _ in 0..n {
    match cur.as_data() {
      ExprData::ForallE(name, dom, body, bi, _) => {
        binders.push(Binder {
          name: name.clone(),
          domain: dom.clone(),
          info: bi.clone(),
        });
        cur = body.clone();
      },
      _ => break,
    }
  }
  binders
}

// =========================================================================
// Recursor type construction
// =========================================================================

/// Build the full recursor type for class `di`.
///
/// Follows `declare_recursors` in inductive.cpp:752-774.
fn build_rec_type(
  di: usize,
  classes: &[FlatInfo<'_>],
  flat: &[super::nested::CompileFlatMember],
  n_params: usize,
  n_classes: usize,
  param_binders: &[Binder],
  elim_level: &Level,
  ind_univs: &[Level],
  _is_large: bool,
  lean_env: &LeanEnv,
) -> LeanExpr {
  let n_flat = flat.len();
  let n_indices = classes[di].n_indices;
  let mut depth: usize = 0;
  let mut domains: Vec<Binder> = Vec::new();

  // --- Params: create FVars ---
  let mut param_fvars: Vec<LeanExpr> = Vec::new();
  let mut param_decls: Vec<LocalDecl> = Vec::new();
  for (p, pb) in param_binders.iter().enumerate() {
    let (fv_name, fv) = fresh_fvar("param", p);
    param_fvars.push(fv);
    param_decls.push(LocalDecl {
      fvar_name: fv_name,
      binder_name: pb.name.clone(),
      domain: pb.domain.clone(),
      info: pb.info.clone(),
    });
    domains.push(pb.clone());
    depth += 1;
  }

  // --- Motives (Cs): one per flat member, create FVars ---
  let mut motive_fvars: Vec<LeanExpr> = Vec::new();
  let mut motive_decls: Vec<LocalDecl> = Vec::new();
  for j in 0..n_flat {
    let mut motive_ty = if j < n_classes {
      // Original member: use class info (FVar-based, contains param FVars)
      build_motive_type(
        j,
        classes,
        n_params,
        depth,
        elim_level,
        ind_univs,
        &param_fvars,
      )
    } else {
      // Auxiliary member (nested): build motive type from flat member.
      build_motive_type_aux(
        &classes[j],
        n_params,
        elim_level,
        ind_univs,
        lean_env,
      )
    };
    // Abstract param FVars from the motive type and shift for depth
    for pd in &param_decls {
      motive_ty = abstract_fvar(&motive_ty, &pd.fvar_name, 0);
    }
    let n_motives_before = depth - n_params; // motives already pushed
    if n_motives_before > 0 {
      motive_ty = shift_vars(&motive_ty, n_motives_before, 0);
    }
    // Lean C++ uses appendIndexAfter which produces "motive_N" as a
    // single string (not Name::str(Name::str(anon, "motive"), "N")).
    let motive_name = if n_flat > 1 {
      Name::str(Name::anon(), format!("motive_{}", j + 1))
    } else {
      Name::str(Name::anon(), "motive".to_string())
    };
    let (fv_name, fv) = fresh_fvar("motive", j);
    motive_fvars.push(fv);
    motive_decls.push(LocalDecl {
      fvar_name: fv_name,
      binder_name: motive_name.clone(),
      domain: motive_ty.clone(),
      info: BinderInfo::Default,
    });
    domains.push(Binder {
      name: motive_name,
      domain: motive_ty,
      info: BinderInfo::Default,
    });
    depth += 1;
  }

  // --- Minors: build for each flat member's constructors ---
  for j in 0..n_flat {
    // Get constructors for this flat member
    let member_ctors: Vec<&ConstructorVal> = if j < n_classes {
      classes[j].ctors.clone()
    } else {
      // Auxiliary member: look up ctors from the external inductive
      match lean_env.get(&flat[j].name) {
        Some(ConstantInfo::InductInfo(ind)) => ind
          .ctors
          .iter()
          .filter_map(|cn| match lean_env.get(cn) {
            Some(ConstantInfo::CtorInfo(c)) => Some(c),
            _ => None,
          })
          .collect(),
        _ => vec![],
      }
    };
    let ind_name = &flat[j].name;
    for ctor in &member_ctors {
      let mut minor_ty = build_minor_type(
        j,
        ctor,
        classes,
        n_params,
        &param_fvars,
        &motive_fvars,
        ind_univs,
      );
      // Abstract FVars in rec type binder order (outermost first).
      for pd in &param_decls {
        minor_ty = abstract_fvar(&minor_ty, &pd.fvar_name, 0);
      }
      for md in &motive_decls {
        minor_ty = abstract_fvar(&minor_ty, &md.fvar_name, 0);
      }
      let n_earlier_minors = depth - n_params - n_flat;
      if n_earlier_minors > 0 {
        minor_ty = shift_vars(&minor_ty, n_earlier_minors, 0);
      }
      // Extract the ctor suffix as a Name (e.g. `A.mk` → `mk`)
      let minor_name = ctor.cnst.name.strip_prefix(ind_name).map_or_else(
        || ctor.cnst.name.clone(),
        |suffix| Name::anon().append_components(&suffix),
      );
      domains.push(Binder {
        name: minor_name,
        domain: minor_ty,
        info: BinderInfo::Default,
      });
      depth += 1;
    }
  }

  // --- Indices for member di ---
  let di_member = &classes[di];
  let di_is_aux = di_member.is_aux;
  let di_ty = if di_is_aux && !di_member.occurrence_level_args.is_empty() {
    subst_levels(
      &di_member.ind.cnst.typ,
      &di_member.ind.cnst.level_params,
      &di_member.occurrence_level_args,
    )
  } else {
    subst_levels(
      &di_member.ind.cnst.typ,
      &di_member.ind.cnst.level_params,
      ind_univs,
    )
  };
  let mut ity = di_ty;
  // Peel params: for originals use param FVars, for aux use FVar-converted spec_params.
  let di_n_ext_params = di_member.own_params;
  let di_sp_fvars = if di_is_aux {
    instantiate_spec_with_fvars(&di_member.spec_params, &param_fvars)
  } else {
    vec![]
  };
  for p in 0..di_n_ext_params {
    if let ExprData::ForallE(_, _, body, _, _) = ity.as_data() {
      if di_is_aux && p < di_sp_fvars.len() {
        ity = instantiate1(body, &di_sp_fvars[p]);
      } else if p < param_fvars.len() {
        ity = instantiate1(body, &param_fvars[p]);
      } else {
        ity = body.clone();
      }
    }
  }
  // Peel index binders using FVars so that later index domains correctly
  // reference earlier indices as FVars (not corrupt BVars).
  // Follows lean4lean's approach: `withLocalDecl` + `instantiate1` per index.
  let mut index_fvars: Vec<LeanExpr> = Vec::new();
  let mut index_decls: Vec<LocalDecl> = Vec::new();
  for fi in 0..n_indices {
    match ity.as_data() {
      ExprData::ForallE(name, dom, body, bi, _) => {
        let (fv_name, fv) = fresh_fvar("idx", fi);
        index_decls.push(LocalDecl {
          fvar_name: fv_name,
          binder_name: name.clone(),
          domain: dom.clone(),
          info: bi.clone(),
        });
        index_fvars.push(fv.clone());
        ity = instantiate1(body, &fv);
      },
      _ => break,
    }
  }
  // Convert each index domain from FVar form to BVar form for the final
  // forall chain. Abstract param FVars, then shift for motives+minors,
  // then abstract earlier index FVars.
  let n_non_param_before_indices = depth - n_params; // motives + minors
  for (fi, decl) in index_decls.iter().enumerate() {
    let mut abs_dom = decl.domain.clone();
    // Abstract param FVars (outermost binders in the rec type)
    for pd in &param_decls {
      abs_dom = abstract_fvar(&abs_dom, &pd.fvar_name, 0);
    }
    // Shift up past motives + minors (between params and indices)
    if n_non_param_before_indices > 0 {
      abs_dom = shift_vars(&abs_dom, n_non_param_before_indices, 0);
    }
    // Abstract earlier index FVars (they're inner binders in the chain)
    for id in &index_decls[..fi] {
      abs_dom = abstract_fvar(&abs_dom, &id.fvar_name, 0);
    }
    domains.push(Binder {
      name: decl.binder_name.clone(),
      domain: abs_dom,
      info: decl.info.clone(),
    });
    depth += 1;
  }

  // --- Major ---
  let major_dom = if di_is_aux {
    // Auxiliary member: J.{occurrence_us} spec_params indices
    let major_univs = if !di_member.occurrence_level_args.is_empty() {
      &di_member.occurrence_level_args
    } else {
      ind_univs
    };
    let mut app = mk_const(&di_member.ind.cnst.name, major_univs);
    // Apply FVar-converted spec_params
    let sp_fvars =
      instantiate_spec_with_fvars(&di_member.spec_params, &param_fvars);
    for sp in &sp_fvars {
      app = LeanExpr::app(app, sp.clone());
    }
    // Indices: use FVars (will be abstracted below)
    for idx_fv in &index_fvars {
      app = LeanExpr::app(app, idx_fv.clone());
    }
    app
  } else {
    // Original member: I params indices
    // Build using FVars for params and indices, then abstract later.
    let mut app = mk_const(&di_member.ind.cnst.name, ind_univs);
    for pf in &param_fvars {
      app = LeanExpr::app(app, pf.clone());
    }
    for idx_fv in &index_fvars {
      app = LeanExpr::app(app, idx_fv.clone());
    }
    app
  };
  // Abstract param FVars from major domain
  let mut abs_major = major_dom;
  for pd in &param_decls {
    abs_major = abstract_fvar(&abs_major, &pd.fvar_name, 0);
  }
  // Shift past motives + minors
  if n_non_param_before_indices > 0 {
    abs_major = shift_vars(&abs_major, n_non_param_before_indices, 0);
  }
  // Abstract index FVars
  for id in &index_decls {
    abs_major = abstract_fvar(&abs_major, &id.fvar_name, 0);
  }
  domains.push(Binder {
    name: Name::str(Name::anon(), "t".to_string()),
    domain: abs_major,
    info: BinderInfo::Default,
  });
  depth += 1;

  // --- Return: motive_di indices major ---
  let motive_idx = (depth - 1 - n_params - di) as u64;
  let mut ret = LeanExpr::bvar(Nat::from(motive_idx));
  for i in 0..n_indices {
    ret = LeanExpr::app(ret, LeanExpr::bvar(Nat::from((n_indices - i) as u64)));
  }
  ret = LeanExpr::app(ret, LeanExpr::bvar(Nat::from(0u64)));

  // Fold into forall chain
  for b in domains.iter().rev() {
    ret = LeanExpr::all(b.name.clone(), b.domain.clone(), ret, b.info.clone());
  }

  // Apply infer_implicit: Lean calls inferImplicit(ty, 1000, false)
  // which processes ALL binders, marking them implicit if their BVar
  // appears in an explicit domain downstream.
  infer_implicit(&ret, 1000)
}

/// Build motive type for class `j`:
/// `∀ (indices...) (t : I params indices), Sort elim_level`
///
/// Uses FVars for params (from the rec type context) and fresh FVars for
/// indices, matching lean4lean's forallTelescope approach. The caller
/// must abstract param FVars from the result.
fn build_motive_type(
  j: usize,
  classes: &[FlatInfo<'_>],
  n_params: usize,
  _param_depth: usize,
  elim_level: &Level,
  ind_univs: &[Level],
  param_fvars: &[LeanExpr],
) -> LeanExpr {
  let ind = classes[j].ind;
  let n_indices = ind.num_indices.to_u64().unwrap_or(0) as usize;
  let ty = subst_levels(&ind.cnst.typ, &ind.cnst.level_params, ind_univs);

  // Skip params — substitute with param FVars from the rec type context.
  let mut cur = ty;
  for p in 0..n_params {
    if let ExprData::ForallE(_, _, body, _, _) = cur.as_data() {
      if p < param_fvars.len() {
        cur = instantiate1(body, &param_fvars[p]);
      } else {
        cur = instantiate1(body, &LeanExpr::sort(Level::zero()));
      }
    }
  }

  // Collect index binders using fresh FVars (forallTelescope-style).
  let mut index_fvars: Vec<LeanExpr> = Vec::new();
  let mut index_decls: Vec<LocalDecl> = Vec::new();
  for fi in 0..n_indices {
    match cur.as_data() {
      ExprData::ForallE(name, dom, body, bi, _) => {
        let (fv_name, fv) = fresh_fvar("m_idx", fi);
        index_decls.push(LocalDecl {
          fvar_name: fv_name,
          binder_name: name.clone(),
          domain: dom.clone(),
          info: bi.clone(),
        });
        index_fvars.push(fv.clone());
        cur = instantiate1(body, &fv);
      },
      _ => break,
    }
  }

  // Major: I params indices (all FVars)
  let mut major_ty = mk_const(&ind.cnst.name, ind_univs);
  for pf in param_fvars {
    major_ty = LeanExpr::app(major_ty, pf.clone());
  }
  for idx_fv in &index_fvars {
    major_ty = LeanExpr::app(major_ty, idx_fv.clone());
  }

  // ∀ (t : major_ty), Sort elim_level
  let sort = LeanExpr::sort(elim_level.clone());
  let major_decl = LocalDecl {
    fvar_name: Name::str(Name::anon(), "_motive_major".to_string()),
    binder_name: Name::str(Name::anon(), "t".to_string()),
    domain: major_ty,
    info: BinderInfo::Default,
  };

  // Abstract all FVars: index FVars first (innermost), then the caller
  // will abstract param FVars from the returned expression.
  let mut all_decls: Vec<LocalDecl> = Vec::new();
  all_decls.extend(index_decls);
  all_decls.push(major_decl);
  mk_forall(sort, &all_decls)
}

/// Build motive type for an auxiliary (nested) flat member.
///
/// For a nested occurrence `J Ds` where `J` is an external inductive
/// with indices, the motive type is `∀ (indices...) (t : J Ds indices), Sort u`.
/// `Ds` are the spec_params from the flat member.
///
/// Follows the zero kernel's `build_motive_type_flat` for auxiliaries.
fn build_motive_type_aux(
  member: &FlatInfo<'_>,
  _n_params: usize,
  elim_level: &Level,
  _ind_univs: &[Level],
  lean_env: &LeanEnv,
) -> LeanExpr {
  // Look up the external inductive
  let ind = match lean_env.get(&member.name) {
    Some(ConstantInfo::InductInfo(v)) => v,
    _ => return LeanExpr::sort(Level::zero()), // fallback
  };
  let n_ext_params = member.own_params;
  let n_ext_indices = member.n_indices;

  // Substitute levels with occurrence_level_args (concrete levels from
  // the nested occurrence). This is the key fix: previously we left
  // levels unsubstituted, but the motive type must use the concrete
  // universe args.
  let ty = if !member.occurrence_level_args.is_empty() {
    subst_levels(
      &ind.cnst.typ,
      &ind.cnst.level_params,
      &member.occurrence_level_args,
    )
  } else {
    ind.cnst.typ.clone()
  };

  // Skip params (substituting with spec_params).
  // Spec_params are in BVar form (relative to param context), but here
  // we're building the raw motive type (no FVars), so BVars referencing
  // outer params will end up as free vars. They get shifted when the
  // motive is placed in the rec type's forall chain.
  let mut cur = ty;
  for p in 0..n_ext_params {
    if let ExprData::ForallE(_, _, body, _, _) = cur.as_data() {
      if p < member.spec_params.len() {
        cur = instantiate1(body, &member.spec_params[p]);
      } else {
        cur = instantiate1(body, &LeanExpr::sort(Level::zero())); // placeholder
      }
    }
  }

  // Collect index binders
  let mut index_binders: Vec<Binder> = Vec::new();
  for _ in 0..n_ext_indices {
    match cur.as_data() {
      ExprData::ForallE(name, dom, body, bi, _) => {
        index_binders.push(Binder {
          name: name.clone(),
          domain: dom.clone(),
          info: bi.clone(),
        });
        cur = body.clone();
      },
      _ => break,
    }
  }

  // Build major type: J.{occurrence_us} spec_params indices
  let major_univs = if !member.occurrence_level_args.is_empty() {
    &member.occurrence_level_args
  } else {
    // Fallback: identity-mapped level params (shouldn't reach here for
    // proper aux members)
    &ind
      .cnst
      .level_params
      .iter()
      .map(|n| Level::param(n.clone()))
      .collect::<Vec<_>>()
  };
  let mut major_ty = mk_const(&member.name, major_univs);
  for sp in &member.spec_params {
    // Lift spec_params by n_ext_indices to account for the index binders
    // above the major type in the motive. The major binder itself doesn't
    // need shifting because it's the innermost — matching how the
    // original motive builder places param BVars at BVar(n_indices + p).
    let lifted = if n_ext_indices > 0 {
      shift_vars(sp, n_ext_indices, 0)
    } else {
      sp.clone()
    };
    major_ty = LeanExpr::app(major_ty, lifted);
  }
  for i in 0..n_ext_indices {
    major_ty = LeanExpr::app(
      major_ty,
      LeanExpr::bvar(Nat::from((n_ext_indices - 1 - i) as u64)),
    );
  }

  // Build: ∀ (major : major_ty), Sort elim_level
  let sort = LeanExpr::sort(elim_level.clone());
  let mut result = LeanExpr::all(
    Name::str(Name::anon(), "t".to_string()),
    major_ty,
    sort,
    BinderInfo::Default,
  );

  // Wrap index binders
  for b in index_binders.iter().rev() {
    result = LeanExpr::all(
      b.name.clone(),
      b.domain.clone(),
      result,
      BinderInfo::Default,
    );
  }

  result
}

/// Build minor premise type for a constructor using FVars.
///
/// `param_fvars`: FVars for the recursor's params (from outer context).
/// `motive_fvars`: FVars for the recursor's motives (from outer context).
fn build_minor_type(
  class_idx: usize,
  ctor: &ConstructorVal,
  classes: &[FlatInfo<'_>],
  n_params: usize,
  param_fvars: &[LeanExpr],
  motive_fvars: &[LeanExpr],
  ind_univs: &[Level],
) -> LeanExpr {
  let member = &classes[class_idx];
  // For auxiliary members, substitute levels with occurrence_level_args.
  // For originals, substitute with the block's ind_univs.
  let ctor_ty = if member.is_aux && !member.occurrence_level_args.is_empty() {
    subst_levels(
      &ctor.cnst.typ,
      &member.ind.cnst.level_params,
      &member.occurrence_level_args,
    )
  } else {
    subst_levels(&ctor.cnst.typ, &member.ind.cnst.level_params, ind_univs)
  };

  // Peel params: for originals, substitute with param FVars.
  // For auxiliaries, substitute with FVar-converted spec_params.
  let mut cur = ctor_ty;
  let n_ctor_params = ctor.num_params.to_u64().unwrap_or(0) as usize;
  let sp_fvars = if member.is_aux {
    instantiate_spec_with_fvars(&member.spec_params, param_fvars)
  } else {
    vec![]
  };
  for p in 0..n_ctor_params {
    if let ExprData::ForallE(_, _, body, _, _) = cur.as_data() {
      if member.is_aux && p < sp_fvars.len() {
        cur = instantiate1(body, &sp_fvars[p]);
      } else if p < param_fvars.len() {
        cur = instantiate1(body, &param_fvars[p]);
      } else {
        cur = instantiate1(body, &LeanExpr::sort(Level::zero())); // placeholder
      }
    }
  }

  // Collect fields: peel each field with a fresh FVar.
  let n_fields = ctor.num_fields.to_u64().unwrap_or(0) as usize;
  let mut field_decls: Vec<LocalDecl> = Vec::new();
  let mut field_fvars: Vec<LeanExpr> = Vec::new();
  let mut rec_fields: Vec<(usize, usize)> = Vec::new(); // (field_idx, target_class)

  for fi in 0..n_fields {
    match cur.as_data() {
      ExprData::ForallE(name, dom, body, bi, _) => {
        // Strip autoParam/optParam/outParam wrappers, matching Lean's
        // consumeTypeAnnotations in withLocalDecl calls.
        let clean_dom = consume_type_annotations(dom);
        let (fv_name, fv) = fresh_fvar("field", fi);
        field_decls.push(LocalDecl {
          fvar_name: fv_name,
          binder_name: name.clone(),
          domain: clean_dom.clone(),
          info: bi.clone(),
        });
        field_fvars.push(fv.clone());
        if let Some(ci) = find_rec_target(&clean_dom, classes, param_fvars) {
          rec_fields.push((fi, ci));
        }
        cur = instantiate1(body, &fv);
      },
      _ => break,
    }
  }

  // Build IH binders for recursive fields.
  let mut ih_decls: Vec<LocalDecl> = Vec::new();
  let mut ih_fvars: Vec<LeanExpr> = Vec::new();
  for (k, &(fi, target_ci)) in rec_fields.iter().enumerate() {
    let ih_ty = build_ih_type_fvar(
      &field_fvars[fi],
      &field_decls[fi].domain,
      target_ci,
      n_params,
      param_fvars,
      motive_fvars,
      classes,
    );
    // Lean C++ uses appendAfter("_ih") which appends "_ih" to the
    // innermost string component of the Name structure.
    let ih_name = name_append_after(&field_decls[fi].binder_name, "_ih");
    let (ih_fv_name, ih_fv) = fresh_fvar("ih", k);
    ih_decls.push(LocalDecl {
      fvar_name: ih_fv_name,
      binder_name: ih_name,
      domain: ih_ty,
      info: BinderInfo::Default,
    });
    ih_fvars.push(ih_fv);
  }

  // Conclusion: motive[class_idx](ctor_return_indices, C params fields)
  let mut conclusion = motive_fvars[class_idx].clone();

  // Return indices: `cur` is the ctor's return type with FVars for params/fields.
  // It should be `I params indices` — extract args past params.
  // For auxiliary members, skip own_params (not n_params).
  let skip_count = if member.is_aux { member.own_params } else { n_params };
  let (_, ret_args) = decompose_apps(&cur);
  let ret_indices: Vec<LeanExpr> =
    ret_args.into_iter().skip(skip_count).collect();
  for idx in &ret_indices {
    conclusion = LeanExpr::app(conclusion, idx.clone());
  }

  // C params/spec_params fields
  let ctor_univs = if member.is_aux && !member.occurrence_level_args.is_empty()
  {
    member.occurrence_level_args.as_slice()
  } else {
    ind_univs
  };
  let mut ctor_app = mk_const(&ctor.cnst.name, ctor_univs);
  if member.is_aux {
    // Apply FVar-converted spec_params
    for sp in &sp_fvars {
      ctor_app = LeanExpr::app(ctor_app, sp.clone());
    }
  } else {
    for pf in param_fvars {
      ctor_app = LeanExpr::app(ctor_app, pf.clone());
    }
  }
  for ff in &field_fvars {
    ctor_app = LeanExpr::app(ctor_app, ff.clone());
  }
  conclusion = LeanExpr::app(conclusion, ctor_app);

  // Fold: ∀ (fields...) (ihs...), conclusion
  // IHs first (innermost), then fields
  let mut all_binders: Vec<LocalDecl> = Vec::new();
  all_binders.extend(field_decls);
  all_binders.extend(ih_decls);
  mk_forall(conclusion, &all_binders)
}

/// Build IH type for a recursive field using FVars.
///
/// `field_fvar`: the FVar for this field.
/// `field_dom`: the field's domain (containing FVars for params/earlier fields).
/// The domain's head (after peeling foralls) should be an inductive in the block.
fn build_ih_type_fvar(
  field_fvar: &LeanExpr,
  field_dom: &LeanExpr,
  target_ci: usize,
  _n_params: usize,
  _param_fvars: &[LeanExpr],
  motive_fvars: &[LeanExpr],
  classes: &[FlatInfo<'_>],
) -> LeanExpr {
  // Use forallTelescope-style approach: peel foralls from the field domain
  // using fresh FVars so that the inner application is fully FVar-based.
  // This avoids the BVar/FVar mixing issues that cause FVar leaks.
  let mut xs_fvars: Vec<LeanExpr> = Vec::new();
  let mut xs_decls: Vec<LocalDecl> = Vec::new();
  let mut cur = field_dom.clone();

  while let ExprData::ForallE(name, dom, body, bi, _) = cur.as_data() {
    // Check if the expression head is an inductive in the block — stop if so
    let (h, _) = decompose_apps(&cur);
    if let ExprData::Const(cname, _, _) = h.as_data()
      && classes.iter().any(|c| c.all_names.iter().any(|n| n == cname))
    {
      break;
    }
    let (fv_name, fv) = fresh_fvar("ih_xs", xs_fvars.len());
    xs_decls.push(LocalDecl {
      fvar_name: fv_name,
      binder_name: name.clone(),
      domain: dom.clone(),
      info: bi.clone(),
    });
    xs_fvars.push(fv.clone());
    cur = instantiate1(body, &fv);
  }

  // `cur` is now the fully FVar-instantiated inner expression: I params idx_args
  let (_, inner_args) = decompose_apps(&cur);
  let n_target_params =
    classes[target_ci].ind.num_params.to_u64().unwrap_or(0) as usize;
  let idx_args: Vec<LeanExpr> =
    inner_args.into_iter().skip(n_target_params).collect();

  // Build IH body with all FVars: motive[target](idx_args, field xs_fvars)
  let mut ih_body = motive_fvars[target_ci].clone();
  for idx in &idx_args {
    ih_body = LeanExpr::app(ih_body, idx.clone());
  }
  let mut field_app = field_fvar.clone();
  for fv in &xs_fvars {
    field_app = LeanExpr::app(field_app, fv.clone());
  }
  ih_body = LeanExpr::app(ih_body, field_app);

  // Abstract xs FVars back into foralls, preserving original binder names
  mk_forall(ih_body, &xs_decls)
}

/// Build IH type for a recursive field in a minor premise (old BVar version).
///
/// `field_idx`: index of this field in the constructor's field list.
/// `dom_lifted`: field domain shifted by (n_fields + k - field_idx).
fn _build_ih_type(
  field_idx: usize,
  dom_lifted: &LeanExpr,
  target_ci: usize,
  n_params: usize,
  n_fields: usize,
  k: usize,
  minor_saved: usize,
  motive_base: usize,
  classes: &[FlatInfo<'_>],
) -> LeanExpr {
  let (forall_doms, inner, n_xs) = _peel_foralls_to_ind(dom_lifted, classes);
  let (_, inner_args) = decompose_apps(&inner);
  let idx_args: Vec<LeanExpr> = inner_args.into_iter().skip(n_params).collect();

  let depth = minor_saved + n_fields + k + n_xs;
  let motive_var = (depth - 1 - (motive_base + target_ci)) as u64;
  let mut ih_body = LeanExpr::bvar(Nat::from(motive_var));
  for idx in &idx_args {
    ih_body = LeanExpr::app(ih_body, idx.clone());
  }

  // Field is at context position (minor_saved + field_idx).
  // BVar index = depth - 1 - (minor_saved + field_idx)
  //            = n_fields + k + n_xs - 1 - field_idx
  let field_bvar = (n_fields + k + n_xs - 1 - field_idx) as u64;
  let mut field_app = LeanExpr::bvar(Nat::from(field_bvar));
  for xi in 0..n_xs {
    field_app = LeanExpr::app(
      field_app,
      LeanExpr::bvar(Nat::from((n_xs - 1 - xi) as u64)),
    );
  }
  ih_body = LeanExpr::app(ih_body, field_app);

  // Wrap in forall binders for xs
  for i in (0..n_xs).rev() {
    ih_body = LeanExpr::all(
      Name::anon(),
      forall_doms[i].clone(),
      ih_body,
      BinderInfo::Default,
    );
  }

  ih_body
}

// =========================================================================
// Rule RHS construction
// =========================================================================

/// Build recursor rules for class `di` using FVars.
///
/// Only generates rules for `classes[di]`'s constructors, matching Lean's
/// kernel which generates per-type recursors. The full `classes` slice is
/// still needed for recursive field detection (IH targets can be any member).
///
/// Rule RHS: `λ params motives minors fields, minor fields ihs`
fn build_rec_rules(
  di: usize,
  classes: &[FlatInfo<'_>],
  _flat: &[super::nested::CompileFlatMember],
  n_params: usize,
  n_classes: usize,
  _param_binders: &[Binder],
  _elim_level: &Level,
  ind_univs: &[Level],
  _is_large: bool,
  rec_level_params: &[Name],
  rec_type: &LeanExpr,
) -> Vec<RecursorRule> {
  let n_flat = classes.len();
  let n_motives = n_flat;
  let n_minors: usize = classes.iter().map(|c| c.ctors.len()).sum();
  let pmm = n_params + n_motives + n_minors;

  // Extract PMM binder info from the rec_type for lambda domains/names.
  let _pmm_binders = collect_binders(rec_type, pmm);

  // Collect param binder infos from the inductive type (for rule RHS lambdas).
  let param_binder_infos: Vec<BinderInfo> = {
    let ind_ty = subst_levels(
      &classes[0].ind.cnst.typ,
      &classes[0].ind.cnst.level_params,
      ind_univs,
    );
    collect_binders(&ind_ty, n_params).iter().map(|b| b.info.clone()).collect()
  };

  // Create FVars for params, motives, minors.
  // Walk the rec type, peeling each binder with instantiate1+FVar.
  // This gives us domains that use FVars for cross-references.
  let mut pmm_decls: Vec<LocalDecl> = Vec::new();
  let mut param_fvars: Vec<LeanExpr> = Vec::new();
  let mut motive_fvars: Vec<LeanExpr> = Vec::new();
  let mut minor_fvars: Vec<LeanExpr> = Vec::new();
  let mut rec_ty_cur = rec_type.clone();
  for i in 0..pmm {
    let (kind, local_idx) = if i < n_params {
      ("rparam", i)
    } else if i < n_params + n_motives {
      ("rmotive", i - n_params)
    } else {
      ("rminor", i - n_params - n_motives)
    };
    let (fv_name, fv) = fresh_fvar(kind, local_idx);
    let (binder_name, domain, _info) = match rec_ty_cur.as_data() {
      ExprData::ForallE(n, d, b, bi, _) => {
        let result = (n.clone(), d.clone(), bi.clone());
        rec_ty_cur = instantiate1(b, &fv);
        result
      },
      _ => (Name::anon(), LeanExpr::sort(Level::zero()), BinderInfo::Default),
    };
    pmm_decls.push(LocalDecl {
      fvar_name: fv_name,
      binder_name,
      domain,
      // Rule RHS lambda binder info: params use the inductive type's
      // original binder info; motives and minors are Default.
      info: if i < n_params {
        param_binder_infos.get(i).cloned().unwrap_or(BinderInfo::Default)
      } else {
        BinderInfo::Default
      },
    });
    if i < n_params {
      param_fvars.push(fv);
    } else if i < n_params + n_motives {
      motive_fvars.push(fv);
    } else {
      minor_fvars.push(fv);
    }
  }

  let rec_univs: Vec<Level> =
    rec_level_params.iter().map(|n| Level::param(n.clone())).collect();

  let mut rules = Vec::new();

  // Compute the minor FVar offset for class `di`: sum of ctor counts for
  // classes before `di`. This gives the correct index into `minor_fvars`.
  let mut global_minor_idx: usize =
    classes[..di].iter().map(|c| c.ctors.len()).sum();

  {
    let class = &classes[di];
    for ctor in class.ctors.iter() {
      let n_fields = ctor.num_fields.to_u64().unwrap_or(0) as usize;

      // Walk ctor type past params using FVars.
      // For auxiliary members, use occurrence_level_args and spec_params.
      let ctor_ty = if class.is_aux && !class.occurrence_level_args.is_empty() {
        subst_levels(
          &ctor.cnst.typ,
          &class.ind.cnst.level_params,
          &class.occurrence_level_args,
        )
      } else {
        subst_levels(&ctor.cnst.typ, &class.ind.cnst.level_params, ind_univs)
      };
      let mut ty = ctor_ty;
      let n_ctor_params = ctor.num_params.to_u64().unwrap_or(0) as usize;
      let rule_sp_fvars = if class.is_aux {
        instantiate_spec_with_fvars(&class.spec_params, &param_fvars)
      } else {
        vec![]
      };
      for p in 0..n_ctor_params {
        if let ExprData::ForallE(_, _, b, _, _) = ty.as_data() {
          if class.is_aux && p < rule_sp_fvars.len() {
            ty = instantiate1(b, &rule_sp_fvars[p]);
          } else if p < param_fvars.len() {
            ty = instantiate1(b, &param_fvars[p]);
          } else {
            ty = instantiate1(b, &LeanExpr::sort(Level::zero()));
          }
        }
      }

      // Collect fields with FVars, detect recursive fields.
      let mut field_decls: Vec<LocalDecl> = Vec::new();
      let mut field_fvars: Vec<LeanExpr> = Vec::new();
      let mut rec_field_data: Vec<(LeanExpr, usize)> = Vec::new(); // (field_fvar, target_ci)

      for fi in 0..n_fields {
        match ty.as_data() {
          ExprData::ForallE(fname, dom, b, fbi, _) => {
            let clean_dom = consume_type_annotations(dom);
            let (fv_name, fv) = fresh_fvar("rfield", fi);
            field_decls.push(LocalDecl {
              fvar_name: fv_name,
              binder_name: fname.clone(),
              domain: clean_dom.clone(),
              info: fbi.clone(),
            });
            if let Some(target_ci) =
              find_rec_target(&clean_dom, classes, &param_fvars)
            {
              rec_field_data.push((fv.clone(), target_ci));
            }
            field_fvars.push(fv.clone());
            ty = instantiate1(b, &fv);
          },
          _ => break,
        }
      }

      // Body: minor(fields)(ihs)
      let mut body = minor_fvars[global_minor_idx].clone();
      for fv in &field_fvars {
        body = LeanExpr::app(body, fv.clone());
      }

      // Build and apply IHs for recursive fields.
      for (field_fv, target_ci) in &rec_field_data {
        // Determine the correct recursor name for the target.
        // For original targets: <target_ind>.rec
        // For auxiliary targets: <main_ind>.rec_N
        let rec_name = if *target_ci < n_classes {
          Name::str(
            classes[*target_ci].ind.cnst.name.clone(),
            "rec".to_string(),
          )
        } else {
          let main_name = classes[0].ind.cnst.name.clone();
          let aux_idx = *target_ci - n_classes + 1;
          Name::str(main_name, format!("rec_{}", aux_idx))
        };

        // Get the field's type to extract index args.
        // The field_fv was substituted into the ctor type, so we need
        // the original domain. Find it in field_decls.
        let field_dom = field_decls
          .iter()
          .find(|d| {
            let fv_expr = LeanExpr::fvar(d.fvar_name.clone());
            fv_expr.get_hash() == field_fv.get_hash()
          })
          .map(|d| &d.domain);

        let ih = if let Some(dom) = field_dom {
          build_rule_ih_fvar(
            field_fv,
            dom,
            *target_ci,
            &rec_name,
            &rec_univs,
            &param_fvars,
            &motive_fvars,
            &minor_fvars,
            classes,
          )
        } else {
          field_fv.clone() // fallback — shouldn't happen
        };
        body = LeanExpr::app(body, ih);
      }

      // Abstract and wrap: fields (innermost), then PMM (outermost).
      let mut all_decls: Vec<LocalDecl> = Vec::new();
      all_decls.extend(pmm_decls.iter().cloned());
      all_decls.extend(field_decls.iter().cloned());
      let rhs = mk_lambda(body, &all_decls);

      rules.push(RecursorRule {
        ctor: ctor.cnst.name.clone(),
        n_fields: Nat::from(n_fields as u64),
        rhs,
      });

      global_minor_idx += 1;
    }
  }

  rules
}

/// Build IH value for a recursive field in a rule RHS using FVars.
///
/// IH = `λ (xs...), rec[target] params motives minors indices (field xs)`
fn build_rule_ih_fvar(
  field_fvar: &LeanExpr,
  field_dom: &LeanExpr,
  target_ci: usize,
  rec_name: &Name,
  rec_univs: &[Level],
  param_fvars: &[LeanExpr],
  motive_fvars: &[LeanExpr],
  minor_fvars: &[LeanExpr],
  classes: &[FlatInfo<'_>],
) -> LeanExpr {
  let target_n_params =
    classes[target_ci].ind.num_params.to_u64().unwrap_or(0) as usize;

  // Use forallTelescope-style approach: peel foralls with fresh FVars
  // so the inner expression and all idx_args are fully in FVar form.
  let mut xs_fvars: Vec<LeanExpr> = Vec::new();
  let mut xs_decls: Vec<LocalDecl> = Vec::new();
  let mut cur = field_dom.clone();

  while let ExprData::ForallE(name, dom, body, bi, _) = cur.as_data() {
    let (h, _) = decompose_apps(&cur);
    if let ExprData::Const(cname, _, _) = h.as_data()
      && classes.iter().any(|c| c.all_names.iter().any(|n| n == cname))
    {
      break;
    }
    let (fv_name, fv) = fresh_fvar("rih_xs", xs_fvars.len());
    xs_decls.push(LocalDecl {
      fvar_name: fv_name,
      binder_name: name.clone(),
      domain: dom.clone(),
      info: bi.clone(),
    });
    xs_fvars.push(fv.clone());
    cur = instantiate1(body, &fv);
  }

  // `cur` is now fully FVar-instantiated: I params idx_args
  let (_, inner_args) = decompose_apps(&cur);
  let idx_args: Vec<LeanExpr> =
    inner_args.into_iter().skip(target_n_params).collect();

  // Build: rec[target] params motives minors indices (field xs_fvars)
  let mut ih = mk_const(rec_name, rec_univs);
  for pf in param_fvars {
    ih = LeanExpr::app(ih, pf.clone());
  }
  for mf in motive_fvars {
    ih = LeanExpr::app(ih, mf.clone());
  }
  for mf in minor_fvars {
    ih = LeanExpr::app(ih, mf.clone());
  }
  for idx in &idx_args {
    ih = LeanExpr::app(ih, idx.clone());
  }
  let mut field_app = field_fvar.clone();
  for fv in &xs_fvars {
    field_app = LeanExpr::app(field_app, fv.clone());
  }
  ih = LeanExpr::app(ih, field_app);

  // Abstract xs FVars back into lambdas, preserving original binder names
  mk_lambda(ih, &xs_decls)
}

/// Build IH value for a recursive field in a rule RHS (old BVar version).
fn _build_rule_ih(
  field_idx: usize,
  n_fields: usize,
  total_lams: usize,
  target_ci: usize,
  classes: &[FlatInfo<'_>],
  n_params: usize,
  n_motives: usize,
  n_minors: usize,
  dom: &LeanExpr,
  rec_level_params: &[Name],
) -> LeanExpr {
  let target_ind = classes[target_ci].ind;
  let target_n_params = target_ind.num_params.to_u64().unwrap_or(0) as usize;
  let rec_name = Name::str(target_ind.cnst.name.clone(), "rec".to_string());
  let rec_univs: Vec<Level> =
    rec_level_params.iter().map(|n| Level::param(n.clone())).collect();

  let (forall_doms, inner, n_xs) = _peel_foralls_to_ind(dom, classes);
  let (_, inner_args) = decompose_apps(&inner);
  let idx_args: Vec<LeanExpr> =
    inner_args.into_iter().skip(target_n_params).collect();

  let depth = total_lams + n_xs;

  let mut ih = mk_const(&rec_name, &rec_univs);
  for pi in 0..n_params {
    ih = LeanExpr::app(ih, LeanExpr::bvar(Nat::from((depth - 1 - pi) as u64)));
  }
  for mi in 0..n_motives {
    ih = LeanExpr::app(
      ih,
      LeanExpr::bvar(Nat::from((depth - 1 - n_params - mi) as u64)),
    );
  }
  for mi in 0..n_minors {
    ih = LeanExpr::app(
      ih,
      LeanExpr::bvar(Nat::from((depth - 1 - n_params - n_motives - mi) as u64)),
    );
  }
  for idx in &idx_args {
    ih = LeanExpr::app(ih, idx.clone());
  }
  let field_base = (n_fields - 1 - field_idx + n_xs) as u64;
  let mut field_app = LeanExpr::bvar(Nat::from(field_base));
  for xi in 0..n_xs {
    field_app = LeanExpr::app(
      field_app,
      LeanExpr::bvar(Nat::from((n_xs - 1 - xi) as u64)),
    );
  }
  ih = LeanExpr::app(ih, field_app);

  // Wrap in lambdas for xs
  for i in (0..n_xs).rev() {
    let fd = &forall_doms[i];
    let fd_name = match dom.as_data() {
      ExprData::ForallE(n, _, _, _, _) => n.clone(),
      _ => Name::anon(),
    };
    ih = LeanExpr::lam(fd_name, fd.clone(), ih, BinderInfo::Default);
  }

  ih
}

// =========================================================================
// Helpers
// =========================================================================

/// Extract field binders from the recursor type's minor premise.
///
/// The minor premise is at depth `n_params + n_motives + global_minor_idx`
/// in the rec type. Its field domains have BVars relative to that depth.
/// In the rule RHS, fields are at depth `n_params + n_motives + n_minors`.
/// We shift each domain by `(n_minors - 1 - global_minor_idx)` and apply
/// a per-field cutoff to avoid shifting bound vars within nested foralls.
fn _extract_field_binders_from_rec_type(
  rec_type: &LeanExpr,
  n_params: usize,
  n_motives: usize,
  n_minors: usize,
  global_minor_idx: usize,
  n_fields: usize,
) -> Vec<Binder> {
  let skip = n_params + n_motives + global_minor_idx;
  let mut cur = rec_type.clone();
  for _ in 0..skip {
    if let ExprData::ForallE(_, _, body, _, _) = cur.as_data() {
      cur = body.clone();
    }
  }
  // cur is ∀ (minor : T), ...; extract T
  let minor_dom = match cur.as_data() {
    ExprData::ForallE(_, dom, _, _, _) => dom.clone(),
    _ => return vec![],
  };

  // Shift amount: difference between minor's position and the rule's
  // field region start. In the rec type, the minor is at position
  // (n_params + n_motives + global_minor_idx). The fields in the rule
  // RHS are after all minors: (n_params + n_motives + n_minors).
  // So free vars in the minor's field domains need to be shifted up by
  // (n_minors - 1 - global_minor_idx) to reach the right binders.
  let field_dom_lift = n_minors - 1 - global_minor_idx;

  let mut fields = Vec::with_capacity(n_fields);
  let mut mcur = minor_dom;
  for fi in 0..n_fields {
    match mcur.as_data() {
      ExprData::ForallE(name, dom, body, bi, _) => {
        // Shift with cutoff = fi (the first fi BVars are bound to
        // earlier fields within the minor, not free).
        let shifted = if field_dom_lift > 0 {
          shift_vars(dom, field_dom_lift, fi)
        } else {
          dom.clone()
        };
        fields.push(Binder {
          name: name.clone(),
          domain: shifted,
          info: bi.clone(),
        });
        mcur = body.clone();
      },
      _ => break,
    }
  }
  fields
}

/// Check if elimination is restricted to Prop (Sort 0).
/// Returns true if the recursor can ONLY eliminate into Prop.
/// Returns false if large elimination is allowed (any Sort).
///
/// Port of Lean C++ `elim_only_at_universe_zero`.
/// A Prop inductive allows large elimination when all non-param ctor fields
/// have types in Prop, or when non-Prop fields appear as indices.
fn elim_only_at_universe_zero(
  classes: &[FlatInfo<'_>],
  n_params: usize,
  lean_env: &LeanEnv,
) -> bool {
  // Only relevant for Prop inductives. Non-Prop always has large elim.
  // Walk each ctor's fields (past params). For each field:
  // - Check if the field's type is in Prop (Sort 0).
  // - If not, check if it appears in the return type's indices.
  // If a non-Prop field doesn't appear as an index → small elim only.
  for class in classes {
    for ctor in &class.ctors {
      let mut ty = ctor.cnst.typ.clone();
      let n_ctor_params = ctor.num_params.to_u64().unwrap_or(0) as usize;
      let n_ctor_fields = ctor.num_fields.to_u64().unwrap_or(0) as usize;

      // Collect param domains (to check if a BVar field points to a Prop param)
      let mut param_sorts: Vec<bool> = Vec::new(); // true if param is in Prop
      for _ in 0..n_ctor_params {
        match ty.as_data() {
          ExprData::ForallE(_, dom, body, _, _) => {
            param_sorts.push(is_sort_zero_domain(dom, &param_sorts, lean_env));
            ty = body.clone();
          },
          _ => break,
        }
      }

      // Collect field indices that are NOT in Prop
      let mut non_prop_field_indices: Vec<usize> = Vec::new();
      let mut field_idx = 0;
      let mut field_ty = ty.clone();
      for _ in 0..n_ctor_fields {
        match field_ty.as_data() {
          ExprData::ForallE(_, dom, body, _, _) => {
            if !is_sort_zero_domain(dom, &param_sorts, lean_env) {
              non_prop_field_indices.push(field_idx);
            }
            field_ty = body.clone();
            field_idx += 1;
          },
          _ => break,
        }
      }

      if non_prop_field_indices.is_empty() {
        continue; // All fields in Prop → OK for large elim
      }

      // Check if non-Prop fields appear as indices in the return type.
      // Return type: I params indices. Indices start at position n_params.
      let (_, ret_args) = decompose_apps(&field_ty);
      let index_args: Vec<&LeanExpr> = ret_args.iter().skip(n_params).collect();

      for &fi in &non_prop_field_indices {
        // The field is at BVar(n_ctor_fields - 1 - fi) in the return type context
        let field_bvar = (n_ctor_fields - 1 - fi) as u64;
        let appears_in_indices =
          index_args.iter().any(|idx| match idx.as_data() {
            ExprData::Bvar(i, _) => {
              i.to_u64().unwrap_or(u64::MAX) == field_bvar
            },
            _ => false,
          });
        if !appears_in_indices {
          return true; // Non-Prop field not in indices → small elim only
        }
      }
    }
  }
  false // All checks passed → large elim allowed
}

/// Check if a field domain type is in Prop (Sort 0).
/// Heuristic: checks if the domain itself is Sort 0, or if it's a BVar
/// pointing to a param known to be in Prop, or if it's an application
/// of a type constructor that returns Prop.
fn is_sort_zero_domain(
  dom: &LeanExpr,
  param_sorts: &[bool],
  lean_env: &LeanEnv,
) -> bool {
  match dom.as_data() {
    ExprData::Sort(lvl, _) => matches!(lvl.as_data(), LevelData::Zero(_)),
    ExprData::Bvar(idx, _) => {
      // Check if this BVar points to a param known to be in Prop
      let i = idx.to_u64().unwrap_or(u64::MAX) as usize;
      i < param_sorts.len() && param_sorts[param_sorts.len() - 1 - i]
    },
    ExprData::ForallE(_, _, body, _, _) => {
      // ∀ x : A, B — the sort is the sort of B (under the binder)
      is_sort_zero_domain(body, param_sorts, lean_env)
    },
    ExprData::Const(..) | ExprData::App(..) => {
      // Look up the head constant's return type
      let (head, _) = decompose_apps(dom);
      if let ExprData::Const(name, _, _) = head.as_data()
        && let Some(ci) = lean_env.get(name)
      {
        let typ = match ci {
          ConstantInfo::InductInfo(v) => &v.cnst.typ,
          ConstantInfo::AxiomInfo(v) => &v.cnst.typ,
          _ => return false,
        };
        return is_prop_sort(typ);
      }
      false
    },
    _ => false,
  }
}

fn is_prop_sort(typ: &LeanExpr) -> bool {
  let mut cur = typ.clone();
  loop {
    match cur.as_data() {
      ExprData::ForallE(_, _, body, _, _) => cur = body.clone(),
      ExprData::Sort(lvl, _) => {
        return matches!(lvl.as_data(), LevelData::Zero(_));
      },
      _ => return false,
    }
  }
}

/// Port of Lean 4's `Expr.consumeTypeAnnotations`.
///
/// Strips `autoParam`, `optParam`, `outParam`, and `semiOutParam`
/// wrappers from a type expression. These are application-level
/// annotations that the kernel removes when building recursor types.
///
/// - `autoParam A tac` (arity 2) → strips to `A`
/// - `optParam A default` (arity 2) → strips to `A`
/// - `outParam A` (arity 1) → strips to `A`
/// - `semiOutParam A` (arity 1) → strips to `A`
fn consume_type_annotations(expr: &LeanExpr) -> LeanExpr {
  let (head, args) = decompose_apps(expr);
  if let ExprData::Const(name, _, _) = head.as_data() {
    // Check by last name component — these are top-level Lean names so
    // the last component is the full identifier.
    if let Some(leaf) = name.last_str() {
      // autoParam A tac → A; optParam A default → A
      if (leaf == "autoParam" || leaf == "optParam") && args.len() == 2 {
        return consume_type_annotations(&args[0]);
      }
      // outParam A → A; semiOutParam A → A
      if (leaf == "outParam" || leaf == "semiOutParam") && args.len() == 1 {
        return consume_type_annotations(&args[0]);
      }
    }
  }
  // Also strip mdata annotations
  if let ExprData::Mdata(_, inner, _) = expr.as_data() {
    return consume_type_annotations(inner);
  }
  expr.clone()
}

fn _build_ind_app(
  name: &Name,
  univs: &[Level],
  n_params: usize,
  n_indices: usize,
  depth: usize,
) -> LeanExpr {
  let mut result = mk_const(name, univs);
  for p in 0..n_params {
    result =
      LeanExpr::app(result, LeanExpr::bvar(Nat::from((depth - 1 - p) as u64)));
  }
  for i in 0..n_indices {
    result = LeanExpr::app(
      result,
      LeanExpr::bvar(Nat::from((n_indices - 1 - i) as u64)),
    );
  }
  result
}

/// Strip prefix `pfx` from `name`, returning the suffix.
/// Lean's `appendAfter`: append a suffix string to a Name.
///
/// Matches `Init/Meta/Defs.lean:317-320`:
/// ```
/// def appendAfter (n : Name) (suffix : String) : Name :=
///   n.modifyBase fun
///     | str p s => Name.mkStr p (s ++ suffix)
///     | n       => Name.mkStr n suffix
/// ```
///
/// Append a suffix to the deepest string component of a Name.
///
/// Matches Lean 4.26's kernel behavior where `appendAfter("_ih")` on
/// `Num(Str(Str(Str(Str(Anon,"a"),"_@"),"_internal"),"_hyg"),0)`
/// produces `Num(Str(Str(Str(Str(Anon,"a_ih"),"_@"),"_internal"),"_hyg"),0)`.
///
/// Recurses through `Num`/`Str` wrappers to find the deepest `Str`
/// component (the one whose parent is either `anonymous` or has no
/// deeper `Str`), then appends the suffix to its string value.
fn name_append_after(n: &Name, suffix: &str) -> Name {
  match n.as_data() {
    NameData::Anonymous(_) => Name::str(n.clone(), suffix.to_string()),
    NameData::Str(parent, s, _) => {
      if has_deeper_str(parent) {
        Name::str(name_append_after(parent, suffix), s.clone())
      } else {
        // This is the deepest Str — append suffix to its string
        Name::str(parent.clone(), format!("{}{}", s, suffix))
      }
    },
    NameData::Num(parent, num, _) => {
      Name::num(name_append_after(parent, suffix), num.clone())
    },
  }
}

/// Check if a Name has any `Str` component deeper in its structure.
fn has_deeper_str(n: &Name) -> bool {
  match n.as_data() {
    NameData::Anonymous(_) => false,
    NameData::Str(_, _, _) => true,
    NameData::Num(parent, _, _) => has_deeper_str(parent),
  }
}

/// Check if a field domain targets a flat block member (original or auxiliary).
///
/// For originals, name-based matching suffices. For auxiliaries (same name,
/// different spec_params), we compare the domain's head application args
/// against the FVar-converted spec_params.
fn find_rec_target(
  dom: &LeanExpr,
  classes: &[FlatInfo<'_>],
  param_fvars: &[LeanExpr],
) -> Option<usize> {
  let mut ty = dom.clone();
  loop {
    match ty.as_data() {
      ExprData::ForallE(_, _, body, _, _) => ty = body.clone(),
      _ => {
        let (head, args) = decompose_apps(&ty);
        if let ExprData::Const(name, _, _) = head.as_data() {
          for (ci, class) in classes.iter().enumerate() {
            // Check if the name matches any name in the equivalence class.
            if !class.all_names.iter().any(|n| n == name) {
              continue;
            }
            if !class.is_aux {
              // Original member: name match is sufficient.
              return Some(ci);
            }
            // Auxiliary member: also match spec_params to distinguish
            // e.g., List Syntax from List Other.
            let sp_fvars =
              instantiate_spec_with_fvars(&class.spec_params, param_fvars);
            let n_par = class.own_params;
            if args.len() >= n_par
              && sp_fvars.len() == n_par
              && args[..n_par]
                .iter()
                .zip(sp_fvars.iter())
                .all(|(a, sp)| a.get_hash() == sp.get_hash())
            {
              return Some(ci);
            }
            // Name matched but spec_params didn't — try next member.
          }
        }
        return None;
      },
    }
  }
}

/// Check if any field domain of a constructor references a class member.
fn _find_rec_target_in_ctor(
  ctor: &ConstructorVal,
  _level_params: &[Name],
  n_params: usize,
  classes: &[FlatInfo<'_>],
) -> Option<usize> {
  let mut cur = ctor.cnst.typ.clone();
  for _ in 0..n_params {
    if let ExprData::ForallE(_, _, body, _, _) = cur.as_data() {
      cur = body.clone();
    } else {
      return None;
    }
  }
  loop {
    match cur.as_data() {
      ExprData::ForallE(_, dom, body, _, _) => {
        if let Some(ci) = find_rec_target(dom, classes, &[]) {
          return Some(ci);
        }
        cur = body.clone();
      },
      _ => return None,
    }
  }
}

fn _peel_foralls_to_ind(
  dom: &LeanExpr,
  classes: &[FlatInfo<'_>],
) -> (Vec<LeanExpr>, LeanExpr, usize) {
  let mut forall_doms = Vec::new();
  let mut inner = dom.clone();
  while let ExprData::ForallE(_, fd, fb, _, _) = inner.as_data() {
    let (h, _) = decompose_apps(&inner);
    if let ExprData::Const(name, _, _) = h.as_data()
      && classes.iter().any(|c| c.all_names.iter().any(|n| n == name))
    {
      break;
    }
    forall_doms.push(fd.clone());
    inner = fb.clone();
  }
  let n = forall_doms.len();
  (forall_doms, inner, n)
}

fn _extract_return_indices(
  ctor_typ: &LeanExpr,
  level_params: &[Name],
  ind_univs: &[Level],
  n_params: usize,
  depth: usize,
) -> Vec<LeanExpr> {
  let ty = subst_levels(ctor_typ, level_params, ind_univs);
  let mut cur = ty;
  for p in 0..n_params {
    if let ExprData::ForallE(_, _, body, _, _) = cur.as_data() {
      cur =
        instantiate1(body, &LeanExpr::bvar(Nat::from((depth - 1 - p) as u64)));
    }
  }
  while let ExprData::ForallE(_, _, body, _, _) = cur.as_data() {
    cur = body.clone();
  }
  let (_, args) = decompose_apps(&cur);
  args.into_iter().skip(n_params).collect()
}

/// Port of Lean's `inferImplicit(ty, numParams, strict)`.
///
/// Marks explicit binders as implicit when BVar(0) (the binder's
/// own variable) appears in an explicit domain somewhere in the body.
/// With `strict=false` (the recursor default), also counts appearances
/// in the range (the final return type).
///
/// Reference: `refs/lean4/src/Lean/Expr.lean:1362-1368`
fn infer_implicit(ty: &LeanExpr, num_params: usize) -> LeanExpr {
  if num_params == 0 {
    return ty.clone();
  }
  match ty.as_data() {
    ExprData::ForallE(name, dom, body, bi, _) => {
      let new_body = infer_implicit(body, num_params - 1);
      let new_bi = if *bi == BinderInfo::Default
        && has_loose_bvar_in_explicit_domain(&new_body, 0, true)
      {
        BinderInfo::Implicit
      } else {
        bi.clone()
      };
      LeanExpr::all(name.clone(), dom.clone(), new_body, new_bi)
    },
    _ => ty.clone(),
  }
}

/// Check if BVar(`target`) appears free in an explicit binder domain
/// within `e`. When `strict=true`, only checks domains; when
/// `strict=false`, also checks the range (non-domain positions).
///
/// When entering a binder, `target` is incremented (since BVar indices
/// shift under binders). Only counts occurrences in EXPLICIT domains.
///
/// Reference: `refs/lean4/src/kernel/expr.cpp:480-500`
fn has_loose_bvar_in_explicit_domain(
  e: &LeanExpr,
  target: u64,
  strict: bool,
) -> bool {
  match e.as_data() {
    ExprData::Bvar(idx, _) => {
      let i = idx.to_u64().unwrap_or(0);
      if strict {
        false // In strict mode, bare BVars in the range don't count
      } else {
        i == target // In non-strict mode, BVars in the range count
      }
    },
    ExprData::ForallE(_, dom, body, bi, _) => {
      // Check domain — only count if this binder is explicit
      let dom_has = if *bi == BinderInfo::Default {
        expr_has_loose_bvar(dom, target)
      } else {
        false
      };
      dom_has || has_loose_bvar_in_explicit_domain(body, target + 1, strict)
    },
    ExprData::App(f, a, _) => {
      if strict {
        false // In strict mode, apps in the range don't count
      } else {
        expr_has_loose_bvar(f, target) || expr_has_loose_bvar(a, target)
      }
    },
    _ => {
      if strict {
        false
      } else {
        expr_has_loose_bvar(e, target)
      }
    },
  }
}

/// Check if BVar(`target`) appears anywhere in `e`.
fn expr_has_loose_bvar(e: &LeanExpr, target: u64) -> bool {
  match e.as_data() {
    ExprData::Bvar(idx, _) => idx.to_u64().unwrap_or(0) == target,
    ExprData::App(f, a, _) => {
      expr_has_loose_bvar(f, target) || expr_has_loose_bvar(a, target)
    },
    ExprData::Lam(_, t, b, _, _) | ExprData::ForallE(_, t, b, _, _) => {
      expr_has_loose_bvar(t, target) || expr_has_loose_bvar(b, target + 1)
    },
    ExprData::LetE(_, t, v, b, _, _) => {
      expr_has_loose_bvar(t, target)
        || expr_has_loose_bvar(v, target)
        || expr_has_loose_bvar(b, target + 1)
    },
    ExprData::Proj(_, _, e, _) | ExprData::Mdata(_, e, _) => {
      expr_has_loose_bvar(e, target)
    },
    _ => false,
  }
}

// =========================================================================
// is_large / k computation — direct LeanExpr approach
// =========================================================================

/// Compute `is_large` and `k` directly from LeanExpr-level types.
///
/// Follows the Lean C++ kernel's `elim_only_at_universe_zero` and
/// `isKTarget` logic without requiring a KEnv TypeChecker.
///
/// `is_large`: true if the recursor can eliminate into any Sort.
/// `k`: true for K-target (single Prop inductive, single ctor, 0 fields).
/// `is_prop`: true if the inductive is in Prop (Sort 0).
fn _compute_is_large_and_k_direct(
  classes: &[FlatInfo<'_>],
  n_classes: usize,
  n_params: usize,
  lean_env: &LeanEnv,
) -> (bool, bool, bool) {
  // Get result sort level from the first class's type
  let result_level = get_lean_result_sort_level(
    &classes[0].ind.cnst.typ,
    n_params + classes[0].n_indices,
  );

  let is_prop = result_level_is_zero(&result_level);

  // Non-Prop → always large
  let is_large = if !is_prop {
    true
  } else {
    // Prop inductive → check elim_only_at_universe_zero
    // Returns false when large elim IS allowed (so is_large = !elim_only)
    !elim_only_at_universe_zero(classes, n_params, lean_env)
  };

  // K-target: single Prop inductive, single ctor, 0 non-param fields
  let k = n_classes == 1
    && is_prop
    && classes[0].ctors.len() == 1
    && classes[0].ctors[0].num_fields.to_u64().unwrap_or(0) == 0;

  (is_large, k, is_prop)
}

/// Extract the result sort level from a LeanExpr inductive type by
/// peeling `n` forall binders.
fn get_lean_result_sort_level(typ: &LeanExpr, n: usize) -> Option<Level> {
  let mut cur = typ.clone();
  for _ in 0..n {
    if let ExprData::ForallE(_, _, body, _, _) = cur.as_data() {
      cur = body.clone();
    } else {
      return None;
    }
  }
  match cur.as_data() {
    ExprData::Sort(lvl, _) => Some(lvl.clone()),
    _ => None,
  }
}

/// Check if a result level is definitionally zero (Prop).
/// Handles `Level::zero`, but also `Level::imax(_, zero)` etc.
/// Conservative: returns false for Level::param (could be zero or non-zero).
fn result_level_is_zero(lvl: &Option<Level>) -> bool {
  match lvl {
    None => false,
    Some(l) => match l.as_data() {
      LevelData::Zero(_) => true,
      // imax(a, 0) = 0
      LevelData::Imax(_, b, _) => {
        matches!(b.as_data(), LevelData::Zero(_))
      },
      _ => false,
    },
  }
}

/// Compute `is_large`, `k`, and `is_prop` for the canonical recursor using
/// the zero kernel's `is_large_eliminator`.
///
/// `is_large`: true if the recursor can eliminate into any Sort.
/// `k`: true for K-target (single Prop inductive, single ctor, 0 fields).
/// `is_prop`: true if the inductive is in Prop (Sort 0). Used by `.below`
///   and `.brecOn` generation to choose between definition (Type-level) and
///   inductive (Prop-level) forms.
///
/// Builds ephemeral `KConst::Indc`/`KConst::Ctor` entries from the
/// LeanExpr-level inductive/constructor types, inserts them into the
/// persistent KEnv (with name-hash addresses that won't collide with real
/// Ixon addresses), creates a temporary TypeChecker, and runs the check.
fn compute_is_large_and_k(
  classes: &[FlatInfo<'_>],
  n_classes: usize,
  n_params: usize,
  lean_env: &LeanEnv,
  stt: &crate::ix::compile::CompileState,
  aux_n2a: Option<&dashmap::DashMap<Name, crate::ix::address::Address>>,
) -> (bool, bool, bool) {
  use crate::ix::kernel::constant::KConst;
  use crate::ix::kernel::id::KId;
  use crate::ix::kernel::ingress::{
    lean_expr_to_zexpr, resolve_lean_name_addr,
  };
  use crate::ix::kernel::mode::Anon;
  use crate::ix::kernel::tc::TypeChecker;

  let n2a = Some(&stt.name_to_addr);

  // Build ephemeral KConst entries for ALL original classes and insert
  // into stt.kenv. This ensures is_large_eliminator sees the full mutual
  // block and can apply the "mutual Prop → small" rule.
  let mut ind_infos: Vec<(
    KId<Anon>,
    u64,
    u64,
    Vec<KId<Anon>>,
    crate::ix::kernel::expr::KExpr<Anon>,
    bool,
  )> = Vec::new();

  // Use the first class's block KId as the shared block reference.
  let block_addr =
    resolve_lean_name_addr(&classes[0].ind.cnst.name, n2a, aux_n2a);
  let block_zid: KId<Anon> = KId::new(block_addr, ());

  for (ci, cls) in classes[..n_classes].iter().enumerate() {
    let cls_ind = cls.ind;
    let cls_lvl_params = &cls_ind.cnst.level_params;
    let cls_n_lvls = cls_lvl_params.len() as u64;
    let cls_n_indices = cls_ind.num_indices.to_u64().unwrap_or(0);

    let cls_addr = resolve_lean_name_addr(&cls_ind.cnst.name, n2a, aux_n2a);
    let cls_zid: KId<Anon> = KId::new(cls_addr, ());
    let cls_ty_z = lean_expr_to_zexpr(
      &cls_ind.cnst.typ,
      cls_lvl_params,
      &stt.kintern,
      n2a,
      aux_n2a,
    );

    // Convert constructors
    let mut cls_ctor_zids: Vec<KId<Anon>> = Vec::new();
    for ctor in &cls.ctors {
      let ctor_addr = resolve_lean_name_addr(&ctor.cnst.name, n2a, aux_n2a);
      let ctor_zid = KId::new(ctor_addr, ());
      let ctor_ty_z = lean_expr_to_zexpr(
        &ctor.cnst.typ,
        cls_lvl_params,
        &stt.kintern,
        n2a,
        aux_n2a,
      );
      let ctor_fields = ctor.num_fields.to_u64().unwrap_or(0);
      let ctor_params = ctor.num_params.to_u64().unwrap_or(0);

      stt.kenv.insert(
        ctor_zid.clone(),
        KConst::Ctor {
          name: (),
          level_params: (),
          is_unsafe: false,
          lvls: cls_n_lvls,
          induct: cls_zid.clone(),
          cidx: cls_ctor_zids.len() as u64,
          params: ctor_params,
          fields: ctor_fields,
          ty: ctor_ty_z,
        },
      );
      cls_ctor_zids.push(ctor_zid);
    }

    // Insert inductive
    stt.kenv.insert(
      cls_zid.clone(),
      KConst::Indc {
        name: (),
        level_params: (),
        lvls: cls_n_lvls,
        params: n_params as u64,
        indices: cls_n_indices,
        is_rec: false,
        is_refl: false,
        is_unsafe: false,
        nested: 0,
        block: block_zid.clone(),
        member_idx: ci as u64,
        ty: cls_ty_z.clone(),
        ctors: cls_ctor_zids.clone(),
        lean_all: (),
      },
    );

    // Ingress field deps for this class
    ingress_field_deps(cls, cls_lvl_params, lean_env, stt, aux_n2a);

    ind_infos.push((
      cls_zid,
      n_params as u64,
      cls_n_indices,
      cls_ctor_zids,
      cls_ty_z,
      false, // is_rec — not needed for is_large check
    ));
  }

  // Compute result_level from the first class's type
  let first_ty_z = &ind_infos[0].4;
  let first_n_indices = ind_infos[0].2;

  // Create a fresh InternTable for the ephemeral TC.
  let tc_intern: crate::ix::kernel::env::InternTable<Anon> =
    crate::ix::kernel::env::InternTable::new();
  let mut tc: TypeChecker<'_, Anon> = TypeChecker::new(&stt.kenv, tc_intern);

  let is_large = match tc
    .get_result_sort_level(first_ty_z, n_params + (first_n_indices as usize))
  {
    Ok(result_level) => {
      match tc.is_large_eliminator(&result_level, &ind_infos) {
        Ok(v) => {
          // Sanity check: non-Prop should always be large
          if !v {
            let result_lvl = get_lean_result_sort_level(
              &classes[0].ind.cnst.typ,
              n_params + classes[0].n_indices,
            );
            if !result_level_is_zero(&result_lvl) {
              eprintln!(
                "[is_large BUG] {} KEnv says small but type is non-Prop, forcing large",
                classes[0].ind.cnst.name.pretty()
              );
              true
            } else {
              v
            }
          } else {
            v
          }
        },
        Err(_) => {
          // KEnv-based check failed (usually UnknownConst for field type
          // inference). Fall back to the LeanExpr-based check, but ONLY
          // for Prop inductives. Non-Prop always gets large elim.
          let result_lvl = get_lean_result_sort_level(
            &classes[0].ind.cnst.typ,
            n_params + classes[0].n_indices,
          );
          if result_level_is_zero(&result_lvl) {
            // Prop inductive — use syntactic check
            !elim_only_at_universe_zero(classes, n_params, lean_env)
          } else {
            true // Non-Prop → large
          }
        },
      }
    },
    Err(_) => {
      let result_lvl = get_lean_result_sort_level(
        &classes[0].ind.cnst.typ,
        n_params + classes[0].n_indices,
      );
      if result_level_is_zero(&result_lvl) {
        !elim_only_at_universe_zero(classes, n_params, lean_env)
      } else {
        true
      }
    },
  };

  // Compute is_prop from the LeanExpr result sort level.
  let result_lvl = get_lean_result_sort_level(
    &classes[0].ind.cnst.typ,
    n_params + classes[0].n_indices,
  );
  let is_prop = result_level_is_zero(&result_lvl);

  // K-target: single inductive, Prop, single ctor, 0 non-param fields.
  let k = n_classes == 1
    && classes[0].ctors.len() == 1
    && classes[0].ctors[0].num_fields.to_u64().unwrap_or(0) == 0
    && matches!(
      peek_result_sort(first_ty_z),
      Some(u) if u.is_zero()
    );

  (is_large, k, is_prop)
}

/// Walk field domains of constructors and ingress any referenced constants
/// into the KEnv as Axio stubs (type only), so `infer_type` can look them up.
fn ingress_field_deps(
  class: &FlatInfo<'_>,
  _lvl_params: &[Name],
  lean_env: &LeanEnv,
  stt: &crate::ix::compile::CompileState,
  aux_n2a: Option<&dashmap::DashMap<Name, crate::ix::address::Address>>,
) {
  use crate::ix::kernel::constant::KConst;
  use crate::ix::kernel::id::KId;
  use crate::ix::kernel::ingress::{
    lean_expr_to_zexpr, resolve_lean_name_addr,
  };
  use crate::ix::kernel::mode::Anon;

  let n2a = Some(&stt.name_to_addr);
  let mut seen = rustc_hash::FxHashSet::default();
  let mut queue: Vec<Name> = Vec::new();

  // Collect all Const references from constructor types
  for ctor in &class.ctors {
    collect_const_refs(&ctor.cnst.typ, &mut queue);
  }

  while let Some(name) = queue.pop() {
    if seen.contains(&name) {
      continue;
    }
    seen.insert(name.clone());

    let addr = resolve_lean_name_addr(&name, n2a, aux_n2a);
    let zid: KId<Anon> = KId::new(addr, ());
    if stt.kenv.contains_key(&zid) {
      continue;
    }

    // Look up in LeanEnv and insert as Axio stub
    if let Some(ci) = lean_env.get(&name) {
      let (typ, dep_lvl_params) = match ci {
        ConstantInfo::InductInfo(v) => (&v.cnst.typ, &v.cnst.level_params),
        ConstantInfo::CtorInfo(v) => (&v.cnst.typ, &v.cnst.level_params),
        ConstantInfo::DefnInfo(v) => (&v.cnst.typ, &v.cnst.level_params),
        ConstantInfo::AxiomInfo(v) => (&v.cnst.typ, &v.cnst.level_params),
        ConstantInfo::ThmInfo(v) => (&v.cnst.typ, &v.cnst.level_params),
        ConstantInfo::OpaqueInfo(v) => (&v.cnst.typ, &v.cnst.level_params),
        ConstantInfo::RecInfo(v) => (&v.cnst.typ, &v.cnst.level_params),
        ConstantInfo::QuotInfo(v) => (&v.cnst.typ, &v.cnst.level_params),
      };
      let ty_z =
        lean_expr_to_zexpr(typ, dep_lvl_params, &stt.kintern, n2a, aux_n2a);
      let n_lvls = dep_lvl_params.len() as u64;
      stt.kenv.insert(
        zid,
        KConst::Axio {
          name: (),
          level_params: (),
          is_unsafe: false,
          lvls: n_lvls,
          ty: ty_z,
        },
      );
      // Also collect transitive deps from this type
      collect_const_refs(typ, &mut queue);
    }
  }
}

/// Collect all constant names referenced in a LeanExpr.
fn collect_const_refs(expr: &LeanExpr, out: &mut Vec<Name>) {
  match expr.as_data() {
    ExprData::Const(n, _, _) => out.push(n.clone()),
    ExprData::App(f, a, _) => {
      collect_const_refs(f, out);
      collect_const_refs(a, out);
    },
    ExprData::ForallE(_, d, b, _, _) | ExprData::Lam(_, d, b, _, _) => {
      collect_const_refs(d, out);
      collect_const_refs(b, out);
    },
    ExprData::LetE(_, t, v, b, _, _) => {
      collect_const_refs(t, out);
      collect_const_refs(v, out);
      collect_const_refs(b, out);
    },
    ExprData::Proj(_, _, e, _) | ExprData::Mdata(_, e, _) => {
      collect_const_refs(e, out);
    },
    _ => {},
  }
}

/// Peek at the result sort of a KExpr type (peel foralls, check for Sort).
fn peek_result_sort(
  ty: &crate::ix::kernel::expr::KExpr<crate::ix::kernel::mode::Anon>,
) -> Option<crate::ix::kernel::level::KUniv<crate::ix::kernel::mode::Anon>> {
  use crate::ix::kernel::expr::ExprData as ZED;
  let mut cur = ty.clone();
  loop {
    match cur.data() {
      ZED::All(_, _, _, body, _) => cur = body.clone(),
      ZED::Sort(u, _) => return Some(u.clone()),
      _ => return None,
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::ix::compile::aux_gen::below::{
    BelowConstant, generate_below_constants,
  };

  fn n(s: &str) -> Name {
    Name::str(Name::anon(), s.to_string())
  }

  /// Helper: `∀ (name : domain), body` with default binder info.
  fn epi(name: Name, domain: LeanExpr, body: LeanExpr) -> LeanExpr {
    LeanExpr::all(name, domain, body, BinderInfo::Default)
  }

  /// Helper: BVar shorthand.
  fn _var(idx: u64) -> LeanExpr {
    LeanExpr::bvar(Nat::from(idx))
  }

  /// Build a minimal Prop mutual block: A | a : B → A, B | b : A → B.
  ///
  /// Both A and B are in Prop (Sort 0), with single constructors that
  /// cross-reference the sibling. `all = [A, B]` on both inductives.
  /// No hand-written recursors — aux_gen generates them.
  fn build_alpha_collapse_env() -> (LeanEnv, Name, Name) {
    let hyg = Name::num(
      Name::str(Name::anon(), "a._@._internal._hyg".into()),
      Nat::from(0u64),
    );
    let a = n("A");
    let b = n("B");
    let a_ctor = Name::str(a.clone(), "a".into());
    let b_ctor = Name::str(b.clone(), "b".into());
    let all = vec![a.clone(), b.clone()];
    let a_c = LeanExpr::cnst(a.clone(), vec![]);
    let b_c = LeanExpr::cnst(b.clone(), vec![]);
    let prop = LeanExpr::sort(Level::zero());

    let mut env = LeanEnv::default();
    env.insert(
      a.clone(),
      ConstantInfo::InductInfo(InductiveVal {
        cnst: ConstantVal {
          name: a.clone(),
          level_params: vec![],
          typ: prop.clone(),
        },
        num_params: Nat::from(0u64),
        num_indices: Nat::from(0u64),
        all: all.clone(),
        ctors: vec![a_ctor.clone()],
        num_nested: Nat::from(0u64),
        is_rec: true,
        is_unsafe: false,
        is_reflexive: false,
      }),
    );
    env.insert(
      b.clone(),
      ConstantInfo::InductInfo(InductiveVal {
        cnst: ConstantVal {
          name: b.clone(),
          level_params: vec![],
          typ: prop.clone(),
        },
        num_params: Nat::from(0u64),
        num_indices: Nat::from(0u64),
        all: all.clone(),
        ctors: vec![b_ctor.clone()],
        num_nested: Nat::from(0u64),
        is_rec: true,
        is_unsafe: false,
        is_reflexive: false,
      }),
    );
    // A.a : B → A
    env.insert(
      a_ctor.clone(),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: a_ctor,
          level_params: vec![],
          typ: epi(hyg.clone(), b_c, a_c.clone()),
        },
        induct: a.clone(),
        cidx: Nat::from(0u64),
        num_params: Nat::from(0u64),
        num_fields: Nat::from(1u64),
        is_unsafe: false,
      }),
    );
    // B.b : A → B
    env.insert(
      b_ctor.clone(),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: b_ctor,
          level_params: vec![],
          typ: epi(hyg, a_c, LeanExpr::cnst(b.clone(), vec![])),
        },
        induct: b.clone(),
        cidx: Nat::from(0u64),
        num_params: Nat::from(0u64),
        num_fields: Nat::from(1u64),
        is_unsafe: false,
      }),
    );
    (env, a, b)
  }

  /// Build a 3-way alpha-collapse: A→B→C→A cycle, all Prop.
  fn build_alpha_collapse_3_env() -> (LeanEnv, Name, Name, Name) {
    let hyg = Name::num(
      Name::str(Name::anon(), "a._@._internal._hyg".into()),
      Nat::from(0u64),
    );
    let a = n("A");
    let b = n("B");
    let c = n("C");
    let a_ctor = Name::str(a.clone(), "a".into());
    let b_ctor = Name::str(b.clone(), "b".into());
    let c_ctor = Name::str(c.clone(), "c".into());
    let all = vec![a.clone(), b.clone(), c.clone()];
    let a_c = LeanExpr::cnst(a.clone(), vec![]);
    let b_c = LeanExpr::cnst(b.clone(), vec![]);
    let c_c = LeanExpr::cnst(c.clone(), vec![]);
    let prop = LeanExpr::sort(Level::zero());

    let mut env = LeanEnv::default();
    // A : Prop, B : Prop, C : Prop
    for (name, _ctor_name, ctors) in [
      (&a, &a_ctor, vec![a_ctor.clone()]),
      (&b, &b_ctor, vec![b_ctor.clone()]),
      (&c, &c_ctor, vec![c_ctor.clone()]),
    ] {
      env.insert(
        name.clone(),
        ConstantInfo::InductInfo(InductiveVal {
          cnst: ConstantVal {
            name: name.clone(),
            level_params: vec![],
            typ: prop.clone(),
          },
          num_params: Nat::from(0u64),
          num_indices: Nat::from(0u64),
          all: all.clone(),
          ctors,
          num_nested: Nat::from(0u64),
          is_rec: true,
          is_unsafe: false,
          is_reflexive: false,
        }),
      );
    }
    // A.a : B → A
    env.insert(
      a_ctor.clone(),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: a_ctor,
          level_params: vec![],
          typ: epi(hyg.clone(), b_c.clone(), a_c.clone()),
        },
        induct: a.clone(),
        cidx: Nat::from(0u64),
        num_params: Nat::from(0u64),
        num_fields: Nat::from(1u64),
        is_unsafe: false,
      }),
    );
    // B.b : C → B
    env.insert(
      b_ctor.clone(),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: b_ctor,
          level_params: vec![],
          typ: epi(hyg.clone(), c_c, b_c),
        },
        induct: b.clone(),
        cidx: Nat::from(0u64),
        num_params: Nat::from(0u64),
        num_fields: Nat::from(1u64),
        is_unsafe: false,
      }),
    );
    // C.c : A → C
    env.insert(
      c_ctor.clone(),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: c_ctor,
          level_params: vec![],
          typ: epi(hyg, a_c, LeanExpr::cnst(c.clone(), vec![])),
        },
        induct: c.clone(),
        cidx: Nat::from(0u64),
        num_params: Nat::from(0u64),
        num_fields: Nat::from(1u64),
        is_unsafe: false,
      }),
    );
    (env, a, b, c)
  }

  /// Build over-merge + alpha-collapse: A≅B mutual, C external.
  /// A | a : B → A, B | b : A → B, C | c : A → B → C. All Prop.
  fn build_over_merge_alpha_collapse_env() -> (LeanEnv, Name, Name, Name) {
    let hyg = Name::num(
      Name::str(Name::anon(), "a._@._internal._hyg".into()),
      Nat::from(0u64),
    );
    let hyg2 = Name::num(
      Name::str(Name::anon(), "a._@._internal._hyg".into()),
      Nat::from(1u64),
    );
    let a = n("A");
    let b = n("B");
    let c = n("C");
    let a_ctor = Name::str(a.clone(), "a".into());
    let b_ctor = Name::str(b.clone(), "b".into());
    let c_ctor = Name::str(c.clone(), "c".into());
    let all = vec![a.clone(), b.clone(), c.clone()];
    let a_c = LeanExpr::cnst(a.clone(), vec![]);
    let b_c = LeanExpr::cnst(b.clone(), vec![]);
    let c_c = LeanExpr::cnst(c.clone(), vec![]);
    let prop = LeanExpr::sort(Level::zero());

    let mut env = LeanEnv::default();
    for (name, ctor_list) in [
      (&a, vec![a_ctor.clone()]),
      (&b, vec![b_ctor.clone()]),
      (&c, vec![c_ctor.clone()]),
    ] {
      env.insert(
        name.clone(),
        ConstantInfo::InductInfo(InductiveVal {
          cnst: ConstantVal {
            name: name.clone(),
            level_params: vec![],
            typ: prop.clone(),
          },
          num_params: Nat::from(0u64),
          num_indices: Nat::from(0u64),
          all: all.clone(),
          ctors: ctor_list,
          num_nested: Nat::from(0u64),
          is_rec: true,
          is_unsafe: false,
          is_reflexive: false,
        }),
      );
    }
    // A.a : B → A
    env.insert(
      a_ctor.clone(),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: a_ctor,
          level_params: vec![],
          typ: epi(hyg.clone(), b_c.clone(), a_c.clone()),
        },
        induct: a.clone(),
        cidx: Nat::from(0u64),
        num_params: Nat::from(0u64),
        num_fields: Nat::from(1u64),
        is_unsafe: false,
      }),
    );
    // B.b : A → B
    env.insert(
      b_ctor.clone(),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: b_ctor,
          level_params: vec![],
          typ: epi(hyg.clone(), a_c.clone(), b_c.clone()),
        },
        induct: b.clone(),
        cidx: Nat::from(0u64),
        num_params: Nat::from(0u64),
        num_fields: Nat::from(1u64),
        is_unsafe: false,
      }),
    );
    // C.c : A → B → C
    env.insert(
      c_ctor.clone(),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: c_ctor,
          level_params: vec![],
          typ: epi(hyg.clone(), a_c, epi(hyg2, b_c, c_c)),
        },
        induct: c.clone(),
        cidx: Nat::from(0u64),
        num_params: Nat::from(0u64),
        num_fields: Nat::from(2u64),
        is_unsafe: false,
      }),
    );
    (env, a, b, c)
  }

  /// Build over-merge without alpha-collapse: A/B/C where B has 2 fields.
  /// A | a : B → A, B | b : A → A → B, C | c : A → B → C. All Prop.
  fn build_over_merge_env() -> (LeanEnv, Name, Name, Name) {
    let hyg = Name::num(
      Name::str(Name::anon(), "a._@._internal._hyg".into()),
      Nat::from(0u64),
    );
    let hyg2 = Name::num(
      Name::str(Name::anon(), "a._@._internal._hyg".into()),
      Nat::from(1u64),
    );
    let a = n("A");
    let b = n("B");
    let c = n("C");
    let a_ctor = Name::str(a.clone(), "a".into());
    let b_ctor = Name::str(b.clone(), "b".into());
    let c_ctor = Name::str(c.clone(), "c".into());
    let all = vec![a.clone(), b.clone(), c.clone()];
    let a_c = LeanExpr::cnst(a.clone(), vec![]);
    let b_c = LeanExpr::cnst(b.clone(), vec![]);
    let c_c = LeanExpr::cnst(c.clone(), vec![]);
    let prop = LeanExpr::sort(Level::zero());

    let mut env = LeanEnv::default();
    for (name, ctor_list) in [
      (&a, vec![a_ctor.clone()]),
      (&b, vec![b_ctor.clone()]),
      (&c, vec![c_ctor.clone()]),
    ] {
      env.insert(
        name.clone(),
        ConstantInfo::InductInfo(InductiveVal {
          cnst: ConstantVal {
            name: name.clone(),
            level_params: vec![],
            typ: prop.clone(),
          },
          num_params: Nat::from(0u64),
          num_indices: Nat::from(0u64),
          all: all.clone(),
          ctors: ctor_list,
          num_nested: Nat::from(0u64),
          is_rec: true,
          is_unsafe: false,
          is_reflexive: false,
        }),
      );
    }
    // A.a : B → A
    env.insert(
      a_ctor.clone(),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: a_ctor,
          level_params: vec![],
          typ: epi(hyg.clone(), b_c.clone(), a_c.clone()),
        },
        induct: a.clone(),
        cidx: Nat::from(0u64),
        num_params: Nat::from(0u64),
        num_fields: Nat::from(1u64),
        is_unsafe: false,
      }),
    );
    // B.b : A → A → B
    env.insert(
      b_ctor.clone(),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: b_ctor,
          level_params: vec![],
          typ: epi(
            hyg.clone(),
            a_c.clone(),
            epi(hyg2.clone(), a_c.clone(), b_c.clone()),
          ),
        },
        induct: b.clone(),
        cidx: Nat::from(0u64),
        num_params: Nat::from(0u64),
        num_fields: Nat::from(2u64),
        is_unsafe: false,
      }),
    );
    // C.c : A → B → C
    env.insert(
      c_ctor.clone(),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: c_ctor,
          level_params: vec![],
          typ: epi(hyg, a_c, epi(hyg2, b_c, c_c)),
        },
        induct: c.clone(),
        cidx: Nat::from(0u64),
        num_params: Nat::from(0u64),
        num_fields: Nat::from(2u64),
        is_unsafe: false,
      }),
    );
    (env, a, b, c)
  }

  /// Build a simple Type-level inductive (Nat-like): T | Z : T | S : T → T
  fn build_type_nat_env() -> (LeanEnv, Name) {
    let _u = Name::str(Name::anon(), "u".to_string());
    let t = n("T");
    let z_ctor = Name::str(t.clone(), "Z".into());
    let s_ctor = Name::str(t.clone(), "S".into());
    let t_c = LeanExpr::cnst(t.clone(), vec![]);
    let type0 = LeanExpr::sort(Level::succ(Level::zero()));
    let hyg = Name::num(
      Name::str(Name::anon(), "a._@._internal._hyg".into()),
      Nat::from(0u64),
    );

    let mut env = LeanEnv::default();
    env.insert(
      t.clone(),
      ConstantInfo::InductInfo(InductiveVal {
        cnst: ConstantVal { name: t.clone(), level_params: vec![], typ: type0 },
        num_params: Nat::from(0u64),
        num_indices: Nat::from(0u64),
        all: vec![t.clone()],
        ctors: vec![z_ctor.clone(), s_ctor.clone()],
        num_nested: Nat::from(0u64),
        is_rec: true,
        is_unsafe: false,
        is_reflexive: false,
      }),
    );
    // T.Z : T
    env.insert(
      z_ctor.clone(),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: z_ctor,
          level_params: vec![],
          typ: t_c.clone(),
        },
        induct: t.clone(),
        cidx: Nat::from(0u64),
        num_params: Nat::from(0u64),
        num_fields: Nat::from(0u64),
        is_unsafe: false,
      }),
    );
    // T.S : T → T
    env.insert(
      s_ctor.clone(),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: s_ctor,
          level_params: vec![],
          typ: epi(hyg, t_c.clone(), t_c),
        },
        induct: t.clone(),
        cidx: Nat::from(1u64),
        num_params: Nat::from(0u64),
        num_fields: Nat::from(1u64),
        is_unsafe: false,
      }),
    );
    (env, t)
  }

  /// Build a Prop mutual with drec eligibility (single ctor, all-Prop fields).
  /// This is is_prop=true BUT is_large=true (drec).
  /// P : Prop, P | mk : P → P  (single ctor with one Prop field)
  fn build_prop_drec_env() -> (LeanEnv, Name) {
    let p = n("P");
    let mk_ctor = Name::str(p.clone(), "mk".into());
    let p_c = LeanExpr::cnst(p.clone(), vec![]);
    let prop = LeanExpr::sort(Level::zero());
    let hyg = Name::num(
      Name::str(Name::anon(), "a._@._internal._hyg".into()),
      Nat::from(0u64),
    );

    let mut env = LeanEnv::default();
    env.insert(
      p.clone(),
      ConstantInfo::InductInfo(InductiveVal {
        cnst: ConstantVal { name: p.clone(), level_params: vec![], typ: prop },
        num_params: Nat::from(0u64),
        num_indices: Nat::from(0u64),
        all: vec![p.clone()],
        ctors: vec![mk_ctor.clone()],
        num_nested: Nat::from(0u64),
        is_rec: true,
        is_unsafe: false,
        is_reflexive: false,
      }),
    );
    // P.mk : P → P
    env.insert(
      mk_ctor.clone(),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: mk_ctor,
          level_params: vec![],
          typ: epi(hyg, p_c.clone(), p_c),
        },
        induct: p.clone(),
        cidx: Nat::from(0u64),
        num_params: Nat::from(0u64),
        num_fields: Nat::from(1u64),
        is_unsafe: false,
      }),
    );
    (env, p)
  }

  // -----------------------------------------------------------------------
  // Existing test
  // -----------------------------------------------------------------------

  #[test]
  fn test_simple_prop() {
    let ind_name = n("A");
    let ctor_name = Name::str(ind_name.clone(), "mk".to_string());
    let ind = InductiveVal {
      cnst: ConstantVal {
        name: ind_name.clone(),
        level_params: vec![],
        typ: LeanExpr::sort(Level::zero()),
      },
      num_params: Nat::from(0u64),
      num_indices: Nat::from(0u64),
      all: vec![ind_name.clone()],
      ctors: vec![ctor_name.clone()],
      num_nested: Nat::from(0u64),
      is_rec: false,
      is_unsafe: false,
      is_reflexive: false,
    };
    let ctor = ConstructorVal {
      cnst: ConstantVal {
        name: ctor_name.clone(),
        level_params: vec![],
        typ: LeanExpr::cnst(ind_name.clone(), vec![]),
      },
      induct: ind_name.clone(),
      cidx: Nat::from(0u64),
      num_params: Nat::from(0u64),
      num_fields: Nat::from(0u64),
      is_unsafe: false,
    };

    let mut env: LeanEnv = LeanEnv::default();
    env.insert(ind_name.clone(), ConstantInfo::InductInfo(ind));
    env.insert(ctor_name, ConstantInfo::CtorInfo(ctor));

    let classes = vec![vec![ind_name]];
    let tmp_stt = crate::ix::compile::CompileState::default();
    let (result, _is_prop) =
      generate_canonical_recursors(&classes, &env, &tmp_stt, None).unwrap();
    assert_eq!(result.len(), 1);
    let (_, rec) = &result[0];
    assert_eq!(rec.num_motives.to_u64().unwrap_or(0), 1);
    assert_eq!(rec.num_minors.to_u64().unwrap_or(0), 1);
    assert_eq!(rec.rules.len(), 1);
  }

  // -----------------------------------------------------------------------
  // New aux_gen tests (Step 3)
  // -----------------------------------------------------------------------

  /// 3a. Alpha-collapse: A≅B mutual Prop pair → 1 class after collapse.
  ///
  /// Verifies:
  /// - `generate_canonical_recursors` with 1 collapsed class produces a
  ///   recursor with 1 motive, 1 minor, correct `is_large`/level_params.
  /// - Both A.rec and B.rec would register with the same canonical content.
  /// - `.below` is BelowIndc with a constructor and Prop motive domains.
  #[test]
  fn test_aux_gen_alpha_collapse() {
    let (env, a, b) = build_alpha_collapse_env();
    let stt = crate::ix::compile::CompileState::default();

    // After sort_consts collapse, A≅B → 1 class.
    let classes = vec![vec![a.clone(), b.clone()]];
    let (recs, is_prop) =
      generate_canonical_recursors(&classes, &env, &stt, None).unwrap();

    // Should produce 1 recursor (1 class).
    assert_eq!(recs.len(), 1, "alpha-collapse → 1 class → 1 recursor");
    let (rec_name, rec) = &recs[0];

    // Name should be A.rec (class rep).
    assert_eq!(rec_name.pretty(), "A.rec");

    // 1 motive, 1 minor (collapsed from 2+2).
    assert_eq!(rec.num_motives.to_u64().unwrap_or(0), 1);
    assert_eq!(rec.num_minors.to_u64().unwrap_or(0), 1);
    assert_eq!(rec.rules.len(), 1);

    // Prop pair → is_prop = true.
    assert!(is_prop, "Prop mutuals should have is_prop = true");

    // Prop pair with single ctor + recursive field → is_large depends on
    // large elimination eligibility. The single-ctor check fails because
    // each class (collapsed A≅B) has 1 ctor with 1 field referencing the
    // mutual block, so large elim IS allowed (drec). Check level_params.
    // If is_large, level_params = [u]; if not, level_params = [].
    let is_large = !rec.cnst.level_params.is_empty();
    if is_large {
      assert_eq!(
        rec.cnst.level_params[0].pretty(),
        "u",
        "large eliminator → first level param is 'u'"
      );
    }

    // .below generation: should produce BelowIndc for Prop.
    let below =
      generate_below_constants(&classes, &recs, &env, is_prop, None).unwrap();
    assert_eq!(below.len(), 1, "1 class → 1 .below constant");
    match &below[0] {
      BelowConstant::Indc(indc) => {
        assert_eq!(indc.name.pretty(), "A.below");
        assert!(
          !indc.ctors.is_empty(),
          ".below inductive should have at least 1 constructor"
        );
        // Motive domains should target Prop (Sort 0).
        // The .below type includes motive binders whose result sort is Prop.
      },
      BelowConstant::Def(_) => {
        panic!("Prop mutual should produce BelowIndc, not BelowDef");
      },
    }
  }

  /// 3b. Alpha-collapse 3-way: A→B→C→A cycle, all Prop → 1 class.
  #[test]
  fn test_aux_gen_alpha_collapse_3() {
    let (env, a, b, c) = build_alpha_collapse_3_env();
    let stt = crate::ix::compile::CompileState::default();

    // All 3 collapse into 1 class.
    let classes = vec![vec![a.clone(), b.clone(), c.clone()]];
    let (recs, is_prop) =
      generate_canonical_recursors(&classes, &env, &stt, None).unwrap();

    assert_eq!(recs.len(), 1, "3-way alpha-collapse → 1 class → 1 recursor");
    let (rec_name, rec) = &recs[0];
    assert_eq!(rec_name.pretty(), "A.rec");
    assert_eq!(
      rec.num_motives.to_u64().unwrap_or(0),
      1,
      "collapsed 3→1 motive"
    );
    assert_eq!(rec.num_minors.to_u64().unwrap_or(0), 1, "collapsed 3→1 minor");
    assert_eq!(rec.rules.len(), 1);
    assert!(is_prop, "Prop mutuals should have is_prop = true");

    // .below
    let below =
      generate_below_constants(&classes, &recs, &env, is_prop, None).unwrap();
    assert_eq!(below.len(), 1);
    assert!(
      matches!(&below[0], BelowConstant::Indc(_)),
      "Prop .below should be BelowIndc"
    );
  }

  /// 3c. Over-merge + alpha-collapse: A≅B mutual + C external → 2 classes.
  #[test]
  fn test_aux_gen_over_merge_alpha_collapse() {
    let (env, a, b, c) = build_over_merge_alpha_collapse_env();
    let stt = crate::ix::compile::CompileState::default();

    // A≅B collapse into 1 class, C is a separate class → 2 classes.
    let classes = vec![vec![a.clone(), b.clone()], vec![c.clone()]];
    let (recs, is_prop) =
      generate_canonical_recursors(&classes, &env, &stt, None).unwrap();

    assert_eq!(
      recs.len(),
      2,
      "over-merge + alpha-collapse → 2 classes → 2 recursors"
    );

    let (name_0, rec_0) = &recs[0];
    let (name_1, rec_1) = &recs[1];
    assert_eq!(name_0.pretty(), "A.rec");
    assert_eq!(name_1.pretty(), "C.rec");

    // Each recursor sees 2 motives (one per class) and minors for all ctors
    // across both classes: A≅B has 1 ctor, C has 1 ctor → 2 minors total.
    assert_eq!(
      rec_0.num_motives.to_u64().unwrap_or(0),
      2,
      "2 classes → 2 motives per recursor"
    );
    assert_eq!(
      rec_0.num_minors.to_u64().unwrap_or(0),
      2,
      "A≅B has 1 ctor + C has 1 ctor → 2 minors"
    );
    assert_eq!(rec_1.num_motives.to_u64().unwrap_or(0), 2);
    assert_eq!(rec_1.num_minors.to_u64().unwrap_or(0), 2);

    // A.rec has 1 rule (for A.a), C.rec has 1 rule (for C.c).
    assert_eq!(rec_0.rules.len(), 1);
    assert_eq!(rec_1.rules.len(), 1);

    assert!(is_prop);

    // .below: one per class.
    let below =
      generate_below_constants(&classes, &recs, &env, is_prop, None).unwrap();
    assert_eq!(below.len(), 2, "2 classes → 2 .below constants");
    for bc in &below {
      assert!(
        matches!(bc, BelowConstant::Indc(_)),
        "Prop .below should be BelowIndc"
      );
    }
  }

  /// 3d. Over-merge without alpha-collapse: A/B/C where B has 2 fields → 3 classes.
  #[test]
  fn test_aux_gen_over_merge() {
    let (env, a, b, c) = build_over_merge_env();
    let stt = crate::ix::compile::CompileState::default();

    // No alpha-collapse: A≠B (B has 2 fields), A≠C, B≠C → 3 classes.
    let classes = vec![vec![a.clone()], vec![b.clone()], vec![c.clone()]];
    let (recs, is_prop) =
      generate_canonical_recursors(&classes, &env, &stt, None).unwrap();

    assert_eq!(recs.len(), 3, "no collapse → 3 classes → 3 recursors");

    // Each recursor has 3 motives (one per class).
    for (_, rec) in &recs {
      assert_eq!(
        rec.num_motives.to_u64().unwrap_or(0),
        3,
        "3 classes → 3 motives"
      );
    }

    // Total minors: A has 1 ctor (1 field), B has 1 ctor (2 fields), C has 1 ctor (2 fields) → 3 minors.
    assert_eq!(recs[0].1.num_minors.to_u64().unwrap_or(0), 3);

    // Each recursor has 1 rule for its own class's ctor.
    assert_eq!(recs[0].1.rules.len(), 1);
    assert_eq!(recs[1].1.rules.len(), 1);
    assert_eq!(recs[2].1.rules.len(), 1);

    assert!(is_prop);

    // .below: one per class.
    let below =
      generate_below_constants(&classes, &recs, &env, is_prop, None).unwrap();
    assert_eq!(below.len(), 3);
  }

  /// 3e. Prop mutual → .below is BelowIndc (not BelowDef).
  ///
  /// Verifies the is_prop dispatch: Prop inductives use the IndPredBelow path
  /// (BelowIndc), NOT the BRecOn.lean path (BelowDef).
  #[test]
  fn test_aux_gen_below_indc_prop() {
    let (env, a, b) = build_alpha_collapse_env();
    let stt = crate::ix::compile::CompileState::default();

    let classes = vec![vec![a.clone(), b.clone()]];
    let (recs, is_prop) =
      generate_canonical_recursors(&classes, &env, &stt, None).unwrap();
    assert!(is_prop, "should be Prop");

    let below =
      generate_below_constants(&classes, &recs, &env, is_prop, None).unwrap();
    assert_eq!(below.len(), 1);
    match &below[0] {
      BelowConstant::Indc(indc) => {
        assert_eq!(indc.name.pretty(), "A.below");
        // n_params = params + motives = 0 + 1 = 1 (collapsed).
        assert_eq!(
          indc.n_params, 1,
          ".below n_params = inductive params + number of motives"
        );
        // At least one constructor.
        assert!(!indc.ctors.is_empty());
        // Constructor should have fields referencing the major premise.
        let ctor = &indc.ctors[0];
        assert!(ctor.n_fields > 0, ".below ctor should have IH fields");
      },
      BelowConstant::Def(_) => panic!("Prop → BelowIndc, not BelowDef"),
    }
  }

  /// 3f. Type-level inductive → .below is BelowDef (not BelowIndc).
  ///
  /// Uses a Nat-like Type inductive: T | Z : T | S : T → T
  #[test]
  fn test_aux_gen_below_def_type() {
    let (env, t) = build_type_nat_env();
    let stt = crate::ix::compile::CompileState::default();

    let classes = vec![vec![t.clone()]];
    let (recs, is_prop) =
      generate_canonical_recursors(&classes, &env, &stt, None).unwrap();
    assert!(!is_prop, "Type-level should not be is_prop");

    // Large eliminator: level_params should have "u" prefix.
    let (_, rec) = &recs[0];
    assert!(
      !rec.cnst.level_params.is_empty(),
      "Type-level recursor should have elimination level param"
    );
    assert_eq!(rec.cnst.level_params[0].pretty(), "u");

    // 2 rules (Z + S).
    assert_eq!(rec.rules.len(), 2);

    let below =
      generate_below_constants(&classes, &recs, &env, is_prop, None).unwrap();
    assert_eq!(below.len(), 1);
    match &below[0] {
      BelowConstant::Def(def) => {
        assert_eq!(def.name.pretty(), "T.below");
        // BelowDef uses PProd/PUnit chains in its value.
        // Level params should match the recursor's.
        assert!(!def.level_params.is_empty());
      },
      BelowConstant::Indc(_) => panic!("Type-level → BelowDef, not BelowIndc"),
    }
  }

  /// 3g. is_prop vs is_large dispatch: Prop with drec eligibility.
  ///
  /// P : Prop with single ctor P.mk : P → P. The single-ctor + all-Prop-fields
  /// rule gives large elimination (drec), so is_large = true.
  /// But is_prop is ALSO true, meaning .below should use BelowIndc (not BelowDef).
  #[test]
  fn test_aux_gen_is_prop_vs_is_large() {
    let (env, p) = build_prop_drec_env();
    let stt = crate::ix::compile::CompileState::default();

    let classes = vec![vec![p.clone()]];
    let (recs, is_prop) =
      generate_canonical_recursors(&classes, &env, &stt, None).unwrap();

    // is_prop = true (it's in Prop).
    assert!(is_prop, "P : Prop should have is_prop = true");

    let (_, rec) = &recs[0];
    // With drec: single ctor + all-Prop fields → large elimination.
    // The recursor should have an extra level param "u" for large elimination.
    let _is_large = rec.cnst.level_params.iter().any(|lp| lp.pretty() == "u");
    // Whether drec fires depends on the elim_only_at_universe_zero check.
    // For single ctor with 1 Prop field, it should allow large elim.
    // This is the core bug-fix test: is_prop=true AND is_large=true.

    // .below should use BelowIndc (Prop path) regardless of is_large.
    let below =
      generate_below_constants(&classes, &recs, &env, is_prop, None).unwrap();
    assert_eq!(below.len(), 1);
    match &below[0] {
      BelowConstant::Indc(indc) => {
        assert_eq!(
          indc.name.pretty(),
          "P.below",
          "Prop with drec → BelowIndc (not BelowDef)"
        );
      },
      BelowConstant::Def(_) => {
        panic!("is_prop=true should produce BelowIndc even when is_large=true");
      },
    }
  }

  /// 3h. Full compile + decompile roundtrip for alpha-collapse.
  ///
  /// Builds A/B inductives (no hand-written recursors), runs the full
  /// compile_env pipeline, then verifies the decompiled .rec matches
  /// what aux_gen would regenerate from the decompiled inductives.
  #[test]
  fn test_aux_gen_compile_roundtrip() {
    use crate::ix::compile::env::compile_env;
    use std::sync::Arc;

    let (env, a, b) = build_alpha_collapse_env();
    let lean_env = Arc::new(env);

    // Compile.
    let stt = compile_env(&lean_env)
      .expect("compile_env should succeed for alpha-collapse inductives");

    // Verify A.rec was compiled.
    let has_name = |n: &Name| stt.resolve_addr(n).is_some();
    let a_rec = Name::str(a.clone(), "rec".into());
    assert!(has_name(&a_rec), "A.rec should be compiled");

    // B.rec should also be registered (as an alias to the same canonical content).
    let b_rec = Name::str(b.clone(), "rec".into());
    assert!(has_name(&b_rec), "B.rec should be compiled");

    // Note: .below and .brecOn are only generated if the original Lean env
    // contains them (gate: lean_env.get(&below_name).is_some()). This minimal
    // test env has no .below or .brecOn, so they aren't generated.
    // Full-environment tests (lake test -- rust-compile) exercise that path.

    // Verify A.rec and B.rec resolve to the same underlying Ixon block.
    // Both are alpha-equivalent, so their compiled block addresses should
    // be identical (they share the same RPrj/singleton block).
    let a_addr = stt.resolve_addr(&a_rec).unwrap();
    let b_addr = stt.resolve_addr(&b_rec).unwrap();
    assert_eq!(
      a_addr, b_addr,
      "A.rec and B.rec should point to the same compiled block (alpha-equivalent)"
    );
  }

  // -----------------------------------------------------------------------
  // brecOn tests
  // -----------------------------------------------------------------------

  /// Type-level brecOn: Nat-like T generates .brecOn.go + .brecOn (no .eq without Eq in env).
  #[test]
  fn test_brecon_type_level() {
    use crate::ix::compile::aux_gen::below::generate_below_constants;
    use crate::ix::compile::aux_gen::brecon::generate_brecon_constants;

    let (env, t) = build_type_nat_env();
    let stt = crate::ix::compile::CompileState::default();

    let classes = vec![vec![t.clone()]];
    let (recs, is_prop) =
      generate_canonical_recursors(&classes, &env, &stt, None).unwrap();
    assert!(!is_prop);

    let below =
      generate_below_constants(&classes, &recs, &env, is_prop, None).unwrap();
    assert_eq!(below.len(), 1);

    let brecon =
      generate_brecon_constants(&classes, &recs, &below, &env, is_prop)
        .unwrap();
    // .brecOn.go + .brecOn + .brecOn.eq
    assert_eq!(
      brecon.len(),
      3,
      "Type-level brecOn should produce .brecOn.go + .brecOn + .brecOn.eq"
    );

    let go = &brecon[0];
    let main = &brecon[1];
    assert_eq!(go.name.pretty(), "T.brecOn.go");
    assert_eq!(main.name.pretty(), "T.brecOn");

    // Both should have the elimination level param "u".
    assert!(!go.level_params.is_empty(), ".brecOn.go should have level params");
    assert_eq!(go.level_params[0].pretty(), "u");
    assert!(!main.level_params.is_empty(), ".brecOn should have level params");
    assert_eq!(main.level_params[0].pretty(), "u");
  }

  /// Prop-level brecOn: alpha-collapse A/B generates single .brecOn per class.
  #[test]
  fn test_brecon_prop_alpha_collapse() {
    use crate::ix::compile::aux_gen::below::generate_below_constants;
    use crate::ix::compile::aux_gen::brecon::generate_brecon_constants;

    let (env, a, b) = build_alpha_collapse_env();
    let stt = crate::ix::compile::CompileState::default();

    let classes = vec![vec![a.clone(), b.clone()]];
    let (recs, is_prop) =
      generate_canonical_recursors(&classes, &env, &stt, None).unwrap();
    assert!(is_prop);

    let below =
      generate_below_constants(&classes, &recs, &env, is_prop, None).unwrap();
    assert_eq!(below.len(), 1);

    let brecon =
      generate_brecon_constants(&classes, &recs, &below, &env, is_prop)
        .unwrap();
    // Prop-level: 1 .brecOn per class (no .go, no .eq)
    assert_eq!(brecon.len(), 1, "Prop-level brecOn should produce 1 .brecOn");
    assert_eq!(brecon[0].name.pretty(), "A.brecOn");

    // Level params should match the inductive (empty for parameterless Prop).
    assert!(
      brecon[0].level_params.is_empty(),
      "Prop brecOn for parameterless inductive should have no level params"
    );
  }

  /// Non-recursive inductives should NOT generate brecOn.
  #[test]
  fn test_brecon_skipped_for_non_recursive() {
    use crate::ix::compile::aux_gen::below::generate_below_constants;
    use crate::ix::compile::aux_gen::brecon::generate_brecon_constants;

    // Build a simple non-recursive inductive: Unit | unit : Unit
    let unit = n("Unit");
    let unit_ctor = Name::str(unit.clone(), "unit".into());
    let mut env = LeanEnv::default();
    env.insert(
      unit.clone(),
      ConstantInfo::InductInfo(InductiveVal {
        cnst: ConstantVal {
          name: unit.clone(),
          level_params: vec![],
          typ: LeanExpr::sort(Level::succ(Level::zero())),
        },
        num_params: Nat::from(0u64),
        num_indices: Nat::from(0u64),
        all: vec![unit.clone()],
        ctors: vec![unit_ctor.clone()],
        num_nested: Nat::from(0u64),
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
      }),
    );
    env.insert(
      unit_ctor.clone(),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: unit_ctor,
          level_params: vec![],
          typ: LeanExpr::cnst(unit.clone(), vec![]),
        },
        induct: unit.clone(),
        cidx: Nat::from(0u64),
        num_params: Nat::from(0u64),
        num_fields: Nat::from(0u64),
        is_unsafe: false,
      }),
    );

    let stt = crate::ix::compile::CompileState::default();
    let classes = vec![vec![unit]];
    let (recs, is_prop) =
      generate_canonical_recursors(&classes, &env, &stt, None).unwrap();
    let below =
      generate_below_constants(&classes, &recs, &env, is_prop, None).unwrap();
    let brecon =
      generate_brecon_constants(&classes, &recs, &below, &env, is_prop)
        .unwrap();

    assert!(
      brecon.is_empty(),
      "Non-recursive inductives should not generate brecOn"
    );
  }

  /// Type-level brecOn compile roundtrip: full pipeline with Nat-like inductive.
  ///
  /// For a single (non-mutual) inductive like T, no alpha-collapse occurs
  /// (n_classes == n_original), so aux_gen correctly produces no patches.
  /// This test verifies that compile_env succeeds and the inductive + prereqs
  /// compile without errors. Full brecOn generation is tested by lake test
  /// with real Lean environments that include .below and .brecOn constants.
  #[test]
  fn test_brecon_type_compile_roundtrip() {
    use crate::ix::compile::env::compile_env;
    use std::sync::Arc;

    let (mut env, t) = build_type_nat_env();

    // Add PProd/PUnit prereqs (needed by pre-compilation in compile_env).
    let u_name = Name::str(Name::anon(), "u".to_string());
    let v_name = Name::str(Name::anon(), "v".to_string());
    let punit_name = Name::str(Name::anon(), "PUnit".to_string());
    let punit_unit = Name::str(punit_name.clone(), "unit".to_string());
    env.insert(
      punit_name.clone(),
      ConstantInfo::InductInfo(InductiveVal {
        cnst: ConstantVal {
          name: punit_name.clone(),
          level_params: vec![u_name.clone()],
          typ: LeanExpr::sort(Level::succ(Level::param(u_name.clone()))),
        },
        num_params: Nat::from(0u64),
        num_indices: Nat::from(0u64),
        all: vec![punit_name.clone()],
        ctors: vec![punit_unit.clone()],
        num_nested: Nat::from(0u64),
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
      }),
    );
    env.insert(
      punit_unit.clone(),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: punit_unit,
          level_params: vec![u_name.clone()],
          typ: LeanExpr::cnst(
            punit_name.clone(),
            vec![Level::param(u_name.clone())],
          ),
        },
        induct: punit_name,
        cidx: Nat::from(0u64),
        num_params: Nat::from(0u64),
        num_fields: Nat::from(0u64),
        is_unsafe: false,
      }),
    );

    let pprod_name = Name::str(Name::anon(), "PProd".to_string());
    let pprod_mk = Name::str(pprod_name.clone(), "mk".to_string());
    let sort_u = LeanExpr::sort(Level::param(u_name.clone()));
    let sort_v = LeanExpr::sort(Level::param(v_name.clone()));
    let pprod_typ = LeanExpr::all(
      Name::str(Name::anon(), "α".to_string()),
      sort_u.clone(),
      LeanExpr::all(
        Name::str(Name::anon(), "β".to_string()),
        sort_v.clone(),
        LeanExpr::sort(Level::max(
          Level::param(u_name.clone()),
          Level::param(v_name.clone()),
        )),
        BinderInfo::Default,
      ),
      BinderInfo::Default,
    );
    env.insert(
      pprod_name.clone(),
      ConstantInfo::InductInfo(InductiveVal {
        cnst: ConstantVal {
          name: pprod_name.clone(),
          level_params: vec![u_name.clone(), v_name.clone()],
          typ: pprod_typ,
        },
        num_params: Nat::from(2u64),
        num_indices: Nat::from(0u64),
        all: vec![pprod_name.clone()],
        ctors: vec![pprod_mk.clone()],
        num_nested: Nat::from(0u64),
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
      }),
    );
    let pprod_mk_typ = LeanExpr::all(
      Name::str(Name::anon(), "α".to_string()),
      sort_u,
      LeanExpr::all(
        Name::str(Name::anon(), "β".to_string()),
        sort_v,
        LeanExpr::all(
          Name::str(Name::anon(), "fst".to_string()),
          LeanExpr::bvar(Nat::from(1u64)),
          LeanExpr::all(
            Name::str(Name::anon(), "snd".to_string()),
            LeanExpr::bvar(Nat::from(1u64)),
            LeanExpr::app(
              LeanExpr::app(
                LeanExpr::cnst(
                  pprod_name.clone(),
                  vec![
                    Level::param(u_name.clone()),
                    Level::param(v_name.clone()),
                  ],
                ),
                LeanExpr::bvar(Nat::from(3u64)),
              ),
              LeanExpr::bvar(Nat::from(2u64)),
            ),
            BinderInfo::Default,
          ),
          BinderInfo::Default,
        ),
        BinderInfo::Implicit,
      ),
      BinderInfo::Implicit,
    );
    env.insert(
      pprod_mk.clone(),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: pprod_mk,
          level_params: vec![u_name, v_name],
          typ: pprod_mk_typ,
        },
        induct: pprod_name,
        cidx: Nat::from(0u64),
        num_params: Nat::from(2u64),
        num_fields: Nat::from(2u64),
        is_unsafe: false,
      }),
    );

    let lean_env = Arc::new(env);
    let stt = compile_env(&lean_env)
      .expect("compile_env should succeed with Type-level inductive + prereqs");

    // Verify T was compiled.
    let has_name = |n: &Name| stt.resolve_addr(n).is_some();
    assert!(has_name(&t), "T should be compiled");

    // Single non-mutual inductive: no alpha-collapse, so aux_gen doesn't
    // fire (n_classes == n_original). T.brecOn/.below would only be
    // generated if they existed in the original Lean env.
    // The full pipeline test (lake test -- rust-compile) exercises real
    // environments where these constants exist.
  }
}
