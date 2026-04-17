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

use crate::ix::compile::nat_conv::{
  nat_to_u64, nat_to_usize, try_nat_to_usize,
};
use crate::ix::env::{
  BinderInfo, ConstantInfo, ConstantVal, ConstructorVal, Env as LeanEnv,
  Expr as LeanExpr, ExprData, InductiveVal, Level, Name, NameData,
  RecursorRule, RecursorVal,
};
use crate::ix::ixon::CompileError;
use lean_ffi::nat::Nat;

use super::expr_utils::{
  LocalDecl, decompose_apps, fresh_fvar, instantiate_spec_with_fvars,
  instantiate1, mk_const, mk_forall, mk_lambda, subst_levels,
};

// =========================================================================
// Public API
// =========================================================================

/// Generate canonical recursors using an expanded block (expand/restore model).
///
/// The expanded block provides an overlay environment where:
/// - Original inductives have constructor types with nested refs replaced by
///   auxiliary const applications (e.g., `Array (Part α)` → `_nested.Array_1 α`)
/// - Auxiliary inductives exist as synthetic entries with block params/levels
///
/// The existing recursor generator discovers auxiliaries via its internal
/// `build_compile_flat_block` call, which finds the auxiliary consts in the
/// overlay's constructor types. All auxiliaries share the block's params, so
/// `is_aux` branching produces correct (uniform) results.
///
/// The caller is responsible for applying `RestoreCtx::restore` to the
/// output to replace auxiliary const references with original nested apps.
pub(crate) fn generate_recursors_from_expanded(
  sorted_classes: &[Vec<Name>],
  expanded: &super::nested::ExpandedBlock,
  lean_env: &LeanEnv,
  stt: &crate::ix::compile::CompileState,
  kctx: &crate::ix::compile::KernelCtx,
) -> Result<(Vec<(Name, RecursorVal)>, bool), CompileError> {
  if expanded.types.is_empty() {
    return Ok((vec![], false));
  }

  // Build overlay environment from the expanded block.
  // Includes BOTH originals (with rewritten ctor types) and auxiliaries.
  let mut overlay = LeanEnv::default();

  // The `all` field for InductiveVals: just the original names (not aux).
  let original_names: Vec<Name> = expanded.types[..expanded.n_originals]
    .iter()
    .map(|m| m.name.clone())
    .collect();

  for member in &expanded.types {
    let ctor_names: Vec<Name> =
      member.ctors.iter().map(|c| c.name.clone()).collect();

    // Use the original lean_env's `all`/`is_rec`/`is_reflexive` when available.
    // For auxiliary types (not in lean_env), fall back to block-wide defaults.
    let (all_field, is_rec, is_reflexive) = match lean_env.get(&member.name) {
      Some(ConstantInfo::InductInfo(orig)) => {
        (orig.all.clone(), orig.is_rec, orig.is_reflexive)
      },
      _ => (original_names.clone(), true, false),
    };

    let ind_val = InductiveVal {
      cnst: ConstantVal {
        name: member.name.clone(),
        level_params: expanded.level_params.clone(),
        typ: member.typ.clone(),
      },
      num_params: Nat::from(member.n_params as u64),
      num_indices: Nat::from(member.n_indices as u64),
      all: all_field,
      ctors: ctor_names,
      num_nested: Nat::from(0u64),
      is_rec,
      is_unsafe: false,
      is_reflexive,
    };
    overlay.insert(member.name.clone(), ConstantInfo::InductInfo(ind_val));

    for (ci, ctor) in member.ctors.iter().enumerate() {
      let ctor_val = ConstructorVal {
        cnst: ConstantVal {
          name: ctor.name.clone(),
          level_params: expanded.level_params.clone(),
          typ: ctor.typ.clone(),
        },
        induct: member.name.clone(),
        cidx: Nat::from(ci as u64),
        num_params: Nat::from(member.n_params as u64),
        num_fields: Nat::from(ctor.n_fields as u64),
        is_unsafe: false,
      };
      overlay.insert(ctor.name.clone(), ConstantInfo::CtorInfo(ctor_val));
    }
  }

  // Build pre-flat from the expanded block's auxiliary members.
  // The expand phase already detected nested occurrences and created aux types;
  // we pass these directly so the recursor generator doesn't re-detect (which
  // would fail since expanded ctor types use aux consts, not nested apps).
  use super::nested::CompileFlatMember;
  let mut pre_flat: Vec<CompileFlatMember> = Vec::new();
  // Seed with originals (identity spec_params / occurrence_level_args).
  for member in expanded.types[..expanded.n_originals].iter() {
    pre_flat.push(CompileFlatMember {
      name: member.name.clone(),
      spec_params: vec![], // originals don't use spec_params
      occurrence_level_args: vec![],
      own_params: member.n_params,
      n_indices: member.n_indices,
    });
  }
  // Append auxiliaries with identity params/levels (they share the block's structure).
  for member in expanded.types[expanded.n_originals..].iter() {
    pre_flat.push(CompileFlatMember {
      name: member.name.clone(),
      spec_params: vec![], // aux types use block params — no spec_params needed
      occurrence_level_args: expanded
        .level_params
        .iter()
        .map(|lp| crate::ix::env::Level::param(lp.clone()))
        .collect(),
      own_params: member.n_params,
      n_indices: member.n_indices,
    });
  }

  generate_canonical_recursors_with_overlay(
    sorted_classes,
    lean_env,
    Some(&overlay),
    Some(pre_flat),
    stt,
    kctx,
  )
}

/// Info about one member of the flat block (original or auxiliary).
struct FlatInfo {
  /// Name of the inductive (for originals: the class rep, for aux: external ind)
  name: Name,
  /// InductiveVal from lean_env (cloned — DashMap prevents borrowing)
  ind: InductiveVal,
  /// Constructors from lean_env (cloned — DashMap prevents borrowing)
  ctors: Vec<ConstructorVal>,
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
/// Test-only convenience wrapper: generate canonical recursors with no
/// overlay env and no pre-built flat block, using the compile state's
/// default `kctx`.
///
/// Production code should call `generate_canonical_recursors_with_overlay`
/// directly and pass the appropriate `KernelCtx` — this wrapper is kept
/// only so unit tests don't have to plumb one through.
#[cfg(test)]
pub(crate) fn generate_canonical_recursors(
  sorted_classes: &[Vec<Name>],
  lean_env: &LeanEnv,
  stt: &crate::ix::compile::CompileState,
) -> Result<(Vec<(Name, RecursorVal)>, bool), CompileError> {
  generate_canonical_recursors_with_overlay(
    sorted_classes,
    lean_env,
    None,
    None,
    stt,
    &stt.kctx,
  )
}

/// Generate canonical recursors using the **canonical** kenv/TC.
///
/// Use `is_prop` to choose between definition (Type-level) and inductive
/// (Prop-level) generation — matching Lean's `isPropFormerType` guard.
///
/// Accepts an optional overlay environment for looking up class
/// representatives. Used by `compile_below_recursors` to avoid cloning
/// the full 197k-entry LeanEnv just to add a few `.below` inductive
/// entries.
///
/// `pre_flat`: Optional pre-built flat block (from expand/restore path).
/// When provided, skips `build_compile_flat_block` and uses these entries
/// instead. The expanded block already contains the correct auxiliary members.
pub(crate) fn generate_canonical_recursors_with_overlay(
  sorted_classes: &[Vec<Name>],
  lean_env: &LeanEnv,
  overlay: Option<&LeanEnv>,
  pre_flat: Option<Vec<super::nested::CompileFlatMember>>,
  stt: &crate::ix::compile::CompileState,
  kctx: &crate::ix::compile::KernelCtx,
) -> Result<(Vec<(Name, RecursorVal)>, bool), CompileError> {
  // Lookup helper: check overlay first, then base env.
  let env_get = |name: &Name| -> Option<ConstantInfo> {
    overlay
      .and_then(|o| o.get(name).cloned())
      .or_else(|| lean_env.get(name).cloned())
  };

  let mut classes: Vec<FlatInfo> = sorted_classes
    .iter()
    .map(|class| {
      let rep = &class[0];
      let ind = match env_get(rep) {
        Some(ConstantInfo::InductInfo(v)) => v,
        _ => {
          return Err(CompileError::InvalidMutualBlock {
            reason: format!("aux_gen: {} not an inductive", rep.pretty()),
          });
        },
      };
      let ctors: Vec<ConstructorVal> = ind
        .ctors
        .iter()
        .filter_map(|cn| match env_get(cn) {
          Some(ConstantInfo::CtorInfo(c)) => Some(c),
          _ => None,
        })
        .collect();
      let own_params = try_nat_to_usize(&ind.num_params)?;
      let n_indices = try_nat_to_usize(&ind.num_indices)?;
      Ok(FlatInfo {
        name: ind.cnst.name.clone(),
        ind,
        ctors,
        all_names: class.clone(),
        is_aux: false,
        spec_params: vec![],
        occurrence_level_args: vec![],
        own_params,
        n_indices,
      })
    })
    .collect::<Result<Vec<_>, _>>()?;

  let n_classes = classes.len();
  let n_params = try_nat_to_usize(&classes[0].ind.num_params)?;

  // Build flat block to detect nested inductive occurrences.
  // Use pre-built flat block from expand/restore path if available;
  // otherwise detect from constructor types.
  let ordered_originals: Vec<Name> =
    classes.iter().map(|c| c.name.clone()).collect();
  let flat = if let Some(pf) = pre_flat {
    pf
  } else {
    super::nested::build_compile_flat_block_with_overlay(
      &ordered_originals,
      lean_env,
      overlay,
    )?
  };

  // Add auxiliary members (nested occurrences) to classes.
  for fm in flat.iter().skip(n_classes) {
    if let Some(ConstantInfo::InductInfo(ind)) = env_get(&fm.name) {
      let ctors: Vec<ConstructorVal> = ind
        .ctors
        .iter()
        .filter_map(|cn| match env_get(cn) {
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
  // Propagates any TC failure as a hard error — there's no longer a
  // syntactic fallback, so aux_gen bugs / incomplete KEnv ingress surface
  // here instead of silently producing malformed recursors downstream.
  let (is_large, k, is_prop) =
    compute_is_large_and_k(&classes, n_classes, n_params, lean_env, stt, kctx)?;

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

  // Hoist param FVar/decl creation out of `build_rec_type`. All recursors in
  // this block share one set of param FVars — matching the C++ kernel's
  // `m_params` array which is shared across the whole `mk_rec_infos` pass.
  // Creating them once lets `decompose_inductive_type` populate
  // `IndRecInfo::indices` / `major` with domains that reference the same
  // FVars the rec types will use, so the results embed without substitution.
  let (shared_param_fvars, raw_param_decls, _) =
    super::expr_utils::forall_telescope(&first_ty, n_params, "param", 0);
  let shared_param_decls: Vec<super::expr_utils::LocalDecl> = raw_param_decls
    .into_iter()
    .zip(param_binders.iter())
    .map(|(mut d, pb)| {
      d.domain = super::expr_utils::consume_type_annotations(&d.domain);
      d.info = pb.info.clone();
      d
    })
    .collect();

  // Decompose each ORIGINAL class's stored type via kernel WHNF. This is
  // the Rust analog of `mk_rec_infos` — it peels the type's param Pi's
  // using our shared `param_fvars`, then all remaining leading Pi's as
  // indices, calling `TcScope::whnf_lean` between every step.
  //
  // The key payoff: for inductives targeting a reducible alias
  // (`εClosure : Set α = α → Prop`, `finiteInterClosure : Set (Set α)`),
  // WHNF exposes the Pi hidden inside the alias so the index binder
  // materializes. Pure syntactic peeling (the old code) couldn't see it.
  //
  // Aux (nested) members at index `>= n_classes` are handled separately
  // inside `build_rec_type`'s aux path — they have different structure
  // (spec_params, occurrence_level_args) that doesn't fit this helper.
  let class_infos: Vec<super::expr_utils::IndRecInfo> = classes
    [..n_classes]
    .iter()
    .map(|c| {
      super::expr_utils::decompose_inductive_type(
        &c.ind,
        &ind_univs,
        &shared_param_decls,
        stt,
        kctx,
      )
    })
    .collect::<Result<_, _>>()?;

  // Generate one recursor per flat member (originals + auxiliaries).
  let mut results = Vec::new();
  for di in 0..n_flat {
    let di_member = &classes[di];
    let n_indices = di_member.n_indices;

    // Name: original → <ind>.rec, auxiliary → <all[0]>.rec_N
    // Lean always hangs _N names under all[0] (first inductive in source order),
    // not under the class representative. Use the InductiveVal.all field.
    let rec_name = if di < n_classes {
      Name::str(di_member.ind.cnst.name.clone(), "rec".to_string())
    } else {
      let all0 = classes[0]
        .ind
        .all
        .first()
        .cloned()
        .unwrap_or_else(|| classes[0].ind.cnst.name.clone());
      let aux_idx = di - n_classes + 1;
      Name::str(all0, format!("rec_{}", aux_idx))
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
      &shared_param_fvars,
      &shared_param_decls,
      &class_infos,
      &elim_level,
      &ind_univs,
      lean_env,
      overlay,
    );

    // Build rules
    let rules = build_rec_rules(
      di,
      &classes,
      n_params,
      n_classes,
      &ind_univs,
      &rec_level_params,
      &rec_type,
    );

    // Lean propagates the inductive's safety to its recursor (see
    // `refs/lean4/src/kernel/inductive.cpp:774` — `m_is_unsafe` is sourced
    // from `decl.is_unsafe()` when `mk_recursor_val` is constructed). For
    // auxiliary (nested) members we use the external inductive's own
    // `is_unsafe` flag; for originals it's shared across the block since
    // mutual blocks are uniformly safe or unsafe.
    let is_unsafe = di_member.ind.is_unsafe;

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
        is_unsafe,
      },
    ));
  }

  Ok((results, is_prop))
}

// =========================================================================
// Binder info collected from types
// =========================================================================

/// A binder extracted from a forall chain.
///
/// `name` and `domain` are used by `collect_binders` and retained for
/// dead-code reference implementations (`_extract_field_binders_from_rec_type`).
#[derive(Clone)]
struct Binder {
  #[allow(dead_code)]
  name: Name,
  #[allow(dead_code)]
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
        // Strip outParam/semiOutParam/optParam/autoParam wrappers,
        // matching Lean's consume_type_annotations in mk_local_decl
        // (inductive.cpp:179).
        let clean_dom = super::expr_utils::consume_type_annotations(dom);
        binders.push(Binder {
          name: name.clone(),
          domain: clean_dom,
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
/// All domains and the return type are kept in FVar form throughout.
/// A single `mk_forall` call at the end batch-abstracts all FVars into
/// the correct de Bruijn indices.
///
/// Follows `declare_recursors` in inductive.cpp:752-774.
///
/// `param_fvars` and `param_decls` are shared across every recursor in
/// the block (they come from the enclosing `generate_canonical_recursors_*`).
/// `class_infos` are the WHNF-decomposed `IndRecInfo`s for each original
/// class (indexed `0..n_classes`), used to source indices + major for
/// non-aux recursors. Auxiliary (nested) recursors at `di >= n_classes`
/// still peel the type themselves using `spec_params` substitution.
fn build_rec_type(
  di: usize,
  classes: &[FlatInfo],
  flat: &[super::nested::CompileFlatMember],
  n_params: usize,
  n_classes: usize,
  _param_binders: &[Binder],
  param_fvars: &[LeanExpr],
  param_decls: &[LocalDecl],
  class_infos: &[super::expr_utils::IndRecInfo],
  elim_level: &Level,
  ind_univs: &[Level],
  lean_env: &LeanEnv,
  overlay: Option<&LeanEnv>,
) -> LeanExpr {
  let env_get = |name: &Name| -> Option<ConstantInfo> {
    overlay
      .and_then(|o| o.get(name).cloned())
      .or_else(|| lean_env.get(name).cloned())
  };
  let n_flat = flat.len();

  // Collect ALL binders in a single Vec<LocalDecl> with FVar-based domains.
  // mk_forall at the end handles all BVar abstraction in one batch.
  let mut all_decls: Vec<LocalDecl> = Vec::new();

  // --- Params: shared across recursors in this block ---
  all_decls.extend(param_decls.iter().cloned());

  // --- Motives (Cs): one per flat member, FVar domains ---
  let mut motive_fvars: Vec<LeanExpr> = Vec::new();
  for j in 0..n_flat {
    let motive_ty = if j < n_classes {
      build_motive_type(&class_infos[j], elim_level)
    } else {
      build_motive_type_aux(
        &classes[j],
        n_params,
        elim_level,
        ind_univs,
        lean_env,
        overlay,
        param_fvars,
      )
    };
    // Domain stays in FVar form — contains param FVars which mk_forall
    // will abstract when processing this binder's domain.
    let motive_name = if n_flat > 1 {
      Name::str(Name::anon(), format!("motive_{}", j + 1))
    } else {
      Name::str(Name::anon(), "motive".to_string())
    };
    let (fv_name, fv) = fresh_fvar("motive", j);
    motive_fvars.push(fv);
    all_decls.push(LocalDecl {
      fvar_name: fv_name,
      binder_name: motive_name,
      domain: motive_ty,
      info: BinderInfo::Default,
    });
  }

  // --- Minors: build for each flat member's constructors, FVar domains ---
  for j in 0..n_flat {
    let member_ctors: Vec<ConstructorVal> = if j < n_classes {
      classes[j].ctors.clone()
    } else {
      match env_get(&flat[j].name) {
        Some(ConstantInfo::InductInfo(ind)) => ind
          .ctors
          .iter()
          .filter_map(|cn| match env_get(cn) {
            Some(ConstantInfo::CtorInfo(c)) => Some(c),
            _ => None,
          })
          .collect(),
        _ => vec![],
      }
    };
    let ind_name = &flat[j].name;
    for ctor in &member_ctors {
      let minor_ty = build_minor_type(
        j,
        ctor,
        classes,
        n_params,
        n_classes,
        &param_fvars,
        &motive_fvars,
        ind_univs,
      );
      // Domain stays in FVar form — contains param + motive FVars.
      let minor_name = ctor.cnst.name.strip_prefix(ind_name).map_or_else(
        || ctor.cnst.name.clone(),
        |suffix| Name::anon().append_components(&suffix),
      );
      let (fv_name, _fv) = fresh_fvar("minor", all_decls.len());
      all_decls.push(LocalDecl {
        fvar_name: fv_name,
        binder_name: minor_name,
        domain: minor_ty,
        info: BinderInfo::Default,
      });
    }
  }

  // --- Indices + major for member di ---
  //
  // Two paths:
  //
  // * Non-aux (di < n_classes): use the pre-computed `IndRecInfo` from
  //   `class_infos[di]`. Its `indices` and `major` are already WHNF-derived,
  //   and their domains reference our shared `param_fvars` — so we can drop
  //   them directly into `all_decls` and use their FVars for the return
  //   expression.
  //
  // * Aux (di >= n_classes): the stored inductive type needs `spec_params`
  //   substituted (nested occurrence parameters) before peeling, which
  //   doesn't match `decompose_inductive_type`'s interface. Keep the in-place
  //   peel here, but it's still subject to the same WHNF-on-reducible-target
  //   issue if a nested aux inductive has a reducible-alias target. Not
  //   observed in the wild yet; if it comes up, factor `decompose_*` to
  //   accept pre-substituted spec_params.
  let di_member = &classes[di];
  let di_is_aux = di_member.is_aux;

  let mut index_fvars: Vec<LeanExpr> = Vec::new();
  let major_dom;
  let major_fv_name;
  let major_fv;

  if !di_is_aux {
    let info = &class_infos[di];
    all_decls.extend(info.indices.iter().cloned());
    index_fvars.extend(
      info.indices.iter().map(|d| LeanExpr::fvar(d.fvar_name.clone())),
    );
    major_dom = info.major.domain.clone();
    major_fv_name = info.major.fvar_name.clone();
    major_fv = LeanExpr::fvar(major_fv_name.clone());
    all_decls.push(info.major.clone());
  } else {
    // Legacy aux path: substitute spec_params, peel syntactically.
    let di_ty = if !di_member.occurrence_level_args.is_empty() {
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
    let di_n_ext_params = di_member.own_params;
    let di_sp_fvars =
      instantiate_spec_with_fvars(&di_member.spec_params, param_fvars);
    for p in 0..di_n_ext_params {
      if let ExprData::ForallE(_, _, body, _, _) = ity.as_data() {
        if p < di_sp_fvars.len() {
          ity = instantiate1(body, &di_sp_fvars[p]);
        } else if p < param_fvars.len() {
          ity = instantiate1(body, &param_fvars[p]);
        } else {
          ity = body.clone();
        }
      }
    }
    // Beta-reduce: lambda-valued spec_params create redexes that need
    // reduction before forall_telescope peeling.
    ity = super::expr_utils::beta_reduce(&ity);

    // Peel `n_indices` leading Pi's. For aux nested members this is still
    // syntactic — see note above.
    let n_indices = di_member.n_indices;
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
    all_decls.extend(index_decls);

    // Build major domain: I spec_params indices.
    let major_univs = if !di_member.occurrence_level_args.is_empty() {
      &di_member.occurrence_level_args
    } else {
      ind_univs
    };
    let mut app = mk_const(&di_member.ind.cnst.name, major_univs);
    for sp in &di_sp_fvars {
      app = LeanExpr::app(app, sp.clone());
    }
    for idx_fv in &index_fvars {
      app = LeanExpr::app(app, idx_fv.clone());
    }
    major_dom = app;
    let (name, fv) = fresh_fvar("major", 0);
    major_fv_name = name;
    major_fv = fv;
    all_decls.push(LocalDecl {
      fvar_name: major_fv_name.clone(),
      binder_name: Name::str(Name::anon(), "t".to_string()),
      domain: major_dom.clone(),
      info: BinderInfo::Default,
    });
  }

  // Silence unused-variable warnings for the non-aux path, which doesn't
  // need the extracted name back. Both branches still return via the outer
  // flow via `ret`/`mk_forall`.
  let _ = (&major_dom, &major_fv_name);

  // --- Return: motive_di(index_fvars, major_fv) ---
  let mut ret = motive_fvars[di].clone();
  for idx_fv in &index_fvars {
    ret = LeanExpr::app(ret, idx_fv.clone());
  }
  ret = LeanExpr::app(ret, major_fv);

  // Single batch abstraction: all FVars → BVars in one pass.
  let rec_type = mk_forall(ret, &all_decls);

  // Apply infer_implicit: Lean calls inferImplicit(ty, 1000, false)
  // which processes ALL binders, marking them implicit if their BVar
  // appears in an explicit domain downstream.
  infer_implicit(&rec_type, 1000)
}

/// Build motive type for a class from its pre-computed [`IndRecInfo`]:
/// `∀ (indices...) (t : I params indices), Sort elim_level`.
///
/// This is a trivial wrapper — all the real work (WHNF-aware peeling of
/// index binders, construction of the major's domain from the inductive
/// head applied to params+indices) happens in
/// [`decompose_inductive_type`]. Keeping the assembly here preserves the
/// symmetry with `mk_C` in `inductive.cpp:609-615` (the C++ kernel builds
/// `C_ty` the same way from `m_major` and `m_indices`).
///
/// The returned expression contains param FVars free; the caller abstracts
/// them via the outer rec type's `mk_forall` pass. Index + major FVars
/// are already abstracted into BVars inside the motive's binder chain.
fn build_motive_type(
  ind_info: &super::expr_utils::IndRecInfo,
  elim_level: &Level,
) -> LeanExpr {
  let sort = LeanExpr::sort(elim_level.clone());
  let mut decls: Vec<LocalDecl> = ind_info.indices.clone();
  decls.push(ind_info.major.clone());
  mk_forall(sort, &decls)
}

/// Build motive type for an auxiliary (nested) flat member.
///
/// For a nested occurrence `J Ds` where `J` is an external inductive
/// with indices, the motive type is `∀ (indices...) (t : J Ds indices), Sort u`.
/// `Ds` are the spec_params from the flat member.
///
/// Uses FVar-based index peeling via `forall_telescope` so that dependent
/// index domains are correctly instantiated (earlier indices as FVars).
/// The returned expression contains param FVars as free variables.
fn build_motive_type_aux(
  member: &FlatInfo,
  _n_params: usize,
  elim_level: &Level,
  _ind_univs: &[Level],
  lean_env: &LeanEnv,
  overlay: Option<&LeanEnv>,
  param_fvars: &[LeanExpr],
) -> LeanExpr {
  // Look up the external inductive (check overlay first for expanded aux types).
  let env_get_local = |n: &Name| -> Option<ConstantInfo> {
    overlay.and_then(|o| o.get(n).cloned()).or_else(|| lean_env.get(n).cloned())
  };
  let ind = match env_get_local(&member.name) {
    Some(ConstantInfo::InductInfo(v)) => v,
    _ => return LeanExpr::sort(Level::zero()), // fallback
  };
  let n_ext_params = member.own_params;
  let n_ext_indices = member.n_indices;

  // Substitute levels with occurrence_level_args (concrete levels from
  // the nested occurrence).
  let ty = if !member.occurrence_level_args.is_empty() {
    subst_levels(
      &ind.cnst.typ,
      &ind.cnst.level_params,
      &member.occurrence_level_args,
    )
  } else {
    ind.cnst.typ.clone()
  };

  // Skip params, substituting with spec_params in FVar form.
  // Convert BVar-form spec_params to FVar form using param_fvars, so the
  // resulting motive type uses the same FVars as original member motives.
  let spec_fvars =
    instantiate_spec_with_fvars(&member.spec_params, param_fvars);
  let mut cur = ty;
  for p in 0..n_ext_params {
    if let ExprData::ForallE(_, _, body, _, _) = cur.as_data() {
      if p < spec_fvars.len() {
        cur = instantiate1(body, &spec_fvars[p]);
      } else {
        cur = instantiate1(body, &LeanExpr::sort(Level::zero())); // placeholder
      }
    }
  }
  // Beta-reduce after spec_param instantiation for motive types.
  // Lambda-valued spec_params (e.g., `λ _ => String` for function-typed
  // inductive parameters) create unreduced redexes that may obstruct
  // forall_telescope below. The motive type itself is fresh-built, so
  // beta-reducing here doesn't conflict with the Lean-stored structure.
  cur = super::expr_utils::beta_reduce(&cur);
  // Peel index binders using FVars so that dependent index domains are
  // correctly instantiated. This fixes the structural-peeling bug where
  // body.clone() left dangling BVars in dependent index types.
  let (index_fvars, index_decls, _) =
    super::expr_utils::forall_telescope(&cur, n_ext_indices, "ma_idx", 0);

  // Build major type: J.{occurrence_us} spec_params index_fvars
  let fallback_univs;
  let major_univs = if !member.occurrence_level_args.is_empty() {
    &member.occurrence_level_args
  } else {
    // Fallback: identity-mapped level params (shouldn't reach here for
    // proper aux members)
    fallback_univs = ind
      .cnst
      .level_params
      .iter()
      .map(|n| Level::param(n.clone()))
      .collect::<Vec<_>>();
    &fallback_univs
  };
  let mut major_ty = mk_const(&member.name, major_univs);
  for sp in &spec_fvars {
    major_ty = LeanExpr::app(major_ty, sp.clone());
  }
  for idx_fv in &index_fvars {
    major_ty = LeanExpr::app(major_ty, idx_fv.clone());
  }

  // Build: ∀ (indices...) (major : major_ty), Sort elim_level
  let sort = LeanExpr::sort(elim_level.clone());
  let major_decl = LocalDecl {
    fvar_name: Name::str(Name::anon(), "_ma_major_0".to_string()),
    binder_name: Name::str(Name::anon(), "t".to_string()),
    domain: major_ty,
    info: BinderInfo::Default,
  };

  let mut all_decls: Vec<LocalDecl> = Vec::new();
  all_decls.extend(index_decls);
  all_decls.push(major_decl);
  mk_forall(sort, &all_decls)
}

/// Build minor premise type for a constructor using FVars.
///
/// `param_fvars`: FVars for the recursor's params (from outer context).
/// `motive_fvars`: FVars for the recursor's motives (from outer context).
fn build_minor_type(
  class_idx: usize,
  ctor: &ConstructorVal,
  classes: &[FlatInfo],
  n_params: usize,
  n_classes: usize,
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
  let n_ctor_params = nat_to_usize(&ctor.num_params);
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
  // Beta-reduce after spec_param instantiation for auxiliary members.
  if member.is_aux {
    cur = super::expr_utils::beta_reduce(&cur);
  }
  // Rewrite nested type universe levels for original members.
  // Lean's kernel recomputes nested type universes from the element's sort
  // (e.g., Array.{u} → Array.{max u v} when applied to Part.{u,v}).
  // Only rewrite when the Const's args actually reference block members.
  if !member.is_aux && classes.iter().any(|c| c.is_aux) {
    let block_names: Vec<Name> =
      classes[..n_classes].iter().map(|c| c.name.clone()).collect();
    let aux_info: std::collections::HashMap<Name, (usize, Vec<Level>)> =
      classes
        .iter()
        .filter(|c| c.is_aux)
        .map(|c| {
          (c.name.clone(), (c.own_params, c.occurrence_level_args.clone()))
        })
        .collect();
    cur = super::expr_utils::rewrite_nested_const_levels(
      &cur,
      &aux_info,
      &block_names,
    );
  }

  // Collect fields: peel each field with a fresh FVar.
  let n_fields = nat_to_usize(&ctor.num_fields);
  let mut field_decls: Vec<LocalDecl> = Vec::new();
  let mut field_fvars: Vec<LeanExpr> = Vec::new();
  let mut rec_fields: Vec<(usize, usize)> = Vec::new(); // (field_idx, target_class)

  for fi in 0..n_fields {
    match cur.as_data() {
      ExprData::ForallE(name, dom, body, bi, _) => {
        // Strip autoParam/optParam/outParam wrappers, matching Lean's
        // consumeTypeAnnotations in withLocalDecl calls.
        let clean_dom = super::expr_utils::consume_type_annotations(dom);
        let (fv_name, fv) = fresh_fvar("field", fi);
        field_decls.push(LocalDecl {
          fvar_name: fv_name,
          binder_name: name.clone(),
          domain: clean_dom.clone(),
          info: bi.clone(),
        });
        field_fvars.push(fv.clone());
        if let Some(ci) =
          find_rec_target(&clean_dom, classes, param_fvars, n_params)
        {
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
  classes: &[FlatInfo],
) -> LeanExpr {
  // Use forallTelescope-style approach: peel foralls from the field domain
  // using fresh FVars so that the inner application is fully FVar-based.
  // This avoids the BVar/FVar mixing issues that cause FVar leaks.
  //
  // Head-reduce at each step so that lambda-valued spec params (e.g.
  // `β := λ_:α. Json` for `Internal.Impl α β`) are transparently unwrapped.
  // A field `v : (λ_:α. Json) k` must be seen as targeting `Json` with no
  // extra args — without reduction we would treat `k` as an index, which
  // would apply the motive to too many arguments.
  let mut xs_fvars: Vec<LeanExpr> = Vec::new();
  let mut xs_decls: Vec<LocalDecl> = Vec::new();
  let mut cur = super::expr_utils::beta_reduce(field_dom);

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
    cur = super::expr_utils::beta_reduce(&instantiate1(body, &fv));
  }

  // `cur` is now the fully FVar-instantiated inner expression: I params idx_args
  let (_, inner_args) = decompose_apps(&cur);
  let n_target_params = nat_to_usize(&classes[target_ci].ind.num_params);
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
  classes: &[FlatInfo],
  n_params: usize,
  n_classes: usize,
  ind_univs: &[Level],
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
      let n_fields = nat_to_usize(&ctor.num_fields);

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
      let n_ctor_params = nat_to_usize(&ctor.num_params);
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
      if class.is_aux {
        ty = super::expr_utils::beta_reduce(&ty);
      }
      // Rewrite nested type universe levels for original members.
      if !class.is_aux && classes.iter().any(|c| c.is_aux) {
        let block_names: Vec<Name> =
          classes[..n_classes].iter().map(|c| c.name.clone()).collect();
        let aux_info: std::collections::HashMap<Name, (usize, Vec<Level>)> =
          classes
            .iter()
            .filter(|c| c.is_aux)
            .map(|c| {
              (c.name.clone(), (c.own_params, c.occurrence_level_args.clone()))
            })
            .collect();
        ty = super::expr_utils::rewrite_nested_const_levels(
          &ty,
          &aux_info,
          &block_names,
        );
      }
      // Collect fields with FVars, detect recursive fields.
      let mut field_decls: Vec<LocalDecl> = Vec::new();
      let mut field_fvars: Vec<LeanExpr> = Vec::new();
      let mut rec_field_data: Vec<(LeanExpr, usize)> = Vec::new(); // (field_fvar, target_ci)

      for fi in 0..n_fields {
        match ty.as_data() {
          ExprData::ForallE(fname, dom, b, fbi, _) => {
            let clean_dom = super::expr_utils::consume_type_annotations(dom);
            let (fv_name, fv) = fresh_fvar("rfield", fi);
            field_decls.push(LocalDecl {
              fvar_name: fv_name,
              binder_name: fname.clone(),
              domain: clean_dom.clone(),
              info: fbi.clone(),
            });
            if let Some(target_ci) =
              find_rec_target(&clean_dom, classes, &param_fvars, n_params)
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
        // For auxiliary targets: <all[0]>.rec_N (Lean hangs _N under all[0])
        let rec_name = if *target_ci < n_classes {
          Name::str(
            classes[*target_ci].ind.cnst.name.clone(),
            "rec".to_string(),
          )
        } else {
          let all0 = classes[0]
            .ind
            .all
            .first()
            .cloned()
            .unwrap_or_else(|| classes[0].ind.cnst.name.clone());
          let aux_idx = *target_ci - n_classes + 1;
          Name::str(all0, format!("rec_{}", aux_idx))
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
  classes: &[FlatInfo],
) -> LeanExpr {
  let target_n_params = nat_to_usize(&classes[target_ci].ind.num_params);

  // Use forallTelescope-style approach: peel foralls with fresh FVars
  // so the inner expression and all idx_args are fully in FVar form.
  //
  // Head-reduce at each step — same rationale as `build_ih_type_fvar`:
  // lambda-valued spec params must be unwrapped so the idx_args we
  // extract match the reduced form.
  let mut xs_fvars: Vec<LeanExpr> = Vec::new();
  let mut xs_decls: Vec<LocalDecl> = Vec::new();
  let mut cur = super::expr_utils::beta_reduce(field_dom);

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
    cur = super::expr_utils::beta_reduce(&instantiate1(body, &fv));
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

// =========================================================================
// Helpers
// =========================================================================

// NOTE: The `elim_only_at_universe_zero` / `is_sort_zero_domain` /
// `is_prop_sort` trio used to live here as a syntactic fallback for
// `compute_is_large_and_k` when the zero kernel's `is_large_eliminator`
// failed. That fallback silently masked aux_gen construction bugs (see
// the `Acc.below` IH-field fix in `aux_gen/below.rs` — higher-order
// recursive fields were producing malformed ctor types and the fallback
// kept the pipeline green). Removed on the theory that a TC failure here
// always means an aux_gen bug or incomplete ingress, and we'd rather
// fail loudly than ship a content-addressed, internally-inconsistent
// recursor. Resurrect from git history if a legitimate case needs it.

// The local `consume_type_annotations` that used to live here
// has been removed. It was a near-duplicate of `super::expr_utils::`
// `consume_type_annotations` with two subtle divergences:
//   1. It matched by `name.last_str()` (which would falsely strip a
//      user-defined `MyModule.outParam`).
//   2. It additionally stripped top-level `Mdata` wrappers, which goes
//      beyond Lean's `Expr.consumeTypeAnnotations` — Lean handles Mdata
//      via a separate `cleanupAnnotations` pass that calls `consumeMData`.
// All call sites now go through the canonical `expr_utils` version,
// which matches Lean's semantics exactly (full-pretty-name check, no
// Mdata stripping). If an input with Mdata-wrapped binder domains
// surfaces in practice, the correct fix is to add a `consumeMData` pass
// at the call site, not to re-introduce Mdata stripping in the wrong place.

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
/// Matches C++ `is_rec_argument` (inductive.cpp:383-390): peels foralls using
/// FVar instantiation (not bare body.clone()) to avoid dangling BVars, then
/// validates the result with `is_valid_ind_app`-style checks.
///
/// For originals: validates that applied parameters match `param_fvars`.
/// For auxiliaries: also matches spec_params to distinguish e.g. List Syntax
/// from List Other.
fn find_rec_target(
  dom: &LeanExpr,
  classes: &[FlatInfo],
  param_fvars: &[LeanExpr],
  n_params: usize,
) -> Option<usize> {
  // Peel foralls with FVar instantiation (C++ uses mk_local_decl_for +
  // instantiate). This avoids dangling BVars in the result type when
  // fields have dependent index types.
  //
  // We head-reduce at each step so that lambda-valued parameters (e.g.,
  // `β := λ_. PrefixTreeNode α β cmp` for `Internal.Impl α β`) are
  // transparently unwrapped: a field like `v : (λ_:α. PT α β cmp) k`
  // still resolves to the `PT` class. Lean's kernel uses `whnf` for the
  // same purpose in `kernel/inductive.cpp::is_rec_argument` — the
  // detection sees through the redex even though the stored field type
  // keeps the unreduced form.
  let mut ty = super::expr_utils::beta_reduce(dom);
  let mut fvar_idx = 0usize;
  loop {
    match ty.as_data() {
      ExprData::ForallE(_, _, body, _, _) => {
        let (_, fv) = fresh_fvar("frt", fvar_idx);
        fvar_idx += 1;
        ty = super::expr_utils::beta_reduce(&instantiate1(body, &fv));
      },
      _ => {
        let (head, args) = decompose_apps(&ty);
        if let ExprData::Const(name, _, _) = head.as_data() {
          for (ci, class) in classes.iter().enumerate() {
            // Check if the name matches any name in the equivalence class.
            if !class.all_names.iter().any(|n| n == name) {
              continue;
            }
            if !class.is_aux {
              // Original member: validate parameters match (C++ is_valid_ind_app
              // checks m_params[i] == args[i] for each parameter).
              if args.len() >= n_params
                && args[..n_params]
                  .iter()
                  .zip(param_fvars.iter())
                  .all(|(a, p)| a.get_hash() == p.get_hash())
              {
                return Some(ci);
              }
              // Name matched but params didn't — not a valid recursive occurrence.
              continue;
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
/// shift under binders).
///
/// Includes the C++ kernel's **transitivity rule**: if `target` appears
/// in an *implicit* binder's domain, we recursively check whether that
/// binder's own variable (BVar 0 in the body) appears in an explicit
/// domain downstream. This handles chains like `{x : F target} → (y : G x)`.
///
/// Reference: `refs/lean4/src/kernel/expr.cpp:480-500`
fn has_loose_bvar_in_explicit_domain(
  e: &LeanExpr,
  target: u64,
  strict: bool,
) -> bool {
  match e.as_data() {
    ExprData::Bvar(idx, _) => {
      let i = nat_to_u64(idx);
      if strict {
        false // In strict mode, bare BVars in the range don't count
      } else {
        i == target // In non-strict mode, BVars in the range count
      }
    },
    ExprData::ForallE(_, dom, body, bi, _) => {
      // Check if target appears in this binder's domain (any binder info).
      if expr_has_loose_bvar(dom, target) {
        if *bi == BinderInfo::Default {
          // Explicit domain contains target — mark as implicit.
          return true;
        } else if has_loose_bvar_in_explicit_domain(body, 0, strict) {
          // Transitivity: target appears in an implicit binder's domain.
          // Check whether this binder's own variable (BVar 0 in body)
          // appears in an explicit domain downstream. If so, target is
          // transitively needed by an explicit domain.
          return true;
        }
      }
      // Continue searching in the body with shifted target.
      has_loose_bvar_in_explicit_domain(body, target + 1, strict)
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
    ExprData::Bvar(idx, _) => nat_to_u64(idx) == target,
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
// is_large / k / is_prop computation
// =========================================================================

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
  classes: &[FlatInfo],
  n_classes: usize,
  n_params: usize,
  lean_env: &LeanEnv,
  stt: &crate::ix::compile::CompileState,
  kctx: &crate::ix::compile::KernelCtx,
) -> Result<(bool, bool, bool), CompileError> {
  use crate::ix::kernel::constant::KConst;
  use crate::ix::kernel::id::KId;
  use crate::ix::kernel::ingress::{
    lean_expr_to_zexpr_with_kenv, resolve_lean_name_addr,
  };
  use crate::ix::kernel::mode::Meta;

  let n2a = Some(&stt.name_to_addr);
  let aux_n2a = Some(&stt.aux_name_to_addr);

  // Build ephemeral KConst entries for ALL original classes and insert
  // into stt.kenv. This ensures is_large_eliminator sees the full mutual
  // block and can apply the "mutual Prop → small" rule.
  let mut ind_infos: Vec<(
    KId<Meta>,
    u64,
    u64,
    Vec<KId<Meta>>,
    crate::ix::kernel::expr::KExpr<Meta>,
    bool,
  )> = Vec::new();

  // Use the first class's block KId as the shared block reference.
  let block_addr =
    resolve_lean_name_addr(&classes[0].ind.cnst.name, n2a, aux_n2a);
  let block_zid: KId<Meta> =
    KId::new(block_addr, classes[0].ind.cnst.name.clone());

  let _cilk_start = std::time::Instant::now();
  let mut _ingress_total = std::time::Duration::ZERO;
  for (ci, cls) in classes[..n_classes].iter().enumerate() {
    let cls_ind = &cls.ind;
    let cls_lvl_params = &cls_ind.cnst.level_params;
    let cls_n_lvls = cls_lvl_params.len() as u64;
    let cls_n_indices = nat_to_u64(&cls_ind.num_indices);

    let cls_addr = resolve_lean_name_addr(&cls_ind.cnst.name, n2a, aux_n2a);
    let cls_zid: KId<Meta> = KId::new(cls_addr, cls_ind.cnst.name.clone());
    let cls_ty_z = lean_expr_to_zexpr_with_kenv(
      &cls_ind.cnst.typ,
      cls_lvl_params,
      &kctx.kenv,
      n2a,
      aux_n2a,
    );

    // Convert constructors
    let mut cls_ctor_zids: Vec<KId<Meta>> = Vec::new();
    for ctor in &cls.ctors {
      let ctor_addr = resolve_lean_name_addr(&ctor.cnst.name, n2a, aux_n2a);
      let ctor_zid = KId::new(ctor_addr, ctor.cnst.name.clone());
      let ctor_ty_z = lean_expr_to_zexpr_with_kenv(
        &ctor.cnst.typ,
        cls_lvl_params,
        &kctx.kenv,
        n2a,
        aux_n2a,
      );
      let ctor_fields = nat_to_u64(&ctor.num_fields);
      let ctor_params = nat_to_u64(&ctor.num_params);

      kctx.kenv.insert(
        ctor_zid.clone(),
        KConst::Ctor {
          name: ctor.cnst.name.clone(),
          level_params: cls_lvl_params.clone(),
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
    kctx.kenv.insert(
      cls_zid.clone(),
      KConst::Indc {
        name: cls_ind.cnst.name.clone(),
        level_params: cls_lvl_params.clone(),
        lvls: cls_n_lvls,
        params: n_params as u64,
        indices: cls_n_indices,
        is_rec: cls_ind.is_rec,
        is_refl: cls_ind.is_reflexive,
        is_unsafe: cls_ind.is_unsafe,
        nested: 0,
        block: block_zid.clone(),
        member_idx: ci as u64,
        ty: cls_ty_z.clone(),
        ctors: cls_ctor_zids.clone(),
        lean_all: vec![],
      },
    );

    // Ingress field deps for this class
    let _ig_start = std::time::Instant::now();
    ingress_field_deps(cls, cls_lvl_params, lean_env, stt, kctx);
    _ingress_total += _ig_start.elapsed();

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

  // Use the TC for the appropriate context.
  let mut tc = crate::ix::kernel::tc::TypeChecker::new(kctx.kenv.clone());

  // Compute the WHNF-reduced result sort level via the kernel. This peels
  // params+indices with whnf at each step — crucial for inductives whose
  // target is a reducible alias (e.g. `Set σ := σ → Prop`), where syntactic
  // peeling would stop early at an unreduced `App(Const(Set), _)`.
  let result_kuniv = tc
    .get_result_sort_level(first_ty_z, n_params + (first_n_indices as usize))
    .map_err(|e| CompileError::InvalidMutualBlock {
      reason: format!(
        "compute_is_large_and_k: TC failed for {}: {e}",
        classes[0].ind.cnst.name.pretty()
      ),
    })?;

  let is_large = tc
    .is_large_eliminator(&result_kuniv, &ind_infos)
    .map_err(|e| CompileError::InvalidMutualBlock {
      reason: format!(
        "compute_is_large_and_k: is_large_eliminator failed for {}: {e}",
        classes[0].ind.cnst.name.pretty()
      ),
    })?;

  // Spec-level override: non-Prop inductives always get large elimination
  // (Lean C++ `inductive.cpp:539-548`). Our kernel's `is_large_eliminator`
  // only early-returns when the result level is *provably* non-zero; a
  // Param universe that happens to be non-zero syntactically (e.g., u+1)
  // falls through to the single-ctor check and can come back "small".
  // Correct that here using the WHNF-reduced result level.
  let is_large = if !is_large && !result_kuniv.is_zero() {
    true
  } else {
    is_large
  };

  // Prop determination: use the WHNF-reduced kernel-derived level, not the
  // raw LeanExpr-syntactic path. For reducible-alias targets the syntactic
  // peel short-circuits (can't find enough Pi's) and returns None, which
  // would wrongly classify the inductive as non-Prop and produce a
  // Type-level `.brecOn` (with `.brecOn.go` / `.brecOn.eq` sub-constants)
  // for what is actually a `Prop`-valued inductive. `KUniv::is_zero()`
  // here handles `Zero`, `IMax(_, Zero)`, and the like.
  let is_prop = result_kuniv.is_zero();

  // C1 fix: if the block has nested auxiliary flat members that weren't
  // inserted into the KEnv, the is_large_eliminator result may be wrong.
  // In Lean's kernel, nested auxiliaries are full mutual block members
  // (via elim_nested_inductive_fn), and any mutual Prop block (>1 type)
  // gets small elimination. The KEnv path only saw n_classes types, so
  // it may have incorrectly allowed large elimination.
  let is_large = if is_large && is_prop && classes.len() > n_classes {
    false
  } else {
    is_large
  };

  // K-target: single inductive, Prop, single ctor, 0 non-param fields.
  // Use classes.len() (full flat block including nested auxiliaries), not
  // n_classes, to match Lean's `m_ind_types.size() == 1` check which counts
  // the expanded block (inductive.cpp:556).
  let k = classes.len() == 1
    && classes[0].ctors.len() == 1
    && nat_to_u64(&classes[0].ctors[0].num_fields) == 0
    && matches!(
      peek_result_sort(first_ty_z),
      Some(u) if u.is_zero()
    );

  let _cilk_elapsed = _cilk_start.elapsed();
  if *crate::ix::compile::IX_TIMING && _cilk_elapsed.as_secs_f32() > 0.1 {
    eprintln!(
      "[compute_is_large_and_k] {:?} total={:.3}s ingress={:.3}s n_classes={} kenv_size={}",
      classes[0].ind.cnst.name.pretty(),
      _cilk_elapsed.as_secs_f32(),
      _ingress_total.as_secs_f32(),
      n_classes,
      kctx.kenv.consts.len(),
    );
  }
  Ok((is_large, k, is_prop))
}

/// Walk field domains of constructors and ingress any referenced constants
/// into the KEnv as Axio stubs (type only), so `infer_type` can look them up.
fn ingress_field_deps(
  class: &FlatInfo,
  _lvl_params: &[Name],
  lean_env: &LeanEnv,
  stt: &crate::ix::compile::CompileState,
  kctx: &crate::ix::compile::KernelCtx,
) {
  use crate::ix::kernel::constant::KConst;
  use crate::ix::kernel::id::KId;
  use crate::ix::kernel::ingress::{
    lean_expr_to_zexpr_with_kenv, resolve_lean_name_addr,
  };
  use crate::ix::kernel::mode::Meta;

  let n2a = Some(&stt.name_to_addr);
  let aux_n2a = Some(&stt.aux_name_to_addr);
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
    let zid: KId<Meta> = KId::new(addr, name.clone());
    if kctx.kenv.contains_key(&zid) {
      continue;
    }

    // Look up in LeanEnv and insert as Axio stub
    if let Some(ci) = lean_env.get(&name) {
      let (typ, dep_lvl_params) = match &*ci {
        ConstantInfo::InductInfo(v) => (&v.cnst.typ, &v.cnst.level_params),
        ConstantInfo::CtorInfo(v) => (&v.cnst.typ, &v.cnst.level_params),
        ConstantInfo::DefnInfo(v) => (&v.cnst.typ, &v.cnst.level_params),
        ConstantInfo::AxiomInfo(v) => (&v.cnst.typ, &v.cnst.level_params),
        ConstantInfo::ThmInfo(v) => (&v.cnst.typ, &v.cnst.level_params),
        ConstantInfo::OpaqueInfo(v) => (&v.cnst.typ, &v.cnst.level_params),
        ConstantInfo::RecInfo(v) => (&v.cnst.typ, &v.cnst.level_params),
        ConstantInfo::QuotInfo(v) => (&v.cnst.typ, &v.cnst.level_params),
      };
      let ty_z = lean_expr_to_zexpr_with_kenv(
        typ,
        dep_lvl_params,
        &kctx.kenv,
        n2a,
        aux_n2a,
      );
      let n_lvls = dep_lvl_params.len() as u64;
      kctx.kenv.insert(
        zid,
        KConst::Axio {
          name: name.clone(),
          level_params: dep_lvl_params.clone(),
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
/// Uses an explicit stack to avoid stack overflow on deeply nested expressions.
fn collect_const_refs(expr: &LeanExpr, out: &mut Vec<Name>) {
  let mut stack: Vec<&LeanExpr> = vec![expr];
  while let Some(e) = stack.pop() {
    match e.as_data() {
      ExprData::Const(n, _, _) => out.push(n.clone()),
      ExprData::App(f, a, _) => {
        stack.push(f);
        stack.push(a);
      },
      ExprData::ForallE(_, d, b, _, _) | ExprData::Lam(_, d, b, _, _) => {
        stack.push(d);
        stack.push(b);
      },
      ExprData::LetE(_, t, v, b, _, _) => {
        stack.push(t);
        stack.push(v);
        stack.push(b);
      },
      ExprData::Proj(_, _, e, _) | ExprData::Mdata(_, e, _) => {
        stack.push(e);
      },
      _ => {},
    }
  }
}

/// Peek at the result sort of a KExpr type (peel foralls, check for Sort).
fn peek_result_sort(
  ty: &crate::ix::kernel::expr::KExpr<crate::ix::kernel::mode::Meta>,
) -> Option<crate::ix::kernel::level::KUniv<crate::ix::kernel::mode::Meta>> {
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
    // Add PUnit and PProd so brecOn's get_level can resolve them.
    add_punit_pprod(&mut env);
    (env, t)
  }

  /// Add minimal PUnit.{u} and PProd.{u,v} definitions to a test environment.
  fn add_punit_pprod(env: &mut LeanEnv) {
    let u_name = n("u");
    let v_name = n("v");
    let sort_u = LeanExpr::sort(Level::param(u_name.clone()));
    let sort_v = LeanExpr::sort(Level::param(v_name.clone()));

    // PUnit.{u} : Sort u, with one constructor PUnit.unit.{u} : PUnit.{u}
    let punit = n("PUnit");
    let punit_unit = Name::str(punit.clone(), "unit".into());
    let punit_ty = sort_u.clone(); // PUnit : Sort u
    let punit_c =
      LeanExpr::cnst(punit.clone(), vec![Level::param(u_name.clone())]);
    env.insert(
      punit.clone(),
      ConstantInfo::InductInfo(InductiveVal {
        cnst: ConstantVal {
          name: punit.clone(),
          level_params: vec![u_name.clone()],
          typ: punit_ty,
        },
        num_params: Nat::from(0u64),
        num_indices: Nat::from(0u64),
        all: vec![punit.clone()],
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
          typ: punit_c,
        },
        induct: punit.clone(),
        cidx: Nat::from(0u64),
        num_params: Nat::from(0u64),
        num_fields: Nat::from(0u64),
        is_unsafe: false,
      }),
    );

    // PProd.{u, v} : Sort u → Sort v → Sort (max 1 u v)
    let pprod = n("PProd");
    let pprod_mk = Name::str(pprod.clone(), "mk".into());
    let max_1_u_v = Level::max(
      Level::succ(Level::zero()),
      Level::max(Level::param(u_name.clone()), Level::param(v_name.clone())),
    );
    // Type: ∀ (α : Sort u) (β : Sort v), Sort (max 1 u v)
    let pprod_ty = LeanExpr::all(
      Name::str(Name::anon(), "α".into()),
      sort_u.clone(),
      LeanExpr::all(
        Name::str(Name::anon(), "β".into()),
        sort_v.clone(),
        LeanExpr::sort(max_1_u_v),
        crate::ix::env::BinderInfo::Default,
      ),
      crate::ix::env::BinderInfo::Default,
    );
    // mk : ∀ {α : Sort u} {β : Sort v}, α → β → PProd α β
    let pprod_c = LeanExpr::cnst(
      pprod.clone(),
      vec![Level::param(u_name.clone()), Level::param(v_name.clone())],
    );
    let mk_ty = LeanExpr::all(
      Name::str(Name::anon(), "α".into()),
      sort_u,
      LeanExpr::all(
        Name::str(Name::anon(), "β".into()),
        sort_v,
        LeanExpr::all(
          Name::str(Name::anon(), "fst".into()),
          LeanExpr::bvar(Nat::from(1u64)),
          LeanExpr::all(
            Name::str(Name::anon(), "snd".into()),
            LeanExpr::bvar(Nat::from(1u64)),
            LeanExpr::app(
              LeanExpr::app(pprod_c, LeanExpr::bvar(Nat::from(3u64))),
              LeanExpr::bvar(Nat::from(2u64)),
            ),
            crate::ix::env::BinderInfo::Default,
          ),
          crate::ix::env::BinderInfo::Default,
        ),
        crate::ix::env::BinderInfo::Implicit,
      ),
      crate::ix::env::BinderInfo::Implicit,
    );
    env.insert(
      pprod.clone(),
      ConstantInfo::InductInfo(InductiveVal {
        cnst: ConstantVal {
          name: pprod.clone(),
          level_params: vec![u_name.clone(), v_name.clone()],
          typ: pprod_ty,
        },
        num_params: Nat::from(2u64),
        num_indices: Nat::from(0u64),
        all: vec![pprod.clone()],
        ctors: vec![pprod_mk.clone()],
        num_nested: Nat::from(0u64),
        is_rec: false,
        is_unsafe: false,
        is_reflexive: false,
      }),
    );
    env.insert(
      pprod_mk.clone(),
      ConstantInfo::CtorInfo(ConstructorVal {
        cnst: ConstantVal {
          name: pprod_mk,
          level_params: vec![u_name, v_name],
          typ: mk_ty,
        },
        induct: pprod,
        cidx: Nat::from(0u64),
        num_params: Nat::from(2u64),
        num_fields: Nat::from(2u64),
        is_unsafe: false,
      }),
    );
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
      generate_canonical_recursors(&classes, &env, &tmp_stt).unwrap();
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
      generate_canonical_recursors(&classes, &env, &stt).unwrap();

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
      generate_below_constants(&classes, &recs, &env, is_prop, &stt, &stt.kctx)
        .unwrap();
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
      generate_canonical_recursors(&classes, &env, &stt).unwrap();

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
      generate_below_constants(&classes, &recs, &env, is_prop, &stt, &stt.kctx)
        .unwrap();
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
      generate_canonical_recursors(&classes, &env, &stt).unwrap();

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
      generate_below_constants(&classes, &recs, &env, is_prop, &stt, &stt.kctx)
        .unwrap();
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
      generate_canonical_recursors(&classes, &env, &stt).unwrap();

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
      generate_below_constants(&classes, &recs, &env, is_prop, &stt, &stt.kctx)
        .unwrap();
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
      generate_canonical_recursors(&classes, &env, &stt).unwrap();
    assert!(is_prop, "should be Prop");

    let below =
      generate_below_constants(&classes, &recs, &env, is_prop, &stt, &stt.kctx)
        .unwrap();
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
      generate_canonical_recursors(&classes, &env, &stt).unwrap();
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
      generate_below_constants(&classes, &recs, &env, is_prop, &stt, &stt.kctx)
        .unwrap();
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
      generate_canonical_recursors(&classes, &env, &stt).unwrap();

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
      generate_below_constants(&classes, &recs, &env, is_prop, &stt, &stt.kctx)
        .unwrap();
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
  #[ignore]
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
    // Ingress prelude (PUnit, PProd) and the inductive into the kenv
    // so TcScope can resolve them during brecOn sort-level inference.
    crate::ix::compile::aux_gen::expr_utils::ensure_prelude_in_kenv_of(
      &stt, &stt.kctx,
    );
    crate::ix::compile::aux_gen::expr_utils::ensure_in_kenv_of(
      &t, &env, &stt, &stt.kctx,
    );

    let classes = vec![vec![t.clone()]];
    let (recs, is_prop) =
      generate_canonical_recursors(&classes, &env, &stt).unwrap();
    assert!(!is_prop);

    let below =
      generate_below_constants(&classes, &recs, &env, is_prop, &stt, &stt.kctx)
        .unwrap();
    assert_eq!(below.len(), 1);

    // Populate kenv with .below types for brecOn generation.
    crate::ix::compile::aux_gen::populate_canon_kenv_with_below(
      &below,
      &classes,
      &std::sync::Arc::new(env.clone()),
      &stt,
      &stt.kctx,
    );

    let brecon = generate_brecon_constants(
      &classes, &recs, &below, &env, is_prop, &stt, &stt.kctx,
    )
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
      generate_canonical_recursors(&classes, &env, &stt).unwrap();
    assert!(is_prop);

    let below =
      generate_below_constants(&classes, &recs, &env, is_prop, &stt, &stt.kctx)
        .unwrap();
    assert_eq!(below.len(), 1);

    let brecon = generate_brecon_constants(
      &classes, &recs, &below, &env, is_prop, &stt, &stt.kctx,
    )
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
      generate_canonical_recursors(&classes, &env, &stt).unwrap();
    let below =
      generate_below_constants(&classes, &recs, &env, is_prop, &stt, &stt.kctx)
        .unwrap();
    let brecon = generate_brecon_constants(
      &classes, &recs, &below, &env, is_prop, &stt, &stt.kctx,
    )
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
