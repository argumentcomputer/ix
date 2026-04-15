//! Canonical auxiliary generation for alpha-collapsed inductive blocks.
//!
//! When `sort_consts` collapses N mutual inductives into fewer equivalence
//! classes, Lean's auto-generated auxiliaries (`.rec`, `.recOn`, `.casesOn`,
//! `.below`, `.brecOn`, `.noConfusion`, etc.) have the wrong arity. Rather
//! than surgically patching them (fragile, source-order dependent), we
//! regenerate them from the canonical class structure.
//!
//! Only generates an auxiliary if the original Lean constant exists in the
//! environment — correctly handles bootstrap-early types (e.g., Eq has no .below).

pub(crate) mod below;
pub(crate) mod brecon;
pub(crate) mod cases_on;
pub(crate) mod expr_utils;
pub(crate) mod nested;
pub(crate) mod no_confusion;
pub(crate) mod rec_on;
pub(crate) mod recursor;

use std::sync::Arc;

use rustc_hash::FxHashMap;

use crate::ix::compile::CompileState;
use crate::ix::env::{Env as LeanEnv, Expr as LeanExpr, Name, RecursorVal};
use crate::ix::ixon::CompileError;
use crate::ix::mutual::MutConst;

/// A regenerated constant ready for compilation.
#[derive(Clone)]
pub(crate) enum PatchedConstant {
  /// A regenerated `.rec` recursor.
  Rec(RecursorVal),
  /// A regenerated `.recOn` definition (arg-reordered `.rec` wrapper).
  RecOn(AuxDef),
  /// A regenerated `.casesOn` definition (`.rec` wrapper without inductive hypotheses).
  CasesOn(AuxDef),
  /// A regenerated `.below` definition (Type-level case).
  BelowDef(below::BelowDef),
  /// A regenerated `.below` inductive (Prop-level case).
  BelowIndc(below::BelowIndc),
  /// A regenerated `.brecOn` (or `.brecOn.go`, `.brecOn.eq`) definition.
  BRecOn(brecon::BRecOnDef),
  /// A regenerated `.noConfusionType` definition.
  _NoConfusionType(AuxDef),
  /// A regenerated `.noConfusion` definition.
  _NoConfusion(AuxDef),
}

/// A simple auxiliary definition (type + value + level params).
#[derive(Clone)]
pub(crate) struct AuxDef {
  pub name: Name,
  pub level_params: Vec<Name>,
  pub typ: LeanExpr,
  pub value: LeanExpr,
}

/// Generate all canonical auxiliary patches for a collapsed inductive block.
///
/// Called from `compile_mutual` after `sort_consts` determines the canonical
/// classes. Returns a map from auxiliary name -> regenerated constant.
///
/// Only generates patches when alpha-collapse or SCC-splitting actually
/// changes the block structure. Each auxiliary is only generated if the
/// original Lean constant exists in the environment.
pub(crate) fn generate_aux_patches(
  sorted_classes: &[Vec<Name>],
  original_cs: &[MutConst],
  lean_env: &Arc<LeanEnv>,
  stt: &CompileState,
  kctx: &crate::ix::compile::KernelCtx,
) -> Result<FxHashMap<Name, PatchedConstant>, CompileError> {
  let mut patches: FxHashMap<Name, PatchedConstant> = FxHashMap::default();

  // Collect the original inductive names from the mutual block.
  let original_all: Vec<Name> = original_cs
    .iter()
    .find_map(|c| match c {
      MutConst::Indc(ind) => Some(ind.ind.all.clone()),
      _ => None,
    })
    .unwrap_or_default();

  if original_all.is_empty() {
    return Ok(patches);
  }

  let n_original = original_all.len();
  let n_classes = sorted_classes.len();

  let has_nested = original_all.iter().any(|name| {
    matches!(
      lean_env.get(name),
      Some(crate::ix::env::ConstantInfo::InductInfo(v))
        if v.num_nested.to_u64().unwrap_or(0) > 0
    )
  });

  // Ensure PUnit and PProd are in kenv BEFORE any ingress (Phase 1) runs.
  // ingress_field_deps may encounter PProd in constructor field types and
  // would insert it as a bare Axio stub; the hardcoded Indc definitions
  // here are authoritative and must be present first.
  expr_utils::ensure_prelude_in_kenv_of(stt, kctx);

  // Phase 1: Generate canonical recursors.
  let _p1_start = std::time::Instant::now();
  let (canonical_recs, is_prop) =
    recursor::generate_canonical_recursors_with_overlay(
      sorted_classes,
      lean_env,
      None,
      stt,
      kctx,
    )?;
  let _p1_elapsed = _p1_start.elapsed();

  for (rec_name, rec_val) in &canonical_recs {
    // Only emit .rec if the original Lean env has it (some inductives,
    // e.g. structures, may not have .rec in the exported env subset).
    if lean_env.get(rec_name).is_some() {
      patches.insert(rec_name.clone(), PatchedConstant::Rec(rec_val.clone()));
    }
  }

  // Phase 1b: Generate .casesOn definitions.
  // .casesOn is a definition that wraps .rec, stripping IH fields from minors
  // and replacing non-target motives with PUnit. Needed by .brecOn.eq which
  // uses casesOn-based proofs (via Lean's `cases` tactic).
  //
  // Only generate for original recursors (first n_classes), not auxiliary rec_N.
  // This is intentional: Lean does NOT generate casesOn_N for nested auxiliary
  // types (unlike below_N/brecOn_N which ARE generated via BRecOn.lean).
  for (rec_name, rec_val) in canonical_recs.iter().take(n_classes) {
    // Build casesOn name: rec_name is "I.rec", casesOn name is "I.casesOn"
    let ind_name = match rec_name.as_data() {
      crate::ix::env::NameData::Str(parent, _, _) => parent.clone(),
      _ => continue,
    };
    let cases_on_name = Name::str(ind_name, "casesOn".to_string());
    // Only generate if the original env has this constant.
    if lean_env.get(&cases_on_name).is_some()
      && let Some(aux_def) =
        cases_on::generate_cases_on(&cases_on_name, rec_val, lean_env)
    {
      patches.insert(cases_on_name, PatchedConstant::CasesOn(aux_def));
    }
  }

  // Phase 1c: Generate .recOn definitions (arg-reordered .rec wrapper).
  //
  // Only generate for original recursors (first n_classes), not auxiliary rec_N.
  // This is intentional: Lean does NOT generate recOn_N for nested auxiliary
  // types (unlike below_N/brecOn_N which ARE generated via BRecOn.lean).
  for (rec_name, rec_val) in canonical_recs.iter().take(n_classes) {
    let ind_name = match rec_name.as_data() {
      crate::ix::env::NameData::Str(parent, _, _) => parent.clone(),
      _ => continue,
    };
    let rec_on_name = Name::str(ind_name, "recOn".to_string());
    if lean_env.get(&rec_on_name).is_some()
      && let Some(aux_def) = rec_on::generate_rec_on(&rec_on_name, rec_val)
    {
      patches.insert(rec_on_name, PatchedConstant::RecOn(aux_def));
    }
  }

  // Phase 2: Generate .below constants (if originals exist).
  let _p2_start = std::time::Instant::now();
  {
    let first_class_name = &sorted_classes[0][0];
    let below_name = Name::str(first_class_name.clone(), "below".to_string());
    if lean_env.get(&below_name).is_some() {
      let _bt = std::time::Instant::now();
      let below_consts = below::generate_below_constants(
        sorted_classes,
        &canonical_recs,
        lean_env,
        is_prop,
        Some(stt),
      )?;
      let _below_elapsed = _bt.elapsed();
      for bc in &below_consts {
        match bc {
          below::BelowConstant::Def(d) => {
            patches
              .insert(d.name.clone(), PatchedConstant::BelowDef(d.clone()));
          },
          below::BelowConstant::Indc(i) => {
            patches
              .insert(i.name.clone(), PatchedConstant::BelowIndc(i.clone()));
          },
        }
      }

      // Populate canon_kenv with canonical .below types for Phase 3.
      // The canonical TC needs these to infer PProd(motive, I.below ...)
      // during brecOn generation. We insert the regenerated types (which
      // match the alpha-collapsed block structure), not the originals.
      populate_canon_kenv_with_below(
        &below_consts,
        sorted_classes,
        lean_env,
        stt,
        kctx,
      );

      // Phase 3: Generate .brecOn constants (if originals exist).
      let brecon_name =
        Name::str(first_class_name.clone(), "brecOn".to_string());
      if lean_env.get(&brecon_name).is_some() {
        let _brt = std::time::Instant::now();
        let brecon_consts = brecon::generate_brecon_constants(
          sorted_classes,
          &canonical_recs,
          &below_consts,
          lean_env,
          is_prop,
          stt,
          kctx,
        )?;
        let _brecon_elapsed = _brt.elapsed();
        for d in brecon_consts {
          // Only emit if the original Lean env has this constant
          // (e.g. .brecOn.eq may not be in the exported env subset).
          if lean_env.get(&d.name).is_some() {
            patches.insert(d.name.clone(), PatchedConstant::BRecOn(d));
          }
        }

        let _gen_label = sorted_classes
          .first()
          .and_then(|c| c.first())
          .map(|n| n.pretty())
          .unwrap_or_default();
        if _below_elapsed.as_secs_f32() + _brecon_elapsed.as_secs_f32() > 0.3 {
          eprintln!(
            "[gen_patches_detail] {:?} belowGen={:.2}s breconGen={:.2}s",
            _gen_label,
            _below_elapsed.as_secs_f32(),
            _brecon_elapsed.as_secs_f32(),
          );
        }
      }
    }
  }

  let _gen_label = sorted_classes
    .first()
    .and_then(|c| c.first())
    .map(|n| n.pretty())
    .unwrap_or_default();
  if _p1_elapsed.as_secs_f32() > 0.5 {
    eprintln!(
      "[gen_patches] {:?} recGen={:.2}s patches={}",
      _gen_label,
      _p1_elapsed.as_secs_f32(),
      patches.len(),
    );
  }

  // Phase 4: .noConfusionType + .noConfusion — deferred to call-site surgery.
  // See comment in Phase 1b/1c above.

  // Register patches for non-representative names (alpha-collapsed aliases).
  // Each alias gets deep-renamed: internal Const references to the
  // representative's auxiliaries are rewritten to reference the alias's own.
  let mut alias_patches: Vec<(Name, PatchedConstant)> = Vec::new();
  for class in sorted_classes {
    if class.len() <= 1 {
      continue;
    }
    let rep = &class[0];
    for alias in &class[1..] {
      // Build the rep→alias name map for deep renaming.
      let name_map = build_alias_name_map(rep, alias, lean_env);

      // For each active suffix that has a patch for rep, register the same for alias.
      let suffixes = ["rec", "recOn", "casesOn", "below", "brecOn"];
      for suffix in &suffixes {
        let rep_name = Name::str(rep.clone(), suffix.to_string());
        let alias_name = Name::str(alias.clone(), suffix.to_string());
        if let Some(patch) = patches.get(&rep_name) {
          // BelowIndc needs structural renaming (constructor names in the
          // BelowCtor structs change too, not just expression-level Consts).
          let aliased = match patch {
            PatchedConstant::BelowIndc(bi) => PatchedConstant::BelowIndc(
              below::rename_below_indc(bi, alias, rep, lean_env),
            ),
            _ => rename_patch(patch, &alias_name, &name_map),
          };
          alias_patches.push((alias_name, aliased));
        }
      }
      // Also .brecOn.go and .brecOn.eq — sub-names of brecOn that are
      // generated for Type-level inductives by build_type_brecon_fvar.
      for sub in &["go", "eq"] {
        let rep_base = Name::str(rep.clone(), "brecOn".to_string());
        let alias_base = Name::str(alias.clone(), "brecOn".to_string());
        let rep_name = Name::str(rep_base, sub.to_string());
        let alias_name = Name::str(alias_base, sub.to_string());
        if let Some(patch) = patches.get(&rep_name) {
          let aliased = rename_patch(patch, &alias_name, &name_map);
          alias_patches.push((alias_name, aliased));
        }
      }

      // Note: _N suffixed names (rec_1, below_1, brecOn_1, etc.) are NOT
      // aliased here. They always hang off all[0] (the first inductive in
      // source order), not per-class-representative. There is no TreeB.rec_1
      // in Lean — only TreeA.rec_1.
    }
  }
  for (name, patch) in alias_patches {
    patches.insert(name, patch);
  }

  // Register original-order auxiliary aliases. When alpha-collapse merges
  // inductives, the original Lean block (.all) may have MORE nested
  // auxiliaries than the canonical block. E.g., {RoseA, RoseB} in .all
  // discovers List(RoseA α) + List(RoseB α) → rec_1, rec_2. But after
  // alpha-collapse to {RoseA}, the canonical flat block has only List(RoseA α)
  // → rec_1. We need rec_2 to alias to the canonical rec_1.
  //
  // The mapping is built by matching each original auxiliary's
  // (ext_ind_name, normalized_spec_params) against the canonical auxiliaries.
  // Normalization substitutes original names with their class representatives
  // so that List(RoseB α) matches List(RoseA α).
  if has_nested {
    let n_canonical_aux = canonical_recs.len().saturating_sub(n_classes);
    let original_flat =
      nested::build_compile_flat_block(&original_all, lean_env);
    let n_original_aux = original_flat.len().saturating_sub(n_original);

    if n_original_aux > 0 && n_canonical_aux > 0 {
      // Lean hangs _N suffixed names off all[0] (first in source order).
      let first_orig_name = &original_all[0];
      // Canonical _N names also use all[0] (via below.rs/brecon.rs fix).
      let canon_first = first_orig_name;

      // Build name substitution: original name → canonical class representative.
      let orig_to_canon_names: std::collections::HashMap<Name, Name> =
        sorted_classes
          .iter()
          .flat_map(|class| {
            let rep = &class[0];
            class.iter().map(move |name| (name.clone(), rep.clone()))
          })
          .collect();

      // Build canonical flat block for matching.
      let canonical_names: Vec<Name> =
        sorted_classes.iter().map(|c| c[0].clone()).collect();
      let canonical_flat =
        nested::build_compile_flat_block(&canonical_names, lean_env);

      // Map each original auxiliary to its canonical match.
      for oj in 0..n_original_aux {
        let orig_aux = &original_flat[n_original + oj];
        let orig_idx = oj + 1; // 1-based

        // Normalize original spec_params: replace original names with
        // canonical representatives.
        let normalized_specs: Vec<LeanExpr> = orig_aux
          .spec_params
          .iter()
          .map(|sp| expr_utils::replace_const_names(sp, &orig_to_canon_names))
          .collect();

        // Find matching canonical auxiliary by (ext_ind_name, spec_params hash).
        let canon_match = canonical_flat[n_classes..].iter().enumerate().find(
          |(_, canon_aux)| {
            canon_aux.name == orig_aux.name
              && canon_aux.spec_params.len() == normalized_specs.len()
              && canon_aux
                .spec_params
                .iter()
                .zip(normalized_specs.iter())
                .all(|(a, b)| a.get_hash() == b.get_hash())
          },
        );

        let Some((cj, _)) = canon_match else {
          // No canonical match — this auxiliary references inductives
          // outside the current SCC (cross-SCC case). Don't insert as
          // a patch — let the scheduler compile it normally from lean_env
          // once all deps (including the external SCC) are available.
          continue;
        };
        let canon_idx = cj + 1; // 1-based

        // Alias original _N names to canonical _N patches.
        // These only rename the _N suffix — both share the same parent
        // inductive (canon_first == first_orig_name), so no internal
        // Const rewriting is needed.
        let empty_map = std::collections::HashMap::new();
        for suffix in &["rec", "below", "brecOn"] {
          let orig_name =
            Name::str(first_orig_name.clone(), format!("{suffix}_{orig_idx}"));
          if patches.contains_key(&orig_name) {
            continue; // Already generated canonically.
          }
          let canon_name =
            Name::str(canon_first.clone(), format!("{suffix}_{canon_idx}"));
          if let Some(patch) = patches.get(&canon_name) {
            let aliased = rename_patch(patch, &orig_name, &empty_map);
            patches.insert(orig_name, aliased);
          }
        }
        // Also .brecOn_N.go and .brecOn_N.eq
        for sub in &["go", "eq"] {
          let orig_base =
            Name::str(first_orig_name.clone(), format!("brecOn_{orig_idx}"));
          let orig_name = Name::str(orig_base, sub.to_string());
          if patches.contains_key(&orig_name) {
            continue;
          }
          let canon_base =
            Name::str(canon_first.clone(), format!("brecOn_{canon_idx}"));
          let canon_name = Name::str(canon_base, sub.to_string());
          if let Some(patch) = patches.get(&canon_name) {
            let aliased = rename_patch(patch, &orig_name, &empty_map);
            patches.insert(orig_name, aliased);
          }
        }
      }
    }
  }

  Ok(patches)
}

/// Extract the parent prefix from a Name.
/// E.g., `A.rec` → `A`, `A.below` → `A`.
fn _name_parent(name: &Name) -> Name {
  match name.as_data() {
    crate::ix::env::NameData::Str(parent, _, _)
    | crate::ix::env::NameData::Num(parent, _, _) => parent.clone(),
    crate::ix::env::NameData::Anonymous(_) => Name::anon(),
  }
}

/// Build a name substitution map for aliasing `rep` → `alias`.
///
/// Covers the inductive itself, its constructors (positional mapping),
/// and all known auxiliary suffixes. This ensures `replace_const_names`
/// rewrites all internal Const references when creating alias patches.
fn build_alias_name_map(
  rep: &Name,
  alias: &Name,
  lean_env: &Arc<LeanEnv>,
) -> std::collections::HashMap<Name, Name> {
  let mut map = std::collections::HashMap::new();

  // Inductive name itself.
  map.insert(rep.clone(), alias.clone());

  // Constructor names: positional mapping rep.ctor_i → alias.ctor_i.
  let rep_ctors = match lean_env.get(rep) {
    Some(crate::ix::env::ConstantInfo::InductInfo(v)) => v.ctors.clone(),
    _ => vec![],
  };
  let alias_ctors = match lean_env.get(alias) {
    Some(crate::ix::env::ConstantInfo::InductInfo(v)) => v.ctors.clone(),
    _ => vec![],
  };
  for (rc, ac) in rep_ctors.iter().zip(alias_ctors.iter()) {
    map.insert(rc.clone(), ac.clone());
  }

  // Auxiliary suffixes.
  for suffix in &[
    "rec",
    "recOn",
    "casesOn",
    "below",
    "brecOn",
    "noConfusionType",
    "noConfusion",
  ] {
    map.insert(
      Name::str(rep.clone(), suffix.to_string()),
      Name::str(alias.clone(), suffix.to_string()),
    );
  }

  // Sub-names of brecOn.
  for sub in &["go", "eq"] {
    let rep_sub =
      Name::str(Name::str(rep.clone(), "brecOn".to_string()), sub.to_string());
    let alias_sub = Name::str(
      Name::str(alias.clone(), "brecOn".to_string()),
      sub.to_string(),
    );
    map.insert(rep_sub, alias_sub);
  }

  // Below constructor names (for Prop-level .below inductives).
  let rep_below = Name::str(rep.clone(), "below".to_string());
  let alias_below = Name::str(alias.clone(), "below".to_string());
  map.insert(rep_below.clone(), alias_below.clone());
  // Map positional .below constructors: Rep.below.ctor_suffix → Alias.below.ctor_suffix.
  for (rc, ac) in rep_ctors.iter().zip(alias_ctors.iter()) {
    if let Some(rc_suffix) = rc.strip_prefix(rep) {
      let rep_bc = rep_below.append_components(&rc_suffix);
      let alias_bc = alias_below.append_components(
        &ac.strip_prefix(alias).unwrap_or_else(|| ac.components()),
      );
      map.insert(rep_bc, alias_bc);
    }
  }

  map
}

/// Clone a PatchedConstant with a new name, rewriting internal Const
/// references via `name_map`.
fn rename_patch(
  patch: &PatchedConstant,
  new_name: &Name,
  name_map: &std::collections::HashMap<Name, Name>,
) -> PatchedConstant {
  match patch {
    PatchedConstant::Rec(r) => {
      let mut r2 = r.clone();
      r2.cnst.name = new_name.clone();
      r2.cnst.typ = expr_utils::replace_const_names(&r2.cnst.typ, name_map);
      for rule in &mut r2.rules {
        if let Some(new_ctor) = name_map.get(&rule.ctor) {
          rule.ctor = new_ctor.clone();
        }
        rule.rhs = expr_utils::replace_const_names(&rule.rhs, name_map);
      }
      // Rewrite the `all` list.
      r2.all = r2
        .all
        .iter()
        .map(|n| name_map.get(n).cloned().unwrap_or_else(|| n.clone()))
        .collect();
      PatchedConstant::Rec(r2)
    },
    PatchedConstant::RecOn(d) => PatchedConstant::RecOn(AuxDef {
      name: new_name.clone(),
      level_params: d.level_params.clone(),
      typ: expr_utils::replace_const_names(&d.typ, name_map),
      value: expr_utils::replace_const_names(&d.value, name_map),
    }),
    PatchedConstant::CasesOn(d) => PatchedConstant::CasesOn(AuxDef {
      name: new_name.clone(),
      level_params: d.level_params.clone(),
      typ: expr_utils::replace_const_names(&d.typ, name_map),
      value: expr_utils::replace_const_names(&d.value, name_map),
    }),
    PatchedConstant::BelowDef(d) => {
      PatchedConstant::BelowDef(below::BelowDef {
        name: new_name.clone(),
        level_params: d.level_params.clone(),
        typ: expr_utils::replace_const_names(&d.typ, name_map),
        value: expr_utils::replace_const_names(&d.value, name_map),
      })
    },
    PatchedConstant::BelowIndc(i) => {
      // BelowIndc is handled by rename_below_indc at the call site.
      // This arm is a fallback — just rename the name.
      PatchedConstant::BelowIndc(below::BelowIndc {
        name: new_name.clone(),
        ..i.clone()
      })
    },
    PatchedConstant::BRecOn(d) => PatchedConstant::BRecOn(brecon::BRecOnDef {
      name: new_name.clone(),
      level_params: d.level_params.clone(),
      typ: expr_utils::replace_const_names(&d.typ, name_map),
      value: expr_utils::replace_const_names(&d.value, name_map),
    }),
    PatchedConstant::_NoConfusionType(d) => {
      PatchedConstant::_NoConfusionType(AuxDef {
        name: new_name.clone(),
        level_params: d.level_params.clone(),
        typ: expr_utils::replace_const_names(&d.typ, name_map),
        value: expr_utils::replace_const_names(&d.value, name_map),
      })
    },
    PatchedConstant::_NoConfusion(d) => PatchedConstant::_NoConfusion(AuxDef {
      name: new_name.clone(),
      level_params: d.level_params.clone(),
      typ: expr_utils::replace_const_names(&d.typ, name_map),
      value: expr_utils::replace_const_names(&d.value, name_map),
    }),
  }
}

/// Populate `stt.canon_kenv` with canonical `.below` types and their
/// dependencies (parent inductives, constructors, PUnit, PProd).
///
/// The canonical `.below` types match the alpha-collapsed block structure
/// and may differ from the originals in `lean_env`. The canonical TC
/// (`stt.canon_tc`) uses `canon_kenv` exclusively, so it sees the
/// correct types for PProd(motive, I.below ...) inference.
pub(crate) fn populate_canon_kenv_with_below(
  below_consts: &[below::BelowConstant],
  sorted_classes: &[Vec<Name>],
  lean_env: &std::sync::Arc<crate::ix::env::Env>,
  stt: &crate::ix::compile::CompileState,
  kctx: &crate::ix::compile::KernelCtx,
) {
  use crate::ix::kernel::constant::KConst;
  use crate::ix::kernel::id::KId;
  use crate::ix::kernel::ingress::{
    lean_expr_to_zexpr_with_kenv, resolve_lean_name_addr,
  };

  let n2a = Some(&stt.name_to_addr);
  let aux_n2a = Some(&stt.aux_name_to_addr);
  let canon = &kctx.kenv;

  // Ensure PUnit and PProd are in kenv.
  expr_utils::ensure_prelude_in_kenv_of(stt, kctx);

  // Ensure parent inductives (and their constructors) are in canon_kenv.
  // The .below types reference these in their motive/major domains.
  for class in sorted_classes {
    let rep = &class[0];
    expr_utils::ensure_in_kenv_of(rep, lean_env, stt, kctx);
  }

  // Insert canonical .below definitions/inductives.
  for bc in below_consts {
    match bc {
      below::BelowConstant::Def(d) => {
        let addr = resolve_lean_name_addr(&d.name, n2a, aux_n2a);
        let zid = KId::new(addr, d.name.clone());
        let ty_z = lean_expr_to_zexpr_with_kenv(
          &d.typ,
          &d.level_params,
          &kctx.kenv,
          n2a,
          aux_n2a,
        );
        let val_z = lean_expr_to_zexpr_with_kenv(
          &d.value,
          &d.level_params,
          &kctx.kenv,
          n2a,
          aux_n2a,
        );
        canon.insert(
          zid.clone(),
          KConst::Defn {
            name: d.name.clone(),
            level_params: d.level_params.clone(),
            kind: crate::ix::ixon::constant::DefKind::Definition,
            safety: crate::ix::env::DefinitionSafety::Safe,
            hints: crate::ix::env::ReducibilityHints::Abbrev,
            lvls: d.level_params.len() as u64,
            ty: ty_z,
            val: val_z,
            lean_all: vec![],
            block: zid,
          },
        );
      },
      below::BelowConstant::Indc(i) => {
        let addr = resolve_lean_name_addr(&i.name, n2a, aux_n2a);
        let zid = KId::new(addr, i.name.clone());
        let ty_z = lean_expr_to_zexpr_with_kenv(
          &i.typ,
          &i.level_params,
          &kctx.kenv,
          n2a,
          aux_n2a,
        );
        let mut ctor_zids = Vec::new();
        for ctor in &i.ctors {
          let ctor_addr = resolve_lean_name_addr(&ctor.name, n2a, aux_n2a);
          let ctor_zid = KId::new(ctor_addr, ctor.name.clone());
          let ctor_ty_z = lean_expr_to_zexpr_with_kenv(
            &ctor.typ,
            &i.level_params,
            &kctx.kenv,
            n2a,
            aux_n2a,
          );
          canon.insert(
            ctor_zid.clone(),
            KConst::Ctor {
              name: ctor.name.clone(),
              level_params: i.level_params.clone(),
              is_unsafe: false,
              lvls: i.level_params.len() as u64,
              induct: zid.clone(),
              cidx: ctor_zids.len() as u64,
              params: ctor.n_params as u64,
              fields: ctor.n_fields as u64,
              ty: ctor_ty_z,
            },
          );
          ctor_zids.push(ctor_zid);
        }
        canon.insert(
          zid.clone(),
          KConst::Indc {
            name: i.name.clone(),
            level_params: i.level_params.clone(),
            lvls: i.level_params.len() as u64,
            params: i.n_params as u64,
            indices: i.n_indices as u64,
            is_rec: false,
            is_refl: false,
            is_unsafe: false,
            ctors: ctor_zids,
            ty: ty_z,
            block: zid,
            nested: 0,
            member_idx: 0,
            lean_all: vec![],
          },
        );
      },
    }
  }
}
