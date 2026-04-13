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
  _RecOn(AuxDef),
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

  // Only generate patches when collapse actually happened.
  if n_classes >= n_original {
    return Ok(patches);
  }

  // Phase 1: Generate canonical recursors.
  let (canonical_recs, is_prop) = recursor::generate_canonical_recursors(
    sorted_classes,
    lean_env,
    stt,
    None,
  )?;

  for (rec_name, rec_val) in &canonical_recs {
    // Register for all original names that map to this class.
    patches.insert(rec_name.clone(), PatchedConstant::Rec(rec_val.clone()));
  }

  // Phase 1b: Generate .casesOn definitions.
  // .casesOn is a definition that wraps .rec, stripping IH fields from minors
  // and replacing non-target motives with PUnit. Needed by .brecOn.eq which
  // uses casesOn-based proofs (via Lean's `cases` tactic).
  for (rec_name, rec_val) in &canonical_recs {
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

  // Phase 1c: .recOn and .noConfusion are deferred to call-site surgery.
  // The implementations exist in rec_on.rs and no_confusion.rs but are inactive.

  // Phase 2: Generate .below constants (if originals exist).
  {
    let first_class_name = &sorted_classes[0][0];
    let below_name = Name::str(first_class_name.clone(), "below".to_string());
    if lean_env.get(&below_name).is_some() {
      let below_consts = below::generate_below_constants(
        sorted_classes,
        &canonical_recs,
        lean_env,
        is_prop,
        Some(stt),
      )?;
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

      // Phase 3: Generate .brecOn constants (if originals exist).
      let brecon_name =
        Name::str(first_class_name.clone(), "brecOn".to_string());
      if lean_env.get(&brecon_name).is_some() {
        let brecon_consts = brecon::generate_brecon_constants(
          sorted_classes,
          &canonical_recs,
          &below_consts,
          lean_env,
          is_prop,
        )?;
        for d in brecon_consts {
          patches.insert(d.name.clone(), PatchedConstant::BRecOn(d));
        }
      }
    }
  }

  // Phase 4: .noConfusionType + .noConfusion — deferred to call-site surgery.
  // See comment in Phase 1b/1c above.

  // Register patches for non-representative names (alpha-collapsed aliases).
  let mut alias_patches: Vec<(Name, PatchedConstant)> = Vec::new();
  for class in sorted_classes {
    if class.len() <= 1 {
      continue;
    }
    let rep = &class[0];
    for alias in &class[1..] {
      // For each active suffix that has a patch for rep, register the same for alias.
      // Only .rec, .below, .brecOn are active; others deferred to call-site surgery.
      let suffixes = ["rec", "casesOn", "below", "brecOn"];
      for suffix in &suffixes {
        let rep_name = Name::str(rep.clone(), suffix.to_string());
        let alias_name = Name::str(alias.clone(), suffix.to_string());
        if let Some(patch) = patches.get(&rep_name) {
          // BelowIndc needs deep renaming (constructor names change too).
          // Other patches only need a shallow name swap.
          let aliased = match patch {
            PatchedConstant::BelowIndc(bi) => PatchedConstant::BelowIndc(
              below::rename_below_indc(bi, alias, rep, lean_env),
            ),
            _ => rename_patch(patch, &alias_name),
          };
          alias_patches.push((alias_name, aliased));
        }
      }
    }
  }
  for (name, patch) in alias_patches {
    patches.insert(name, patch);
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

/// Clone a PatchedConstant with a new name.
fn rename_patch(patch: &PatchedConstant, new_name: &Name) -> PatchedConstant {
  match patch {
    PatchedConstant::Rec(r) => {
      let mut r2 = r.clone();
      r2.cnst.name = new_name.clone();
      PatchedConstant::Rec(r2)
    },
    PatchedConstant::_RecOn(d) => {
      PatchedConstant::_RecOn(AuxDef { name: new_name.clone(), ..d.clone() })
    },
    PatchedConstant::CasesOn(d) => {
      PatchedConstant::CasesOn(AuxDef { name: new_name.clone(), ..d.clone() })
    },
    PatchedConstant::BelowDef(d) => {
      PatchedConstant::BelowDef(below::BelowDef {
        name: new_name.clone(),
        ..d.clone()
      })
    },
    PatchedConstant::BelowIndc(i) => {
      PatchedConstant::BelowIndc(below::BelowIndc {
        name: new_name.clone(),
        ..i.clone()
      })
    },
    PatchedConstant::BRecOn(d) => PatchedConstant::BRecOn(brecon::BRecOnDef {
      name: new_name.clone(),
      ..d.clone()
    }),
    PatchedConstant::_NoConfusionType(d) => {
      PatchedConstant::_NoConfusionType(AuxDef {
        name: new_name.clone(),
        ..d.clone()
      })
    },
    PatchedConstant::_NoConfusion(d) => PatchedConstant::_NoConfusion(AuxDef {
      name: new_name.clone(),
      ..d.clone()
    }),
  }
}
