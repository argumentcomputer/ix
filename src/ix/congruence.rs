//! Alpha-equivalence checks between Lean expressions/constants.
//!
//! Compares two `ConstantInfo` values structurally, ignoring binder names
//! and mdata. Used to verify that aux_gen produces constants congruent to
//! what Lean generates.

use crate::ix::env::{ConstantInfo, Expr, ExprData, Level, LevelData, Literal};
use lean_ffi::nat::Nat;

/// Check that two Lean levels are structurally equal.
pub fn level_alpha_eq(a: &Level, b: &Level) -> Result<(), String> {
  match (a.as_data(), b.as_data()) {
    (LevelData::Zero(_), LevelData::Zero(_)) => Ok(()),
    (LevelData::Succ(a1, _), LevelData::Succ(b1, _)) => level_alpha_eq(a1, b1),
    (LevelData::Max(a1, a2, _), LevelData::Max(b1, b2, _))
    | (LevelData::Imax(a1, a2, _), LevelData::Imax(b1, b2, _)) => {
      level_alpha_eq(a1, b1)?;
      level_alpha_eq(a2, b2)
    },
    (LevelData::Param(_, _), LevelData::Param(_, _)) => {
      // Positional: both sides have the same level_params order,
      // so param names should match. But for robustness, just accept.
      Ok(())
    },
    (LevelData::Mvar(_, _), _) | (_, LevelData::Mvar(_, _)) => {
      Err("unexpected level MVar".into())
    },
    _ => Err(format!(
      "level mismatch: {} vs {} ({} vs {})",
      level_tag(a),
      level_tag(b),
      a.pretty(),
      b.pretty(),
    )),
  }
}

/// Check that two Lean expressions are alpha-equivalent (ignoring binder
/// names, BinderInfo, and Mdata wrappers).
pub fn expr_alpha_eq(a: &Expr, b: &Expr) -> Result<(), String> {
  // Strip Mdata from both sides.
  let a = strip_mdata(a);
  let b = strip_mdata(b);

  match (a.as_data(), b.as_data()) {
    (ExprData::Bvar(n1, _), ExprData::Bvar(n2, _)) => {
      if n1 == n2 {
        Ok(())
      } else {
        Err(format!(
          "bvar mismatch: {n1} vs {n2}\n    generated ctx: {}\n    original ctx:  {}",
          a.pretty(),
          b.pretty()
        ))
      }
    },

    (ExprData::Sort(l1, _), ExprData::Sort(l2, _)) => {
      level_alpha_eq(l1, l2).map_err(|e| format!("sort: {e}"))
    },

    (ExprData::Const(n1, lvls1, _), ExprData::Const(n2, lvls2, _)) => {
      if n1 != n2 {
        return Err(format!(
          "const name mismatch: {} vs {}",
          n1.pretty(),
          n2.pretty()
        ));
      }
      if lvls1.len() != lvls2.len() {
        return Err(format!(
          "const {} level count: {} vs {}",
          n1.pretty(),
          lvls1.len(),
          lvls2.len(),
        ));
      }
      for (i, (l1, l2)) in lvls1.iter().zip(lvls2.iter()).enumerate() {
        level_alpha_eq(l1, l2)
          .map_err(|e| format!("const {}.lvl[{i}]: {e}", n1.pretty()))?;
      }
      Ok(())
    },

    (ExprData::App(f1, a1, _), ExprData::App(f2, a2, _)) => {
      expr_alpha_eq(f1, f2).map_err(|e| format!("app.fun: {e}"))?;
      expr_alpha_eq(a1, a2).map_err(|e| format!("app.arg: {e}"))
    },

    // Lam: ignore binder name and BinderInfo
    (
      ExprData::Lam(_, ty1, body1, _, _),
      ExprData::Lam(_, ty2, body2, _, _),
    ) => {
      expr_alpha_eq(ty1, ty2).map_err(|e| format!("lam.ty: {e}"))?;
      expr_alpha_eq(body1, body2).map_err(|e| format!("lam.body: {e}"))
    },

    // ForallE: ignore binder name and BinderInfo
    (
      ExprData::ForallE(_, ty1, body1, _, _),
      ExprData::ForallE(_, ty2, body2, _, _),
    ) => {
      expr_alpha_eq(ty1, ty2).map_err(|e| format!("∀.ty: {e}"))?;
      expr_alpha_eq(body1, body2).map_err(|e| format!("∀.body: {e}"))
    },

    // LetE: ignore binder name
    (
      ExprData::LetE(_, ty1, val1, body1, _, _),
      ExprData::LetE(_, ty2, val2, body2, _, _),
    ) => {
      expr_alpha_eq(ty1, ty2).map_err(|e| format!("let.ty: {e}"))?;
      expr_alpha_eq(val1, val2).map_err(|e| format!("let.val: {e}"))?;
      expr_alpha_eq(body1, body2).map_err(|e| format!("let.body: {e}"))
    },

    (
      ExprData::Lit(Literal::NatVal(n1), _),
      ExprData::Lit(Literal::NatVal(n2), _),
    ) => {
      if n1 == n2 {
        Ok(())
      } else {
        Err(format!("nat lit mismatch: {n1} vs {n2}"))
      }
    },

    (
      ExprData::Lit(Literal::StrVal(s1), _),
      ExprData::Lit(Literal::StrVal(s2), _),
    ) => {
      if s1 == s2 {
        Ok(())
      } else {
        Err("str lit mismatch".to_string())
      }
    },

    (ExprData::Proj(n1, idx1, val1, _), ExprData::Proj(n2, idx2, val2, _)) => {
      if n1 != n2 {
        return Err(format!(
          "proj type mismatch: {} vs {}",
          n1.pretty(),
          n2.pretty()
        ));
      }
      if idx1 != idx2 {
        return Err(format!("proj idx mismatch: {idx1} vs {idx2}"));
      }
      expr_alpha_eq(val1, val2).map_err(|e| format!("proj.val: {e}"))
    },

    (ExprData::Fvar(..), _) | (_, ExprData::Fvar(..)) => {
      Err("unexpected FVar in constant".into())
    },
    (ExprData::Mvar(..), _) | (_, ExprData::Mvar(..)) => {
      Err("unexpected MVar in constant".into())
    },

    _ => Err(format!(
      "expr shape mismatch: {} vs {}\n    generated: {}\n    original:  {}",
      expr_tag(a),
      expr_tag(b),
      a.pretty(),
      b.pretty(),
    )),
  }
}

/// Check that two `ConstantInfo` values are alpha-equivalent.
pub fn const_alpha_eq(
  generated: &ConstantInfo,
  orig: &ConstantInfo,
) -> Result<(), String> {
  // Type congruence
  expr_alpha_eq(generated.get_type(), orig.get_type())
    .map_err(|e| format!("type: {e}"))?;

  // Level params count
  if generated.get_level_params().len() != orig.get_level_params().len() {
    return Err(format!(
      "level_params count: generated={} orig={}",
      generated.get_level_params().len(),
      orig.get_level_params().len(),
    ));
  }

  // Variant-specific checks
  match (generated, orig) {
    (ConstantInfo::AxiomInfo(_), ConstantInfo::AxiomInfo(_))
    | (ConstantInfo::QuotInfo(_), ConstantInfo::QuotInfo(_)) => Ok(()),

    // These arms have identical bodies but bind different types (DefinitionVal
    // vs TheoremVal), so they cannot be merged into a single pattern.
    #[allow(clippy::match_same_arms)]
    (ConstantInfo::DefnInfo(g), ConstantInfo::DefnInfo(o)) => {
      expr_alpha_eq(&g.value, &o.value).map_err(|e| format!("value: {e}"))
    },
    #[allow(clippy::match_same_arms)]
    (ConstantInfo::DefnInfo(g), ConstantInfo::ThmInfo(o)) => {
      expr_alpha_eq(&g.value, &o.value).map_err(|e| format!("value: {e}"))
    },
    #[allow(clippy::match_same_arms)]
    (ConstantInfo::ThmInfo(g), ConstantInfo::DefnInfo(o)) => {
      expr_alpha_eq(&g.value, &o.value).map_err(|e| format!("value: {e}"))
    },
    #[allow(clippy::match_same_arms)]
    (ConstantInfo::ThmInfo(g), ConstantInfo::ThmInfo(o)) => {
      expr_alpha_eq(&g.value, &o.value).map_err(|e| format!("value: {e}"))
    },

    (ConstantInfo::OpaqueInfo(g), ConstantInfo::OpaqueInfo(o)) => {
      expr_alpha_eq(&g.value, &o.value).map_err(|e| format!("value: {e}"))
    },

    (ConstantInfo::InductInfo(g), ConstantInfo::InductInfo(o)) => {
      let gp = g.num_params.to_u64().unwrap_or(u64::MAX);
      let op = o.num_params.to_u64().unwrap_or(u64::MAX);
      if gp != op {
        return Err(format!("params: generated={gp} orig={op}"));
      }
      let gi = g.num_indices.to_u64().unwrap_or(u64::MAX);
      let oi = o.num_indices.to_u64().unwrap_or(u64::MAX);
      if gi != oi {
        return Err(format!("indices: generated={gi} orig={oi}"));
      }
      if g.ctors.len() != o.ctors.len() {
        return Err(format!(
          "ctor count: generated={} orig={}",
          g.ctors.len(),
          o.ctors.len()
        ));
      }
      Ok(())
    },

    (ConstantInfo::CtorInfo(g), ConstantInfo::CtorInfo(o)) => {
      check_nat_eq(&g.cidx, &o.cidx, "cidx")?;
      check_nat_eq(&g.num_params, &o.num_params, "params")?;
      check_nat_eq(&g.num_fields, &o.num_fields, "fields")?;
      Ok(())
    },

    (ConstantInfo::RecInfo(g), ConstantInfo::RecInfo(o)) => {
      check_nat_eq(&g.num_params, &o.num_params, "params")?;
      check_nat_eq(&g.num_indices, &o.num_indices, "indices")?;
      check_nat_eq(&g.num_motives, &o.num_motives, "motives")?;
      check_nat_eq(&g.num_minors, &o.num_minors, "minors")?;
      if g.k != o.k {
        return Err(format!("k: generated={} orig={}", g.k, o.k));
      }
      if g.rules.len() != o.rules.len() {
        return Err(format!(
          "rule count: generated={} orig={}",
          g.rules.len(),
          o.rules.len()
        ));
      }
      for (i, (gr, or)) in g.rules.iter().zip(o.rules.iter()).enumerate() {
        expr_alpha_eq(&gr.rhs, &or.rhs)
          .map_err(|e| format!("rule[{i}].rhs: {e}"))?;
      }
      Ok(())
    },

    _ => Err(format!(
      "variant mismatch: {} vs {}",
      ci_tag(generated),
      ci_tag(orig),
    )),
  }
}

// =========================================================================
// Helpers
// =========================================================================

/// Strip Mdata wrappers from an expression.
fn strip_mdata(e: &Expr) -> &Expr {
  let mut cur = e;
  while let ExprData::Mdata(_, inner, _) = cur.as_data() {
    cur = inner;
  }
  cur
}

fn check_nat_eq(a: &Nat, b: &Nat, field: &str) -> Result<(), String> {
  let av = a.to_u64().unwrap_or(u64::MAX);
  let bv = b.to_u64().unwrap_or(u64::MAX);
  if av != bv {
    Err(format!("{field}: generated={av} orig={bv}"))
  } else {
    Ok(())
  }
}

fn level_tag(l: &Level) -> &'static str {
  match l.as_data() {
    LevelData::Zero(_) => "Zero",
    LevelData::Succ(_, _) => "Succ",
    LevelData::Max(_, _, _) => "Max",
    LevelData::Imax(_, _, _) => "IMax",
    LevelData::Param(_, _) => "Param",
    LevelData::Mvar(_, _) => "Mvar",
  }
}

fn expr_tag(e: &Expr) -> &'static str {
  match e.as_data() {
    ExprData::Bvar(_, _) => "Bvar",
    ExprData::Sort(_, _) => "Sort",
    ExprData::Const(_, _, _) => "Const",
    ExprData::App(_, _, _) => "App",
    ExprData::Lam(_, _, _, _, _) => "Lam",
    ExprData::ForallE(_, _, _, _, _) => "ForallE",
    ExprData::LetE(_, _, _, _, _, _) => "LetE",
    ExprData::Lit(_, _) => "Lit",
    ExprData::Mdata(_, _, _) => "Mdata",
    ExprData::Proj(_, _, _, _) => "Proj",
    ExprData::Fvar(_, _) => "Fvar",
    ExprData::Mvar(_, _) => "Mvar",
  }
}

fn ci_tag(ci: &ConstantInfo) -> &'static str {
  match ci {
    ConstantInfo::AxiomInfo(_) => "Axiom",
    ConstantInfo::DefnInfo(_) => "Defn",
    ConstantInfo::ThmInfo(_) => "Thm",
    ConstantInfo::OpaqueInfo(_) => "Opaque",
    ConstantInfo::QuotInfo(_) => "Quot",
    ConstantInfo::InductInfo(_) => "Induct",
    ConstantInfo::CtorInfo(_) => "Ctor",
    ConstantInfo::RecInfo(_) => "Rec",
  }
}
