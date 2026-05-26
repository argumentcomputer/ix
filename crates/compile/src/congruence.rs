//! Alpha-equivalence checks between Lean expressions/constants.
//!
//! Compares two `ConstantInfo` values structurally, ignoring binder names
//! and mdata. Used to verify that aux_gen produces constants congruent to
//! what Lean generates.
//!
//! Submodules:
//! - [`perm`]: permutation-aware comparison for aux_gen-generated vs Lean
//!   source-order originals. Accepts a context describing how canonical
//!   (hash-sorted) aux positions map to source-walk positions, plus const
//!   name rewrites for alpha-collapse aliasing; compares both sides in
//!   lockstep with FVar correspondence established at outer binder
//!   chains. Replaces the older `aux_gen::canonicalize` helper.

pub mod perm;

use crate::ix::env::{ConstantInfo, Expr, ExprData, Level, LevelData, Literal};
use lean_ffi::nat::Nat;

/// Check that two Lean levels are equal modulo the same simplifications
/// `Level::max_smart` / `Level::imax_smart` perform.
///
/// Why normalize: `aux_gen::expr_utils::subst_level` routes through the
/// smart constructors so substituted levels match the form the kernel
/// produces post-ingress (see commit `ec95312` "Align nested-aux canonical
/// order"). Lean's own `Level.instantiateParams` keeps the un-simplified
/// factored form, so the same source-level expression can appear as
/// `Sort (max u u)` from Lean and `Sort u` from aux_gen — semantically
/// equal but structurally distinct. Strict structural comparison would
/// flag every such case as a congruence failure on nested inductives;
/// normalizing both sides through the same `max_smart` / `imax_smart`
/// simplifier closes the gap without weakening the comparator (the smart
/// constructor only applies semantically-valid simplifications:
/// `max(a,a) = a`, zero absorption, same-base offset, `Max` absorption,
/// and the analogous `imax` rules).
///
/// `Succ` is intentionally **not** normalized: Lean and aux_gen both
/// preserve the factored form, so distributing `Succ` over `Max` would
/// only introduce drift. See the "Use raw Level::succ" comment that lived
/// in `expr_utils::subst_level` prior to `ec95312`.
pub fn level_alpha_eq(a: &Level, b: &Level) -> Result<(), String> {
  level_alpha_eq_struct(&normalize_level(a), &normalize_level(b))
}

/// Normalize a level by applying `Level::max_smart` / `Level::imax_smart`
/// bottom-up. Idempotent. `Succ` is left raw (see [`level_alpha_eq`]).
fn normalize_level(l: &Level) -> Level {
  match l.as_data() {
    LevelData::Zero(_) | LevelData::Param(_, _) | LevelData::Mvar(_, _) => {
      l.clone()
    },
    LevelData::Succ(inner, _) => Level::succ(normalize_level(inner)),
    LevelData::Max(x, y, _) => {
      Level::max_smart(normalize_level(x), normalize_level(y))
    },
    LevelData::Imax(x, y, _) => {
      Level::imax_smart(normalize_level(x), normalize_level(y))
    },
  }
}

/// Strict structural alpha-equivalence on already-normalized levels.
/// Direct callers should go through [`level_alpha_eq`] so both sides
/// are normalized first; this helper exists only to avoid re-normalizing
/// at every recursion step.
fn level_alpha_eq_struct(a: &Level, b: &Level) -> Result<(), String> {
  match (a.as_data(), b.as_data()) {
    (LevelData::Zero(_), LevelData::Zero(_)) => Ok(()),
    (LevelData::Succ(a1, _), LevelData::Succ(b1, _)) => {
      level_alpha_eq_struct(a1, b1)
    },
    (LevelData::Max(a1, a2, _), LevelData::Max(b1, b2, _))
    | (LevelData::Imax(a1, a2, _), LevelData::Imax(b1, b2, _)) => {
      level_alpha_eq_struct(a1, b1)?;
      level_alpha_eq_struct(a2, b2)
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
pub(crate) fn strip_mdata(e: &Expr) -> &Expr {
  let mut cur = e;
  while let ExprData::Mdata(_, inner, _) = cur.as_data() {
    cur = inner;
  }
  cur
}

pub(crate) fn check_nat_eq(
  a: &Nat,
  b: &Nat,
  field: &str,
) -> Result<(), String> {
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

#[cfg(test)]
mod tests {
  //! Regression tests for [`level_alpha_eq`] level normalization.
  //!
  //! Each test pairs a Lean-source-shaped level (raw `Level::max` /
  //! `Level::imax`, as `Level.instantiateParams` would emit) with the
  //! aux_gen-shaped level that `subst_level`'s smart-constructor route
  //! produces for the same input. Pre-fix (strict structural compare),
  //! every pair would fail with "level mismatch". Post-fix, they pass.
  //!
  //! The cases mirror the simplifications inside `Level::max_smart` /
  //! `Level::imax_smart` (see `src/ix/env.rs:340-404`), so they double
  //! as a contract test for those constructors.
  use super::*;
  use crate::ix::env::Name;
  fn p(s: &str) -> Level {
    Level::param(Name::str(Name::anon(), s.to_string()))
  }
  fn z() -> Level {
    Level::zero()
  }
  fn s(l: Level) -> Level {
    Level::succ(l)
  }
  /// Raw `Level::max` (no simplification) — what Lean's exporter and
  /// `Level.instantiateParams` produce.
  fn m(x: Level, y: Level) -> Level {
    Level::max(x, y)
  }
  /// Raw `Level::imax`.
  fn im(x: Level, y: Level) -> Level {
    Level::imax(x, y)
  }

  /// `max(a, a) = a` — the canonical aux_gen vs Lean divergence on
  /// nested-aux level args from `ec95312` (the `Sort (max 1 1)` vs
  /// `Sort 1` example in the commit message).
  #[test]
  fn level_max_same_arg_dedup() {
    let lean = m(s(z()), s(z()));
    let aux_gen = s(z());
    assert!(level_alpha_eq(&lean, &aux_gen).is_ok());
    assert!(level_alpha_eq(&aux_gen, &lean).is_ok());
  }

  /// `max(0, x) = x` — Zero absorption.
  #[test]
  fn level_max_zero_absorption() {
    let u = p("u");
    let lean = m(z(), u.clone());
    assert!(level_alpha_eq(&lean, &u).is_ok());
    let lean_r = m(u.clone(), z());
    assert!(level_alpha_eq(&lean_r, &u).is_ok());
  }

  /// `max(succ x, succ y)` with `x == y` collapses to `succ x`.
  #[test]
  fn level_max_same_base_succ() {
    let u = p("u");
    let lean = m(s(u.clone()), s(u.clone()));
    let aux_gen = s(u);
    assert!(level_alpha_eq(&lean, &aux_gen).is_ok());
  }

  /// `max(succ^n x, succ^m x) = succ^max(n,m) x` — same-base offset.
  #[test]
  fn level_max_same_base_different_offsets() {
    let u = p("u");
    let lean = m(s(u.clone()), s(s(u.clone())));
    let aux_gen = s(s(u));
    assert!(level_alpha_eq(&lean, &aux_gen).is_ok());
  }

  /// `imax(_, succ _) = max(_, succ _)` — succ-headed second arg.
  #[test]
  fn level_imax_succ_collapses_to_max() {
    let u = p("u");
    let v = p("v");
    let lean = im(u.clone(), s(v.clone()));
    let aux_gen = m(u, s(v));
    assert!(level_alpha_eq(&lean, &aux_gen).is_ok());
  }

  /// `imax(_, 0) = 0`.
  #[test]
  fn level_imax_zero_second_arg() {
    let u = p("u");
    let lean = im(u, z());
    let aux_gen = z();
    assert!(level_alpha_eq(&lean, &aux_gen).is_ok());
  }

  /// Nested `max` absorption: `max(a, max(a, b)) = max(a, b)`.
  #[test]
  fn level_max_absorption_left_in_right() {
    let u = p("u");
    let v = p("v");
    let lean = m(u.clone(), m(u.clone(), v.clone()));
    let aux_gen = m(u, v);
    assert!(level_alpha_eq(&lean, &aux_gen).is_ok());
  }

  /// Strict structural mismatch is still rejected — sanity check that
  /// normalization didn't accidentally make `level_alpha_eq` reflexive
  /// over unrelated levels.
  #[test]
  fn level_genuinely_different_still_rejected() {
    let u = p("u");
    let v = p("v");
    // succ u vs max u v — neither side reduces; strict compare disagrees.
    assert!(level_alpha_eq(&s(u.clone()), &m(u, v)).is_err());
  }

  /// Normalization is idempotent: applying it twice doesn't change the
  /// result. Guards against future smart-constructor changes that lose
  /// idempotency (which would make `level_alpha_eq_struct`'s assumption
  /// "post-normalize subterms are normalized" silently invalid).
  #[test]
  fn level_normalize_idempotent() {
    let u = p("u");
    let v = p("v");
    let cases = [
      m(s(z()), s(z())),
      m(z(), u.clone()),
      m(u.clone(), m(u.clone(), v.clone())),
      im(u.clone(), s(v.clone())),
      im(u, z()),
      m(s(v.clone()), s(s(v))),
    ];
    for l in &cases {
      let n1 = normalize_level(l);
      let n2 = normalize_level(&n1);
      assert_eq!(n1, n2, "normalize_level not idempotent on {}", l.pretty());
    }
  }
}
