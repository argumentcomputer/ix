//! Congruence checks between Lean-side `ix::env` types and zero kernel types.
//!
//! Validates that Ixon ingress in Anon mode produces structurally correct
//! constants by comparing the Lean `ConstantInfo` against the loaded `KConst<Anon>`.

use crate::ix::address::Address;
use crate::ix::env::{self as lean, ConstantInfo as LeanCI, Literal, Name};

use super::constant::KConst;
use super::expr::{ExprData, KExpr};
use super::level::{KUniv, UnivData};
use super::mode::Anon;

/// Name-to-address resolver, built from the Ixon named map.
pub struct NameResolver {
  map: rustc_hash::FxHashMap<Name, Address>,
}

impl NameResolver {
  pub fn from_ixon_env(ixon_env: &crate::ix::ixon::env::Env) -> Self {
    let mut map = rustc_hash::FxHashMap::default();
    for entry in ixon_env.named.iter() {
      map.insert(entry.key().clone(), entry.value().addr.clone());
    }
    NameResolver { map }
  }

  pub fn resolve(&self, name: &Name) -> Option<&Address> {
    self.map.get(name)
  }
}

/// Check that a Lean-side Level matches a zero Univ structurally.
pub fn level_congruent(
  lean_lvl: &lean::Level,
  zero_univ: &KUniv<Anon>,
  _nr: &NameResolver,
) -> Result<(), String> {
  use lean::LevelData as LD;
  match (lean_lvl.as_data(), zero_univ.data()) {
    (LD::Zero(_), UnivData::Zero(_)) => Ok(()),
    (LD::Succ(a, _), UnivData::Succ(b, _)) => level_congruent(a, b, _nr),
    (LD::Max(a1, a2, _), UnivData::Max(b1, b2, _))
    | (LD::Imax(a1, a2, _), UnivData::IMax(b1, b2, _)) => {
      level_congruent(a1, b1, _nr)?;
      level_congruent(a2, b2, _nr)
    },
    (LD::Param(_, _), UnivData::Param(_, _, _)) => {
      // Lean uses named params, zero uses positional indices.
      // Can't check correspondence without level_params list.
      Ok(())
    },
    _ => Err(format!(
      "level mismatch: lean={} vs zero={}",
      lean_lvl_tag(lean_lvl),
      zero_univ_tag(zero_univ),
    )),
  }
}

/// Check that a Lean-side Expr matches a zero Expr<Anon> structurally.
pub fn expr_congruent(
  lean_expr: &lean::Expr,
  zero_expr: &KExpr<Anon>,
  nr: &NameResolver,
) -> Result<(), String> {
  use lean::ExprData as LE;
  match (lean_expr.as_data(), zero_expr.data()) {
    (LE::Bvar(n, _), ExprData::Var(m, _, _)) => {
      let n = n.to_u64().unwrap_or(u64::MAX);
      if n == *m {
        Ok(())
      } else {
        Err(format!("var mismatch: lean={n} vs zero={m}"))
      }
    },

    (LE::Sort(l, _), ExprData::Sort(u, _)) => level_congruent(l, u, nr),

    (LE::Const(name, levels, _), ExprData::Const(id, univs, _)) => {
      match nr.resolve(name) {
        Some(expected) if expected == &id.addr => {},
        Some(expected) => {
          return Err(format!(
            "const address mismatch for {name}: expected {}, got {}",
            expected.hex(),
            id.addr.hex()
          ));
        },
        None => {
          return Err(format!("const name not found in resolver: {name}"));
        },
      }
      if levels.len() != univs.len() {
        return Err(format!(
          "const {name}: level count mismatch: {} vs {}",
          levels.len(),
          univs.len()
        ));
      }
      for (l, u) in levels.iter().zip(univs.iter()) {
        level_congruent(l, u, nr)?;
      }
      Ok(())
    },

    (LE::App(f1, a1, _), ExprData::App(f2, a2, _)) => {
      expr_congruent(f1, f2, nr)?;
      expr_congruent(a1, a2, nr)
    },

    (LE::Lam(_, ty1, body1, _, _), ExprData::Lam(_, _, ty2, body2, _))
    | (LE::ForallE(_, ty1, body1, _, _), ExprData::All(_, _, ty2, body2, _)) =>
    {
      expr_congruent(ty1, ty2, nr)?;
      expr_congruent(body1, body2, nr)
    },

    (
      LE::LetE(_, ty1, val1, body1, _, _),
      ExprData::Let(_, ty2, val2, body2, _, _),
    ) => {
      expr_congruent(ty1, ty2, nr)?;
      expr_congruent(val1, val2, nr)?;
      expr_congruent(body1, body2, nr)
    },

    (LE::Lit(Literal::NatVal(_), _), ExprData::Nat(_, _, _))
    | (LE::Lit(Literal::StrVal(_), _), ExprData::Str(_, _, _)) => Ok(()),

    (LE::Proj(name, idx, struct_expr, _), ExprData::Prj(id, field, val, _)) => {
      match nr.resolve(name) {
        Some(expected) if expected == &id.addr => {},
        Some(expected) => {
          return Err(format!(
            "proj type mismatch for {name}: expected {}, got {}",
            expected.hex(),
            id.addr.hex()
          ));
        },
        None => return Err(format!("proj type name not found: {name}")),
      }
      if idx.to_u64().unwrap_or(u64::MAX) != *field {
        return Err(format!(
          "proj field mismatch: lean={} vs zero={field}",
          idx.to_u64().unwrap_or(u64::MAX)
        ));
      }
      expr_congruent(struct_expr, val, nr)
    },

    // Lean Mdata wraps an inner expr — zero strips it in Anon mode.
    (LE::Mdata(_, inner, _), _) => expr_congruent(inner, zero_expr, nr),

    (LE::Fvar(..) | LE::Mvar(..), _) => {
      Err("unexpected Fvar/Mvar in constant".to_string())
    },

    _ => Err(format!(
      "expr shape mismatch: lean={} vs zero={}",
      lean_expr_tag(lean_expr),
      zero_expr_tag(zero_expr),
    )),
  }
}

/// Check that a Lean `ConstantInfo` matches a `KConst<Anon>` structurally.
pub fn const_congruent(
  lean_ci: &LeanCI,
  zero_const: &KConst<Anon>,
  nr: &NameResolver,
) -> Result<(), String> {
  // Check type congruence
  let lean_type = lean_ci.get_type();
  let zero_type = zero_const.ty();
  expr_congruent(lean_type, zero_type, nr).map_err(|e| format!("type: {e}"))?;

  // Check lvls count
  let lean_lvls = lean_ci.get_level_params().len() as u64;
  let zero_lvls = zero_const.lvls();
  if lean_lvls != zero_lvls {
    return Err(format!("lvls: lean={lean_lvls} vs zero={zero_lvls}"));
  }

  // Variant-specific checks
  match (lean_ci, zero_const) {
    (LeanCI::AxiomInfo(_), KConst::Axio { .. })
    | (LeanCI::QuotInfo(_), KConst::Quot { .. }) => Ok(()),

    (LeanCI::DefnInfo(v), KConst::Defn { val, .. }) => {
      expr_congruent(&v.value, val, nr).map_err(|e| format!("value: {e}"))
    },

    (LeanCI::ThmInfo(v), KConst::Defn { val, .. }) => {
      expr_congruent(&v.value, val, nr).map_err(|e| format!("value: {e}"))
    },

    (LeanCI::OpaqueInfo(v), KConst::Defn { val, .. }) => {
      expr_congruent(&v.value, val, nr).map_err(|e| format!("value: {e}"))
    },

    (LeanCI::InductInfo(v), KConst::Indc { params, indices, ctors, .. }) => {
      let lp = v.num_params.to_u64().unwrap_or(u64::MAX);
      let li = v.num_indices.to_u64().unwrap_or(u64::MAX);
      if lp != *params {
        return Err(format!("params: lean={lp} vs zero={params}"));
      }
      if li != *indices {
        return Err(format!("indices: lean={li} vs zero={indices}"));
      }
      if v.ctors.len() != ctors.len() {
        return Err(format!(
          "ctor count: lean={} vs zero={}",
          v.ctors.len(),
          ctors.len()
        ));
      }
      Ok(())
    },

    (LeanCI::CtorInfo(v), KConst::Ctor { cidx, params, fields, .. }) => {
      let lc = v.cidx.to_u64().unwrap_or(u64::MAX);
      let lp = v.num_params.to_u64().unwrap_or(u64::MAX);
      let lf = v.num_fields.to_u64().unwrap_or(u64::MAX);
      if lc != *cidx {
        return Err(format!("cidx: lean={lc} vs zero={cidx}"));
      }
      if lp != *params {
        return Err(format!("params: lean={lp} vs zero={params}"));
      }
      if lf != *fields {
        return Err(format!("fields: lean={lf} vs zero={fields}"));
      }
      Ok(())
    },

    (
      LeanCI::RecInfo(v),
      KConst::Recr { params, indices, motives, minors, rules, k, .. },
    ) => {
      let lp = v.num_params.to_u64().unwrap_or(u64::MAX);
      let li = v.num_indices.to_u64().unwrap_or(u64::MAX);
      let lm = v.num_motives.to_u64().unwrap_or(u64::MAX);
      let ln = v.num_minors.to_u64().unwrap_or(u64::MAX);
      if lp != *params {
        return Err(format!("params: lean={lp} vs zero={params}"));
      }
      if li != *indices {
        return Err(format!("indices: lean={li} vs zero={indices}"));
      }
      if lm != *motives {
        return Err(format!("motives: lean={lm} vs zero={motives}"));
      }
      if ln != *minors {
        return Err(format!("minors: lean={ln} vs zero={minors}"));
      }
      if v.rules.len() != rules.len() {
        return Err(format!(
          "rule count: lean={} vs zero={}",
          v.rules.len(),
          rules.len()
        ));
      }
      if v.k != *k {
        return Err(format!("k: lean={} vs zero={k}", v.k));
      }
      for (i, (lean_rule, zero_rule)) in
        v.rules.iter().zip(rules.iter()).enumerate()
      {
        expr_congruent(&lean_rule.rhs, &zero_rule.rhs, nr)
          .map_err(|e| format!("rule[{i}].rhs: {e}"))?;
      }
      Ok(())
    },

    _ => Err(format!(
      "variant mismatch: lean={} vs zero={}",
      lean_ci_tag(lean_ci),
      zero_const_tag(zero_const),
    )),
  }
}

fn lean_lvl_tag(l: &lean::Level) -> &'static str {
  use lean::LevelData as LD;
  match l.as_data() {
    LD::Zero(_) => "Zero",
    LD::Succ(..) => "Succ",
    LD::Max(..) => "Max",
    LD::Imax(..) => "IMax",
    LD::Param(..) => "Param",
    LD::Mvar(..) => "Mvar",
  }
}

fn zero_univ_tag<M: super::mode::KernelMode>(u: &KUniv<M>) -> &'static str {
  match u.data() {
    UnivData::Zero(_) => "Zero",
    UnivData::Succ(..) => "Succ",
    UnivData::Max(..) => "Max",
    UnivData::IMax(..) => "IMax",
    UnivData::Param(..) => "Param",
  }
}

fn lean_expr_tag(e: &lean::Expr) -> &'static str {
  use lean::ExprData as LE;
  match e.as_data() {
    LE::Bvar(..) => "Bvar",
    LE::Fvar(..) => "Fvar",
    LE::Mvar(..) => "Mvar",
    LE::Sort(..) => "Sort",
    LE::Const(..) => "Const",
    LE::App(..) => "App",
    LE::Lam(..) => "Lam",
    LE::ForallE(..) => "ForallE",
    LE::LetE(..) => "LetE",
    LE::Lit(..) => "Lit",
    LE::Mdata(..) => "Mdata",
    LE::Proj(..) => "Proj",
  }
}

fn zero_expr_tag(e: &KExpr<Anon>) -> &'static str {
  match e.data() {
    ExprData::Var(..) => "Var",
    ExprData::Sort(..) => "Sort",
    ExprData::Const(..) => "Const",
    ExprData::App(..) => "App",
    ExprData::Lam(..) => "Lam",
    ExprData::All(..) => "All",
    ExprData::Let(..) => "Let",
    ExprData::Prj(..) => "Prj",
    ExprData::Nat(..) => "Nat",
    ExprData::Str(..) => "Str",
  }
}

fn lean_ci_tag(ci: &LeanCI) -> &'static str {
  match ci {
    LeanCI::AxiomInfo(_) => "Axiom",
    LeanCI::DefnInfo(_) => "Defn",
    LeanCI::ThmInfo(_) => "Thm",
    LeanCI::OpaqueInfo(_) => "Opaque",
    LeanCI::QuotInfo(_) => "Quot",
    LeanCI::InductInfo(_) => "Induct",
    LeanCI::CtorInfo(_) => "Ctor",
    LeanCI::RecInfo(_) => "Rec",
  }
}

fn zero_const_tag<M: super::mode::KernelMode>(c: &KConst<M>) -> &'static str {
  match c {
    KConst::Defn { .. } => "Defn",
    KConst::Recr { .. } => "Recr",
    KConst::Axio { .. } => "Axio",
    KConst::Quot { .. } => "Quot",
    KConst::Indc { .. } => "Indc",
    KConst::Ctor { .. } => "Ctor",
  }
}
