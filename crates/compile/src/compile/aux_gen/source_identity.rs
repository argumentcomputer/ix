//! Source-body recognition for the simple recursor wrappers. Names choose a
//! candidate; they do not establish that its actual type or value is standard.
//! Nothing on the compile path calls these functions yet.
//!
//! Mirrors Lean `Ix.AuxGen.SourceIdentity`.

use rustc_hash::FxHashMap;

use ix_common::env::{
  ConstantInfo, DefinitionSafety, Env, Expr, ExprData, Level, Name, NameData,
};

use super::{AuxDef, cases_on::generate_cases_on, rec_on::generate_rec_on};
use crate::compile::level_to_univ;

/// Universes agree when their positional forms are equal: each parameter by
/// its position in its own declaration's list (`level_to_univ`, complete
/// names), with no universe arithmetic normalized. Unknown parameters and
/// metavariables never agree.
fn level_agrees(lp: &[Name], rp: &[Name], left: &Level, right: &Level) -> bool {
  match (level_to_univ(left, lp), level_to_univ(right, rp)) {
    (Ok(left), Ok(right)) => left == right,
    _ => false,
  }
}

/// No free variables or metavariables: an open expression cannot
/// authenticate a source helper.
fn closed(value: &Expr) -> bool {
  match value.as_data() {
    ExprData::Fvar(..) | ExprData::Mvar(..) => false,
    ExprData::App(f, a, _)
    | ExprData::Lam(_, f, a, _, _)
    | ExprData::ForallE(_, f, a, _, _) => closed(f) && closed(a),
    ExprData::LetE(_, t, v, b, _, _) => closed(t) && closed(v) && closed(b),
    ExprData::Mdata(_, e, _) | ExprData::Proj(_, _, e, _) => closed(e),
    _ => true,
  }
}

/// The hash pair selects a candidate entry; the retained expressions confirm
/// both keys before a saved result is reused.
type Memo = FxHashMap<(blake3::Hash, blake3::Hash), (Expr, Expr, bool)>;

/// Lean `Ix.Compile.Image.exprEqWith`: equality up to binder names, binder
/// info and let flags, with paired metadata and exact names, universes
/// decided by `lv`. Hashes only select memo candidates.
fn expr_eq_with(
  a: &Expr,
  b: &Expr,
  lv: &impl Fn(&Level, &Level) -> bool,
  memo: &mut Memo,
) -> bool {
  let key = (*a.get_hash(), *b.get_hash());
  if let Some((saved_a, saved_b, result)) = memo.get(&key)
    && saved_a == a
    && saved_b == b
  {
    return *result;
  }
  let result = match (a.as_data(), b.as_data()) {
    (ExprData::Bvar(i, _), ExprData::Bvar(j, _)) => i == j,
    (ExprData::Fvar(x, _), ExprData::Fvar(y, _))
    | (ExprData::Mvar(x, _), ExprData::Mvar(y, _)) => x == y,
    (ExprData::Sort(u, _), ExprData::Sort(v, _)) => lv(u, v),
    (ExprData::Const(x, us, _), ExprData::Const(y, vs, _)) => {
      x == y && us.len() == vs.len() && us.iter().zip(vs).all(|(u, v)| lv(u, v))
    },
    (ExprData::App(f, x, _), ExprData::App(g, y, _)) => {
      expr_eq_with(f, g, lv, memo) && expr_eq_with(x, y, lv, memo)
    },
    (ExprData::Lam(_, t, b, _, _), ExprData::Lam(_, t2, b2, _, _))
    | (ExprData::ForallE(_, t, b, _, _), ExprData::ForallE(_, t2, b2, _, _)) => {
      expr_eq_with(t, t2, lv, memo) && expr_eq_with(b, b2, lv, memo)
    },
    (ExprData::LetE(_, t, v, b, _, _), ExprData::LetE(_, t2, v2, b2, _, _)) => {
      expr_eq_with(t, t2, lv, memo)
        && expr_eq_with(v, v2, lv, memo)
        && expr_eq_with(b, b2, lv, memo)
    },
    (ExprData::Lit(x, _), ExprData::Lit(y, _)) => x == y,
    (ExprData::Mdata(_, x, _), ExprData::Mdata(_, y, _)) => {
      expr_eq_with(x, y, lv, memo)
    },
    (ExprData::Proj(s, i, x, _), ExprData::Proj(s2, i2, y, _)) => {
      s == s2 && i == i2 && expr_eq_with(x, y, lv, memo)
    },
    _ => false,
  };
  memo.insert(key, (a.clone(), b.clone(), result));
  result
}

/// Conservative syntactic correspondence, including the actual body, with
/// universes by position. Cached expression hashes do not establish equality.
pub fn agrees(lp: &[Name], rp: &[Name], left: &Expr, right: &Expr) -> bool {
  closed(left)
    && closed(right)
    && expr_eq_with(
      left,
      right,
      &|u: &Level, v: &Level| level_agrees(lp, rp, u, v),
      &mut Memo::default(),
    )
}

/// Kind, safety, universe arity, type and body all participate. Hints and
/// binder presentation cannot establish the helper's meaning.
pub fn definition_matches(expected: &AuxDef, source: &ConstantInfo) -> bool {
  let ConstantInfo::DefnInfo(actual) = source else { return false };
  expected.name == actual.cnst.name
    && actual.safety
      == if expected.is_unsafe {
        DefinitionSafety::Unsafe
      } else {
        DefinitionSafety::Safe
      }
    && expected.level_params.len() == actual.cnst.level_params.len()
    && agrees(
      &expected.level_params,
      &actual.cnst.level_params,
      &expected.typ,
      &actual.cnst.typ,
    )
    && agrees(
      &expected.level_params,
      &actual.cnst.level_params,
      &expected.value,
      &actual.value,
    )
}

/// Use the source recursor, including its original mutual layout. The
/// canonical recursor of a collapsed block is not a source-body oracle.
pub fn wrapper(env: &Env, name: &Name) -> Option<AuxDef> {
  let NameData::Str(parent, suffix, _) = name.as_data() else { return None };
  let rec_name = Name::str(parent.clone(), "rec".into());
  let rec = env.get(&rec_name)?;
  let ConstantInfo::RecInfo(rv) = &*rec else { return None };
  match suffix.as_str() {
    "recOn" => generate_rec_on(name, rv),
    "casesOn" => generate_cases_on(name, rv, env),
    _ => None,
  }
}

/// Name lookup chooses a candidate; successful body correspondence licenses
/// the standard-wrapper interpretation.
pub fn checked_wrapper(env: &Env, name: &Name) -> Option<AuxDef> {
  let candidate = wrapper(env, name)?;
  let actual = env.get(name)?;
  definition_matches(&candidate, &actual).then_some(candidate)
}

/// Only the simple wrappers are authenticated here. Other families retain
/// their existing checks and still require their own source-body contracts.
pub fn permits_optimization(env: &Env, name: &Name) -> bool {
  match name.as_data() {
    NameData::Str(_, suffix, _) if suffix == "casesOn" || suffix == "recOn" => {
      checked_wrapper(env, name).is_some()
    },
    _ => true,
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use ix_common::env::{
    BinderInfo, ConstantVal, DefinitionVal, ReducibilityHints,
  };
  use std::sync::Arc;

  fn name(s: &str) -> Name {
    Name::str(Name::anon(), s.into())
  }

  fn identity(param: &str, binder: &str) -> AuxDef {
    let level_param = name(param);
    let sort = Expr::sort(Level::param(level_param.clone()));
    let body = Expr::bvar(0u64.into());
    AuxDef {
      name: name("helper"),
      level_params: vec![level_param],
      typ: Expr::all(
        name(binder),
        sort.clone(),
        sort.clone(),
        BinderInfo::Default,
      ),
      value: Expr::lam(name(binder), sort, body, BinderInfo::Default),
      is_unsafe: false,
    }
  }

  fn source(d: &AuxDef) -> DefinitionVal {
    DefinitionVal {
      cnst: ConstantVal {
        name: d.name.clone(),
        level_params: d.level_params.clone(),
        typ: d.typ.clone(),
      },
      value: d.value.clone(),
      hints: ReducibilityHints::Abbrev,
      safety: DefinitionSafety::Safe,
      all: vec![d.name.clone()],
    }
  }

  #[test]
  fn recognizes_body_with_renamed_universe_and_term_binders() {
    let expected = identity("u", "left");
    let actual = source(&identity("v", "right"));
    assert!(definition_matches(&expected, &ConstantInfo::DefnInfo(actual)));
  }

  #[test]
  fn same_signature_does_not_authenticate_a_different_body() {
    let expected = identity("u", "x");
    let mut actual = source(&expected);
    assert!(definition_matches(
      &expected,
      &ConstantInfo::DefnInfo(actual.clone())
    ));
    actual.value = Expr::app(Expr::cnst(name("hold"), vec![]), actual.value);
    assert!(agrees(
      &expected.level_params,
      &actual.cnst.level_params,
      &expected.typ,
      &actual.cnst.typ
    ));
    assert!(!definition_matches(&expected, &ConstantInfo::DefnInfo(actual)));
  }

  #[test]
  fn wrong_kind_safety_name_and_universe_arity_decline() {
    let expected = identity("u", "x");
    let mut actual = source(&expected);
    actual.safety = DefinitionSafety::Partial;
    assert!(!definition_matches(
      &expected,
      &ConstantInfo::DefnInfo(actual.clone())
    ));
    actual.safety = DefinitionSafety::Unsafe;
    assert!(!definition_matches(
      &expected,
      &ConstantInfo::DefnInfo(actual.clone())
    ));
    actual.safety = DefinitionSafety::Safe;
    actual.cnst.name = name("unrelated");
    assert!(!definition_matches(
      &expected,
      &ConstantInfo::DefnInfo(actual.clone())
    ));
    actual.cnst.name = expected.name.clone();
    actual.cnst.level_params.push(name("unused"));
    assert!(!definition_matches(
      &expected,
      &ConstantInfo::DefnInfo(actual.clone())
    ));
    let theorem = ConstantInfo::ThmInfo(ix_common::env::TheoremVal {
      cnst: source(&expected).cnst,
      value: expected.value.clone(),
      all: vec![],
    });
    assert!(!definition_matches(&expected, &theorem));
  }

  #[test]
  fn parameter_positions_and_unknown_parameters_are_distinct() {
    let u = name("u");
    let v = name("v");
    let p = Expr::sort(Level::param(u.clone()));
    let q = Expr::sort(Level::param(v.clone()));
    assert!(agrees(std::slice::from_ref(&u), std::slice::from_ref(&v), &p, &q));
    assert!(!agrees(&[u.clone(), v.clone()], &[u.clone(), v.clone()], &p, &q));
    // a raw-equal level at another position: no raw fast path
    assert!(!agrees(&[u.clone(), v.clone()], &[v, u.clone()], &p, &p));
    let pmax =
      Expr::sort(Level::max(Level::param(u.clone()), Level::param(u.clone())));
    assert!(!agrees(
      std::slice::from_ref(&u),
      std::slice::from_ref(&u),
      &pmax,
      &p
    ));
    assert!(!agrees(&[], &[], &p, &p));
    let m = Expr::sort(Level::mvar(name("u")));
    assert!(!agrees(&[], &[], &m, &m));
  }

  #[test]
  fn colliding_name_caches_do_not_identify_constants() {
    let hash = blake3::Hash::from([0; 32]);
    let a = Name(Arc::new(NameData::Str(Name::anon(), "a".into(), hash)));
    let b = Name(Arc::new(NameData::Str(Name::anon(), "b".into(), hash)));
    let left = Expr(Arc::new(ExprData::Const(a, vec![], hash)));
    let right = Expr(Arc::new(ExprData::Const(b, vec![], hash)));
    assert!(!agrees(&[], &[], &left, &right));
  }

  #[test]
  fn open_expressions_and_unpaired_metadata_decline() {
    let free = Expr::fvar(name("free"));
    let metavariable = Expr::mvar(name("unknown"));
    assert!(!agrees(&[], &[], &free, &free));
    assert!(!agrees(&[], &[], &metavariable, &metavariable));
    let under = Expr::lam(
      name("x"),
      Expr::sort(Level::zero()),
      free.clone(),
      BinderInfo::Default,
    );
    assert!(!agrees(&[], &[], &under, &under));
    let value = Expr::bvar(0u64.into());
    let annotated = Expr::mdata(vec![], value.clone());
    assert!(agrees(&[], &[], &annotated, &annotated));
    assert!(!agrees(&[], &[], &annotated, &value));
  }
}
