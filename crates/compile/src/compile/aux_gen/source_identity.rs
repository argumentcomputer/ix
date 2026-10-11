//! Source-body recognition for the simple recursor wrappers. Names choose a
//! candidate; they do not establish that its actual type or value is standard.

use ix_common::env::{
  ConstantInfo, DefinitionSafety, Env, Expr, ExprData, Level, LevelData, Name,
  NameData,
};

use super::{AuxDef, cases_on::generate_cases_on, rec_on::generate_rec_on};
use crate::compile::pass3::expr::alpha_eq;

/// Positional universe parameters, without universe arithmetic normalization.
fn level(params: &[Name], value: &Level) -> Option<Level> {
  Some(match value.as_data() {
    LevelData::Zero(_) => Level::zero(),
    LevelData::Succ(u, _) => Level::succ(level(params, u)?),
    LevelData::Max(u, v, _) => Level::max(level(params, u)?, level(params, v)?),
    LevelData::Imax(u, v, _) => {
      Level::imax(level(params, u)?, level(params, v)?)
    },
    LevelData::Param(n, _) => {
      let index = params.iter().position(|p| p == n)?;
      Level::param(Name::num(Name::anon(), (index as u64).into()))
    },
    LevelData::Mvar(..) => return None,
  })
}

/// Rename universe parameters in a closed declaration. Constant and projection
/// names stay exact, and open expressions cannot authenticate a source helper.
fn expr(params: &[Name], value: &Expr) -> Option<Expr> {
  Some(match value.as_data() {
    ExprData::Bvar(i, _) => Expr::bvar(i.clone()),
    ExprData::Fvar(..) | ExprData::Mvar(..) => return None,
    ExprData::Sort(u, _) => Expr::sort(level(params, u)?),
    ExprData::Const(n, us, _) => Expr::cnst(
      n.clone(),
      us.iter().map(|u| level(params, u)).collect::<Option<Vec<_>>>()?,
    ),
    ExprData::App(f, a, _) => Expr::app(expr(params, f)?, expr(params, a)?),
    ExprData::Lam(n, t, b, bi, _) => {
      Expr::lam(n.clone(), expr(params, t)?, expr(params, b)?, bi.clone())
    },
    ExprData::ForallE(n, t, b, bi, _) => {
      Expr::all(n.clone(), expr(params, t)?, expr(params, b)?, bi.clone())
    },
    ExprData::LetE(n, t, v, b, nd, _) => Expr::letE(
      n.clone(),
      expr(params, t)?,
      expr(params, v)?,
      expr(params, b)?,
      *nd,
    ),
    ExprData::Lit(..) => value.clone(),
    ExprData::Mdata(md, e, _) => Expr::mdata(md.clone(), expr(params, e)?),
    ExprData::Proj(n, i, e, _) => {
      Expr::proj(n.clone(), i.clone(), expr(params, e)?)
    },
  })
}

pub fn agrees(lp: &[Name], rp: &[Name], left: &Expr, right: &Expr) -> bool {
  match (expr(lp, left), expr(rp, right)) {
    (Some(left), Some(right)) => alpha_eq(&left, &right),
    _ => false,
  }
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

/// Use the source recursor, including its original mutual layout.
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
    assert!(!agrees(&[u.clone(), v.clone()], &[u, v], &p, &q));
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
    let value = Expr::bvar(0u64.into());
    let annotated = Expr::mdata(vec![], value.clone());
    assert!(agrees(&[], &[], &annotated, &annotated));
    assert!(!agrees(&[], &[], &annotated, &value));
  }
}
