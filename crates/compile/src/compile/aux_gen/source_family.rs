//! Authenticate derived helpers from the original source recursors, including
//! the helper dependencies of each candidate. Run before publishing image
//! heads, so occurrence optimizations cannot reinterpret a custom source body.

use std::sync::Arc;

use ix_common::env::{
  ConstantInfo, ConstantVal, Env, Expr, ExprData, LevelData, Name, NameData,
};

use super::below::{BelowConstant, BelowCtor, BelowIndc};
use super::source_identity::{agrees, definition_matches};
use super::{AuxDef, below, brecon, populate_canon_kenv_with_below};
use crate::compile::{CompileState, KernelCtx};

enum Recipe {
  Definition(AuxDef),
  Theorem(AuxDef),
  Inductive(BelowIndc, Vec<Name>),
  Constructor(BelowCtor, Name, Vec<Name>, usize, bool),
}

fn same_names(a: &[Name], b: &[Name]) -> bool {
  a.len() == b.len() && a.iter().zip(b).all(|(x, y)| x.same_structure(y))
}

fn signature_matches(
  name: &Name,
  params: &[Name],
  typ: &Expr,
  actual: &ConstantVal,
) -> bool {
  name.same_structure(&actual.name)
    && params.len() == actual.level_params.len()
    && agrees(params, &actual.level_params, typ, &actual.typ)
}

fn references(expr: &Expr, out: &mut Vec<Name>) {
  match expr.as_data() {
    ExprData::Const(name, _, _) => out.push(name.clone()),
    ExprData::App(f, a, _)
    | ExprData::Lam(_, f, a, _, _)
    | ExprData::ForallE(_, f, a, _, _) => {
      references(f, out);
      references(a, out);
    },
    ExprData::LetE(_, t, v, b, _, _) => {
      references(t, out);
      references(v, out);
      references(b, out);
    },
    ExprData::Mdata(_, e, _) => references(e, out),
    ExprData::Proj(name, _, e, _) => {
      out.push(name.clone());
      references(e, out);
    },
    _ => {},
  }
}

impl Recipe {
  fn name(&self) -> &Name {
    match self {
      Self::Definition(d) | Self::Theorem(d) => &d.name,
      Self::Inductive(d, _) => &d.name,
      Self::Constructor(d, ..) => &d.name,
    }
  }

  fn matches(&self, actual: &ConstantInfo) -> bool {
    match (self, actual) {
      (Self::Definition(d), actual) => definition_matches(d, actual),
      (Self::Theorem(d), ConstantInfo::ThmInfo(actual)) => {
        !d.is_unsafe
          && signature_matches(&d.name, &d.level_params, &d.typ, &actual.cnst)
      },
      (Self::Inductive(d, all), ConstantInfo::InductInfo(actual)) => {
        signature_matches(&d.name, &d.level_params, &d.typ, &actual.cnst)
          && actual.num_params.to_u64() == Some(d.n_params as u64)
          && actual.num_indices.to_u64() == Some(d.n_indices as u64)
          && actual.num_nested.to_u64() == Some(0)
          && actual.is_unsafe == d.is_unsafe
          && actual.is_reflexive == d.is_reflexive
          && same_names(all, &actual.all)
          && same_names(
            &d.ctors.iter().map(|c| c.name.clone()).collect::<Vec<_>>(),
            &actual.ctors,
          )
      },
      (
        Self::Constructor(d, owner, params, index, is_unsafe),
        ConstantInfo::CtorInfo(actual),
      ) => {
        signature_matches(&d.name, params, &d.typ, &actual.cnst)
          && owner.same_structure(&actual.induct)
          && actual.cidx.to_u64() == Some(*index as u64)
          && actual.num_params.to_u64() == Some(d.n_params as u64)
          && actual.num_fields.to_u64() == Some(d.n_fields as u64)
          && actual.is_unsafe == *is_unsafe
      },
      _ => false,
    }
  }

  fn references(&self) -> Vec<Name> {
    let mut out = Vec::new();
    match self {
      Self::Definition(d) => {
        references(&d.typ, &mut out);
        references(&d.value, &mut out);
      },
      Self::Theorem(d) => references(&d.typ, &mut out),
      Self::Inductive(d, all) => {
        out.extend(all.iter().cloned());
        out.extend(d.ctors.iter().map(|c| c.name.clone()));
        references(&d.typ, &mut out);
      },
      Self::Constructor(d, ..) => references(&d.typ, &mut out),
    }
    out
  }
}

fn authenticated(
  env: &Env,
  recipes: &[Recipe],
  fuel: usize,
  seen: &mut Vec<Name>,
  name: &Name,
) -> bool {
  if fuel == 0 {
    return false;
  }
  let Some(recipe) = recipes.iter().find(|r| r.name().same_structure(name))
  else {
    return false;
  };
  let Some(actual) = env.get(name) else { return false };
  if !name.same_structure(actual.get_name()) || !recipe.matches(&actual) {
    return false;
  }
  if seen.iter().any(|n| n.same_structure(name)) {
    return true;
  }
  seen.push(name.clone());
  recipe.references().iter().all(|dependency| {
    !recipes.iter().any(|r| r.name().same_structure(dependency))
      || authenticated(env, recipes, fuel - 1, seen, dependency)
  })
}

fn is_brec_on(name: &Name) -> bool {
  let family = |s: &str| s == "brecOn" || s.starts_with("brecOn_");
  let NameData::Str(parent, suffix, _) = name.as_data() else { return false };
  family(suffix)
    || ((suffix == "go" || suffix == "eq")
      && matches!(parent.as_data(), NameData::Str(_, s, _) if family(s)))
}

fn is_derived(name: &Name) -> bool {
  is_brec_on(name)
    || matches!(name.as_data(), NameData::Str(_, s, _) if s == "below" || s.starts_with("below_"))
}

fn prop_former(expr: &Expr) -> bool {
  match expr.as_data() {
    ExprData::ForallE(_, _, body, _, _) | ExprData::Mdata(_, body, _) => {
      prop_former(body)
    },
    ExprData::Sort(level, _) => matches!(level.as_data(), LevelData::Zero(_)),
    _ => false,
  }
}

fn reconstruct(
  env: &Arc<Env>,
  all: &[Name],
  include_brec_on: bool,
) -> Result<Vec<Recipe>, String> {
  let Some(owner) = all.first() else {
    return Err("empty source family".into());
  };
  let entry = env.get(owner).ok_or("source owner absent")?;
  let ConstantInfo::InductInfo(ind) = &*entry else {
    return Err("source owner is not inductive".into());
  };
  if !same_names(all, &ind.all) {
    return Err("source mutual order differs".into());
  }
  let classes = all.iter().map(|n| vec![n.clone()]).collect::<Vec<_>>();
  let mut rec_names =
    all.iter().map(|n| Name::str(n.clone(), "rec".into())).collect::<Vec<_>>();
  let nested = ind.num_nested.to_u64().ok_or("nested count overflow")?;
  let nested =
    usize::try_from(nested).map_err(|_overflow| "nested count overflow")?;
  for i in 0..nested {
    rec_names.push(Name::str(owner.clone(), format!("rec_{}", i + 1)));
  }
  let mut recs = Vec::new();
  for name in rec_names {
    let entry = env.get(&name).ok_or("source recursor absent")?;
    let ConstantInfo::RecInfo(rv) = &*entry else {
      return Err("source recursor has wrong kind".into());
    };
    if !name.same_structure(&rv.cnst.name) || !same_names(all, &rv.all) {
      return Err("source recursor family differs".into());
    }
    recs.push((name, rv.clone()));
  }
  let mut stt = CompileState::new_empty();
  stt.lean_env = Some(Arc::clone(env));
  let mut kctx = KernelCtx::new();
  let is_prop = prop_former(&ind.cnst.typ);
  let below = below::generate_below_constants_with(
    &classes, &recs, env, is_prop, true, &stt, &mut kctx,
  )
  .map_err(|e| e.to_string())?;
  let brecon = if include_brec_on {
    populate_canon_kenv_with_below(&below, &classes, env, &stt, &mut kctx)
      .map_err(|e| e.to_string())?;
    brecon::generate_brecon_constants_with(
      &classes, &recs, &below, env, is_prop, true, &stt, &mut kctx,
    )
    .map_err(|e| e.to_string())?
  } else {
    Vec::new()
  };
  let below_all = below
    .iter()
    .filter_map(|b| match b {
      BelowConstant::Indc(i) => Some(i.name.clone()),
      _ => None,
    })
    .collect::<Vec<_>>();
  let mut recipes = Vec::new();
  for b in below {
    match b {
      BelowConstant::Def(d) => recipes.push(Recipe::Definition(AuxDef {
        name: d.name,
        level_params: d.level_params,
        typ: d.typ,
        value: d.value,
        is_unsafe: d.is_unsafe,
      })),
      BelowConstant::Indc(i) => {
        recipes.push(Recipe::Inductive(i.clone(), below_all.clone()));
        for (index, ctor) in i.ctors.into_iter().enumerate() {
          recipes.push(Recipe::Constructor(
            ctor,
            i.name.clone(),
            i.level_params.clone(),
            index,
            i.is_unsafe,
          ));
        }
      },
    }
  }
  for d in brecon {
    let theorem = !d.is_unsafe
      && (d.is_prop
        || matches!(d.name.as_data(), NameData::Str(_, s, _) if s == "eq"));
    let expected = AuxDef {
      name: d.name,
      level_params: d.level_params,
      typ: d.typ,
      value: d.value,
      is_unsafe: d.is_unsafe,
    };
    recipes.push(if theorem {
      Recipe::Theorem(expected)
    } else {
      Recipe::Definition(expected)
    });
  }
  Ok(recipes)
}

/// Recognition is outside the occurrence loop. Only authenticated source
/// declarations enter the image-head table consulted by the optimizations.
pub fn filter_heads(
  env: &Arc<Env>,
  all: &[Name],
  heads: Vec<Name>,
) -> Vec<Name> {
  if !heads.iter().any(is_derived) {
    return heads;
  }
  let recipes =
    reconstruct(env, all, heads.iter().any(is_brec_on)).unwrap_or_default();
  heads
    .into_iter()
    .filter(|n| {
      !is_derived(n)
        || authenticated(env, &recipes, recipes.len() + 1, &mut Vec::new(), n)
    })
    .collect()
}

#[cfg(test)]
mod tests {
  use super::*;
  use ix_common::env::{InductiveVal, Level};

  fn dense_family() -> (Env, Vec<Recipe>, Vec<Name>) {
    let names = (0..32)
      .map(|i| Name::str(Name::anon(), format!("FamilyGraph{i}")))
      .collect::<Vec<_>>();
    let mut env = Env::default();
    let mut recipes = Vec::new();
    for name in &names {
      let typ = Expr::sort(Level::zero());
      let expected = BelowIndc {
        name: name.clone(),
        source_name: name.clone(),
        level_params: vec![],
        n_params: 0,
        n_indices: 0,
        is_reflexive: false,
        is_unsafe: false,
        typ: typ.clone(),
        ctors: vec![],
      };
      env.insert(
        name.clone(),
        ConstantInfo::InductInfo(InductiveVal {
          cnst: ConstantVal { name: name.clone(), level_params: vec![], typ },
          num_params: 0u64.into(),
          num_indices: 0u64.into(),
          all: names.clone(),
          ctors: vec![],
          num_nested: 0u64.into(),
          is_rec: false,
          is_unsafe: false,
          is_reflexive: false,
        }),
      );
      recipes.push(Recipe::Inductive(expected, names.clone()));
    }
    (env, recipes, names)
  }

  #[test]
  fn dense_families_share_completed_visits() {
    let (env, recipes, names) = dense_family();
    let mut seen = Vec::new();
    assert!(authenticated(
      &env,
      &recipes,
      recipes.len() + 1,
      &mut seen,
      &names[0],
    ));
    assert_eq!(seen.len(), names.len());
    assert!(names.iter().all(|n| seen.contains(n)));
  }

  #[test]
  fn a_cycle_or_visited_name_cannot_hide_an_altered_member() {
    let (mut env, recipes, names) = dense_family();
    let bad_name = &names[31];
    let ConstantInfo::InductInfo(mut actual) =
      env.get(bad_name).unwrap().cloned()
    else {
      panic!("dense member missing");
    };
    actual.cnst.typ = Expr::sort(Level::succ(Level::zero()));
    env.insert(bad_name.clone(), ConstantInfo::InductInfo(actual));
    assert!(!authenticated(
      &env,
      &recipes,
      recipes.len() + 1,
      &mut Vec::new(),
      &names[0],
    ));
    assert!(!authenticated(
      &env,
      &recipes,
      recipes.len() + 1,
      &mut names.clone(),
      bad_name,
    ));
  }
}
