//! Canonical structural equation proofs; port of `StructuralEq.lean`.
//!
//! Split an unindexed recursive argument with its actual source casesOn,
//! introduce all alternative/trailing binders and require conversion before
//! emitting Eq.refl. No source proof syntax is transported. Any unsupported
//! case returns an error to the existing structural SHAPE refusal.

use ix_common::env::{
  ConstantInfo, Expr, ExprData, Level, LevelData, Name, NameData,
};

use super::basic::*;
use super::telescope::{WHNF_FUEL, close_binders, open_binders, whnf};
use crate::compile::pass3::expr::{
  inst_forall, nat_usize, strip_mdata, subst_levels,
};

pub fn eq_def_name_eq(a: &Name, b: &Name) -> bool {
  match (a.as_data(), b.as_data()) {
    (NameData::Anonymous(_), NameData::Anonymous(_)) => true,
    (NameData::Str(a, x, _), NameData::Str(b, y, _)) => {
      x == y && eq_def_name_eq(a, b)
    },
    (NameData::Num(a, x, _), NameData::Num(b, y, _)) => {
      x == y && eq_def_name_eq(a, b)
    },
    _ => false,
  }
}

fn eq_def_level_eq(a: &Level, b: &Level) -> bool {
  match (a.as_data(), b.as_data()) {
    (LevelData::Zero(_), LevelData::Zero(_)) => true,
    (LevelData::Succ(a, _), LevelData::Succ(b, _)) => eq_def_level_eq(a, b),
    (LevelData::Max(a, b, _), LevelData::Max(c, d, _))
    | (LevelData::Imax(a, b, _), LevelData::Imax(c, d, _)) => {
      eq_def_level_eq(a, c) && eq_def_level_eq(b, d)
    },
    (LevelData::Param(a, _), LevelData::Param(b, _))
    | (LevelData::Mvar(a, _), LevelData::Mvar(b, _)) => eq_def_name_eq(a, b),
    _ => false,
  }
}

fn eq_def_levels_eq(a: &[Level], b: &[Level]) -> bool {
  a.len() == b.len() && a.iter().zip(b).all(|(x, y)| eq_def_level_eq(x, y))
}

/// Structural admission, without digest or memo-hit equality shortcuts.
pub fn eq_def_expr_eq(a: &Expr, b: &Expr) -> bool {
  match (a.as_data(), b.as_data()) {
    (ExprData::Mdata(_, a, _), _) => eq_def_expr_eq(a, b),
    (_, ExprData::Mdata(_, b, _)) => eq_def_expr_eq(a, b),
    (ExprData::Bvar(a, _), ExprData::Bvar(b, _)) => a == b,
    (ExprData::Fvar(a, _), ExprData::Fvar(b, _))
    | (ExprData::Mvar(a, _), ExprData::Mvar(b, _)) => eq_def_name_eq(a, b),
    (ExprData::Sort(a, _), ExprData::Sort(b, _)) => eq_def_level_eq(a, b),
    (ExprData::Const(a, us, _), ExprData::Const(b, vs, _)) => {
      eq_def_name_eq(a, b) && eq_def_levels_eq(us, vs)
    },
    (ExprData::App(f, a, _), ExprData::App(g, b, _)) => {
      eq_def_expr_eq(f, g) && eq_def_expr_eq(a, b)
    },
    (ExprData::Lam(_, a, b, _, _), ExprData::Lam(_, c, d, _, _))
    | (ExprData::ForallE(_, a, b, _, _), ExprData::ForallE(_, c, d, _, _)) => {
      eq_def_expr_eq(a, c) && eq_def_expr_eq(b, d)
    },
    (ExprData::LetE(_, t, v, b, _, _), ExprData::LetE(_, u, w, c, _, _)) => {
      eq_def_expr_eq(t, u) && eq_def_expr_eq(v, w) && eq_def_expr_eq(b, c)
    },
    (ExprData::Lit(a, _), ExprData::Lit(b, _)) => a == b,
    (ExprData::Proj(s, i, a, _), ExprData::Proj(t, j, b, _)) => {
      i == j && eq_def_name_eq(s, t) && eq_def_expr_eq(a, b)
    },
    _ => false,
  }
}

pub fn eq_def_convertible(
  const_of: ConstOf<'_>,
  fuel: usize,
  a: &Expr,
  b: &Expr,
) -> bool {
  if fuel == 0 {
    return false;
  }
  if eq_def_expr_eq(a, b) {
    return true;
  }
  let a = whnf(const_of, WHNF_FUEL, a);
  let b = whnf(const_of, WHNF_FUEL, b);
  if eq_def_expr_eq(&a, &b) {
    return true;
  }
  match (strip_mdata(&a).as_data(), strip_mdata(&b).as_data()) {
    (ExprData::App(f, x, _), ExprData::App(g, y, _)) => {
      eq_def_convertible(const_of, fuel - 1, f, g)
        && eq_def_convertible(const_of, fuel - 1, x, y)
    },
    (ExprData::Lam(_, t, x, _, _), ExprData::Lam(_, u, y, _, _))
    | (ExprData::ForallE(_, t, x, _, _), ExprData::ForallE(_, u, y, _, _)) => {
      eq_def_convertible(const_of, fuel - 1, t, u)
        && eq_def_convertible(const_of, fuel - 1, x, y)
    },
    (ExprData::Proj(s, i, x, _), ExprData::Proj(t, j, y, _)) => {
      i == j
        && eq_def_name_eq(s, t)
        && eq_def_convertible(const_of, fuel - 1, x, y)
    },
    _ => false,
  }
}

fn eq_def_equality(
  const_of: ConstOf<'_>,
  typ: &Expr,
) -> R<(Vec<Level>, Vec<Expr>)> {
  let Some((head, us, args)) = const_app(&whnf(const_of, WHNF_FUEL, typ))
  else {
    return Err("structural eq_def: branch is not an equality".into());
  };
  if !eq_def_name_eq(&head, &ln("Eq")) || us.len() != 1 || args.len() != 3 {
    return Err("structural eq_def: branch is not an equality".into());
  }
  Ok((us, args))
}

fn eq_def_refl_leaf(
  tm: &mut Tm,
  const_of: ConstOf<'_>,
  fuel: usize,
  typ: &Expr,
) -> R<Expr> {
  if fuel == 0 {
    return Err("structural eq_def: branch telescope bound exhausted".into());
  }
  let typ = whnf(const_of, WHNF_FUEL, typ);
  match strip_mdata(&typ).as_data() {
    ExprData::ForallE(nm, dom, body, bi, _) => {
      let fvar = tm.fresh();
      let x = local(fvar, nm.clone(), dom.clone(), bi.clone());
      let proof = eq_def_refl_leaf(
        tm,
        const_of,
        fuel - 1,
        &instantiate_rev(body, &[x.expr()]),
      )?;
      Ok(mk_lambda(&[x], &proof))
    },
    _ => {
      let (us, args) = eq_def_equality(const_of, &typ)?;
      if !eq_def_convertible(const_of, 256, &args[1], &args[2]) {
        return Err(
          "structural eq_def: constructor branch does not close by conversion"
            .into(),
        );
      }
      Ok(mk_app_n(
        cnst(&ln("Eq.refl"), &us),
        &[args[0].clone(), args[1].clone()],
      ))
    },
  }
}

/// The original complete member application and full statement are retained.
/// Unsupported indexed/dependent cases return the existing caller's refusal.
pub fn regenerate_structural_eq(
  tm: &mut Tm,
  const_of: ConstOf<'_>,
  member: &Decl,
  equation: &Decl,
  new_name: &Name,
  major_pos: usize,
) -> R<Decl> {
  if !equation.is_thm
    || !eq_def_name_eq(&equation.name, &mk_str(&member.name, "eq_def"))
  {
    return Err("structural eq_def: not the member's unfolding theorem".into());
  }
  if equation.level_params.len() != member.level_params.len()
    || !equation
      .level_params
      .iter()
      .zip(&member.level_params)
      .all(|(a, b)| eq_def_name_eq(a, b))
  {
    return Err(
      "structural eq_def: universe parameters differ from the member".into(),
    );
  }
  let arity = forall_arity(&equation.typ);
  if major_pos >= arity {
    return Err("structural eq_def: recursive binder is absent".into());
  }
  let (_, conclusion) = peel_foralls(arity, &equation.typ);
  let (_, eq_args) = eq_def_equality(const_of, &conclusion)?;
  let Some((owner, levels, args)) = const_app(&eq_args[1]) else {
    return Err(
      "structural eq_def: left side is not the member application".into(),
    );
  };
  let expected_levels: Vec<_> =
    member.level_params.iter().cloned().map(Level::param).collect();
  if !eq_def_name_eq(&owner, &member.name)
    || !eq_def_levels_eq(&levels, &expected_levels)
    || args.len() != arity
    || !args.iter().enumerate().all(|(i, a)| {
      eq_def_expr_eq(a, &crate::compile::pass3::expr::bvar(arity - 1 - i))
    })
  {
    return Err("structural eq_def: left side is not the complete ordered member application".into());
  }
  if const_of(&ln("Eq.refl")).is_none() {
    return Err("structural eq_def: Eq.refl is not in the input".into());
  }
  let (prefix, goal) = open_binders(tm, false, major_pos + 1, &equation.typ)?;
  let major = &prefix[major_pos];
  let Some((ind, ind_levels, params)) =
    const_app(&whnf(const_of, WHNF_FUEL, &major.typ))
  else {
    return Err(
      "structural eq_def: recursive argument has no inductive head".into(),
    );
  };
  let Some(ConstantInfo::InductInfo(iv)) = const_of(&ind) else {
    return Err(
      "structural eq_def: recursive argument is not an input inductive".into(),
    );
  };
  if nat_usize(&iv.num_indices) != 0
    || params.len() != nat_usize(&iv.num_params)
  {
    return Err("structural eq_def: indexed recursive telescope needs dependent generalization".into());
  }
  let cases_name = mk_str(&ind, "casesOn");
  let ci = const_of(&cases_name)
    .ok_or("structural eq_def: casesOn is not in the input")?;
  let level_params = ci.get_level_params();
  let cases_levels = if level_params.len() == ind_levels.len() + 1 {
    let mut us = vec![Level::zero()];
    us.extend(ind_levels);
    us
  } else if level_params.len() == ind_levels.len() {
    ind_levels
  } else {
    return Err("structural eq_def: casesOn universe telescope differs".into());
  };
  let mut typ = inst_forall(
    &subst_levels(level_params, &cases_levels, ci.get_type()),
    &params,
  )?;
  let mt = strip_mdata(&typ);
  let ExprData::ForallE(_, motive_type, _, _, _) = mt.as_data() else {
    return Err("structural eq_def: casesOn has no motive".into());
  };
  if !eq_def_convertible(
    const_of,
    256,
    motive_type,
    &mk_forall(std::slice::from_ref(major), &Expr::sort(Level::zero())),
  ) {
    return Err("structural eq_def: casesOn motive is not the recursive-argument predicate".into());
  }
  let motive = mk_lambda(std::slice::from_ref(major), &goal);
  typ = inst_forall(&typ, std::slice::from_ref(&motive))?;
  let mt = strip_mdata(&typ);
  let ExprData::ForallE(_, major_type, _, _, _) = mt.as_data() else {
    return Err("structural eq_def: casesOn has no major".into());
  };
  if !eq_def_convertible(const_of, 256, major_type, &major.typ) {
    return Err("structural eq_def: casesOn major type differs".into());
  }
  typ = inst_forall(&typ, &[major.expr()])?;
  let mut proof_args = params;
  proof_args.extend([motive, major.expr()]);
  for _ in &iv.ctors {
    let mt = strip_mdata(&typ);
    let ExprData::ForallE(_, alternative, _, _, _) = mt.as_data() else {
      return Err("structural eq_def: casesOn has too few alternatives".into());
    };
    let proof = eq_def_refl_leaf(tm, const_of, 256, alternative)?;
    typ = inst_forall(&typ, std::slice::from_ref(&proof))?;
    proof_args.push(proof);
  }
  if !eq_def_convertible(const_of, 256, &typ, &goal) {
    return Err(
      "structural eq_def: casesOn result differs from the full statement"
        .into(),
    );
  }
  let value = close_binders(
    true,
    &prefix,
    &mk_app_n(cnst(&cases_name, &cases_levels), &proof_args),
  )?;
  Ok(Decl { name: new_name.clone(), value, ..equation.clone() })
}

#[cfg(test)]
mod tests {
  use std::sync::Arc;

  use super::*;
  use crate::compile::pass3::expr::nat;

  #[test]
  fn proof_admission_checks_structure_not_cached_hashes() {
    let h = blake3::hash(b"shared adversarial cache");
    let other = blake3::hash(b"different cache for equal structure");
    let zero = Expr(Arc::new(ExprData::Bvar(nat(0), h)));
    let one = Expr(Arc::new(ExprData::Bvar(nat(1), h)));
    let same = Expr(Arc::new(ExprData::Bvar(nat(0), other)));
    assert!(!eq_def_expr_eq(&zero, &one));
    assert!(eq_def_expr_eq(&zero, &same));
    let a = Name(Arc::new(NameData::Str(ln("Prefix"), "a".into(), h)));
    let b = Name(Arc::new(NameData::Str(ln("Prefix"), "b".into(), h)));
    assert!(!eq_def_name_eq(&a, &b));
    let u = Level(Arc::new(LevelData::Zero(h)));
    let v = Level(Arc::new(LevelData::Succ(u.clone(), h)));
    let same_u = Level(Arc::new(LevelData::Zero(other)));
    assert!(!eq_def_level_eq(&u, &v));
    assert!(eq_def_level_eq(&u, &same_u));
  }

  #[test]
  fn conversion_refuses_false_leaves_and_exhaustion() {
    let lookup = |_: &Name| None;
    let a = cnst(&ln("Bool.true"), &[]);
    let b = cnst(&ln("Bool.false"), &[]);
    assert!(eq_def_convertible(&lookup, 256, &a, &a));
    assert!(!eq_def_convertible(&lookup, 256, &a, &b));
    assert!(!eq_def_convertible(&lookup, 0, &a, &a));
    let eq = |lhs, rhs| {
      mk_app_n(
        cnst(&ln("Eq"), &[lvl_one()]),
        &[cnst(&ln("Bool"), &[]), lhs, rhs],
      )
    };
    assert!(
      eq_def_refl_leaf(
        &mut Tm::default(),
        &lookup,
        256,
        &eq(a.clone(), a.clone())
      )
      .is_ok()
    );
    assert!(
      eq_def_refl_leaf(&mut Tm::default(), &lookup, 256, &eq(a, b)).is_err()
    );
  }
}
