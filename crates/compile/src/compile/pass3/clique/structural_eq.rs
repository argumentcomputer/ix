//! Regenerating a structural member's equation proof over the transported
//! definitions (a port of `Ix/Compile/Pass/Clique/StructuralEq.lean`).
//!
//! The old proof is deliberately not an input to the recipe: its
//! `brecOn.go`/`brecOn.eq`, packed tuples and splitter motives use the source
//! order. The supported recipe splits an unindexed recursive argument using
//! its actual `casesOn` declaration and closes every branch by conversion and
//! `Eq.refl`. Trailing dependent binders stay inside the motive. Indexed or
//! otherwise unsupported telescopes, missing input declarations, failed
//! conversion checks and an exhausted bound ([`EQ_DEF_CONVERSION_FUEL`], the
//! reducer's [`WHNF_FUEL`]) return an error; the structural transport
//! ([`super::structural`]) then keeps its refusal. This is a bounded proof
//! constructor, not a new source-domain restriction.

use std::slice;

use ix_common::env::{
  ConstantInfo, Expr, ExprData, Level, LevelData, Name, NameData,
};

use super::basic::{
  ConstOf, Decl, Local, R, TState, bvar, cnst, const_app, dotted, forall_arity,
  instantiate_rev, mk_app_n, mk_forall, mk_lambda, mk_str, peel_foralls,
  tm_idx,
};
use super::bounds::{EQ_DEF_CONVERSION_FUEL, WHNF_FUEL};
use super::telescope::{close_binders, open_binders, whnf};
use crate::compile::pass3::expr::{
  inst_forall, nat_usize, strip_mdata, subst_levels,
};

/// `eqDefNameEq`: name equality by components: proof admission never
/// treats a cached digest as an equality witness.
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

/// `eqDefLevelEq`: level equality by structure, names by components.
pub fn eq_def_level_eq(a: &Level, b: &Level) -> bool {
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

/// `eqDefLevelsEq`.
pub fn eq_def_levels_eq(a: &[Level], b: &[Level]) -> bool {
  a.len() == b.len() && a.iter().zip(b).all(|(x, y)| eq_def_level_eq(x, y))
}

/// `eqDefExprEq`: alpha equality with structural names and levels, ignoring
/// metadata and all stored hashes. No memo hit can admit an unequal proof
/// branch.
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

/// `eqDefConvertible`: a sufficient conversion check, using only
/// beta/delta/zeta/iota and projection reduction from the structural reducer
/// ([`whnf`]). Exhaustion (of `fuel` or of the reducer's bound) or an
/// unsupported conversion refuses the branch; it never assumes equality.
/// Equal subterms are compared before delta reduction, keeping shared
/// recursive calls opaque when their actual syntax already agrees.
pub fn eq_def_convertible(
  const_of: ConstOf<'_>,
  fuel: usize,
  a: &Expr,
  b: &Expr,
) -> bool {
  let Some(fuel) = fuel.checked_sub(1) else { return false };
  if eq_def_expr_eq(a, b) {
    return true;
  }
  let (Ok(a), Ok(b)) =
    (whnf(const_of, WHNF_FUEL, a), whnf(const_of, WHNF_FUEL, b))
  else {
    return false;
  };
  if eq_def_expr_eq(&a, &b) {
    return true;
  }
  match (strip_mdata(&a).as_data(), strip_mdata(&b).as_data()) {
    (ExprData::App(f, x, _), ExprData::App(g, y, _)) => {
      eq_def_convertible(const_of, fuel, f, g)
        && eq_def_convertible(const_of, fuel, x, y)
    },
    (ExprData::Lam(_, t, x, _, _), ExprData::Lam(_, u, y, _, _))
    | (ExprData::ForallE(_, t, x, _, _), ExprData::ForallE(_, u, y, _, _)) => {
      eq_def_convertible(const_of, fuel, t, u)
        && eq_def_convertible(const_of, fuel, x, y)
    },
    (ExprData::Proj(s, i, x, _), ExprData::Proj(t, j, y, _)) => {
      i == j && eq_def_name_eq(s, t) && eq_def_convertible(const_of, fuel, x, y)
    },
    _ => false,
  }
}

/// `eqDefEquality`: read a proposition after reduction as
/// `@Eq.{u} α lhs rhs`: `(us, α, lhs, rhs)`, retaining its exact equality
/// universe.
pub fn eq_def_equality(
  const_of: ConstOf<'_>,
  typ: &Expr,
) -> R<(Vec<Level>, Expr, Expr, Expr)> {
  let not_eq = || "structural eq_def: branch is not an equality".to_string();
  let Some((head, us, args)) = const_app(&whnf(const_of, WHNF_FUEL, typ)?)
  else {
    return Err(not_eq());
  };
  if !(eq_def_name_eq(&head, &dotted("Eq")) && us.len() == 1) {
    return Err(not_eq());
  }
  let [alpha, lhs, rhs] = args.as_slice() else { return Err(not_eq()) };
  Ok((us, alpha.clone(), lhs.clone(), rhs.clone()))
}

/// `eqDefReflLeaf`: introduce the actual alternative fields and trailing
/// dependent binders, then generate reflexivity only after checking both
/// sides by conversion.
pub fn eq_def_refl_leaf(
  tm: &mut TState,
  const_of: ConstOf<'_>,
  fuel: usize,
  typ: &Expr,
) -> R<Expr> {
  let Some(fuel) = fuel.checked_sub(1) else {
    return Err("structural eq_def: branch telescope bound exhausted".into());
  };
  let typ = whnf(const_of, WHNF_FUEL, typ)?;
  let stripped = strip_mdata(&typ);
  match stripped.as_data() {
    ExprData::ForallE(nm, dom, body, bi, _) => {
      let fvar = tm.fresh_fvar();
      let x =
        Local { fvar, user_name: nm.clone(), typ: dom.clone(), bi: bi.clone() };
      let proof = eq_def_refl_leaf(
        tm,
        const_of,
        fuel,
        &instantiate_rev(body, &[x.expr()]),
      )?;
      Ok(mk_lambda(slice::from_ref(&x), &proof))
    },
    _ => {
      let (us, alpha, lhs, rhs) = eq_def_equality(const_of, &typ)?;
      if !eq_def_convertible(const_of, EQ_DEF_CONVERSION_FUEL, &lhs, &rhs) {
        return Err(
          "structural eq_def: constructor branch does not close by conversion"
            .into(),
        );
      }
      Ok(mk_app_n(cnst(&dotted("Eq.refl"), &us), &[alpha, lhs]))
    },
  }
}

/// `regenerateStructuralEq`: regenerate `member.eq_def` over a lookup
/// containing all transported members and functionals. The unchanged
/// statement must apply that exact member to its complete ordered telescope;
/// `major_pos` is the recursive binder's position in it. No source proof
/// syntax is transported. Only this path has the stated grammar; every other
/// case keeps the transport's refusal.
pub fn regenerate_structural_eq(
  tm: &mut TState,
  const_of: ConstOf<'_>,
  member: &Decl,
  equation: &Decl,
  new_name: &Name,
  major_pos: usize,
) -> R<Decl> {
  if !(equation.is_thm
    && eq_def_name_eq(&equation.name, &mk_str(&member.name, "eq_def")))
  {
    return Err("structural eq_def: not the member's unfolding theorem".into());
  }
  if !(equation.level_params.len() == member.level_params.len()
    && equation
      .level_params
      .iter()
      .zip(&member.level_params)
      .all(|(a, b)| eq_def_name_eq(a, b)))
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
  let (_, _, lhs, _) = eq_def_equality(const_of, &conclusion)?;
  let Some((owner, levels, args)) = const_app(&lhs) else {
    return Err(
      "structural eq_def: left side is not the member application".into(),
    );
  };
  let member_levels: Vec<Level> =
    member.level_params.iter().cloned().map(Level::param).collect();
  if !(eq_def_name_eq(&owner, &member.name)
    && eq_def_levels_eq(&levels, &member_levels)
    && args.len() == arity
    && args.iter().enumerate().all(|(i, a)| {
      eq_def_expr_eq(a, &bvar(arity.saturating_sub(1).saturating_sub(i)))
    }))
  {
    return Err(
      "structural eq_def: left side is not the complete ordered member \
       application"
        .into(),
    );
  }
  if const_of(&dotted("Eq.refl")).is_none() {
    return Err("structural eq_def: Eq.refl is not in the input".into());
  }
  let (opened, goal) = open_binders(tm, false, major_pos + 1, &equation.typ)?;
  let major =
    tm_idx(&opened, major_pos, "structural eq_def: the recursive binder")?
      .clone();
  let Some((ind, ind_levels, params)) =
    const_app(&whnf(const_of, WHNF_FUEL, &major.typ)?)
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
  if !(nat_usize(&iv.num_indices) == 0
    && params.len() == nat_usize(&iv.num_params))
  {
    return Err(
      "structural eq_def: indexed recursive telescope needs dependent \
       generalization"
        .into(),
    );
  }
  let cases_name = mk_str(&ind, "casesOn");
  let Some(ci) = const_of(&cases_name) else {
    return Err("structural eq_def: casesOn is not in the input".into());
  };
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
  let mut typ = subst_levels(level_params, &cases_levels, ci.get_type());
  typ = inst_forall(&typ, &params)?;
  let stripped = strip_mdata(&typ);
  let ExprData::ForallE(_, motive_type, _, _, _) = stripped.as_data() else {
    return Err("structural eq_def: casesOn has no motive".into());
  };
  if !eq_def_convertible(
    const_of,
    EQ_DEF_CONVERSION_FUEL,
    motive_type,
    &mk_forall(slice::from_ref(&major), &Expr::sort(Level::zero())),
  ) {
    return Err(
      "structural eq_def: casesOn motive is not the recursive-argument \
       predicate"
        .into(),
    );
  }
  let motive = mk_lambda(slice::from_ref(&major), &goal);
  typ = inst_forall(&typ, slice::from_ref(&motive))?;
  let stripped = strip_mdata(&typ);
  let ExprData::ForallE(_, major_type, _, _, _) = stripped.as_data() else {
    return Err("structural eq_def: casesOn has no major".into());
  };
  if !eq_def_convertible(
    const_of,
    EQ_DEF_CONVERSION_FUEL,
    major_type,
    &major.typ,
  ) {
    return Err("structural eq_def: casesOn major type differs".into());
  }
  typ = inst_forall(&typ, &[major.expr()])?;
  let mut proof_args = params;
  proof_args.extend([motive, major.expr()]);
  for _ in &iv.ctors {
    let stripped = strip_mdata(&typ);
    let ExprData::ForallE(_, alternative, _, _, _) = stripped.as_data() else {
      return Err("structural eq_def: casesOn has too few alternatives".into());
    };
    let proof =
      eq_def_refl_leaf(tm, const_of, EQ_DEF_CONVERSION_FUEL, alternative)?;
    proof_args.push(proof.clone());
    typ = inst_forall(&typ, &[proof])?;
  }
  if !eq_def_convertible(const_of, EQ_DEF_CONVERSION_FUEL, &typ, &goal) {
    return Err(
      "structural eq_def: casesOn result differs from the full statement"
        .into(),
    );
  }
  let value = close_binders(
    true,
    &opened,
    &mk_app_n(cnst(&cases_name, &cases_levels), &proof_args),
  )?;
  Ok(Decl { name: new_name.clone(), value, ..equation.clone() })
}

#[cfg(test)]
mod tests {
  use std::sync::Arc;

  use ix_common::env::{
    ConstantInfo, ConstantVal, DefinitionSafety, DefinitionVal, Expr, ExprData,
    Level, LevelData, Name, NameData, ReducibilityHints,
  };

  use super::{
    eq_def_convertible, eq_def_equality, eq_def_expr_eq, eq_def_level_eq,
    eq_def_name_eq, eq_def_refl_leaf,
  };
  use crate::compile::pass3::clique::basic::{
    TState, cnst, dotted, lvl_one, mk_app_n, sort0,
  };
  use crate::compile::pass3::clique::bounds::EQ_DEF_CONVERSION_FUEL;
  use crate::compile::pass3::expr::nat;

  fn c(s: &str) -> Expr {
    cnst(&dotted(s), &[])
  }

  fn eq(lhs: Expr, rhs: Expr) -> Expr {
    mk_app_n(cnst(&dotted("Eq"), &[lvl_one()]), &[c("Bool"), lhs, rhs])
  }

  /// `loop := loop`: the reducer never reaches a normal form.
  fn env(n: &Name) -> Option<ConstantInfo> {
    (*n == dotted("loop")).then(|| {
      ConstantInfo::DefnInfo(DefinitionVal {
        cnst: ConstantVal {
          name: dotted("loop"),
          level_params: vec![],
          typ: sort0(),
        },
        value: c("loop"),
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![dotted("loop")],
      })
    })
  }

  #[test]
  fn proof_admission_checks_structure_not_cached_hashes() {
    let h = blake3::hash(b"shared adversarial cache");
    let other = blake3::hash(b"different cache for equal structure");
    let zero = Expr(Arc::new(ExprData::Bvar(nat(0), h)));
    let one = Expr(Arc::new(ExprData::Bvar(nat(1), h)));
    let same = Expr(Arc::new(ExprData::Bvar(nat(0), other)));
    assert!(!eq_def_expr_eq(&zero, &one));
    assert!(eq_def_expr_eq(&zero, &same));
    let a = Name(Arc::new(NameData::Str(dotted("Prefix"), "a".into(), h)));
    let b = Name(Arc::new(NameData::Str(dotted("Prefix"), "b".into(), h)));
    assert!(!eq_def_name_eq(&a, &b));
    let u = Level(Arc::new(LevelData::Zero(h)));
    let v = Level(Arc::new(LevelData::Succ(u.clone(), h)));
    let same_u = Level(Arc::new(LevelData::Zero(other)));
    assert!(!eq_def_level_eq(&u, &v));
    assert!(eq_def_level_eq(&u, &same_u));
  }

  #[test]
  fn conversion_refuses_false_leaves_whnf_failure_and_exhaustion() {
    let fuel = EQ_DEF_CONVERSION_FUEL;
    let a = c("Bool.true");
    let b = c("Bool.false");
    assert!(eq_def_convertible(&env, fuel, &a, &a));
    assert!(!eq_def_convertible(&env, fuel, &a, &b));
    assert!(!eq_def_convertible(&env, 0, &a, &a));
    // the reducer's exhaustion refuses, it never assumes equality
    assert!(!eq_def_convertible(&env, fuel, &c("loop"), &a));
    assert_eq!(
      eq_def_equality(&env, &eq(a.clone(), b.clone())),
      Ok((vec![lvl_one()], c("Bool"), a.clone(), b.clone()))
    );
    assert_eq!(
      eq_def_equality(&env, &a),
      Err("structural eq_def: branch is not an equality".to_string())
    );
    assert_eq!(
      eq_def_equality(&env, &c("loop")),
      Err("whnf: fuel exhausted".to_string())
    );
    let mut tm = TState::default();
    assert_eq!(
      eq_def_refl_leaf(&mut tm, &env, fuel, &eq(a.clone(), a.clone())),
      Ok(mk_app_n(
        cnst(&dotted("Eq.refl"), &[lvl_one()]),
        &[c("Bool"), a.clone()]
      ))
    );
    assert_eq!(
      eq_def_refl_leaf(&mut tm, &env, fuel, &eq(a.clone(), b)),
      Err(
        "structural eq_def: constructor branch does not close by conversion"
          .to_string()
      )
    );
    assert_eq!(
      eq_def_refl_leaf(&mut tm, &env, 0, &eq(a.clone(), a)),
      Err("structural eq_def: branch telescope bound exhausted".to_string())
    );
  }
}
