use crate::ix::env::{Expr, ExprData, Level, LevelData, Name};

/// Simplify a universe level expression.
pub fn simplify(l: &Level) -> Level {
  match l.as_data() {
    LevelData::Zero(_) | LevelData::Param(..) | LevelData::Mvar(..) => {
      l.clone()
    },
    LevelData::Succ(inner, _) => {
      let inner_s = simplify(inner);
      Level::succ(inner_s)
    },
    LevelData::Max(a, b, _) => {
      let a_s = simplify(a);
      let b_s = simplify(b);
      combining(&a_s, &b_s)
    },
    LevelData::Imax(a, b, _) => {
      let a_s = simplify(a);
      let b_s = simplify(b);
      if is_zero(&a_s) || is_one(&a_s) {
        b_s
      } else {
        match b_s.as_data() {
          LevelData::Zero(_) => b_s,
          LevelData::Succ(..) => combining(&a_s, &b_s),
          _ => Level::imax(a_s, b_s),
        }
      }
    },
  }
}

/// Combine two levels, simplifying Max(Zero, x) = x and
/// Max(Succ a, Succ b) = Succ(Max(a, b)).
fn combining(l: &Level, r: &Level) -> Level {
  match (l.as_data(), r.as_data()) {
    (LevelData::Zero(_), _) => r.clone(),
    (_, LevelData::Zero(_)) => l.clone(),
    (LevelData::Succ(a, _), LevelData::Succ(b, _)) => {
      let inner = combining(a, b);
      Level::succ(inner)
    },
    _ => Level::max(l.clone(), r.clone()),
  }
}

fn is_one(l: &Level) -> bool {
  matches!(l.as_data(), LevelData::Succ(inner, _) if is_zero(inner))
}

/// Check if a level is definitionally zero: l <= 0.
pub fn is_zero(l: &Level) -> bool {
  leq(l, &Level::zero())
}

/// Check if `l <= r`.
pub fn leq(l: &Level, r: &Level) -> bool {
  let l_s = simplify(l);
  let r_s = simplify(r);
  leq_core(&l_s, &r_s, 0)
}

/// Check `l <= r + diff`.
fn leq_core(l: &Level, r: &Level, diff: isize) -> bool {
  match (l.as_data(), r.as_data()) {
    (LevelData::Zero(_), _) if diff >= 0 => true,
    (_, LevelData::Zero(_)) if diff < 0 => false,
    (LevelData::Param(a, _), LevelData::Param(b, _)) => a == b && diff >= 0,
    (LevelData::Param(..), LevelData::Zero(_)) => false,
    (LevelData::Zero(_), LevelData::Param(..)) => diff >= 0,
    (LevelData::Succ(s, _), _) => leq_core(s, r, diff - 1),
    (_, LevelData::Succ(s, _)) => leq_core(l, s, diff + 1),
    (LevelData::Max(a, b, _), _) => {
      leq_core(a, r, diff) && leq_core(b, r, diff)
    },
    (LevelData::Param(..) | LevelData::Zero(_), LevelData::Max(x, y, _)) => {
      leq_core(l, x, diff) || leq_core(l, y, diff)
    },
    (LevelData::Imax(a, b, _), LevelData::Imax(x, y, _))
      if a == x && b == y =>
    {
      true
    },
    (LevelData::Imax(_, b, _), _) if is_param(b) => {
      leq_imax_by_cases(b, l, r, diff)
    },
    (_, LevelData::Imax(_, y, _)) if is_param(y) => {
      leq_imax_by_cases(y, l, r, diff)
    },
    (LevelData::Imax(a, b, _), _) if is_any_max(b) => {
      match b.as_data() {
        LevelData::Imax(x, y, _) => {
          let new_lhs = Level::imax(a.clone(), y.clone());
          let new_rhs = Level::imax(x.clone(), y.clone());
          let new_max = Level::max(new_lhs, new_rhs);
          leq_core(&new_max, r, diff)
        },
        LevelData::Max(x, y, _) => {
          let new_lhs = Level::imax(a.clone(), x.clone());
          let new_rhs = Level::imax(a.clone(), y.clone());
          let new_max = Level::max(new_lhs, new_rhs);
          let simplified = simplify(&new_max);
          leq_core(&simplified, r, diff)
        },
        _ => unreachable!(),
      }
    },
    (_, LevelData::Imax(x, y, _)) if is_any_max(y) => {
      match y.as_data() {
        LevelData::Imax(j, k, _) => {
          let new_lhs = Level::imax(x.clone(), k.clone());
          let new_rhs = Level::imax(j.clone(), k.clone());
          let new_max = Level::max(new_lhs, new_rhs);
          leq_core(l, &new_max, diff)
        },
        LevelData::Max(j, k, _) => {
          let new_lhs = Level::imax(x.clone(), j.clone());
          let new_rhs = Level::imax(x.clone(), k.clone());
          let new_max = Level::max(new_lhs, new_rhs);
          let simplified = simplify(&new_max);
          leq_core(l, &simplified, diff)
        },
        _ => unreachable!(),
      }
    },
    _ => false,
  }
}

/// Test l <= r by substituting param with 0 and Succ(param) and checking both.
fn leq_imax_by_cases(
  param: &Level,
  lhs: &Level,
  rhs: &Level,
  diff: isize,
) -> bool {
  let zero = Level::zero();
  let succ_param = Level::succ(param.clone());

  let lhs_0 = subst_and_simplify(lhs, param, &zero);
  let rhs_0 = subst_and_simplify(rhs, param, &zero);
  let lhs_s = subst_and_simplify(lhs, param, &succ_param);
  let rhs_s = subst_and_simplify(rhs, param, &succ_param);

  leq_core(&lhs_0, &rhs_0, diff) && leq_core(&lhs_s, &rhs_s, diff)
}

fn subst_and_simplify(level: &Level, from: &Level, to: &Level) -> Level {
  let substituted = subst_single_level(level, from, to);
  simplify(&substituted)
}

/// Substitute a single level parameter.
fn subst_single_level(level: &Level, from: &Level, to: &Level) -> Level {
  if level == from {
    return to.clone();
  }
  match level.as_data() {
    LevelData::Zero(_) | LevelData::Mvar(..) => level.clone(),
    LevelData::Param(..) => {
      if level == from {
        to.clone()
      } else {
        level.clone()
      }
    },
    LevelData::Succ(inner, _) => {
      Level::succ(subst_single_level(inner, from, to))
    },
    LevelData::Max(a, b, _) => Level::max(
      subst_single_level(a, from, to),
      subst_single_level(b, from, to),
    ),
    LevelData::Imax(a, b, _) => Level::imax(
      subst_single_level(a, from, to),
      subst_single_level(b, from, to),
    ),
  }
}

fn is_param(l: &Level) -> bool {
  matches!(l.as_data(), LevelData::Param(..))
}

fn is_any_max(l: &Level) -> bool {
  matches!(l.as_data(), LevelData::Max(..) | LevelData::Imax(..))
}

/// Check universe level equality via antisymmetry: l == r iff l <= r && r <= l.
pub fn eq_antisymm(l: &Level, r: &Level) -> bool {
  leq(l, r) && leq(r, l)
}

/// Check that two lists of levels are pointwise equal.
pub fn eq_antisymm_many(ls: &[Level], rs: &[Level]) -> bool {
  ls.len() == rs.len()
    && ls.iter().zip(rs.iter()).all(|(l, r)| eq_antisymm(l, r))
}

/// Substitute universe parameters: `level[params[i] := values[i]]`.
pub fn subst_level(
  level: &Level,
  params: &[Name],
  values: &[Level],
) -> Level {
  match level.as_data() {
    LevelData::Zero(_) => level.clone(),
    LevelData::Succ(inner, _) => {
      Level::succ(subst_level(inner, params, values))
    },
    LevelData::Max(a, b, _) => Level::max(
      subst_level(a, params, values),
      subst_level(b, params, values),
    ),
    LevelData::Imax(a, b, _) => Level::imax(
      subst_level(a, params, values),
      subst_level(b, params, values),
    ),
    LevelData::Param(name, _) => {
      for (i, p) in params.iter().enumerate() {
        if name == p {
          return values[i].clone();
        }
      }
      level.clone()
    },
    LevelData::Mvar(..) => level.clone(),
  }
}

/// Check that all universe parameters in `level` are contained in `params`.
pub fn all_uparams_defined(level: &Level, params: &[Name]) -> bool {
  match level.as_data() {
    LevelData::Zero(_) => true,
    LevelData::Succ(inner, _) => all_uparams_defined(inner, params),
    LevelData::Max(a, b, _) | LevelData::Imax(a, b, _) => {
      all_uparams_defined(a, params) && all_uparams_defined(b, params)
    },
    LevelData::Param(name, _) => params.iter().any(|p| p == name),
    LevelData::Mvar(..) => true,
  }
}

/// Check that all universe parameters in an expression are contained in `params`.
/// Recursively walks the Expr, checking all Levels in Sort and Const nodes.
pub fn all_expr_uparams_defined(e: &Expr, params: &[Name]) -> bool {
  let mut stack: Vec<&Expr> = vec![e];
  while let Some(e) = stack.pop() {
    match e.as_data() {
      ExprData::Sort(level, _) => {
        if !all_uparams_defined(level, params) {
          return false;
        }
      },
      ExprData::Const(_, levels, _) => {
        if !levels.iter().all(|l| all_uparams_defined(l, params)) {
          return false;
        }
      },
      ExprData::App(f, a, _) => {
        stack.push(f);
        stack.push(a);
      },
      ExprData::Lam(_, t, b, _, _) | ExprData::ForallE(_, t, b, _, _) => {
        stack.push(t);
        stack.push(b);
      },
      ExprData::LetE(_, t, v, b, _, _) => {
        stack.push(t);
        stack.push(v);
        stack.push(b);
      },
      ExprData::Proj(_, _, s, _) => stack.push(s),
      ExprData::Mdata(_, inner, _) => stack.push(inner),
      ExprData::Bvar(..)
      | ExprData::Fvar(..)
      | ExprData::Mvar(..)
      | ExprData::Lit(..) => {},
    }
  }
  true
}

/// Check that a list of levels are all Params with no duplicates.
pub fn no_dupes_all_params(levels: &[Name]) -> bool {
  for (i, a) in levels.iter().enumerate() {
    for b in &levels[i + 1..] {
      if a == b {
        return false;
      }
    }
  }
  true
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_simplify_zero() {
    let z = Level::zero();
    assert_eq!(simplify(&z), z);
  }

  #[test]
  fn test_simplify_max_zero() {
    let z = Level::zero();
    let p = Level::param(Name::str(Name::anon(), "u".into()));
    let m = Level::max(z, p.clone());
    assert_eq!(simplify(&m), p);
  }

  #[test]
  fn test_simplify_imax_zero_right() {
    let p = Level::param(Name::str(Name::anon(), "u".into()));
    let z = Level::zero();
    let im = Level::imax(p, z.clone());
    assert_eq!(simplify(&im), z);
  }

  #[test]
  fn test_simplify_imax_succ_right() {
    let p = Level::param(Name::str(Name::anon(), "u".into()));
    let one = Level::succ(Level::zero());
    let im = Level::imax(p.clone(), one.clone());
    let simplified = simplify(&im);
    // imax(p, 1) where p is nonzero → combining(p, 1)
    // Actually: imax(u, 1) simplifies since a_s = u, b_s = 1 = Succ(0)
    // → combining(u, 1) = max(u, 1) since u is Param, 1 is Succ
    let expected = Level::max(p, one);
    assert_eq!(simplified, expected);
  }

  #[test]
  fn test_simplify_idempotent() {
    let p = Level::param(Name::str(Name::anon(), "u".into()));
    let q = Level::param(Name::str(Name::anon(), "v".into()));
    let l = Level::max(
      Level::imax(p.clone(), q.clone()),
      Level::succ(Level::zero()),
    );
    let s1 = simplify(&l);
    let s2 = simplify(&s1);
    assert_eq!(s1, s2);
  }

  #[test]
  fn test_leq_reflexive() {
    let p = Level::param(Name::str(Name::anon(), "u".into()));
    assert!(leq(&p, &p));
    assert!(leq(&Level::zero(), &Level::zero()));
  }

  #[test]
  fn test_leq_zero_anything() {
    let p = Level::param(Name::str(Name::anon(), "u".into()));
    assert!(leq(&Level::zero(), &p));
    assert!(leq(&Level::zero(), &Level::succ(Level::zero())));
  }

  #[test]
  fn test_leq_succ_not_zero() {
    let one = Level::succ(Level::zero());
    assert!(!leq(&one, &Level::zero()));
  }

  #[test]
  fn test_eq_antisymm_identity() {
    let p = Level::param(Name::str(Name::anon(), "u".into()));
    assert!(eq_antisymm(&p, &p));
  }

  #[test]
  fn test_eq_antisymm_max_comm() {
    let p = Level::param(Name::str(Name::anon(), "u".into()));
    let q = Level::param(Name::str(Name::anon(), "v".into()));
    let m1 = Level::max(p.clone(), q.clone());
    let m2 = Level::max(q, p);
    assert!(eq_antisymm(&m1, &m2));
  }

  #[test]
  fn test_subst_level() {
    let u_name = Name::str(Name::anon(), "u".into());
    let p = Level::param(u_name.clone());
    let one = Level::succ(Level::zero());
    let result = subst_level(&p, &[u_name], &[one.clone()]);
    assert_eq!(result, one);
  }

  #[test]
  fn test_subst_level_nested() {
    let u_name = Name::str(Name::anon(), "u".into());
    let p = Level::param(u_name.clone());
    let l = Level::succ(p);
    let zero = Level::zero();
    let result = subst_level(&l, &[u_name], &[zero]);
    let expected = Level::succ(Level::zero());
    assert_eq!(result, expected);
  }
}
