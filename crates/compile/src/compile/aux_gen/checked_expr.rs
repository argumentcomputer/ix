//! Cancellable, DAG-preserving versions of the transforms used by validation.
//! Caches are local to one substitution context, and include binder depth:
//! the same shared BVar can mean different things beneath different binders.

use bignat::Nat;
use blake3::Hash;
use ix_common::env::{Expr as LeanExpr, ExprData, Level, LevelData, Name};
use rustc_hash::{FxHashMap, FxHashSet};

use super::expr_utils::{LocalDecl, fresh_fvar};
use crate::compile::nat_conv::nat_to_u64;
use crate::compile::validation::{Cancelled, Checkpoint};

type Key = (Hash, u64);
type Result<T> = std::result::Result<T, Cancelled>;

fn rewrite(
  e: &LeanExpr,
  depth: u64,
  control: &Checkpoint,
  cache: &mut FxHashMap<Key, LeanExpr>,
  leaf: &mut impl FnMut(&LeanExpr, u64) -> Result<Option<LeanExpr>>,
) -> Result<LeanExpr> {
  control.visit()?;
  let key = (*e.get_hash(), depth);
  if let Some(value) = cache.get(&key) {
    return Ok(value.clone());
  }
  let result = if let Some(value) = leaf(e, depth)? {
    value
  } else {
    match e.as_data() {
      ExprData::App(f, a, _) => LeanExpr::app(
        rewrite(f, depth, control, cache, leaf)?,
        rewrite(a, depth, control, cache, leaf)?,
      ),
      ExprData::Lam(n, t, b, bi, _) => LeanExpr::lam(
        n.clone(),
        rewrite(t, depth, control, cache, leaf)?,
        rewrite(b, depth + 1, control, cache, leaf)?,
        bi.clone(),
      ),
      ExprData::ForallE(n, t, b, bi, _) => LeanExpr::all(
        n.clone(),
        rewrite(t, depth, control, cache, leaf)?,
        rewrite(b, depth + 1, control, cache, leaf)?,
        bi.clone(),
      ),
      ExprData::LetE(n, t, v, b, nd, _) => LeanExpr::letE(
        n.clone(),
        rewrite(t, depth, control, cache, leaf)?,
        rewrite(v, depth, control, cache, leaf)?,
        rewrite(b, depth + 1, control, cache, leaf)?,
        *nd,
      ),
      ExprData::Proj(n, i, v, _) => LeanExpr::proj(
        n.clone(),
        i.clone(),
        rewrite(v, depth, control, cache, leaf)?,
      ),
      ExprData::Mdata(md, v, _) => {
        LeanExpr::mdata(md.clone(), rewrite(v, depth, control, cache, leaf)?)
      },
      _ => e.clone(),
    }
  };
  // Avoid retaining a second copy of unchanged nodes and their children.
  let result =
    if result.get_hash() == e.get_hash() { e.clone() } else { result };
  cache.insert(key, result.clone());
  control.scratch(
    cache.capacity() * (size_of::<(Key, LeanExpr)>() + size_of::<ExprData>()),
  );
  Ok(result)
}

fn transform(
  e: &LeanExpr,
  control: &Checkpoint,
  mut leaf: impl FnMut(&LeanExpr, u64) -> Result<Option<LeanExpr>>,
) -> Result<LeanExpr> {
  rewrite(e, 0, control, &mut FxHashMap::default(), &mut leaf)
}

pub(super) fn instantiate1(
  e: &LeanExpr,
  replacement: &LeanExpr,
  c: &Checkpoint,
) -> Result<LeanExpr> {
  instantiate1_at(e, replacement, 0, c)
}

pub(super) fn instantiate1_at(
  e: &LeanExpr,
  replacement: &LeanExpr,
  depth: u64,
  c: &Checkpoint,
) -> Result<LeanExpr> {
  rewrite(e, depth, c, &mut FxHashMap::default(), &mut |e, depth| {
    Ok(match e.as_data() {
      ExprData::Bvar(i, _) if nat_to_u64(i) == depth => {
        Some(replacement.clone())
      },
      ExprData::Bvar(i, _) if nat_to_u64(i) > depth => {
        Some(LeanExpr::bvar(Nat::from(nat_to_u64(i) - 1)))
      },
      _ => None,
    })
  })
}

pub(super) fn instantiate_rev(
  e: &LeanExpr,
  args: &[LeanExpr],
  c: &Checkpoint,
) -> Result<LeanExpr> {
  if args.is_empty() {
    c.visit()?;
    return Ok(e.clone());
  }
  let mut shifted = FxHashMap::default();
  transform(e, c, |e, depth| {
    let ExprData::Bvar(i, _) = e.as_data() else {
      return Ok(None);
    };
    let i = nat_to_u64(i);
    if i < depth {
      return Ok(None);
    }
    let index = i - depth;
    if index >= args.len() as u64 {
      return Ok(Some(LeanExpr::bvar(Nat::from(i - args.len() as u64))));
    }
    if let Some(value) = shifted.get(&(index, depth)) {
      return Ok(Some(LeanExpr::clone(value)));
    }
    let value = if depth == 0 {
      args[index as usize].clone()
    } else {
      transform(&args[index as usize], c, |e, inner| {
        Ok(match e.as_data() {
          ExprData::Bvar(i, _) if nat_to_u64(i) >= inner => {
            Some(LeanExpr::bvar(Nat::from(nat_to_u64(i) + depth)))
          },
          _ => None,
        })
      })?
    };
    shifted.insert((index, depth), value.clone());
    Ok(Some(value))
  })
}

pub(super) fn instantiate_pi_params(
  e: &LeanExpr,
  n: usize,
  args: &[LeanExpr],
  c: &Checkpoint,
) -> Result<LeanExpr> {
  debug_assert!(args.len() >= n);
  let mut cur = e.clone();
  for arg in args.iter().take(n) {
    c.visit()?;
    if let ExprData::ForallE(_, _, body, _, _) = cur.as_data() {
      cur = instantiate_rev(body, std::slice::from_ref(arg), c)?;
    } else {
      break;
    }
  }
  Ok(cur)
}

pub(super) fn forall_telescope(
  e: &LeanExpr,
  n: usize,
  prefix: &str,
  start: usize,
  c: &Checkpoint,
) -> Result<(Vec<LeanExpr>, Vec<LocalDecl>, LeanExpr)> {
  let mut fvars = Vec::new();
  let mut decls = Vec::new();
  let mut cur = e.clone();
  for i in 0..n {
    c.visit()?;
    while let ExprData::Mdata(_, inner, _) = cur.as_data() {
      c.visit()?;
      cur = inner.clone();
    }
    let ExprData::ForallE(name, dom, body, bi, _) = cur.as_data() else {
      break;
    };
    let (fvar_name, fv) = fresh_fvar(prefix, start + i);
    decls.push(LocalDecl {
      fvar_name,
      binder_name: name.clone(),
      domain: dom.clone(),
      info: bi.clone(),
    });
    fvars.push(fv.clone());
    cur = instantiate1(body, &fv, c)?;
  }
  Ok((fvars, decls, cur))
}

fn batch_abstract(
  e: &LeanExpr,
  vars: &FxHashMap<Name, usize>,
  scope: usize,
  c: &Checkpoint,
) -> Result<LeanExpr> {
  batch_abstract_at(e, vars, scope, 0, c)
}

pub(super) fn batch_abstract_at(
  e: &LeanExpr,
  vars: &FxHashMap<Name, usize>,
  scope: usize,
  depth: u64,
  c: &Checkpoint,
) -> Result<LeanExpr> {
  if scope == 0 {
    c.visit()?;
    return Ok(e.clone());
  }
  rewrite(e, depth, c, &mut FxHashMap::default(), &mut |e, depth| {
    Ok(match e.as_data() {
      ExprData::Fvar(n, _) => {
        vars.get(n).filter(|&&pos| pos < scope).map(|&pos| {
          LeanExpr::bvar(Nat::from((scope - 1 - pos) as u64 + depth))
        })
      },
      ExprData::Bvar(i, _) if nat_to_u64(i) >= depth => {
        Some(LeanExpr::bvar(Nat::from(nat_to_u64(i) + scope as u64)))
      },
      _ => None,
    })
  })
}

pub(super) fn mk_forall(
  body: LeanExpr,
  binders: &[LocalDecl],
  c: &Checkpoint,
) -> Result<LeanExpr> {
  c.visit()?;
  if binders.is_empty() {
    return Ok(body);
  }
  let vars =
    binders.iter().enumerate().map(|(i, d)| (d.fvar_name.clone(), i)).collect();
  let mut result = batch_abstract(&body, &vars, binders.len(), c)?;
  for (j, decl) in binders.iter().enumerate().rev() {
    c.visit()?;
    let domain = batch_abstract(&decl.domain, &vars, j, c)?;
    result = LeanExpr::all(
      decl.binder_name.clone(),
      domain,
      result,
      decl.info.clone(),
    );
  }
  Ok(result)
}

pub(super) fn replace_params(
  e: &LeanExpr,
  from: &[LeanExpr],
  to: &[LeanExpr],
  c: &Checkpoint,
) -> Result<LeanExpr> {
  if from.is_empty() {
    c.visit()?;
    return Ok(e.clone());
  }
  let vars: FxHashMap<_, _> = from
    .iter()
    .zip(to)
    .filter_map(|(a, b)| match a.as_data() {
      ExprData::Fvar(n, _) => Some((n.clone(), b.clone())),
      _ => None,
    })
    .collect();
  transform(e, c, |e, _| {
    Ok(match e.as_data() {
      ExprData::Fvar(n, _) => vars.get(n).cloned(),
      _ => None,
    })
  })
}

pub(super) fn subst_fvar(
  e: &LeanExpr,
  name: &Name,
  value: &LeanExpr,
  c: &Checkpoint,
) -> Result<LeanExpr> {
  transform(e, c, |e, _| {
    Ok(match e.as_data() {
      ExprData::Fvar(n, _) if n == name => Some(value.clone()),
      _ => None,
    })
  })
}

pub(super) fn shift_vars(
  e: &LeanExpr,
  amount: usize,
  cutoff: usize,
  lower: bool,
  c: &Checkpoint,
) -> Result<LeanExpr> {
  c.visit()?;
  if amount == 0 {
    return Ok(e.clone());
  }
  rewrite(e, cutoff as u64, c, &mut FxHashMap::default(), &mut |e, depth| {
    Ok(match e.as_data() {
      ExprData::Bvar(i, _)
        if nat_to_u64(i) >= depth + if lower { amount as u64 } else { 0 } =>
      {
        let i = nat_to_u64(i);
        Some(LeanExpr::bvar(Nat::from(if lower {
          i - amount as u64
        } else {
          i + amount as u64
        })))
      },
      _ => None,
    })
  })
}

pub(super) fn subst_levels(
  e: &LeanExpr,
  params: &[Name],
  univs: &[Level],
  c: &Checkpoint,
) -> Result<LeanExpr> {
  if params.is_empty() || univs.is_empty() {
    c.visit()?;
    return Ok(e.clone());
  }
  fn level(
    l: &Level,
    params: &[Name],
    univs: &[Level],
    c: &Checkpoint,
    cache: &mut FxHashMap<Hash, Level>,
  ) -> Result<Level> {
    c.visit()?;
    let key = *l.get_hash();
    if let Some(value) = cache.get(&key) {
      return Ok(value.clone());
    }
    let value = match l.as_data() {
      LevelData::Param(n, _) => params
        .iter()
        .position(|p| p == n)
        .and_then(|i| univs.get(i))
        .unwrap_or(l)
        .clone(),
      LevelData::Succ(v, _) => Level::succ(level(v, params, univs, c, cache)?),
      LevelData::Max(a, b, _) => Level::max_smart(
        level(a, params, univs, c, cache)?,
        level(b, params, univs, c, cache)?,
      ),
      LevelData::Imax(a, b, _) => Level::imax_smart(
        level(a, params, univs, c, cache)?,
        level(b, params, univs, c, cache)?,
      ),
      _ => l.clone(),
    };
    cache.insert(key, value.clone());
    Ok(value)
  }
  let mut levels = FxHashMap::default();
  transform(e, c, |e, _| {
    Ok(match e.as_data() {
      ExprData::Sort(l, _) => {
        Some(LeanExpr::sort(level(l, params, univs, c, &mut levels)?))
      },
      ExprData::Const(n, ls, _) => Some(LeanExpr::cnst(
        n.clone(),
        ls.iter()
          .map(|l| level(l, params, univs, c, &mut levels))
          .collect::<Result<_>>()?,
      )),
      _ => None,
    })
  })
}

/// DAG-memoized predicate traversal, including binder depth for free-BVar tests.
pub(super) fn any(
  e: &LeanExpr,
  c: &Checkpoint,
  mut predicate: impl FnMut(&LeanExpr, u64) -> bool,
) -> Result<bool> {
  let mut seen = FxHashSet::default();
  let mut stack = vec![(e, 0)];
  while let Some((e, depth)) = stack.pop() {
    c.visit()?;
    if !seen.insert((*e.get_hash(), depth)) {
      continue;
    }
    if predicate(e, depth) {
      return Ok(true);
    }
    match e.as_data() {
      ExprData::App(f, a, _) => {
        stack.push((f, depth));
        stack.push((a, depth));
      },
      ExprData::Lam(_, t, b, _, _) | ExprData::ForallE(_, t, b, _, _) => {
        stack.push((t, depth));
        stack.push((b, depth + 1));
      },
      ExprData::LetE(_, t, v, b, _, _) => {
        stack.push((t, depth));
        stack.push((v, depth));
        stack.push((b, depth + 1));
      },
      ExprData::Proj(_, _, v, _) | ExprData::Mdata(_, v, _) => {
        stack.push((v, depth))
      },
      _ => {},
    }
    c.scratch(
      seen.capacity() * size_of::<Key>()
        + stack.capacity() * size_of::<(&LeanExpr, u64)>(),
    );
  }
  Ok(false)
}

#[cfg(test)]
mod tests {
  use super::super::expr_reference as old;
  use super::*;
  use ix_common::env::BinderInfo;

  fn name(s: &str) -> Name {
    Name::str(Name::anon(), s.into())
  }
  fn b(i: u64) -> LeanExpr {
    LeanExpr::bvar(Nat::from(i))
  }
  fn pi(t: LeanExpr, body: LeanExpr) -> LeanExpr {
    LeanExpr::all(name("x"), t, body, BinderInfo::Default)
  }

  #[test]
  fn matches_reference_transforms_with_shared_terms_at_different_depths() {
    let c = Checkpoint::default();
    let u = name("u");
    let f = LeanExpr::fvar(name("f"));
    let leaf = LeanExpr::app(b(1), f.clone());
    let terms = vec![
      b(0),
      b(3),
      f.clone(),
      LeanExpr::sort(Level::param(u.clone())),
      LeanExpr::cnst(
        name("C"),
        vec![Level::imax(Level::param(u.clone()), Level::zero())],
      ),
      pi(leaf.clone(), pi(leaf.clone(), LeanExpr::app(leaf.clone(), b(2)))),
      LeanExpr::lam(
        name("x"),
        leaf.clone(),
        leaf.clone(),
        BinderInfo::Implicit,
      ),
      LeanExpr::letE(name("v"), leaf.clone(), b(0), leaf.clone(), false),
      LeanExpr::proj(name("P"), Nat::from(0u64), leaf),
    ];
    let vars = [(name("f"), 0), (name("g"), 1)].into_iter().collect();
    for e in &terms {
      assert_eq!(instantiate1(e, &f, &c).unwrap(), old::instantiate1(e, &f));
      assert_eq!(
        instantiate_rev(e, &[b(2), f.clone()], &c).unwrap(),
        old::instantiate_rev(e, &[b(2), f.clone()])
      );
      for scope in 0..=2 {
        assert_eq!(
          batch_abstract(e, &vars, scope, &c).unwrap(),
          old::batch_abstract(e, &vars, scope, 0)
        );
      }
      assert_eq!(
        subst_levels(e, std::slice::from_ref(&u), &[Level::zero()], &c)
          .unwrap(),
        old::subst_levels(e, std::slice::from_ref(&u), &[Level::zero()])
      );
      let ty = pi(e.clone(), pi(e.clone(), b(1)));
      assert_eq!(
        instantiate_pi_params(&ty, 1, &[b(2)], &c).unwrap(),
        old::instantiate_pi_params(&ty, 1, &[b(2)])
      );
      let (fvars, decls, body) =
        forall_telescope(&ty, 2, "test", 3, &c).unwrap();
      let (ref_fvars, ref_decls, ref_body) =
        old::forall_telescope(&ty, 2, "test", 3);
      assert_eq!(fvars, ref_fvars);
      assert_eq!(body, ref_body);
      assert_eq!(
        mk_forall(body, &decls, &c).unwrap(),
        old::mk_forall(ref_body, &ref_decls)
      );
    }
  }

  #[test]
  fn diamond_dag_is_visited_linearly() {
    let mut e = b(0);
    for _ in 0..40 {
      e = LeanExpr::app(e.clone(), e);
    }
    let mut visits = 0;
    let result = transform(&e, &Checkpoint::default(), |_, _| {
      visits += 1;
      Ok(None)
    })
    .unwrap();
    assert_eq!(result, e);
    assert_eq!(visits, 41); // Not 2^40 visits/copies.
  }

  #[test]
  fn cancellation_unwinds_an_in_progress_walk_without_panicking() {
    let mut e = b(0);
    for _ in 0..40 {
      e = LeanExpr::app(e.clone(), e);
    }
    let mut visits = 0;
    let result = transform(&e, &Checkpoint::default(), |_, _| {
      visits += 1;
      if visits == 20 { Err(Cancelled) } else { Ok(None) }
    });
    assert!(matches!(result, Err(Cancelled)));
    assert_eq!(visits, 20);
  }

  #[test]
  fn predicate_cache_distinguishes_binder_depth() {
    // BVar 0 is bound in the body (visited first), but free in the domain.
    let e = pi(b(0), b(0));
    assert!(any(&e, &Checkpoint::default(), |e, depth|
      matches!(e.as_data(), ExprData::Bvar(i, _) if nat_to_u64(i) >= depth)).unwrap());
  }

  #[test]
  fn main_compiler_helpers_match_frozen_reference_on_mixed_shared_terms() {
    use super::super::expr_utils as main;
    let f = name("f");
    let g = name("g");
    let u = name("u");
    let fv = LeanExpr::fvar(f.clone());
    let mut terms = vec![
      b(0),
      b(1),
      b(3),
      fv.clone(),
      LeanExpr::fvar(g.clone()),
      LeanExpr::sort(Level::param(u.clone())),
      LeanExpr::cnst(
        name("C"),
        vec![Level::max(Level::param(u.clone()), Level::zero())],
      ),
    ];
    for round in 0..5 {
      let previous = terms.clone();
      for (i, e) in previous.iter().take(12).enumerate() {
        let other = &previous[(i * 7 + round) % previous.len()];
        terms.push(match (i + round) % 6 {
          0 => LeanExpr::app(e.clone(), e.clone()),
          1 => pi(e.clone(), other.clone()),
          2 => LeanExpr::lam(
            name("x"),
            e.clone(),
            other.clone(),
            BinderInfo::Implicit,
          ),
          3 => {
            LeanExpr::letE(name("x"), e.clone(), other.clone(), e.clone(), true)
          },
          4 => LeanExpr::proj(name("P"), Nat::from(0u64), e.clone()),
          _ => LeanExpr::mdata(vec![], e.clone()),
        });
      }
    }
    let vars = [(f.clone(), 0), (g.clone(), 1)].into_iter().collect();
    for e in &terms {
      for depth in 0..3 {
        assert_eq!(
          main::instantiate1_at(e, &fv, depth),
          old::instantiate1_at(e, &fv, depth)
        );
        assert_eq!(
          main::batch_abstract(e, &vars, 2, depth),
          old::batch_abstract(e, &vars, 2, depth)
        );
      }
      assert_eq!(
        main::instantiate_rev(e, &[b(1), fv.clone()]),
        old::instantiate_rev(e, &[b(1), fv.clone()])
      );
      for amount in 0..3 {
        for cutoff in 0..3 {
          assert_eq!(
            main::shift_vars(e, amount, cutoff),
            old::shift_vars(e, amount, cutoff)
          );
          assert_eq!(
            main::lower_vars(e, amount, cutoff),
            old::lower_vars(e, amount, cutoff)
          );
        }
      }
      assert_eq!(main::subst_fvar(e, &f, &b(2)), old::subst_fvar(e, &f, &b(2)));
      assert_eq!(
        main::subst_levels(e, std::slice::from_ref(&u), &[Level::zero()]),
        old::subst_levels(e, std::slice::from_ref(&u), &[Level::zero()])
      );
    }
  }

  #[test]
  fn main_compiler_transforms_preserve_large_diamond_sharing() {
    use super::super::expr_utils as main;
    fn diamond(mut e: LeanExpr) -> LeanExpr {
      for _ in 0..40 {
        e = LeanExpr::app(e.clone(), e);
      }
      e
    }
    fn unique_nodes(e: &LeanExpr) -> usize {
      let mut count = 0;
      any(e, &Checkpoint::default(), |_, _| {
        count += 1;
        false
      })
      .unwrap();
      count
    }
    let fv = LeanExpr::fvar(name("f"));
    let e = diamond(b(0));
    let instantiated = main::instantiate1(&e, &fv);
    assert_eq!(instantiated.get_hash(), diamond(fv.clone()).get_hash());
    assert_eq!(unique_nodes(&instantiated), 41);
    let vars = [(name("f"), 0)].into_iter().collect();
    let abstracted = main::batch_abstract(&instantiated, &vars, 1, 0);
    assert_eq!(abstracted.get_hash(), e.get_hash());
    assert_eq!(unique_nodes(&abstracted), 41);
    let shifted = main::shift_vars(&e, 2, 0);
    assert_eq!(shifted.get_hash(), diamond(b(2)).get_hash());
    assert_eq!(unique_nodes(&shifted), 41);
    let replaced = main::subst_fvar(&instantiated, &name("f"), &b(1));
    assert_eq!(replaced.get_hash(), diamond(b(1)).get_hash());
    assert_eq!(unique_nodes(&replaced), 41);
    let universe = diamond(LeanExpr::sort(Level::param(name("u"))));
    let substituted =
      main::subst_levels(&universe, &[name("u")], &[Level::zero()]);
    assert_eq!(
      substituted.get_hash(),
      diamond(LeanExpr::sort(Level::zero())).get_hash()
    );
    assert_eq!(unique_nodes(&substituted), 41);
  }
}
