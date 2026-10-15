//! Exact keys for compiled expressions and universes. Stored digests index the
//! table; complete source equality confirms a hit. Pair memos keep comparisons
//! of independently allocated expression and universe DAGs from becoming tree
//! walks. This mirrors `Ix.Compile.ExactKey`.

use ix_common::{
  address::Address,
  env::{Expr, ExprData, Level, LevelData, Name, NameData},
};
use rustc_hash::FxHashSet;
use std::{
  hash::{Hash, Hasher},
  sync::Arc,
};

#[derive(Clone, Debug)]
pub struct ExprKey(pub Expr);

impl Hash for ExprKey {
  fn hash<H: Hasher>(&self, state: &mut H) {
    self.0.hash(state);
  }
}

impl PartialEq for ExprKey {
  fn eq(&self, other: &Self) -> bool {
    same_expr(&self.0, &other.0)
  }
}

impl Eq for ExprKey {}

/// The source level and its complete positional parameter context. Context
/// digests select candidates but never identify different name sequences.
#[derive(Clone, Debug)]
pub struct UnivKey {
  level: Level,
  params: Vec<Name>,
  context_hash: Address,
}

impl UnivKey {
  pub fn new(level: &Level, params: &[Name]) -> Self {
    Self {
      level: level.clone(),
      params: params.to_vec(),
      context_hash: super::univ_params_key(params),
    }
  }
}

impl Hash for UnivKey {
  fn hash<H: Hasher>(&self, state: &mut H) {
    self.level.hash(state);
    self.context_hash.hash(state);
  }
}

impl PartialEq for UnivKey {
  fn eq(&self, other: &Self) -> bool {
    self.context_hash == other.context_hash
      && self.params.len() == other.params.len()
      && self.params.iter().zip(&other.params).all(|(a, b)| same_name(a, b))
      && same_level(&self.level, &other.level)
  }
}

impl Eq for UnivKey {}

fn same_name(mut a: &Name, mut b: &Name) -> bool {
  loop {
    if Arc::ptr_eq(&a.0, &b.0) {
      return true;
    }
    if a.get_hash() != b.get_hash() {
      return false;
    }
    match (a.as_data(), b.as_data()) {
      (NameData::Anonymous(_), NameData::Anonymous(_)) => return true,
      (NameData::Str(ap, av, _), NameData::Str(bp, bv, _)) if av == bv => {
        (a, b) = (ap, bp);
      },
      (NameData::Num(ap, av, _), NameData::Num(bp, bv, _)) if av == bv => {
        (a, b) = (ap, bp);
      },
      _ => return false,
    }
  }
}

fn same_level(a: &Level, b: &Level) -> bool {
  if Arc::ptr_eq(&a.0, &b.0) {
    return true;
  }
  if a.get_hash() != b.get_hash() {
    return false;
  }
  let mut completed = FxHashSet::default();
  let mut pending = vec![(a, b, false)];
  while let Some((a, b, finish)) = pending.pop() {
    let pair = (Arc::as_ptr(&a.0), Arc::as_ptr(&b.0));
    if finish {
      completed.insert(pair);
      continue;
    }
    if pair.0 == pair.1 || completed.contains(&pair) {
      continue;
    }
    if a.get_hash() != b.get_hash() {
      return false;
    }
    pending.push((a, b, true));
    match (a.as_data(), b.as_data()) {
      (LevelData::Zero(_), LevelData::Zero(_)) => {},
      (LevelData::Succ(a, _), LevelData::Succ(b, _)) => {
        pending.push((a, b, false));
      },
      (LevelData::Max(a, b, _), LevelData::Max(c, d, _))
      | (LevelData::Imax(a, b, _), LevelData::Imax(c, d, _)) => {
        pending.extend([(b, d, false), (a, c, false)]);
      },
      (LevelData::Param(a, _), LevelData::Param(b, _))
      | (LevelData::Mvar(a, _), LevelData::Mvar(b, _))
        if same_name(a, b) => {},
      _ => return false,
    }
  }
  true
}

fn same_expr(a: &Expr, b: &Expr) -> bool {
  if Arc::ptr_eq(&a.0, &b.0) {
    return true;
  }
  if a.get_hash() != b.get_hash() {
    return false;
  }
  // Both borrowed roots retain all nodes until the comparison ends. The
  // memo contains only pairs whose children have already compared equal.
  let mut completed = FxHashSet::default();
  let mut pending = vec![(a, b, false)];
  while let Some((a, b, finish)) = pending.pop() {
    let pair = (Arc::as_ptr(&a.0), Arc::as_ptr(&b.0));
    if finish {
      completed.insert(pair);
      continue;
    }
    if pair.0 == pair.1 || completed.contains(&pair) {
      continue;
    }
    if a.get_hash() != b.get_hash() {
      return false;
    }
    pending.push((a, b, true));
    match (a.as_data(), b.as_data()) {
      (ExprData::Bvar(a, _), ExprData::Bvar(b, _)) if a == b => {},
      (ExprData::Fvar(a, _), ExprData::Fvar(b, _))
      | (ExprData::Mvar(a, _), ExprData::Mvar(b, _))
        if same_name(a, b) => {},
      (ExprData::Sort(a, _), ExprData::Sort(b, _)) if same_level(a, b) => {},
      (ExprData::Const(a, us, _), ExprData::Const(b, vs, _))
        if same_name(a, b)
          && us.len() == vs.len()
          && us.iter().zip(vs).all(|(u, v)| same_level(u, v)) => {},
      (ExprData::App(f, a, _), ExprData::App(g, b, _)) => {
        pending.extend([(a, b, false), (f, g, false)]);
      },
      (
        ExprData::Lam(n, t, body, info, _),
        ExprData::Lam(m, u, other, other_info, _),
      )
      | (
        ExprData::ForallE(n, t, body, info, _),
        ExprData::ForallE(m, u, other, other_info, _),
      ) if same_name(n, m) && info == other_info => {
        pending.extend([(body, other, false), (t, u, false)]);
      },
      (
        ExprData::LetE(n, t, v, body, nd, _),
        ExprData::LetE(m, u, w, other, other_nd, _),
      ) if same_name(n, m) && nd == other_nd => {
        pending.extend([(body, other, false), (v, w, false), (t, u, false)]);
      },
      (ExprData::Lit(a, _), ExprData::Lit(b, _)) if a == b => {},
      (ExprData::Mdata(md, a, _), ExprData::Mdata(other_md, b, _))
        if md == other_md =>
      {
        // Rust syntax metadata is owned Vec/Box data, so its derived
        // equality walks its stored tree and includes names and hashes.
        pending.push((a, b, false));
      },
      (ExprData::Proj(n, i, a, _), ExprData::Proj(m, j, b, _))
        if same_name(n, m) && i == j =>
      {
        pending.push((a, b, false));
      },
      _ => return false,
    }
  }
  true
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::compile::{BlockCache, CompileState, compile_expr, compile_univ};
  use crate::mutual::MutCtx;
  use bignat::Nat;
  use ix_common::env::{BinderInfo, DataValue, Literal};

  fn raw(value: ExprData) -> Expr {
    Expr(Arc::new(value))
  }

  #[test]
  fn constructor_matrix_agrees_with_raw_equality() {
    let h = blake3::hash(b"constructed shared digest");
    let n = Name::anon();
    let x = Name::str(n.clone(), "x".into());
    let y = Name(Arc::new(NameData::Str(n.clone(), "y".into(), *x.get_hash())));
    let a = raw(ExprData::Bvar(Nat::from(0u64), h));
    let b = raw(ExprData::Bvar(Nat::from(1u64), h));
    let l = Level::zero();
    let samples = vec![
      a.clone(),
      b.clone(),
      raw(ExprData::Bvar(Nat::from(0u64), h)),
      raw(ExprData::Fvar(x.clone(), h)),
      raw(ExprData::Fvar(y, h)),
      raw(ExprData::Mvar(x.clone(), h)),
      raw(ExprData::Sort(l.clone(), h)),
      raw(ExprData::Const(x.clone(), vec![l], h)),
      raw(ExprData::App(a.clone(), b.clone(), h)),
      raw(ExprData::Lam(
        n.clone(),
        a.clone(),
        b.clone(),
        BinderInfo::Default,
        h,
      )),
      raw(ExprData::Lam(
        n.clone(),
        a.clone(),
        b.clone(),
        BinderInfo::Implicit,
        h,
      )),
      raw(ExprData::ForallE(
        n.clone(),
        a.clone(),
        b.clone(),
        BinderInfo::Default,
        h,
      )),
      raw(ExprData::LetE(n.clone(), a.clone(), b.clone(), a.clone(), false, h)),
      raw(ExprData::LetE(n, a.clone(), b.clone(), a.clone(), true, h)),
      raw(ExprData::Lit(Literal::NatVal(Nat::from(7u64)), h)),
      raw(ExprData::Lit(Literal::StrVal("7".into()), h)),
      raw(ExprData::Mdata(
        vec![(x.clone(), DataValue::OfBool(false))],
        a.clone(),
        h,
      )),
      raw(ExprData::Mdata(
        vec![(x.clone(), DataValue::OfBool(true))],
        a.clone(),
        h,
      )),
      raw(ExprData::Proj(x, Nat::from(0u64), a, h)),
    ];
    for a in &samples {
      for b in &samples {
        assert_eq!(same_expr(a, b), a == b);
      }
    }
  }

  #[test]
  fn distinct_shared_dags_use_completed_pairs() {
    let n = Name::anon();
    let mut a = Expr::bvar(Nat::from(0u64));
    let mut b = Expr::bvar(Nat::from(0u64));
    for _ in 0..64 {
      a = Expr::lam(n.clone(), a.clone(), a, BinderInfo::Default);
      b = Expr::lam(n.clone(), b.clone(), b, BinderInfo::Default);
    }
    assert!(same_expr(&a, &b));
    let mut u = Level::zero();
    let mut v = Level::zero();
    for _ in 0..64 {
      u = Level::max(u.clone(), u);
      v = Level::max(v.clone(), v);
    }
    assert!(same_expr(&Expr::sort(u), &Expr::sort(v)));
  }

  #[test]
  fn colliding_source_keys_compile_and_cache_independently() {
    let stt = CompileState::default();
    let mut cache = BlockCache::default();
    let ctx = MutCtx::default();
    let a = Expr::bvar(Nat::from(0u64));
    let b = raw(ExprData::Bvar(Nat::from(1u64), *a.get_hash()));
    let bad = raw(ExprData::Mvar(Name::anon(), *a.get_hash()));
    let first = compile_expr(&a, &[], &ctx, &mut cache, &stt).unwrap();
    assert_eq!(first, ixon::expr::Expr::var(0));
    let second = compile_expr(&b, &[], &ctx, &mut cache, &stt).unwrap();
    assert_eq!(second, ixon::expr::Expr::var(1));
    assert_eq!(cache.arena_roots.last(), Some(&1));
    assert_eq!(cache.exprs.len(), 2);
    let again = compile_expr(&a, &[], &ctx, &mut cache, &stt).unwrap();
    assert_eq!(again, first);
    assert_eq!(cache.arena_roots.last(), Some(&0));
    assert!(compile_expr(&bad, &[], &ctx, &mut cache, &stt).is_err());
    assert_eq!(cache.exprs.len(), 2);
  }

  #[test]
  fn universe_cache_distinguishes_equal_digest_contexts() {
    let u = Name::str(Name::anon(), "u".into());
    let v =
      Name(Arc::new(NameData::Str(Name::anon(), "v".into(), *u.get_hash())));
    let level = Level::param(u.clone());
    let first_context = [u.clone(), v.clone()];
    let second_context = [v, u];
    let mut cache = BlockCache::default();
    assert_eq!(
      compile_univ(&level, &first_context, &mut cache).unwrap(),
      ixon::univ::Univ::var(0)
    );
    let cold =
      compile_univ(&level, &second_context, &mut BlockCache::default())
        .unwrap();
    assert_eq!(cold, ixon::univ::Univ::var(1));
    let warm = compile_univ(&level, &second_context, &mut cache).unwrap();
    assert_eq!(warm, cold);
    assert_eq!(cache.univ_cache.len(), 2);
  }

  #[test]
  fn universe_cache_keeps_equal_digest_levels_distinct() {
    let zero = Level::zero();
    let succ = Level(Arc::new(LevelData::Succ(zero.clone(), *zero.get_hash())));
    let bad = Level(Arc::new(LevelData::Mvar(Name::anon(), *zero.get_hash())));
    let mut cache = BlockCache::default();
    assert_eq!(
      compile_univ(&zero, &[], &mut cache).unwrap(),
      ixon::univ::Univ::zero()
    );
    assert_eq!(
      compile_univ(&succ, &[], &mut cache).unwrap(),
      ixon::univ::Univ::succ(ixon::univ::Univ::zero())
    );
    assert!(compile_univ(&bad, &[], &mut cache).is_err());
    assert_eq!(cache.univ_cache.len(), 2);
  }
}
