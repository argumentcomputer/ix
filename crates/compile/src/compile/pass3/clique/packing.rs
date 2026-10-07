//! The right-nested binary packings of the clique encodings (a port of
//! `Ix/Compile/Clique/Packing.lean` and `PackingMatch.lean`).

use ix_common::env::{BinderInfo, Expr, ExprData, Level, Name};

use super::basic::*;
use crate::compile::pass3::expr::{nat_usize, strip_mdata};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PackKind {
  Psum,
  Pprod,
}

/// A decoded packing type.
#[derive(Clone, Debug)]
pub struct Spine {
  pub kind: PackKind,
  pub leaves: Vec<Expr>,
  pub lvls: Vec<Level>,
}

impl Spine {
  pub fn size(&self) -> usize {
    self.leaves.len()
  }

  /// `Spine.suffixes`.
  pub fn suffixes(&self) -> Vec<(Expr, Level)> {
    let n = self.size();
    if n == 0 {
      return Vec::new();
    }
    let mut acc: Vec<(Expr, Level)> =
      vec![(self.leaves[n - 1].clone(), self.lvls[n - 1].clone())];
    for j in (0..n - 1).rev() {
      let (r, lr) = acc.last().unwrap().clone();
      acc.push((
        mk_node(self.kind, &self.lvls[j], &lr, &self.leaves[j], &r),
        node_level(self.kind, &self.lvls[j], &lr),
      ));
    }
    acc.reverse();
    acc
  }

  pub fn typ(&self) -> Expr {
    self.suffixes()[0].0.clone()
  }

  /// `Spine.permute`.
  pub fn permute(&self, s: &[usize]) -> Spine {
    Spine {
      kind: self.kind,
      leaves: permute(s, &self.leaves),
      lvls: permute(s, &self.lvls),
    }
  }

  pub fn map_leaves(&self, f: &dyn Fn(&Expr) -> Expr) -> Spine {
    Spine {
      kind: self.kind,
      leaves: self.leaves.iter().map(f).collect(),
      lvls: self.lvls.clone(),
    }
  }

  pub fn with_leaves(&self, leaves: Vec<Expr>) -> Spine {
    Spine { kind: self.kind, leaves, lvls: self.lvls.clone() }
  }

  /// `Spine.nodeStruct`.
  pub fn node_struct(&self, k: usize) -> Name {
    let suf = self.suffixes();
    if is_always_zero(&self.lvls[k]) && is_always_zero(&suf[k + 1].1) {
      n_and()
    } else {
      n_pprod()
    }
  }

  /// `Spine.projSteps`.
  pub fn proj_steps(&self, j: usize) -> Vec<(Name, usize)> {
    let n = self.size();
    let mut acc = Vec::new();
    for k in 0..j {
      acc.push((self.node_struct(k), 1));
    }
    if j + 1 < n {
      acc.push((self.node_struct(j), 0));
    }
    acc
  }
}

pub fn node_level(k: PackKind, l: &Level, r: &Level) -> Level {
  match k {
    PackKind::Psum => pair_level(l, r),
    PackKind::Pprod => {
      if is_always_zero(l) && is_always_zero(r) {
        Level::zero()
      } else {
        pair_level(l, r)
      }
    },
  }
}

pub fn mk_node(k: PackKind, l: &Level, r: &Level, a: &Expr, b: &Expr) -> Expr {
  match k {
    PackKind::Psum => mk_app_n(
      cnst(&n_psum(), &[l.clone(), r.clone()]),
      &[a.clone(), b.clone()],
    ),
    PackKind::Pprod => {
      if is_always_zero(l) && is_always_zero(r) {
        mk_app_n(cnst(&n_and(), &[]), &[a.clone(), b.clone()])
      } else {
        mk_app_n(
          cnst(&n_pprod(), &[l.clone(), r.clone()]),
          &[a.clone(), b.clone()],
        )
      }
    },
  }
}

/// `decodeNode`.
pub fn decode_node(
  k: PackKind,
  e: &Expr,
) -> Option<(Level, Level, Expr, Expr)> {
  let (n, us, args) = const_app(e)?;
  if args.len() != 2 {
    return None;
  }
  match k {
    PackKind::Psum => {
      if us.len() == 2 && n == n_psum() {
        Some((us[0].clone(), us[1].clone(), args[0].clone(), args[1].clone()))
      } else {
        None
      }
    },
    PackKind::Pprod => {
      if us.len() == 2 && n == n_pprod() {
        Some((us[0].clone(), us[1].clone(), args[0].clone(), args[1].clone()))
      } else if us.is_empty() && n == n_and() {
        Some((Level::zero(), Level::zero(), args[0].clone(), args[1].clone()))
      } else {
        None
      }
    },
  }
}

/// `decodeSpine`.
pub fn decode_spine(k: PackKind, n: usize, e: &Expr) -> Option<Spine> {
  if n < 2 {
    return None;
  }
  let mut cur = e.clone();
  let mut leaves = Vec::new();
  let mut lvls = Vec::new();
  let mut last_r = Level::zero();
  for _ in 0..n - 1 {
    let (l, r, a, b) = decode_node(k, &cur)?;
    leaves.push(a);
    lvls.push(l);
    last_r = r;
    cur = b;
  }
  leaves.push(cur);
  lvls.push(last_r);
  let s = Spine { kind: k, leaves, lvls };
  if alpha_eq(&s.typ(), e) { Some(s) } else { None }
}

/// `mkInj`.
pub fn mk_inj(s: &Spine, j: usize, v: &Expr) -> Expr {
  let n = s.size();
  let suf = s.suffixes();
  let mut acc = v.clone();
  let top = if j + 1 < n { j } else { n - 1 };
  if j + 1 < n {
    let (r, lr) = &suf[j + 1];
    acc = mk_app_n(
      cnst(&n_psum_inl(), &[s.lvls[j].clone(), lr.clone()]),
      &[s.leaves[j].clone(), r.clone(), acc],
    );
  }
  for k in (0..top).rev() {
    let (r, lr) = &suf[k + 1];
    acc = mk_app_n(
      cnst(&n_psum_inr(), &[s.lvls[k].clone(), lr.clone()]),
      &[s.leaves[k].clone(), r.clone(), acc],
    );
  }
  acc
}

/// `decodeInj`.
pub fn decode_inj(n: usize, e: &Expr) -> Option<(Spine, usize, Expr)> {
  let (h, us, args) = const_app(e)?;
  if !((h == n_psum_inl() || h == n_psum_inr())
    && args.len() == 3
    && us.len() == 2)
  {
    return None;
  }
  let s = decode_spine(
    PackKind::Psum,
    n,
    &mk_app_n(cnst(&n_psum(), &us), &[args[0].clone(), args[1].clone()]),
  )?;
  let mut cur = e.clone();
  let mut idx = 0;
  let mut found: Option<Expr> = None;
  for _ in 0..n - 1 {
    if found.is_some() {
      break;
    }
    match const_app(&cur) {
      Some((h2, _, a)) if a.len() == 3 => {
        if h2 == n_psum_inl() {
          found = Some(a[2].clone());
        } else if h2 == n_psum_inr() {
          idx += 1;
          cur = a[2].clone();
        } else {
          return None;
        }
      },
      _ => return None,
    }
  }
  let v = found.unwrap_or(cur);
  if idx >= n {
    return None;
  }
  if alpha_eq(&mk_inj(&s, idx, &v), e) { Some((s, idx, v)) } else { None }
}

/// A decoded case tree.
#[derive(Clone, Debug)]
pub struct Tree {
  pub spine: Spine,
  pub w: Level,
  pub motive_body: Expr,
  pub motive_name: Name,
  pub major: Expr,
  pub leaves: Vec<Expr>,
  pub extras: Vec<Expr>,
  pub alt_names: Vec<Name>,
}

/// `mkPrefix`.
pub fn mk_prefix(s: &Spine, k: usize, t: &Expr) -> Expr {
  let suf = s.suffixes();
  let mut acc = t.clone();
  for j in (0..k).rev() {
    let (r, lr) = &suf[j + 1];
    acc = mk_app_n(
      cnst(&n_psum_inr(), &[s.lvls[j].clone(), lr.clone()]),
      &[s.leaves[j].clone(), r.clone(), acc],
    );
  }
  acc
}

/// `forallDomains`.
pub fn forall_domains(r: usize, e: &Expr) -> Option<Vec<(Name, Expr)>> {
  let mut cur = e.clone();
  let mut acc = Vec::new();
  for _ in 0..r {
    let s = strip_mdata(&cur);
    match s.as_data() {
      ExprData::ForallE(nm, t, b, _, _) => {
        acc.push((nm.clone(), t.clone()));
        cur = b.clone();
      },
      _ => return None,
    }
  }
  Some(acc)
}

/// `motiveAt`.
pub fn motive_at(t: &Tree, k: usize, dk: usize) -> Expr {
  let m = crate::compile::pass3::expr::lift_loose(&t.motive_body, dk, 1);
  let s2 = t.spine.map_leaves(&|x| lift(x, dk + 1));
  subst_bvar0_same(&m, &mk_prefix(&s2, k, &mk_bvar(0)))
}

fn build_tree_at(
  t: &Tree,
  fuel: usize,
  k: usize,
  dk: usize,
  major: &Expr,
  extras: &[Expr],
) -> Option<Expr> {
  if fuel == 0 {
    return None;
  }
  let fuel = fuel - 1;
  let s = &t.spine;
  let n = s.size();
  let suf = s.suffixes();
  let r = t.extras.len();
  let (sk, _) = suf.get(k)?.clone();
  let (sk1, lk1) = suf.get(k + 1)?.clone();
  let motive = Expr::lam(
    t.motive_name.clone(),
    lift(&sk, dk),
    motive_at(t, k, dk),
    BinderInfo::Default,
  );
  let alt1 = lift(t.leaves.get(k)?, dk);
  let alt2 = if k + 2 == n {
    lift(t.leaves.get(n - 1)?, dk)
  } else {
    let ds = forall_domains(r, &motive_at(t, k + 1, dk))?;
    let inner_extras: Vec<Expr> = (0..r).map(|i| mk_bvar(r - 1 - i)).collect();
    let inner =
      build_tree_at(t, fuel, k + 1, dk + 1 + r, &mk_bvar(r), &inner_extras)?;
    let mut body = inner;
    for (i, (nm, ty)) in ds.iter().enumerate().rev() {
      let name = t.alt_names.get(i + 1).cloned().unwrap_or_else(|| nm.clone());
      body = Expr::lam(name, ty.clone(), body, BinderInfo::Default);
    }
    let z_name = t.alt_names.first().cloned().unwrap_or_else(|| root("_x"));
    Expr::lam(z_name, lift(&sk1, dk), body, BinderInfo::Default)
  };
  let head =
    cnst(&n_psum_cases_on(), &[t.w.clone(), s.lvls.get(k)?.clone(), lk1]);
  let mut args = vec![
    lift(s.leaves.get(k)?, dk),
    lift(&sk1, dk),
    motive,
    major.clone(),
    alt1,
    alt2,
  ];
  args.extend(extras.iter().cloned());
  Some(mk_app_n(head, &args))
}

impl Tree {
  /// `Tree.build`.
  pub fn build(&self) -> Option<Expr> {
    if self.spine.size() < 2 {
      return None;
    }
    build_tree_at(self, self.spine.size() + 2, 0, 0, &self.major, &self.extras)
  }

  /// `Tree.permute`.
  pub fn permute(&self, s: &[usize]) -> Tree {
    Tree {
      spine: self.spine.permute(s),
      leaves: permute(s, &self.leaves),
      ..self.clone()
    }
  }
}

/// `decodeTree`.
pub fn decode_tree(n: usize, e: &Expr) -> Option<Tree> {
  let (h, us, args) = const_app(e)?;
  if !(h == n_psum_cases_on() && us.len() == 3 && args.len() >= 6) {
    return None;
  }
  let s = decode_spine(
    PackKind::Psum,
    n,
    &mk_app_n(
      cnst(&n_psum(), &[us[1].clone(), us[2].clone()]),
      &[args[0].clone(), args[1].clone()],
    ),
  )?;
  let w = us[0].clone();
  let (m_name, m_body) = match strip_mdata(&args[2]).as_data() {
    ExprData::Lam(nm, _, b, _, _) => (nm.clone(), b.clone()),
    _ => return None,
  };
  let extras = args[6..].to_vec();
  let r = extras.len();
  let mut leaves = vec![args[4].clone()];
  let mut cur = args[5].clone();
  let mut names: Vec<Name> = Vec::new();
  for k in 1..n.saturating_sub(1) {
    let (bs, body) = peel_lams(1 + r, &cur);
    if bs.len() != 1 + r {
      return None;
    }
    if names.is_empty() {
      names = bs.iter().map(|b| b.0.clone()).collect();
    }
    let (h2, _, args2) = const_app(&body)?;
    if !(h2 == n_psum_cases_on() && args2.len() == 6 + r) {
      return None;
    }
    let depth = k * (1 + r);
    leaves.push(lower_opt(&args2[4], depth)?);
    cur = args2[5].clone();
  }
  leaves.push(lower_opt(&cur, (n - 2) * (1 + r))?);
  let t = Tree {
    spine: s,
    w,
    motive_body: m_body,
    motive_name: m_name,
    major: args[3].clone(),
    leaves,
    extras,
    alt_names: names,
  };
  let e2 = t.build()?;
  if alpha_eq(&e2, e) { Some(t) } else { None }
}

/// `mkTuple`.
pub fn mk_tuple(s: &Spine, cs: &[Expr]) -> Expr {
  let n = s.size();
  let suf = s.suffixes();
  let mut acc = cs[n - 1].clone();
  for k in (0..n - 1).rev() {
    let (r, lr) = &suf[k + 1];
    let l = &s.lvls[k];
    acc = if is_always_zero(l) && is_always_zero(lr) {
      mk_app_n(
        cnst(&n_and_intro(), &[]),
        &[s.leaves[k].clone(), r.clone(), cs[k].clone(), acc],
      )
    } else {
      mk_app_n(
        cnst(&n_pprod_mk(), &[l.clone(), lr.clone()]),
        &[s.leaves[k].clone(), r.clone(), cs[k].clone(), acc],
      )
    };
  }
  acc
}

/// `decodeTuple`.
pub fn decode_tuple(n: usize, e: &Expr) -> Option<(Spine, Vec<Expr>)> {
  let (h, us, args) = const_app(e)?;
  if !((h == n_pprod_mk() || h == n_and_intro()) && args.len() == 4) {
    return None;
  }
  let ty = if h == n_pprod_mk() {
    mk_app_n(cnst(&n_pprod(), &us), &[args[0].clone(), args[1].clone()])
  } else {
    mk_app_n(cnst(&n_and(), &[]), &[args[0].clone(), args[1].clone()])
  };
  let s = decode_spine(PackKind::Pprod, n, &ty)?;
  let mut cs = Vec::new();
  let mut cur = e.clone();
  for _ in 0..n - 1 {
    match const_app(&cur) {
      Some((_, _, a)) if a.len() == 4 => {
        cs.push(a[2].clone());
        cur = a[3].clone();
      },
      _ => return None,
    }
  }
  cs.push(cur);
  if alpha_eq(&mk_tuple(&s, &cs), e) { Some((s, cs)) } else { None }
}

pub fn apply_projs(steps: &[(Name, usize)], e: &Expr) -> Expr {
  steps.iter().fold(e.clone(), |acc, (s, i)| proj(s, *i, acc))
}

/// `pathIndex`.
pub fn path_index(n: usize, steps: &[(Name, usize)]) -> Option<usize> {
  if n < 2 {
    return if steps.is_empty() { Some(0) } else { None };
  }
  let k = steps.iter().take_while(|s| s.1 == 1).count();
  if k + 1 < n {
    if steps.len() == k + 1 && steps[k].1 == 0 { Some(k) } else { None }
  } else if k == n - 1 && steps.len() == k {
    Some(n - 1)
  } else {
    None
  }
}

// ---------------------------------------------------------------------------
// PackingMatch
// ---------------------------------------------------------------------------

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum PackingVariable {
  Loose(usize),
  Free(Name),
}

#[derive(Clone, Default, Debug)]
pub struct PackingCorrespondence {
  pub variables: Vec<(PackingVariable, PackingVariable)>,
}

impl PackingCorrespondence {
  pub fn extend(
    &self,
    actual: PackingVariable,
    expected: PackingVariable,
  ) -> Option<PackingCorrespondence> {
    if let Some((_, old)) = self.variables.iter().find(|v| v.0 == actual) {
      if *old == expected { Some(self.clone()) } else { None }
    } else if self.variables.iter().any(|v| v.1 == expected) {
      None
    } else {
      let mut w = self.clone();
      w.variables.push((actual, expected));
      Some(w)
    }
  }
}

/// `packingAnnotation?`.
pub fn packing_annotation(e: &Expr) -> Option<Expr> {
  let (h, args) = crate::compile::pass3::expr::get_app_fn_args(&strip_mdata(e));
  match h.as_data() {
    ExprData::Const(n, _, _) => {
      if args.len() == 2 && (*n == ln("optParam") || *n == ln("autoParam")) {
        Some(args[0].clone())
      } else if args.len() == 1
        && (*n == ln("outParam") || *n == ln("semiOutParam"))
      {
        Some(args[0].clone())
      } else {
        None
      }
    },
    _ => None,
  }
}

/// `matchPackingExpr`.
pub fn match_packing_expr(
  fuel: usize,
  depth: usize,
  w: PackingCorrespondence,
  actual: &Expr,
  expected: &Expr,
) -> Option<PackingCorrespondence> {
  if fuel == 0 {
    return None;
  }
  let fuel = fuel - 1;
  if let Some(t) = packing_annotation(actual) {
    return match_packing_expr(fuel, depth, w, &t, expected);
  }
  if let Some(t) = packing_annotation(expected) {
    return match_packing_expr(fuel, depth, w, actual, &t);
  }
  use PackingVariable as V;
  match (actual.as_data(), expected.as_data()) {
    (ExprData::Mdata(_, a, _), _) => {
      match_packing_expr(fuel, depth, w, a, expected)
    },
    (_, ExprData::Mdata(_, b, _)) => {
      match_packing_expr(fuel, depth, w, actual, b)
    },
    (ExprData::Bvar(a, _), ExprData::Bvar(b, _)) => {
      let (a, b) = (nat_usize(a), nat_usize(b));
      if a < depth || b < depth {
        if a == b { Some(w) } else { None }
      } else {
        w.extend(V::Loose(a - depth), V::Loose(b - depth))
      }
    },
    (ExprData::Fvar(a, _), ExprData::Fvar(b, _)) => {
      w.extend(V::Free(a.clone()), V::Free(b.clone()))
    },
    (ExprData::Bvar(a, _), ExprData::Fvar(b, _)) => {
      let a = nat_usize(a);
      if a < depth {
        None
      } else {
        w.extend(V::Loose(a - depth), V::Free(b.clone()))
      }
    },
    (ExprData::Fvar(a, _), ExprData::Bvar(b, _)) => {
      let b = nat_usize(b);
      if b < depth {
        None
      } else {
        w.extend(V::Free(a.clone()), V::Loose(b - depth))
      }
    },
    (ExprData::Sort(a, _), ExprData::Sort(b, _)) => {
      if a == b {
        Some(w)
      } else {
        None
      }
    },
    (ExprData::Const(a, us, _), ExprData::Const(b, vs, _)) => {
      if a == b && us == vs { Some(w) } else { None }
    },
    (ExprData::App(f, a, _), ExprData::App(g, b, _)) => {
      let w = match_packing_expr(fuel, depth, w, f, g)?;
      match_packing_expr(fuel, depth, w, a, b)
    },
    (ExprData::Lam(_, a, body, _, _), ExprData::Lam(_, b, body2, _, _))
    | (
      ExprData::ForallE(_, a, body, _, _),
      ExprData::ForallE(_, b, body2, _, _),
    ) => {
      let w = match_packing_expr(fuel, depth, w, a, b)?;
      match_packing_expr(fuel, depth + 1, w, body, body2)
    },
    (
      ExprData::LetE(_, a, v, body, _, _),
      ExprData::LetE(_, b, v2, body2, _, _),
    ) => {
      let w = match_packing_expr(fuel, depth, w, a, b)?;
      let w = match_packing_expr(fuel, depth, w, v, v2)?;
      match_packing_expr(fuel, depth + 1, w, body, body2)
    },
    (ExprData::Lit(a, _), ExprData::Lit(b, _)) => {
      if a == b {
        Some(w)
      } else {
        None
      }
    },
    (ExprData::Proj(a, i, v, _), ExprData::Proj(b, j, v2, _)) => {
      if a == b && i == j {
        match_packing_expr(fuel, depth, w, v, v2)
      } else {
        None
      }
    },
    _ => None,
  }
}

/// `matchPackingLeaves`.
pub fn match_packing_leaves(
  actual: &[Expr],
  expected: &[Expr],
) -> Option<PackingCorrespondence> {
  if actual.len() != expected.len() {
    return None;
  }
  let mut witness = PackingCorrespondence::default();
  for (a, b) in actual.iter().zip(expected.iter()) {
    witness = match_packing_expr(DEFAULT_FUEL, 0, witness, a, b)?;
  }
  Some(witness)
}
