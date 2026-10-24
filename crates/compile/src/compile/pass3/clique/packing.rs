//! The right-nested binary packings of the clique encodings, the
//! transport's packing step (a port of `Ix/Compile/Pass/Clique/Packing.lean`
//! and `PackingMatch.lean`).
//!
//! Two packings, both nested to the right, as `Lean.Meta.ArgsPacker.Mutual`
//! and `Lean.Meta.PProdN` build them (Lean 4.34.1):
//!
//! * **sums** `PSum D₀ (PSum D₁ … D_{n-1})` (well-founded recursion): the
//!   type, its injections `inj_i v = inr (… (inr (inl v)))` (`inr^{n-1} v`
//!   for the last summand), and its case trees (`PSum.casesOn` nested in the
//!   second alternative, with any motive and any number of extra arguments
//!   threaded through the alternatives);
//! * **products** `PProd R₀ (PProd R₁ … R_{n-1})`, or `And` where both sides
//!   are propositions (`mkPProd`): the type, its tuples (`PProd.mk` /
//!   `And.intro`), and its projection paths (`.proj PProd 1` …
//!   `.proj PProd 0`).
//!
//! For every construct there is a decoder (`decode_*`, `None` when the term
//! is not of that shape) and a builder that re-encodes from the decoded parts
//! in any order. Decoders are checked by re-encoding: a term is accepted only
//! when the builder, run in Lean's own order on the decoded parts, gives the
//! term back (up to binder names and `mdata`, [`alpha_eq_skip_mdata`]).
//! Levels are those Lean computes ([`pair_level`]).
//!
//! The builders are total: a spine whose leaves and levels differ in number,
//! or a position past its leaves, gives `None`, never a default term.
//!
//! [`match_packing_leaves`] compares the leaves of a packing with the
//! expected leaves under one injective correspondence of their external
//! variables, erasing only the transparent annotations `optParam`,
//! `autoParam`, `outParam` and `semiOutParam`: syntactic evidence for
//! recognition, not a proof of type equality.

use ix_common::env::{BinderInfo, Expr, ExprData, Level, Name};

use super::basic::{
  alpha_eq_skip_mdata, bvar, cnst, const_app, dotted, is_always_zero,
  lift_loose, lower_opt, mk_app_n, n_and, n_and_intro, n_pprod, n_pprod_mk,
  n_psum, n_psum_cases_on, n_psum_inl, n_psum_inr, pair_level, peel_lams,
  permute, proj, root_name, subst_bvar0_same,
};
use super::bounds::TRANSPORT_FUEL;
use crate::compile::pass3::expr::{get_app_fn_args, nat_usize, strip_mdata};

/// The kind of a packing (`PackKind`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PackKind {
  Psum,
  Pprod,
}

/// A decoded packing type (`Spine`): its leaves in packing order and their
/// levels (`0` for a leaf of an `And` node).
#[derive(Clone, Debug)]
pub struct Spine {
  pub kind: PackKind,
  pub leaves: Vec<Expr>,
  pub lvls: Vec<Level>,
}

impl Spine {
  /// `Spine.size`: the number of leaves.
  pub fn size(&self) -> usize {
    self.leaves.len()
  }

  /// `Spine.suffixes`: `S_k` (the suffix type from leaf `k`) and its level,
  /// for every `k < n` (empty for a spine without leaves); `None` when the
  /// spine's leaves and levels differ in number.
  pub fn suffixes(&self) -> Option<Vec<(Expr, Level)>> {
    if self.leaves.len() != self.lvls.len() {
      return None;
    }
    let (Some((last_leaf, leaves)), Some((last_lvl, lvls))) =
      (self.leaves.split_last(), self.lvls.split_last())
    else {
      return Some(Vec::new());
    };
    // from the last leaf leftwards: each node over the leaf and the suffix
    // after it
    let mut cur = (last_leaf.clone(), last_lvl.clone());
    let mut acc = vec![cur.clone()];
    for (a, l) in leaves.iter().zip(lvls).rev() {
      cur = (
        mk_node(self.kind, l, &cur.1, a, &cur.0),
        node_level(self.kind, l, &cur.1),
      );
      acc.push(cur.clone());
    }
    acc.reverse();
    Some(acc)
  }

  /// `Spine.type?`: the packing type itself (`S_0`); `None` for a spine
  /// without leaves or whose leaves and levels differ in number.
  pub fn typ(&self) -> Option<Expr> {
    self.suffixes()?.into_iter().next().map(|(t, _)| t)
  }

  /// `Spine.permute`: the same packing with its leaves (and their levels) in
  /// another order, `s[i]` the new position of leaf `i`; `None` when `s` is
  /// not a permutation of the leaves.
  pub fn permute(&self, s: &[usize]) -> Option<Spine> {
    Some(Spine {
      kind: self.kind,
      leaves: permute(s, &self.leaves)?,
      lvls: permute(s, &self.lvls)?,
    })
  }

  /// The same packing with `f` applied to every leaf.
  pub fn map_leaves(&self, f: &dyn Fn(&Expr) -> Expr) -> Spine {
    self.with_leaves(self.leaves.iter().map(f).collect())
  }

  /// The same packing with other leaves.
  pub fn with_leaves(&self, leaves: Vec<Expr>) -> Spine {
    Spine { kind: self.kind, leaves, lvls: self.lvls.clone() }
  }

  /// `Spine.nodeStruct`: the structure name of node `k < n - 1` of a product
  /// packing (`None` past the last node).
  pub fn node_struct(&self, k: usize) -> Option<Name> {
    let suf = self.suffixes()?;
    let (_, lr) = suf.get(k.checked_add(1)?)?;
    let l = self.lvls.get(k)?;
    Some(if is_always_zero(l) && is_always_zero(lr) {
      n_and()
    } else {
      n_pprod()
    })
  }

  /// `Spine.projSteps`: the projection steps `(structure, field)` from a
  /// value of the packing to its component `j < n` (`PProdN.proj`): `j`
  /// times `.2`, then `.1` unless last; `None` for `j >= n`.
  pub fn proj_steps(&self, j: usize) -> Option<Vec<(Name, usize)>> {
    let mut acc = Vec::new();
    for k in 0..j {
      acc.push((self.node_struct(k)?, 1));
    }
    if j < self.size().saturating_sub(1) {
      acc.push((self.node_struct(j)?, 0));
    }
    Some(acc)
  }
}

/// `nodeLevel`: the level of a node over a leaf of level `l` and a rest of
/// level `r`.
pub fn node_level(k: PackKind, l: &Level, r: &Level) -> Level {
  match k {
    PackKind::Pprod if is_always_zero(l) && is_always_zero(r) => Level::zero(),
    PackKind::Psum | PackKind::Pprod => pair_level(l, r),
  }
}

/// `mkNode`: the node type former applied to a leaf and a rest.
pub fn mk_node(k: PackKind, l: &Level, r: &Level, a: &Expr, b: &Expr) -> Expr {
  let head = match k {
    PackKind::Psum => cnst(&n_psum(), &[l.clone(), r.clone()]),
    PackKind::Pprod if is_always_zero(l) && is_always_zero(r) => {
      cnst(&n_and(), &[])
    },
    PackKind::Pprod => cnst(&n_pprod(), &[l.clone(), r.clone()]),
  };
  mk_app_n(head, &[a.clone(), b.clone()])
}

/// `decodeNode`: one node, `(leaf level, rest level, leaf, rest)`.
pub fn decode_node(
  k: PackKind,
  e: &Expr,
) -> Option<(Level, Level, Expr, Expr)> {
  let (n, us, args) = const_app(e)?;
  let [a, b] = args.as_slice() else { return None };
  match (k, us.as_slice()) {
    (PackKind::Psum, [l, r]) if n == n_psum() => {
      Some((l.clone(), r.clone(), a.clone(), b.clone()))
    },
    (PackKind::Pprod, [l, r]) if n == n_pprod() => {
      Some((l.clone(), r.clone(), a.clone(), b.clone()))
    },
    (PackKind::Pprod, []) if n == n_and() => {
      Some((Level::zero(), Level::zero(), a.clone(), b.clone()))
    },
    _ => None,
  }
}

/// `decodeSpine`: decode an `n`-leaf packing type (`n >= 2`), walking
/// `n - 1` nodes to the right. The last right child is a leaf, whatever its
/// shape; the levels of the inner nodes must be the ones Lean computes.
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
  if alpha_eq_skip_mdata(&s.typ()?, e) { Some(s) } else { None }
}

// ---------------------------------------------------------------------------
// Sums: injections
// ---------------------------------------------------------------------------

/// `head` (`PSum.inl` or `PSum.inr`) at node `j` of the packing `s` (with
/// suffixes `suf`) applied to `acc`.
fn psum_inj(
  head: &Name,
  s: &Spine,
  suf: &[(Expr, Level)],
  j: usize,
  acc: Expr,
) -> Option<Expr> {
  let (r, lr) = suf.get(j.checked_add(1)?)?;
  let head = cnst(head, &[s.lvls.get(j)?.clone(), lr.clone()]);
  Some(mk_app_n(head, &[s.leaves.get(j)?.clone(), r.clone(), acc]))
}

/// `mkInj`: `inj_j v` over the packing `s` (`ArgsPacker.Mutual.pack`); for
/// `j >= n - 1` the injection into the last summand.
pub fn mk_inj(s: &Spine, j: usize, v: &Expr) -> Option<Expr> {
  let suf = s.suffixes()?;
  // `j + 1 < n`, and Lean's `n - 1` (truncated at 0)
  let last = s.size().saturating_sub(1);
  let mut acc = v.clone();
  if j < last {
    acc = psum_inj(&n_psum_inl(), s, &suf, j, acc)?;
  }
  let inr = n_psum_inr();
  for k in (0..j.min(last)).rev() {
    acc = psum_inj(&inr, s, &suf, k, acc)?;
  }
  Some(acc)
}

/// `decodeInj`: decode an injection into an `n`-summand packing: its
/// packing, the index, the injected value. Checked by re-encoding.
pub fn decode_inj(n: usize, e: &Expr) -> Option<(Spine, usize, Expr)> {
  let (h, us, args) = const_app(e)?;
  let (inl, inr) = (n_psum_inl(), n_psum_inr());
  if !((h == inl || h == inr) && args.len() == 3 && us.len() == 2) {
    return None;
  }
  let ty = mk_app_n(
    cnst(&n_psum(), &us),
    &[args.first()?.clone(), args.get(1)?.clone()],
  );
  let s = decode_spine(PackKind::Psum, n, &ty)?;
  // follow the chain (`n >= 2`: the spine decoded)
  let mut cur = e.clone();
  let mut idx = 0;
  let mut found: Option<Expr> = None;
  for _ in 0..n - 1 {
    if found.is_some() {
      break;
    }
    let (h2, _, a) = const_app(&cur)?;
    let [_, _, v] = a.as_slice() else { return None };
    if h2 == inl {
      found = Some(v.clone());
    } else if h2 == inr {
      idx += 1;
      cur = v.clone();
    } else {
      return None;
    }
  }
  let v = found.unwrap_or(cur);
  if idx >= n {
    return None;
  }
  if alpha_eq_skip_mdata(&mk_inj(&s, idx, &v)?, e) {
    Some((s, idx, v))
  } else {
    None
  }
}

// ---------------------------------------------------------------------------
// Sums: case trees
// ---------------------------------------------------------------------------

/// A decoded case tree over an `n`-summand packing (`Tree`).
#[derive(Clone, Debug)]
pub struct Tree {
  pub spine: Spine,
  /// the motive's result level (`PSum.casesOn`'s first level), equal at
  /// every node
  pub w: Level,
  /// the body of the top motive `λ x. M`
  pub motive_body: Expr,
  pub motive_name: Name,
  pub major: Expr,
  /// the alternative for summand `i`, in the top context
  pub leaves: Vec<Expr>,
  /// the arguments threaded through the alternatives
  pub extras: Vec<Expr>,
  /// binder names of the inner alternatives (the summand variable and the
  /// extra arguments), for readability only
  pub alt_names: Vec<Name>,
}

/// `mkPrefix`: `pre_k(t) = inr (… (inr t))` (`k` times) over the packing,
/// the term of type `S_0` that the inner alternatives' variable stands for;
/// `None` for `k >= n`.
pub fn mk_prefix(s: &Spine, k: usize, t: &Expr) -> Option<Expr> {
  let suf = s.suffixes()?;
  let inr = n_psum_inr();
  let mut acc = t.clone();
  for j in (0..k).rev() {
    acc = psum_inj(&inr, s, &suf, j, acc)?;
  }
  Some(acc)
}

/// `forallDomains`: peel `r` leading `∀`s (through `mdata`), returning the
/// domains as consecutive binders.
pub fn forall_domains(r: usize, e: &Expr) -> Option<Vec<(Name, Expr)>> {
  let mut cur = e.clone();
  let mut acc = Vec::new();
  for _ in 0..r {
    let s = strip_mdata(&cur);
    let ExprData::ForallE(nm, t, b, _, _) = s.as_data() else { return None };
    acc.push((nm.clone(), t.clone()));
    cur = b.clone();
  }
  Some(acc)
}

/// `motiveAt`: `M[x := pre_k(z)]` for the motive body `M` (in the top
/// context plus the motive binder), placed under `dk` alternative binders
/// and a new binder `z` (`bvar 0`).
pub fn motive_at(t: &Tree, k: usize, dk: usize) -> Option<Expr> {
  let m = lift_loose(&t.motive_body, dk, 1);
  let s2 = t.spine.map_leaves(&|x| lift_loose(x, dk + 1, 0));
  Some(subst_bvar0_same(&m, &mk_prefix(&s2, k, &bvar(0))?))
}

/// `buildTreeAt`: build the case tree (Lean's construction) at node `k`,
/// under `dk` binders introduced by the alternatives above it. All parts of
/// `t` live in the top context and are lifted here.
pub fn build_tree_at(
  t: &Tree,
  fuel: usize,
  k: usize,
  dk: usize,
  major: &Expr,
  extras: &[Expr],
) -> Option<Expr> {
  let fuel = fuel.checked_sub(1)?;
  let s = &t.spine;
  let n = s.size();
  let suf = s.suffixes()?;
  let r = t.extras.len();
  let (sk, _) = suf.get(k)?;
  let (sk1, lk1) = suf.get(k + 1)?;
  let motive = Expr::lam(
    t.motive_name.clone(),
    lift_loose(sk, dk, 0),
    motive_at(t, k, dk)?,
    BinderInfo::Default,
  );
  let alt1 = lift_loose(t.leaves.get(k)?, dk, 0);
  let alt2 = if k + 2 == n {
    lift_loose(t.leaves.get(n - 1)?, dk, 0)
  } else {
    // λ (z : S_{k+1}) (e₁ … e_r). tree_{k+1} z e₁ … e_r
    let ds = forall_domains(r, &motive_at(t, k + 1, dk)?)?;
    let inner_extras: Vec<Expr> = (0..r).map(|i| bvar(r - 1 - i)).collect();
    let inner =
      build_tree_at(t, fuel, k + 1, dk + 1 + r, &bvar(r), &inner_extras)?;
    let body = ds.iter().enumerate().rev().fold(inner, |acc, (i, (nm, ty))| {
      let name = t.alt_names.get(i + 1).cloned().unwrap_or_else(|| nm.clone());
      Expr::lam(name, ty.clone(), acc, BinderInfo::Default)
    });
    let z_name =
      t.alt_names.first().cloned().unwrap_or_else(|| root_name("_x"));
    Expr::lam(z_name, lift_loose(sk1, dk, 0), body, BinderInfo::Default)
  };
  let head = cnst(
    &n_psum_cases_on(),
    &[t.w.clone(), s.lvls.get(k)?.clone(), lk1.clone()],
  );
  let mut args = vec![
    lift_loose(s.leaves.get(k)?, dk, 0),
    lift_loose(sk1, dk, 0),
    motive,
    major.clone(),
    alt1,
    alt2,
  ];
  args.extend_from_slice(extras);
  Some(mk_app_n(head, &args))
}

impl Tree {
  /// `Tree.build`: the whole tree.
  pub fn build(&self) -> Option<Expr> {
    if self.spine.size() < 2 {
      return None;
    }
    build_tree_at(self, self.spine.size() + 2, 0, 0, &self.major, &self.extras)
  }

  /// `Tree.permute`: the tree with its leaves and spine in canonical order
  /// (`s[i]` the new position of Lean's summand `i`); `None` when `s` is not
  /// a permutation of the summands.
  pub fn permute(&self, s: &[usize]) -> Option<Tree> {
    Some(Tree {
      spine: self.spine.permute(s)?,
      leaves: permute(s, &self.leaves)?,
      ..self.clone()
    })
  }
}

/// `decodeTree`: decode a case tree over an `n`-summand packing, checked by
/// re-encoding.
pub fn decode_tree(n: usize, e: &Expr) -> Option<Tree> {
  let (h, us, args) = const_app(e)?;
  let cases_on = n_psum_cases_on();
  if !(h == cases_on && us.len() == 3 && args.len() >= 6) {
    return None;
  }
  let ty = mk_app_n(
    cnst(&n_psum(), &[us.get(1)?.clone(), us.get(2)?.clone()]),
    &[args.first()?.clone(), args.get(1)?.clone()],
  );
  let s = decode_spine(PackKind::Psum, n, &ty)?;
  let w = us.first()?.clone();
  let motive = strip_mdata(args.get(2)?);
  let ExprData::Lam(m_name, _, m_body, _, _) = motive.as_data() else {
    return None;
  };
  let extras = args.get(6..)?.to_vec();
  let r = extras.len();
  // walk the nested second alternatives (`n >= 2`: the spine decoded)
  let mut leaves = vec![args.get(4)?.clone()];
  let mut cur = args.get(5)?.clone();
  let mut names: Vec<Name> = Vec::new();
  for k in 1..n - 1 {
    // cur = λ z e₁ … e_r. PSum.casesOn … z alt1 alt2 e₁ … e_r
    let (bs, body) = peel_lams(1 + r, &cur);
    if bs.len() != 1 + r {
      return None;
    }
    if names.is_empty() {
      names = bs.into_iter().map(|b| b.0).collect();
    }
    let (h2, _, args2) = const_app(&body)?;
    if !(h2 == cases_on && args2.len() == 6 + r) {
      return None;
    }
    leaves.push(lower_opt(args2.get(4)?, k * (1 + r))?);
    cur = args2.get(5)?.clone();
  }
  leaves.push(lower_opt(&cur, (n - 2) * (1 + r))?);
  let t = Tree {
    spine: s,
    w,
    motive_body: m_body.clone(),
    motive_name: m_name.clone(),
    major: args.get(3)?.clone(),
    leaves,
    extras,
    alt_names: names,
  };
  if alpha_eq_skip_mdata(&t.build()?, e) { Some(t) } else { None }
}

// ---------------------------------------------------------------------------
// Products: tuples and projections
// ---------------------------------------------------------------------------

/// `mkTuple`: `⟨c₀, ⟨c₁, … c_{n-1}⟩⟩` over the packing (`PProdN.mk`);
/// `None` when there are fewer than `n` components.
pub fn mk_tuple(s: &Spine, cs: &[Expr]) -> Option<Expr> {
  let suf = s.suffixes()?;
  // Lean's `n - 1` (truncated at 0)
  let last = s.size().saturating_sub(1);
  let mut acc = cs.get(last)?.clone();
  for k in (0..last).rev() {
    let (r, lr) = suf.get(k + 1)?;
    let l = s.lvls.get(k)?;
    let leaf = s.leaves.get(k)?;
    let c = cs.get(k)?;
    let head = if is_always_zero(l) && is_always_zero(lr) {
      cnst(&n_and_intro(), &[])
    } else {
      cnst(&n_pprod_mk(), &[l.clone(), lr.clone()])
    };
    acc = mk_app_n(head, &[leaf.clone(), r.clone(), c.clone(), acc]);
  }
  Some(acc)
}

/// `decodeTuple`: decode an `n`-component tuple, checked by re-encoding.
pub fn decode_tuple(n: usize, e: &Expr) -> Option<(Spine, Vec<Expr>)> {
  let (h, us, args) = const_app(e)?;
  let is_pprod = h == n_pprod_mk();
  if !((is_pprod || h == n_and_intro()) && args.len() == 4) {
    return None;
  }
  let a = args.first()?.clone();
  let b = args.get(1)?.clone();
  let ty = if is_pprod {
    mk_app_n(cnst(&n_pprod(), &us), &[a, b])
  } else {
    mk_app_n(cnst(&n_and(), &[]), &[a, b])
  };
  let s = decode_spine(PackKind::Pprod, n, &ty)?;
  let mut cs = Vec::new();
  let mut cur = e.clone();
  for _ in 0..n - 1 {
    let (_, _, a) = const_app(&cur)?;
    let [_, _, c, rest] = a.as_slice() else { return None };
    cs.push(c.clone());
    cur = rest.clone();
  }
  cs.push(cur);
  if alpha_eq_skip_mdata(&mk_tuple(&s, &cs)?, e) { Some((s, cs)) } else { None }
}

/// `applyProjs`: the projections `steps` applied to `e`, outermost last.
pub fn apply_projs(steps: &[(Name, usize)], e: &Expr) -> Expr {
  steps.iter().fold(e.clone(), |acc, (s, i)| proj(s, *i, acc))
}

// ---------------------------------------------------------------------------
// Recognising leaves up to a renaming (`PackingMatch.lean`)
// ---------------------------------------------------------------------------

/// A variable from outside the packing leaf being compared
/// (`PackingVariable`). Locally bound variables are rigid and never enter
/// the correspondence.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum PackingVariable {
  Loose(usize),
  Free(Name),
}

/// A consistent, injective syntactic correspondence across every leaf of one
/// packing (`PackingCorrespondence`). This is not a proof of type equality
/// or encoding-position ownership; the transport's region and layout
/// establish where recognition may be used.
#[derive(Clone, Default, Debug)]
pub struct PackingCorrespondence {
  pub variables: Vec<(PackingVariable, PackingVariable)>,
}

impl PackingCorrespondence {
  /// `PackingCorrespondence.extend`: `actual ↦ expected`, refused when it
  /// contradicts an entry or makes the correspondence non-injective.
  pub fn extend(
    mut self,
    actual: PackingVariable,
    expected: PackingVariable,
  ) -> Option<PackingCorrespondence> {
    if let Some((_, old)) = self.variables.iter().find(|v| v.0 == actual) {
      return if *old == expected { Some(self) } else { None };
    }
    if self.variables.iter().any(|v| v.1 == expected) {
      return None;
    }
    self.variables.push((actual, expected));
    Some(self)
  }
}

/// `packingAnnotation?`: the type under one of the transparent annotations
/// `optParam`, `autoParam`, `outParam`, `semiOutParam` (the only ones erased
/// for recognition; the caller keeps the original leaf spelling when it
/// rebuilds a packing).
pub fn packing_annotation(e: &Expr) -> Option<Expr> {
  let (h, args) = get_app_fn_args(&strip_mdata(e));
  let ExprData::Const(n, _, _) = h.as_data() else { return None };
  match args.as_slice() {
    [ty, _] if *n == dotted("optParam") || *n == dotted("autoParam") => {
      Some(ty.clone())
    },
    [ty] if *n == dotted("outParam") || *n == dotted("semiOutParam") => {
      Some(ty.clone())
    },
    _ => None,
  }
}

/// `matchPackingExpr`: compare binder structure and carry one
/// correspondence throughout the comparison. External de Bruijn indices are
/// adjusted by the local binder depth; an external variable can never stand
/// for a binder introduced inside the leaf. Fuel exhaustion is a
/// recognition failure, never successful evidence.
pub fn match_packing_expr(
  fuel: usize,
  depth: usize,
  w: PackingCorrespondence,
  actual: &Expr,
  expected: &Expr,
) -> Option<PackingCorrespondence> {
  use PackingVariable::{Free, Loose};
  let fuel = fuel.checked_sub(1)?;
  if let Some(t) = packing_annotation(actual) {
    return match_packing_expr(fuel, depth, w, &t, expected);
  }
  if let Some(t) = packing_annotation(expected) {
    return match_packing_expr(fuel, depth, w, actual, &t);
  }
  match (actual.as_data(), expected.as_data()) {
    (ExprData::Mdata(_, a, _), _) => {
      match_packing_expr(fuel, depth, w, a, expected)
    },
    (_, ExprData::Mdata(_, b, _)) => {
      match_packing_expr(fuel, depth, w, actual, b)
    },
    (ExprData::Bvar(a, _), ExprData::Bvar(b, _)) => {
      let (i, j) = (nat_usize(a), nat_usize(b));
      if i < depth || j < depth {
        if a == b { Some(w) } else { None }
      } else {
        w.extend(Loose(i - depth), Loose(j - depth))
      }
    },
    (ExprData::Fvar(a, _), ExprData::Fvar(b, _)) => {
      w.extend(Free(a.clone()), Free(b.clone()))
    },
    (ExprData::Bvar(a, _), ExprData::Fvar(b, _)) => {
      let i = nat_usize(a);
      if i < depth { None } else { w.extend(Loose(i - depth), Free(b.clone())) }
    },
    (ExprData::Fvar(a, _), ExprData::Bvar(b, _)) => {
      let j = nat_usize(b);
      if j < depth { None } else { w.extend(Free(a.clone()), Loose(j - depth)) }
    },
    (ExprData::Sort(a, _), ExprData::Sort(b, _)) => (a == b).then_some(w),
    (ExprData::Const(a, us, _), ExprData::Const(b, vs, _)) => {
      (a == b && us == vs).then_some(w)
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
    (ExprData::Lit(a, _), ExprData::Lit(b, _)) => (a == b).then_some(w),
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

/// `matchPackingLeaves`: one correspondence for the complete vector,
/// including relationships between different leaves (independent per-leaf
/// matches could lose sharing and mistake two distinct parameters for one
/// repeated parameter).
pub fn match_packing_leaves(
  actual: &[Expr],
  expected: &[Expr],
) -> Option<PackingCorrespondence> {
  if actual.len() != expected.len() {
    return None;
  }
  actual
    .iter()
    .zip(expected)
    .try_fold(PackingCorrespondence::default(), |witness, (a, b)| {
      match_packing_expr(TRANSPORT_FUEL, 0, witness, a, b)
    })
}

#[cfg(test)]
mod tests {
  use ix_common::env::{BinderInfo, Expr, Level};

  use super::{
    PackKind, PackingVariable, Spine, Tree, decode_inj, decode_spine,
    decode_tree, decode_tuple, match_packing_leaves, mk_inj, mk_tuple,
  };
  use crate::compile::pass3::clique::basic::{
    bvar, cnst, dotted, mk_app_n, n_and, n_pprod, n_psum, pair_level,
  };

  fn c(s: &str) -> Expr {
    cnst(&dotted(s), &[])
  }

  fn one() -> Level {
    Level::succ(Level::zero())
  }

  fn spine(kind: PackKind, lvl: &Level) -> Spine {
    Spine {
      kind,
      leaves: vec![c("A"), c("B"), c("C")],
      lvls: vec![lvl.clone(); 3],
    }
  }

  fn same_spine(a: &Spine, b: &Spine) -> bool {
    a.kind == b.kind && a.leaves == b.leaves && a.lvls == b.lvls
  }

  #[test]
  fn spine_round_trip_and_refusals() {
    let u = Level::param(dotted("u"));
    let s = spine(PackKind::Psum, &u);
    let ty = s.typ().unwrap();
    let back = decode_spine(PackKind::Psum, 3, &ty).unwrap();
    assert!(same_spine(&back, &s));
    // the inner level must be the one Lean computes (`max 1 u`, not `u`)
    assert_ne!(pair_level(&u, &u), u);
    let wrong = mk_app_n(
      cnst(&n_psum(), &[u.clone(), u.clone()]),
      &[
        c("A"),
        mk_app_n(cnst(&n_psum(), &[u.clone(), u.clone()]), &[c("B"), c("C")]),
      ],
    );
    assert!(decode_spine(PackKind::Psum, 3, &wrong).is_none());
    assert!(decode_spine(PackKind::Psum, 1, &ty).is_none());
    // a malformed spine (two levels for three leaves) builds nothing
    let bad = Spine { lvls: vec![u.clone(); 2], ..s.clone() };
    assert!(bad.suffixes().is_none());
    assert!(bad.typ().is_none());
    assert!(mk_inj(&bad, 0, &c("v")).is_none());
    assert!(mk_tuple(&bad, &[c("a"), c("b"), c("c")]).is_none());
    assert!(bad.node_struct(0).is_none());
    assert!(bad.proj_steps(1).is_none());
    let empty = Spine { leaves: vec![], lvls: vec![], ..s.clone() };
    assert!(empty.typ().is_none());
    // permutations
    let p = s.permute(&[1, 0, 2]).unwrap();
    assert_eq!(p.leaves, vec![c("B"), c("A"), c("C")]);
    assert!(s.permute(&[0, 0, 1]).is_none());
    assert!(s.permute(&[1, 0]).is_none());
  }

  #[test]
  fn injection_round_trip() {
    let s = spine(PackKind::Psum, &one());
    for j in 0..3 {
      let inj = mk_inj(&s, j, &c("v")).unwrap();
      let (s2, idx, v) = decode_inj(3, &inj).unwrap();
      assert!(same_spine(&s2, &s));
      assert_eq!((idx, v), (j, c("v")));
    }
    // past the last summand: the injection into the last one
    assert_eq!(mk_inj(&s, 5, &c("v")), mk_inj(&s, 2, &c("v")));
    assert!(decode_inj(3, &c("v")).is_none());
  }

  #[test]
  fn tuple_round_trip_and_projections() {
    let s = spine(PackKind::Pprod, &one());
    let cs = [c("a"), c("b"), c("c")];
    let t = mk_tuple(&s, &cs).unwrap();
    let (s2, cs2) = decode_tuple(3, &t).unwrap();
    assert!(same_spine(&s2, &s));
    assert_eq!(cs2, cs);
    assert!(mk_tuple(&s, &cs[..2]).is_none());
    assert_eq!(s.proj_steps(1), Some(vec![(n_pprod(), 1), (n_pprod(), 0)]));
    // propositions pack with `And`
    let p = spine(PackKind::Pprod, &Level::zero());
    let t = mk_tuple(&p, &cs).unwrap();
    assert!(decode_tuple(3, &t).is_some());
    assert_eq!(p.proj_steps(2), Some(vec![(n_and(), 1), (n_and(), 1)]));
    assert!(p.proj_steps(3).is_none());
  }

  #[test]
  fn tree_round_trip() {
    let alt = |x: &str, ty: &str| {
      Expr::lam(dotted(x), c(ty), c(&format!("r{x}")), BinderInfo::Default)
    };
    let t = Tree {
      spine: spine(PackKind::Psum, &one()),
      w: one(),
      motive_body: c("M"),
      motive_name: dotted("x"),
      major: c("m"),
      leaves: vec![alt("a", "A"), alt("b", "B"), alt("c", "C")],
      extras: vec![],
      alt_names: vec![],
    };
    let e = t.build().unwrap();
    let back = decode_tree(3, &e).unwrap();
    assert_eq!(back.leaves, t.leaves);
    assert_eq!(back.alt_names, vec![dotted("_x")]);
    let p = t.permute(&[2, 0, 1]).unwrap();
    assert!(decode_tree(3, &p.build().unwrap()).is_some());
    assert!(t.permute(&[0, 1]).is_none());
  }

  #[test]
  fn leaves_match_up_to_one_renaming() {
    let f = |x: Expr| Expr::app(c("F"), x);
    let w = match_packing_leaves(&[f(bvar(0))], &[f(bvar(3))]).unwrap();
    assert_eq!(
      w.variables,
      vec![(PackingVariable::Loose(0), PackingVariable::Loose(3))]
    );
    // one correspondence for every leaf: injective and consistent
    assert!(
      match_packing_leaves(&[bvar(0), bvar(0)], &[bvar(1), bvar(2)]).is_none()
    );
    assert!(
      match_packing_leaves(&[bvar(0), bvar(1)], &[bvar(2), bvar(2)]).is_none()
    );
    assert!(match_packing_leaves(&[bvar(0)], &[]).is_none());
    // transparent annotations are erased
    let opt = mk_app_n(c("optParam"), &[c("T"), c("d")]);
    assert!(match_packing_leaves(&[opt], &[c("T")]).is_some());
  }
}
