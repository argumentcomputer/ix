//! Pass 3: the expression toolkit of the image generator and the call-site
//! rewrite.
//!
//! A line-by-line port of the helpers the Lean side uses
//! (`Ix/Compile/Canon/Expr.lean` and `Ix/Compile/Image/Expr.lean`): the
//! results must be the same terms, binder names and `mdata` included, because
//! the generated images and the rewritten constants are compiled to bytes that
//! are compared with the Lean compiler's. Nothing here reduces, infers a type
//! or consults the kernel; every function is total (structural recursion, or
//! an explicit bound with a named error).

use bignat::Nat;
use rustc_hash::{FxHashMap, FxHashSet};

use ix_common::env::{
  BinderInfo, Expr, ExprData, Level, LevelData, Name, NameData,
};

pub type Hash = blake3::Hash;

/// The hash key of an expression (`Ix.Expr`'s `BEq`/`Hashable` are by the
/// embedded hash).
pub fn key(e: &Expr) -> Hash {
  *e.get_hash()
}

pub fn nat(n: usize) -> Nat {
  Nat::from(n as u64)
}

/// A `Nat` that indexes something in memory (bound variables, projection
/// fields); `usize::MAX` when it does not fit (never on real input: such an
/// index matches nothing).
pub fn nat_usize(n: &Nat) -> usize {
  n.to_u64().and_then(|u| usize::try_from(u).ok()).unwrap_or(usize::MAX)
}

pub fn bvar(i: usize) -> Expr {
  Expr::bvar(nat(i))
}

pub fn mk_str(p: &Name, s: &str) -> Name {
  Name::str(p.clone(), s.to_string())
}

pub fn root_name(s: &str) -> Name {
  Name::str(Name::anon(), s.to_string())
}

/// `Ix.Name.fromLeanName` of a dotted ASCII name without numeric parts.
pub fn dotted(s: &str) -> Name {
  let mut n = Name::anon();
  for c in s.split('.') {
    n = Name::str(n, c.to_string());
  }
  n
}

// ---------------------------------------------------------------------------
// Names (`Canon.Expr`)
// ---------------------------------------------------------------------------

/// A name component.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Comp {
  S(String),
  N(Nat),
}

/// The components of a name, outermost first.
pub fn comps(n: &Name) -> Vec<Comp> {
  let mut out = Vec::new();
  let mut cur = n.clone();
  loop {
    let next = match cur.as_data() {
      NameData::Anonymous(_) => break,
      NameData::Str(p, s, _) => {
        out.push(Comp::S(s.clone()));
        p.clone()
      },
      NameData::Num(p, k, _) => {
        out.push(Comp::N(k.clone()));
        p.clone()
      },
    };
    cur = next;
  }
  out.reverse();
  out
}

pub fn append_comps(n: &Name, cs: &[Comp]) -> Name {
  let mut out = n.clone();
  for c in cs {
    out = match c {
      Comp::S(s) => Name::str(out, s.clone()),
      Comp::N(k) => Name::num(out, k.clone()),
    };
  }
  out
}

/// `x ++ cs` with `x`'s components a prefix of `n`'s: the rest.
pub fn strip_prefix(x: &Name, n: &Name) -> Option<Vec<Comp>> {
  let xs = comps(x);
  let ns = comps(n);
  if xs.len() <= ns.len() && ns[..xs.len()] == xs[..] {
    Some(ns[xs.len()..].to_vec())
  } else {
    None
  }
}

/// `Canon.nameReplacePrefix`: replace the prefix `old` of `name` by `new`.
pub fn name_replace_prefix(name: &Name, old: &Name, new: &Name) -> Name {
  match strip_prefix(old, name) {
    Some(rest) => append_comps(new, &rest),
    None => name.clone(),
  }
}

// ---------------------------------------------------------------------------
// Applications
// ---------------------------------------------------------------------------

pub fn get_app_fn_args(e: &Expr) -> (Expr, Vec<Expr>) {
  let mut args = Vec::new();
  let mut cur = e.clone();
  while let ExprData::App(f, a, _) = cur.as_data() {
    args.push(a.clone());
    let f = f.clone();
    cur = f;
  }
  args.reverse();
  (cur, args)
}

pub fn get_app_fn(e: &Expr) -> Expr {
  get_app_fn_args(e).0
}

pub fn get_app_args(e: &Expr) -> Vec<Expr> {
  get_app_fn_args(e).1
}

pub fn mk_app_n(f: Expr, args: &[Expr]) -> Expr {
  args.iter().fold(f, |acc, a| Expr::app(acc, a.clone()))
}

// ---------------------------------------------------------------------------
// de Bruijn arithmetic
// ---------------------------------------------------------------------------

/// Add `n` to every loose bound variable `>= cutoff`.
pub fn lift_loose(e: &Expr, n: usize, cutoff: usize) -> Expr {
  if n == 0 {
    return e.clone();
  }
  fn go(e: &Expr, n: usize, c: usize) -> Expr {
    match e.as_data() {
      ExprData::Bvar(i, _) => {
        let i = nat_usize(i);
        if i >= c { bvar(i + n) } else { bvar(i) }
      },
      ExprData::App(f, a, _) => Expr::app(go(f, n, c), go(a, n, c)),
      ExprData::Lam(nm, t, b, bi, _) => {
        Expr::lam(nm.clone(), go(t, n, c), go(b, n, c + 1), bi.clone())
      },
      ExprData::ForallE(nm, t, b, bi, _) => {
        Expr::all(nm.clone(), go(t, n, c), go(b, n, c + 1), bi.clone())
      },
      ExprData::LetE(nm, t, v, b, nd, _) => {
        Expr::letE(nm.clone(), go(t, n, c), go(v, n, c), go(b, n, c + 1), *nd)
      },
      ExprData::Proj(nm, i, s, _) => {
        Expr::proj(nm.clone(), i.clone(), go(s, n, c))
      },
      ExprData::Mdata(md, x, _) => Expr::mdata(md.clone(), go(x, n, c)),
      _ => e.clone(),
    }
  }
  go(e, n, cutoff)
}

/// Subtract `n` from every loose bound variable `>= cutoff + n`.
pub fn lower_loose(e: &Expr, n: usize, cutoff: usize) -> Expr {
  if n == 0 {
    return e.clone();
  }
  fn go(e: &Expr, n: usize, c: usize) -> Expr {
    match e.as_data() {
      ExprData::Bvar(i, _) => {
        let i = nat_usize(i);
        if i >= c + n { bvar(i - n) } else { bvar(i) }
      },
      ExprData::App(f, a, _) => Expr::app(go(f, n, c), go(a, n, c)),
      ExprData::Lam(nm, t, b, bi, _) => {
        Expr::lam(nm.clone(), go(t, n, c), go(b, n, c + 1), bi.clone())
      },
      ExprData::ForallE(nm, t, b, bi, _) => {
        Expr::all(nm.clone(), go(t, n, c), go(b, n, c + 1), bi.clone())
      },
      ExprData::LetE(nm, t, v, b, nd, _) => {
        Expr::letE(nm.clone(), go(t, n, c), go(v, n, c), go(b, n, c + 1), *nd)
      },
      ExprData::Proj(nm, i, s, _) => {
        Expr::proj(nm.clone(), i.clone(), go(s, n, c))
      },
      ExprData::Mdata(md, x, _) => Expr::mdata(md.clone(), go(x, n, c)),
      _ => e.clone(),
    }
  }
  go(e, n, cutoff)
}

/// `Canon.instantiateRevAt`.
fn instantiate_rev_at(args: &[Expr], e: &Expr, depth: usize) -> Expr {
  match e.as_data() {
    ExprData::Bvar(i, _) => {
      let i = nat_usize(i);
      if i >= depth {
        let r = i - depth;
        if r < args.len() {
          lift_loose(&args[r], depth, 0)
        } else {
          bvar(i - args.len())
        }
      } else {
        bvar(i)
      }
    },
    ExprData::App(f, a, _) => Expr::app(
      instantiate_rev_at(args, f, depth),
      instantiate_rev_at(args, a, depth),
    ),
    ExprData::Lam(nm, t, b, bi, _) => Expr::lam(
      nm.clone(),
      instantiate_rev_at(args, t, depth),
      instantiate_rev_at(args, b, depth + 1),
      bi.clone(),
    ),
    ExprData::ForallE(nm, t, b, bi, _) => Expr::all(
      nm.clone(),
      instantiate_rev_at(args, t, depth),
      instantiate_rev_at(args, b, depth + 1),
      bi.clone(),
    ),
    ExprData::LetE(nm, t, v, b, nd, _) => Expr::letE(
      nm.clone(),
      instantiate_rev_at(args, t, depth),
      instantiate_rev_at(args, v, depth),
      instantiate_rev_at(args, b, depth + 1),
      *nd,
    ),
    ExprData::Proj(nm, i, s, _) => {
      Expr::proj(nm.clone(), i.clone(), instantiate_rev_at(args, s, depth))
    },
    ExprData::Mdata(md, x, _) => {
      Expr::mdata(md.clone(), instantiate_rev_at(args, x, depth))
    },
    _ => e.clone(),
  }
}

/// `Canon.instantiateRev`: `args[i]` for `bvar i`.
pub fn instantiate_rev(body: &Expr, args: &[Expr]) -> Expr {
  if args.is_empty() { body.clone() } else { instantiate_rev_at(args, body, 0) }
}

/// Strip `mdata` wrappers at the head.
pub fn strip_mdata(e: &Expr) -> Expr {
  let mut cur = e.clone();
  while let ExprData::Mdata(_, x, _) = cur.as_data() {
    let x = x.clone();
    cur = x;
  }
  cur
}

/// One binder of a telescope: name, domain, binder info.
pub type Binder = (Name, Expr, BinderInfo);

/// `Canon.peelForalls`: peel up to `n` leading `forall` binders, stripping
/// `mdata` before each, without instantiating.
pub fn peel_foralls(n: usize, e: &Expr) -> (Vec<Binder>, Expr) {
  let mut acc = Vec::new();
  let mut cur = e.clone();
  for _ in 0..n {
    let s = strip_mdata(&cur);
    match s.as_data() {
      ExprData::ForallE(nm, t, b, bi, _) => {
        acc.push((nm.clone(), t.clone(), bi.clone()));
        cur = b.clone();
      },
      _ => return (acc, s),
    }
  }
  (acc, cur)
}

// ---------------------------------------------------------------------------
// Universes
// ---------------------------------------------------------------------------

/// `Canon.substLevel`: parameters by name, through the smart constructors.
pub fn subst_level(params: &[Name], univs: &[Level], l: &Level) -> Level {
  match l.as_data() {
    LevelData::Succ(x, _) => Level::succ(subst_level(params, univs, x)),
    LevelData::Max(a, b, _) => Level::max_smart(
      subst_level(params, univs, a),
      subst_level(params, univs, b),
    ),
    LevelData::Imax(a, b, _) => Level::imax_smart(
      subst_level(params, univs, a),
      subst_level(params, univs, b),
    ),
    LevelData::Param(nm, _) => match params.iter().position(|p| p == nm) {
      Some(i) => univs.get(i).cloned().unwrap_or_else(|| l.clone()),
      None => l.clone(),
    },
    _ => l.clone(),
  }
}

/// `Canon.substLevels`.
pub fn subst_levels(params: &[Name], univs: &[Level], e: &Expr) -> Expr {
  if params.is_empty() || univs.is_empty() {
    return e.clone();
  }
  fn go(params: &[Name], univs: &[Level], e: &Expr) -> Expr {
    match e.as_data() {
      ExprData::Sort(l, _) => Expr::sort(subst_level(params, univs, l)),
      ExprData::Const(nm, us, _) => Expr::cnst(
        nm.clone(),
        us.iter().map(|u| subst_level(params, univs, u)).collect(),
      ),
      ExprData::App(f, a, _) => {
        Expr::app(go(params, univs, f), go(params, univs, a))
      },
      ExprData::Lam(nm, t, b, bi, _) => Expr::lam(
        nm.clone(),
        go(params, univs, t),
        go(params, univs, b),
        bi.clone(),
      ),
      ExprData::ForallE(nm, t, b, bi, _) => Expr::all(
        nm.clone(),
        go(params, univs, t),
        go(params, univs, b),
        bi.clone(),
      ),
      ExprData::LetE(nm, t, v, b, nd, _) => Expr::letE(
        nm.clone(),
        go(params, univs, t),
        go(params, univs, v),
        go(params, univs, b),
        *nd,
      ),
      ExprData::Proj(nm, i, s, _) => {
        Expr::proj(nm.clone(), i.clone(), go(params, univs, s))
      },
      ExprData::Mdata(md, x, _) => {
        Expr::mdata(md.clone(), go(params, univs, x))
      },
      _ => e.clone(),
    }
  }
  go(params, univs, e)
}

/// `Canon.normalizeLevel`: bottom-up through the smart constructors.
pub fn normalize_level(l: &Level) -> Level {
  match l.as_data() {
    LevelData::Succ(x, _) => Level::succ(normalize_level(x)),
    LevelData::Max(a, b, _) => {
      Level::max_smart(normalize_level(a), normalize_level(b))
    },
    LevelData::Imax(a, b, _) => {
      Level::imax_smart(normalize_level(a), normalize_level(b))
    },
    _ => l.clone(),
  }
}

/// Lean's `Level.isAlwaysZero`.
pub fn is_always_zero(l: &Level) -> bool {
  match l.as_data() {
    LevelData::Zero(_) => true,
    LevelData::Max(a, b, _) => is_always_zero(a) && is_always_zero(b),
    LevelData::Imax(_, b, _) => is_always_zero(b),
    _ => false,
  }
}

pub fn lvl_zero() -> Level {
  Level::zero()
}

pub fn lvl_one() -> Level {
  Level::succ(Level::zero())
}

// ---------------------------------------------------------------------------
// Name rewriting
// ---------------------------------------------------------------------------

/// `Canon.replaceConstNames`: constants and projection structure names.
pub fn replace_const_names(map: &FxHashMap<Name, Name>, e: &Expr) -> Expr {
  if map.is_empty() {
    return e.clone();
  }
  fn go(map: &FxHashMap<Name, Name>, e: &Expr) -> Expr {
    match e.as_data() {
      ExprData::Const(nm, ls, _) => Expr::cnst(
        map.get(nm).cloned().unwrap_or_else(|| nm.clone()),
        ls.clone(),
      ),
      ExprData::App(f, a, _) => Expr::app(go(map, f), go(map, a)),
      ExprData::Lam(nm, t, b, bi, _) => {
        Expr::lam(nm.clone(), go(map, t), go(map, b), bi.clone())
      },
      ExprData::ForallE(nm, t, b, bi, _) => {
        Expr::all(nm.clone(), go(map, t), go(map, b), bi.clone())
      },
      ExprData::LetE(nm, t, v, b, nd, _) => {
        Expr::letE(nm.clone(), go(map, t), go(map, v), go(map, b), *nd)
      },
      ExprData::Proj(nm, i, s, _) => Expr::proj(
        map.get(nm).cloned().unwrap_or_else(|| nm.clone()),
        i.clone(),
        go(map, s),
      ),
      ExprData::Mdata(md, x, _) => Expr::mdata(md.clone(), go(map, x)),
      _ => e.clone(),
    }
  }
  go(map, e)
}

/// `Canon.canonicalizeConstNames`: constants only.
pub fn canonicalize_const_names(map: &FxHashMap<Name, Name>, e: &Expr) -> Expr {
  if map.is_empty() {
    return e.clone();
  }
  fn go(map: &FxHashMap<Name, Name>, e: &Expr) -> Expr {
    match e.as_data() {
      ExprData::Const(nm, ls, _) => match map.get(nm) {
        Some(n2) => Expr::cnst(n2.clone(), ls.clone()),
        None => e.clone(),
      },
      ExprData::App(f, a, _) => Expr::app(go(map, f), go(map, a)),
      ExprData::Lam(nm, t, b, bi, _) => {
        Expr::lam(nm.clone(), go(map, t), go(map, b), bi.clone())
      },
      ExprData::ForallE(nm, t, b, bi, _) => {
        Expr::all(nm.clone(), go(map, t), go(map, b), bi.clone())
      },
      ExprData::LetE(nm, t, v, b, nd, _) => {
        Expr::letE(nm.clone(), go(map, t), go(map, v), go(map, b), *nd)
      },
      ExprData::Proj(nm, i, s, _) => {
        Expr::proj(nm.clone(), i.clone(), go(map, s))
      },
      ExprData::Mdata(md, x, _) => Expr::mdata(md.clone(), go(map, x)),
      _ => e.clone(),
    }
  }
  go(map, e)
}

/// `Canon.constsIn`: constants of `e` (heads only) that are in `names`, in
/// the order of a pre-order walk (the Lean result is a set; callers only test
/// membership or iterate where the order is irrelevant).
pub fn consts_in(names: &FxHashSet<Name>, e: &Expr) -> FxHashSet<Name> {
  let mut acc = FxHashSet::default();
  let mut stack = vec![e.clone()];
  while let Some(x) = stack.pop() {
    match x.as_data() {
      ExprData::Const(nm, _, _) => {
        if names.contains(nm) {
          acc.insert(nm.clone());
        }
      },
      ExprData::App(f, a, _) => {
        stack.push(a.clone());
        stack.push(f.clone());
      },
      ExprData::Lam(_, t, b, _, _) | ExprData::ForallE(_, t, b, _, _) => {
        stack.push(b.clone());
        stack.push(t.clone());
      },
      ExprData::LetE(_, t, v, b, _, _) => {
        stack.push(b.clone());
        stack.push(v.clone());
        stack.push(t.clone());
      },
      ExprData::Proj(nm, _, s, _) => {
        if names.contains(nm) {
          acc.insert(nm.clone());
        }
        stack.push(s.clone());
      },
      ExprData::Mdata(_, s, _) => stack.push(s.clone()),
      _ => {},
    }
  }
  acc
}

// ---------------------------------------------------------------------------
// The generator's locally nameless toolkit (`Image.Expr`)
// ---------------------------------------------------------------------------

/// Fresh variables and a trace (`GenM`'s state).
#[derive(Default)]
pub struct Gen {
  pub next: usize,
  pub log: Vec<String>,
}

pub type GenResult<T> = Result<T, String>;

/// The reserved root of the generator's free variables.
pub fn fvar_root() -> Name {
  root_name("_img_fvar")
}

impl Gen {
  pub fn fresh(&mut self) -> Name {
    let n = Name::num(fvar_root(), nat(self.next));
    self.next += 1;
    n
  }
  pub fn trace(&mut self, s: String) {
    self.log.push(s);
  }
}

/// `GenM.idx`: total array access.
pub fn idx<'a, T>(a: &'a [T], i: usize, what: &str) -> GenResult<&'a T> {
  a.get(i).ok_or_else(|| {
    format!("image: {what}: index {i} out of range (size {})", a.len())
  })
}

/// An opened binder.
#[derive(Clone, Debug)]
pub struct Local {
  pub fvar: Name,
  pub user_name: Name,
  pub typ: Expr,
  pub bi: BinderInfo,
}

impl Local {
  pub fn expr(&self) -> Expr {
    Expr::fvar(self.fvar.clone())
  }
}

pub fn exprs(ls: &[Local]) -> Vec<Expr> {
  ls.iter().map(Local::expr).collect()
}

/// The index of the free variable `e` among `xs`.
pub fn fvar_idx(xs: &[Local], e: &Expr) -> Option<usize> {
  match e.as_data() {
    ExprData::Fvar(n, _) => xs.iter().position(|l| l.fvar == *n),
    _ => None,
  }
}

/// Number of leading `forall`s (through `mdata`).
pub fn forall_arity(e: &Expr) -> usize {
  let mut n = 0;
  let mut cur = e.clone();
  loop {
    let next = match cur.as_data() {
      ExprData::ForallE(_, _, b, _, _) => {
        n += 1;
        b.clone()
      },
      ExprData::Mdata(_, x, _) => x.clone(),
      _ => return n,
    };
    cur = next;
  }
}

/// `instLocals`: the last of `xs` for `bvar 0`.
pub fn inst_locals(e: &Expr, xs: &[Expr]) -> Expr {
  let rev: Vec<Expr> = xs.iter().rev().cloned().collect();
  instantiate_rev(e, &rev)
}

/// `telescope`: open up to `n` leading `forall`s with fresh variables.
pub fn telescope(
  g: &mut Gen,
  e: &Expr,
  n: Option<usize>,
) -> (Vec<Local>, Expr) {
  let n = n.unwrap_or_else(|| forall_arity(e));
  let (bs, body) = peel_foralls(n, e);
  let mut ls: Vec<Local> = Vec::with_capacity(bs.len());
  for (nm, t, bi) in bs {
    let t2 = inst_locals(&t, &exprs(&ls));
    let f = g.fresh();
    ls.push(Local { fvar: f, user_name: nm, typ: t2, bi });
  }
  let body = inst_locals(&body, &exprs(&ls));
  (ls, body)
}

/// `instForall`: the body of `forall x1 ... xn, b` at `vs`.
pub fn inst_forall(e: &Expr, vs: &[Expr]) -> GenResult<Expr> {
  let (bs, body) = peel_foralls(vs.len(), e);
  if bs.len() != vs.len() {
    return Err("instForall: too few binders".into());
  }
  Ok(inst_locals(&body, vs))
}

/// `abstractFVars`: free variables `xs` to loose bound variables, `xs.back`
/// the innermost.
pub fn abstract_fvars(xs: &[Name], e: &Expr) -> Expr {
  if xs.is_empty() {
    return e.clone();
  }
  fn go(xs: &[Name], e: &Expr, d: usize) -> Expr {
    match e.as_data() {
      ExprData::Fvar(n, _) => match xs.iter().position(|x| x == n) {
        Some(i) => bvar(d + (xs.len() - 1 - i)),
        None => e.clone(),
      },
      ExprData::App(f, a, _) => Expr::app(go(xs, f, d), go(xs, a, d)),
      ExprData::Lam(nm, t, b, bi, _) => {
        Expr::lam(nm.clone(), go(xs, t, d), go(xs, b, d + 1), bi.clone())
      },
      ExprData::ForallE(nm, t, b, bi, _) => {
        Expr::all(nm.clone(), go(xs, t, d), go(xs, b, d + 1), bi.clone())
      },
      ExprData::LetE(nm, t, v, b, nd, _) => Expr::letE(
        nm.clone(),
        go(xs, t, d),
        go(xs, v, d),
        go(xs, b, d + 1),
        *nd,
      ),
      ExprData::Proj(nm, i, s, _) => {
        Expr::proj(nm.clone(), i.clone(), go(xs, s, d))
      },
      ExprData::Mdata(md, x, _) => Expr::mdata(md.clone(), go(xs, x, d)),
      _ => e.clone(),
    }
  }
  go(xs, e, 0)
}

/// `mkBinders`: `fun xs, b` or `forall xs, b`.
pub fn mk_binders(is_lam: bool, xs: &[Local], b: &Expr) -> Expr {
  let names: Vec<Name> = xs.iter().map(|x| x.fvar.clone()).collect();
  let mut acc = abstract_fvars(&names, b);
  for (i, x) in xs.iter().enumerate().rev() {
    let ty = abstract_fvars(&names[..i], &x.typ);
    acc = if is_lam {
      Expr::lam(x.user_name.clone(), ty, acc, x.bi.clone())
    } else {
      Expr::all(x.user_name.clone(), ty, acc, x.bi.clone())
    };
  }
  acc
}

pub fn mk_lambda(xs: &[Local], b: &Expr) -> Expr {
  mk_binders(true, xs, b)
}

pub fn mk_forall(xs: &[Local], b: &Expr) -> Expr {
  mk_binders(false, xs, b)
}

/// Equality up to binder names and binder info (Lean's `Expr.eqv`).
pub fn alpha_eq(a: &Expr, b: &Expr) -> bool {
  if a.get_hash() == b.get_hash() {
    return true;
  }
  match (a.as_data(), b.as_data()) {
    (ExprData::Bvar(i, _), ExprData::Bvar(j, _)) => i == j,
    (ExprData::Fvar(x, _), ExprData::Fvar(y, _))
    | (ExprData::Mvar(x, _), ExprData::Mvar(y, _)) => x == y,
    (ExprData::Sort(u, _), ExprData::Sort(v, _)) => u == v,
    (ExprData::Const(x, us, _), ExprData::Const(y, vs, _)) => {
      x == y && us == vs
    },
    (ExprData::App(f, x, _), ExprData::App(g, y, _)) => {
      alpha_eq(f, g) && alpha_eq(x, y)
    },
    (ExprData::Lam(_, t, b, _, _), ExprData::Lam(_, t2, b2, _, _))
    | (ExprData::ForallE(_, t, b, _, _), ExprData::ForallE(_, t2, b2, _, _)) => {
      alpha_eq(t, t2) && alpha_eq(b, b2)
    },
    (ExprData::LetE(_, t, v, b, _, _), ExprData::LetE(_, t2, v2, b2, _, _)) => {
      alpha_eq(t, t2) && alpha_eq(v, v2) && alpha_eq(b, b2)
    },
    (ExprData::Lit(x, _), ExprData::Lit(y, _)) => x == y,
    (ExprData::Mdata(_, x, _), ExprData::Mdata(_, y, _)) => alpha_eq(x, y),
    (ExprData::Proj(s, i, x, _), ExprData::Proj(s2, i2, y, _)) => {
      s == s2 && i == i2 && alpha_eq(x, y)
    },
    _ => false,
  }
}

/// `bvar i` occurs loose in `e`.
pub fn has_loose_bvar(e: &Expr, i: usize) -> bool {
  fn go(e: &Expr, k: usize) -> bool {
    match e.as_data() {
      ExprData::Bvar(j, _) => nat_usize(j) == k,
      ExprData::App(f, a, _) => go(f, k) || go(a, k),
      ExprData::Lam(_, t, b, _, _) | ExprData::ForallE(_, t, b, _, _) => {
        go(t, k) || go(b, k + 1)
      },
      ExprData::LetE(_, t, v, b, _, _) => go(t, k) || go(v, k) || go(b, k + 1),
      ExprData::Proj(_, _, s, _) | ExprData::Mdata(_, s, _) => go(s, k),
      _ => false,
    }
  }
  go(e, i)
}

/// Lean's `Expr.eta`: `fun x. f x` to `f` when `x` is not in `f`, inner
/// binders first.
pub fn eta_reduce(e: &Expr) -> Expr {
  match e.as_data() {
    ExprData::Lam(n, d, b, bi, _) => {
      let b2 = eta_reduce(b);
      if let ExprData::App(f, a, _) = b2.as_data()
        && let ExprData::Bvar(z, _) = a.as_data()
        && nat_usize(z) == 0
        && !has_loose_bvar(f, 0)
      {
        return lower_loose(f, 1, 0);
      }
      Expr::lam(n.clone(), d.clone(), b2, bi.clone())
    },
    _ => e.clone(),
  }
}

/// The head constant of an application spine.
pub fn head_const(e: &Expr) -> Option<(Name, Vec<Level>)> {
  match get_app_fn(e).as_data() {
    ExprData::Const(n, us, _) => Some((n.clone(), us.clone())),
    _ => None,
  }
}

/// The last argument of an application.
pub fn app_arg(e: &Expr) -> Option<Expr> {
  match e.as_data() {
    ExprData::App(_, a, _) => Some(a.clone()),
    _ => None,
  }
}

/// Constants of `e` in first-occurrence order of a pre-order walk, function
/// before argument (Lean's `Expr.getUsedConstants`).
pub fn used_constants(e: &Expr) -> Vec<Name> {
  let mut acc = Vec::new();
  let mut seen = FxHashSet::default();
  let mut stack = vec![e.clone()];
  while let Some(x) = stack.pop() {
    match x.as_data() {
      ExprData::Const(n, _, _) => {
        if seen.insert(n.clone()) {
          acc.push(n.clone());
        }
      },
      ExprData::App(f, a, _) => {
        stack.push(a.clone());
        stack.push(f.clone());
      },
      ExprData::Lam(_, t, b, _, _) | ExprData::ForallE(_, t, b, _, _) => {
        stack.push(b.clone());
        stack.push(t.clone());
      },
      ExprData::LetE(_, t, v, b, _, _) => {
        stack.push(b.clone());
        stack.push(v.clone());
        stack.push(t.clone());
      },
      ExprData::Proj(_, _, s, _) | ExprData::Mdata(_, s, _) => {
        stack.push(s.clone());
      },
      _ => {},
    }
  }
  acc
}

/// The first subterm satisfying `p` in a pre-order walk, function before
/// argument (Lean's `Expr.find?`).
pub fn find_sub(p: &dyn Fn(&Expr) -> bool, e: &Expr) -> Option<Expr> {
  let mut stack = vec![e.clone()];
  while let Some(x) = stack.pop() {
    if p(&x) {
      return Some(x);
    }
    match x.as_data() {
      ExprData::App(f, a, _) => {
        stack.push(a.clone());
        stack.push(f.clone());
      },
      ExprData::Lam(_, t, b, _, _) | ExprData::ForallE(_, t, b, _, _) => {
        stack.push(b.clone());
        stack.push(t.clone());
      },
      ExprData::LetE(_, t, v, b, _, _) => {
        stack.push(b.clone());
        stack.push(v.clone());
        stack.push(t.clone());
      },
      ExprData::Proj(_, _, s, _) | ExprData::Mdata(_, s, _) => {
        stack.push(s.clone());
      },
      _ => {},
    }
  }
  None
}

/// The sort at the end of a motive type (`motiveLevel`).
pub fn motive_level(e: &Expr) -> Level {
  let mut cur = e.clone();
  loop {
    let next = match cur.as_data() {
      ExprData::ForallE(_, _, b, _, _) | ExprData::Mdata(_, b, _) => b.clone(),
      ExprData::Sort(l, _) => return l.clone(),
      _ => return lvl_zero(),
    };
    cur = next;
  }
}

/// A motive type with its sort replaced by `Sort 0` (`stripSort`).
pub fn strip_sort(e: &Expr) -> Expr {
  match e.as_data() {
    ExprData::ForallE(n, t, b, bi, _) => {
      Expr::all(n.clone(), t.clone(), strip_sort(b), bi.clone())
    },
    ExprData::Mdata(_, b, _) => strip_sort(b),
    ExprData::Sort(_, _) => Expr::sort(lvl_zero()),
    _ => e.clone(),
  }
}
