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
/// embedded hash). `alpha_eq` confirms retained raw keys. Other hash-only memo
/// hits require run-local key faithfulness: equal keys denote the same complete
/// expression; constructor consistency alone does not rule out collisions.
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
  fn go(
    e: &Expr,
    n: usize,
    c: usize,
    memo: &mut FxHashMap<(Hash, usize), Expr>,
  ) -> Expr {
    let memo_key = (key(e), c);
    if let Some(result) = memo.get(&memo_key) {
      return result.clone();
    }
    let result = {
      match e.as_data() {
        ExprData::Bvar(i, _) => {
          let i = nat_usize(i);
          if i >= c { bvar(i + n) } else { bvar(i) }
        },
        ExprData::App(f, a, _) => {
          Expr::app(go(f, n, c, memo), go(a, n, c, memo))
        },
        ExprData::Lam(nm, t, b, bi, _) => Expr::lam(
          nm.clone(),
          go(t, n, c, memo),
          go(b, n, c + 1, memo),
          bi.clone(),
        ),
        ExprData::ForallE(nm, t, b, bi, _) => Expr::all(
          nm.clone(),
          go(t, n, c, memo),
          go(b, n, c + 1, memo),
          bi.clone(),
        ),
        ExprData::LetE(nm, t, v, b, nd, _) => Expr::letE(
          nm.clone(),
          go(t, n, c, memo),
          go(v, n, c, memo),
          go(b, n, c + 1, memo),
          *nd,
        ),
        ExprData::Proj(nm, i, s, _) => {
          Expr::proj(nm.clone(), i.clone(), go(s, n, c, memo))
        },
        ExprData::Mdata(md, x, _) => Expr::mdata(md.clone(), go(x, n, c, memo)),
        _ => e.clone(),
      }
    };
    memo.insert(memo_key, result.clone());
    result
  }
  go(e, n, cutoff, &mut FxHashMap::default())
}

/// Subtract `n` from every loose bound variable `>= cutoff + n`.
pub fn lower_loose(e: &Expr, n: usize, cutoff: usize) -> Expr {
  if n == 0 {
    return e.clone();
  }
  fn go(
    e: &Expr,
    n: usize,
    c: usize,
    memo: &mut FxHashMap<(Hash, usize), Expr>,
  ) -> Expr {
    let memo_key = (key(e), c);
    if let Some(result) = memo.get(&memo_key) {
      return result.clone();
    }
    let result = {
      match e.as_data() {
        ExprData::Bvar(i, _) => {
          let i = nat_usize(i);
          if i >= c + n { bvar(i - n) } else { bvar(i) }
        },
        ExprData::App(f, a, _) => {
          Expr::app(go(f, n, c, memo), go(a, n, c, memo))
        },
        ExprData::Lam(nm, t, b, bi, _) => Expr::lam(
          nm.clone(),
          go(t, n, c, memo),
          go(b, n, c + 1, memo),
          bi.clone(),
        ),
        ExprData::ForallE(nm, t, b, bi, _) => Expr::all(
          nm.clone(),
          go(t, n, c, memo),
          go(b, n, c + 1, memo),
          bi.clone(),
        ),
        ExprData::LetE(nm, t, v, b, nd, _) => Expr::letE(
          nm.clone(),
          go(t, n, c, memo),
          go(v, n, c, memo),
          go(b, n, c + 1, memo),
          *nd,
        ),
        ExprData::Proj(nm, i, s, _) => {
          Expr::proj(nm.clone(), i.clone(), go(s, n, c, memo))
        },
        ExprData::Mdata(md, x, _) => Expr::mdata(md.clone(), go(x, n, c, memo)),
        _ => e.clone(),
      }
    };
    memo.insert(memo_key, result.clone());
    result
  }
  go(e, n, cutoff, &mut FxHashMap::default())
}

/// `Canon.instantiateRevAt`.
fn instantiate_rev_at(args: &[Expr], e: &Expr, depth: usize) -> Expr {
  fn visit(
    args: &[Expr],
    e: &Expr,
    depth: usize,
    memo: &mut FxHashMap<(Hash, usize), Expr>,
  ) -> Expr {
    let memo_key = (key(e), depth);
    if let Some(result) = memo.get(&memo_key) {
      return result.clone();
    }
    let result = {
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
        ExprData::App(f, a, _) => {
          Expr::app(visit(args, f, depth, memo), visit(args, a, depth, memo))
        },
        ExprData::Lam(nm, t, b, bi, _) => Expr::lam(
          nm.clone(),
          visit(args, t, depth, memo),
          visit(args, b, depth + 1, memo),
          bi.clone(),
        ),
        ExprData::ForallE(nm, t, b, bi, _) => Expr::all(
          nm.clone(),
          visit(args, t, depth, memo),
          visit(args, b, depth + 1, memo),
          bi.clone(),
        ),
        ExprData::LetE(nm, t, v, b, nd, _) => Expr::letE(
          nm.clone(),
          visit(args, t, depth, memo),
          visit(args, v, depth, memo),
          visit(args, b, depth + 1, memo),
          *nd,
        ),
        ExprData::Proj(nm, i, s, _) => {
          Expr::proj(nm.clone(), i.clone(), visit(args, s, depth, memo))
        },
        ExprData::Mdata(md, x, _) => {
          Expr::mdata(md.clone(), visit(args, x, depth, memo))
        },
        _ => e.clone(),
      }
    };
    memo.insert(memo_key, result.clone());
    result
  }

  visit(args, e, depth, &mut FxHashMap::default())
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
    LevelData::Param(nm, _) => {
      match params.iter().position(|p| p.same_structure(nm)) {
        Some(i) => univs.get(i).cloned().unwrap_or_else(|| l.clone()),
        None => l.clone(),
      }
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
  fn go(
    xs: &[Name],
    e: &Expr,
    d: usize,
    memo: &mut FxHashMap<(Hash, usize), Expr>,
  ) -> Expr {
    let memo_key = (key(e), d);
    if let Some(result) = memo.get(&memo_key) {
      return result.clone();
    }
    let result = {
      match e.as_data() {
        ExprData::Fvar(n, _) => match xs.iter().position(|x| x == n) {
          Some(i) => bvar(d + (xs.len() - 1 - i)),
          None => e.clone(),
        },
        ExprData::App(f, a, _) => {
          Expr::app(go(xs, f, d, memo), go(xs, a, d, memo))
        },
        ExprData::Lam(nm, t, b, bi, _) => Expr::lam(
          nm.clone(),
          go(xs, t, d, memo),
          go(xs, b, d + 1, memo),
          bi.clone(),
        ),
        ExprData::ForallE(nm, t, b, bi, _) => Expr::all(
          nm.clone(),
          go(xs, t, d, memo),
          go(xs, b, d + 1, memo),
          bi.clone(),
        ),
        ExprData::LetE(nm, t, v, b, nd, _) => Expr::letE(
          nm.clone(),
          go(xs, t, d, memo),
          go(xs, v, d, memo),
          go(xs, b, d + 1, memo),
          *nd,
        ),
        ExprData::Proj(nm, i, s, _) => {
          Expr::proj(nm.clone(), i.clone(), go(xs, s, d, memo))
        },
        ExprData::Mdata(md, x, _) => {
          Expr::mdata(md.clone(), go(xs, x, d, memo))
        },
        _ => e.clone(),
      }
    };
    memo.insert(memo_key, result.clone());
    result
  }
  go(xs, e, 0, &mut FxHashMap::default())
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

/// The hash pair selects a candidate entry; retained raw expression owners
/// confirm both keys before reusing either a true or a false result.
type AlphaMemo = FxHashMap<(Hash, Hash), (Expr, Expr, bool)>;

fn alpha_eq_visit(a: &Expr, b: &Expr, memo: &mut AlphaMemo) -> bool {
  let memo_key = (key(a), key(b));
  if let Some((saved_a, saved_b, result)) = memo.get(&memo_key)
    && saved_a == a
    && saved_b == b
  {
    return *result;
  }
  let result = (|| {
    if a.get_hash() == b.get_hash() && a == b {
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
        alpha_eq_visit(f, g, memo) && alpha_eq_visit(x, y, memo)
      },
      (ExprData::Lam(_, t, b, _, _), ExprData::Lam(_, t2, b2, _, _))
      | (
        ExprData::ForallE(_, t, b, _, _),
        ExprData::ForallE(_, t2, b2, _, _),
      ) => alpha_eq_visit(t, t2, memo) && alpha_eq_visit(b, b2, memo),
      (
        ExprData::LetE(_, t, v, b, _, _),
        ExprData::LetE(_, t2, v2, b2, _, _),
      ) => {
        alpha_eq_visit(t, t2, memo)
          && alpha_eq_visit(v, v2, memo)
          && alpha_eq_visit(b, b2, memo)
      },
      (ExprData::Lit(x, _), ExprData::Lit(y, _)) => x == y,
      (ExprData::Mdata(_, x, _), ExprData::Mdata(_, y, _)) => {
        alpha_eq_visit(x, y, memo)
      },
      (ExprData::Proj(s, i, x, _), ExprData::Proj(s2, i2, y, _)) => {
        s == s2 && i == i2 && alpha_eq_visit(x, y, memo)
      },
      _ => false,
    }
  })();
  memo.insert(memo_key, (a.clone(), b.clone(), result));
  result
}

/// Equality up to binder names, binder info, let flags and paired metadata.
/// Name/Level/Expr derived equality includes every raw cached field. Hashes
/// only select candidates: the fast return and every memo hit are confirmed.
/// One-sided metadata is not skipped (unlike the separate clique comparator).
pub fn alpha_eq(a: &Expr, b: &Expr) -> bool {
  alpha_eq_visit(a, b, &mut AlphaMemo::default())
}

/// Universe equality for motive-slot matching uses the compiler's canonical
/// positional wire form. `level_to_univ` confirms complete parameter names;
/// unresolved unequal levels never match. Keep exact raw matches, including
/// those outside the supplied context, as the raw alpha comparator does.
pub fn motive_level_eq(params: &[Name], a: &Level, b: &Level) -> bool {
  a == b
    || crate::compile::compare_level(a, b, params, params).is_ok_and(|order| {
      order.strong && order.ordering == std::cmp::Ordering::Equal
    })
}

fn motive_eq_visit(
  params: &[Name],
  a: &Expr,
  b: &Expr,
  memo: &mut AlphaMemo,
) -> bool {
  let memo_key = (key(a), key(b));
  if let Some((saved_a, saved_b, result)) = memo.get(&memo_key)
    && saved_a == a
    && saved_b == b
  {
    return *result;
  }
  let result = if a.get_hash() == b.get_hash() && a == b {
    true
  } else {
    match (a.as_data(), b.as_data()) {
      (ExprData::Bvar(i, _), ExprData::Bvar(j, _)) => i == j,
      (ExprData::Fvar(x, _), ExprData::Fvar(y, _))
      | (ExprData::Mvar(x, _), ExprData::Mvar(y, _)) => x == y,
      (ExprData::Sort(u, _), ExprData::Sort(v, _)) => {
        motive_level_eq(params, u, v)
      },
      (ExprData::Const(x, us, _), ExprData::Const(y, vs, _)) => {
        x == y
          && us.len() == vs.len()
          && us.iter().zip(vs).all(|(u, v)| motive_level_eq(params, u, v))
      },
      (ExprData::App(f, x, _), ExprData::App(g, y, _)) => {
        motive_eq_visit(params, f, g, memo)
          && motive_eq_visit(params, x, y, memo)
      },
      (ExprData::Lam(_, t, b, _, _), ExprData::Lam(_, t2, b2, _, _))
      | (
        ExprData::ForallE(_, t, b, _, _),
        ExprData::ForallE(_, t2, b2, _, _),
      ) => {
        motive_eq_visit(params, t, t2, memo)
          && motive_eq_visit(params, b, b2, memo)
      },
      (
        ExprData::LetE(_, t, v, b, _, _),
        ExprData::LetE(_, t2, v2, b2, _, _),
      ) => {
        motive_eq_visit(params, t, t2, memo)
          && motive_eq_visit(params, v, v2, memo)
          && motive_eq_visit(params, b, b2, memo)
      },
      (ExprData::Lit(x, _), ExprData::Lit(y, _)) => x == y,
      (ExprData::Mdata(_, x, _), ExprData::Mdata(_, y, _)) => {
        motive_eq_visit(params, x, y, memo)
      },
      (ExprData::Proj(s, i, x, _), ExprData::Proj(s2, i2, y, _)) => {
        s == s2 && i == i2 && motive_eq_visit(params, x, y, memo)
      },
      _ => false,
    }
  };
  memo.insert(memo_key, (a.clone(), b.clone(), result));
  result
}

/// Image motive/slot comparison. Names remain exact and metadata is paired;
/// only universe comparison differs from `alpha_eq`. The shared parameter
/// context is fixed for the lifetime of this call's confirmed memo entries.
pub fn motive_eq(params: &[Name], a: &Expr, b: &Expr) -> bool {
  motive_eq_visit(params, a, b, &mut AlphaMemo::default())
}

/// `bvar i` occurs loose in `e`.
pub fn has_loose_bvar(e: &Expr, i: usize) -> bool {
  fn go(e: &Expr, k: usize, memo: &mut FxHashMap<(Hash, usize), bool>) -> bool {
    let memo_key = (key(e), k);
    if let Some(result) = memo.get(&memo_key) {
      return *result;
    }
    let result = {
      match e.as_data() {
        ExprData::Bvar(j, _) => nat_usize(j) == k,
        ExprData::App(f, a, _) => go(f, k, memo) || go(a, k, memo),
        ExprData::Lam(_, t, b, _, _) | ExprData::ForallE(_, t, b, _, _) => {
          go(t, k, memo) || go(b, k + 1, memo)
        },
        ExprData::LetE(_, t, v, b, _, _) => {
          go(t, k, memo) || go(v, k, memo) || go(b, k + 1, memo)
        },
        ExprData::Proj(_, _, s, _) | ExprData::Mdata(_, s, _) => go(s, k, memo),
        _ => false,
      }
    };
    memo.insert(memo_key, result);
    result
  }
  go(e, i, &mut FxHashMap::default())
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

#[cfg(test)]
mod alpha_eq_tests {
  use super::*;
  use ix_common::env::{DataValue, Literal};
  use std::sync::Arc;

  fn h(n: u8) -> Hash {
    Hash::from_bytes([n; 32])
  }

  fn raw(data: ExprData) -> Expr {
    Expr(Arc::new(data))
  }

  fn raw_bvar(index: usize, cache: u8) -> Expr {
    raw(ExprData::Bvar(nat(index), h(cache)))
  }

  /// Labels and constructor cases mirror Tests/Ix/Compile/AlphaEq.lean.
  fn controls() -> Vec<(&'static str, Expr, Expr, bool)> {
    use ExprData::*;
    let n = Name(Arc::new(NameData::Anonymous(h(0))));
    let m = Name(Arc::new(NameData::Str(n.clone(), "different".into(), h(0))));
    let na = Name(Arc::new(NameData::Str(
      Name(Arc::new(NameData::Anonymous(h(1)))),
      "same".into(),
      h(0),
    )));
    let nb = Name(Arc::new(NameData::Str(
      Name(Arc::new(NameData::Anonymous(h(2)))),
      "same".into(),
      h(0),
    )));
    let z = Level(Arc::new(LevelData::Zero(h(0))));
    let s = Level(Arc::new(LevelData::Succ(z.clone(), h(0))));
    let za = Level(Arc::new(LevelData::Succ(
      Level(Arc::new(LevelData::Zero(h(1)))),
      h(0),
    )));
    let zb = Level(Arc::new(LevelData::Succ(
      Level(Arc::new(LevelData::Zero(h(2)))),
      h(0),
    )));
    let t = raw(Sort(z.clone(), h(0)));
    let x = raw_bvar(0, 1);
    let y = raw_bvar(0, 2);
    vec![
      ("identical-bvar", raw_bvar(0, 0), raw_bvar(0, 0), true),
      ("expression-hash-collision", raw_bvar(0, 0), raw_bvar(1, 0), false),
      ("expression-cache-ignored", x.clone(), y.clone(), true),
      ("constructor-hash-collision", raw_bvar(0, 0), t.clone(), false),
      (
        "fvar-name-collision",
        raw(Fvar(n.clone(), h(1))),
        raw(Fvar(m.clone(), h(2))),
        false,
      ),
      (
        "mvar-name-collision",
        raw(Mvar(n.clone(), h(1))),
        raw(Mvar(m.clone(), h(2))),
        false,
      ),
      (
        "sort-level-collision",
        raw(Sort(z.clone(), h(1))),
        raw(Sort(s.clone(), h(2))),
        false,
      ),
      (
        "constant-name-collision",
        raw(Const(n.clone(), vec![], h(1))),
        raw(Const(m.clone(), vec![], h(2))),
        false,
      ),
      (
        "constant-level-collision",
        raw(Const(n.clone(), vec![z.clone()], h(1))),
        raw(Const(n.clone(), vec![s.clone()], h(2))),
        false,
      ),
      (
        "constant-level-count",
        raw(Const(n.clone(), vec![], h(1))),
        raw(Const(n.clone(), vec![z.clone()], h(2))),
        false,
      ),
      (
        "projection-name-collision",
        raw(Proj(n.clone(), nat(0), x.clone(), h(1))),
        raw(Proj(m.clone(), nat(0), y.clone(), h(2))),
        false,
      ),
      (
        "nested-name-cache-retained",
        raw(Fvar(na.clone(), h(1))),
        raw(Fvar(nb.clone(), h(2))),
        false,
      ),
      (
        "nested-level-cache-retained",
        raw(Sort(za.clone(), h(1))),
        raw(Sort(zb.clone(), h(2))),
        false,
      ),
      (
        "level-param-name-cache-retained",
        raw(Sort(Level(Arc::new(LevelData::Param(na, h(0)))), h(1))),
        raw(Sort(Level(Arc::new(LevelData::Param(nb, h(0)))), h(2))),
        false,
      ),
      (
        "level-max-child-collision",
        raw(Sort(
          Level(Arc::new(LevelData::Max(z.clone(), z.clone(), h(0)))),
          h(1),
        )),
        raw(Sort(
          Level(Arc::new(LevelData::Max(z.clone(), s.clone(), h(0)))),
          h(2),
        )),
        false,
      ),
      (
        "constant-nested-level-cache",
        raw(Const(n.clone(), vec![za], h(1))),
        raw(Const(n.clone(), vec![zb], h(2))),
        false,
      ),
      (
        "lambda-binder-neighbour",
        raw(Lam(n.clone(), t.clone(), x.clone(), BinderInfo::Default, h(1))),
        raw(Lam(m.clone(), t.clone(), y.clone(), BinderInfo::Implicit, h(2))),
        true,
      ),
      (
        "forall-binder-neighbour",
        raw(ForallE(
          n.clone(),
          t.clone(),
          x.clone(),
          BinderInfo::Default,
          h(1),
        )),
        raw(ForallE(
          m.clone(),
          t.clone(),
          y.clone(),
          BinderInfo::InstImplicit,
          h(2),
        )),
        true,
      ),
      (
        "let-flag-neighbour",
        raw(LetE(n.clone(), t.clone(), x.clone(), x.clone(), false, h(1))),
        raw(LetE(m.clone(), t.clone(), y.clone(), y.clone(), true, h(2))),
        true,
      ),
      (
        "paired-metadata-neighbour",
        raw(Mdata(
          vec![(n.clone(), DataValue::OfNat(nat(0)))],
          x.clone(),
          h(1),
        )),
        raw(Mdata(vec![(m, DataValue::OfBool(true))], y.clone(), h(2))),
        true,
      ),
      (
        "one-sided-metadata-left",
        raw(Mdata(vec![], x.clone(), h(0))),
        x.clone(),
        false,
      ),
      (
        "one-sided-metadata-right",
        x.clone(),
        raw(Mdata(vec![], x.clone(), h(0))),
        false,
      ),
      (
        "metadata-child-collision",
        raw(Mdata(vec![], raw_bvar(0, 0), h(1))),
        raw(Mdata(vec![], raw_bvar(1, 0), h(2))),
        false,
      ),
      (
        "projection-index",
        raw(Proj(n.clone(), nat(0), x.clone(), h(1))),
        raw(Proj(n.clone(), nat(1), y.clone(), h(2))),
        false,
      ),
      (
        "equal-literal-neighbour",
        raw(Lit(Literal::NatVal(nat(0)), h(1))),
        raw(Lit(Literal::NatVal(nat(0)), h(2))),
        true,
      ),
      (
        "different-literal",
        raw(Lit(Literal::NatVal(nat(0)), h(1))),
        raw(Lit(Literal::NatVal(nat(1)), h(2))),
        false,
      ),
      (
        "literal-constructor",
        raw(Lit(Literal::NatVal(nat(0)), h(1))),
        raw(Lit(Literal::StrVal("0".into()), h(2))),
        false,
      ),
      (
        "equal-constant-neighbour",
        raw(Const(n.clone(), vec![z.clone()], h(1))),
        raw(Const(n.clone(), vec![z.clone()], h(2))),
        true,
      ),
      (
        "universe-order",
        raw(Const(n.clone(), vec![z.clone(), s.clone()], h(1))),
        raw(Const(n.clone(), vec![s, z], h(2))),
        false,
      ),
      (
        "sibling-memo-collision",
        raw(App(x.clone(), raw_bvar(1, 1), h(3))),
        raw(App(y.clone(), raw_bvar(2, 2), h(4))),
        false,
      ),
      (
        "repeated-pair-neighbour",
        raw(App(x.clone(), x.clone(), h(3))),
        raw(App(y.clone(), y.clone(), h(4))),
        true,
      ),
      (
        "false-child-neighbour",
        raw(App(x, raw_bvar(0, 1), h(3))),
        raw(App(raw_bvar(1, 2), y, h(4))),
        false,
      ),
      (
        "equal-fvar-neighbour",
        raw(Fvar(n.clone(), h(1))),
        raw(Fvar(n, h(2))),
        true,
      ),
      (
        "smart-lambda-neighbour",
        Expr::lam(
          root_name("x"),
          Expr::sort(Level::zero()),
          bvar(0),
          BinderInfo::Default,
        ),
        Expr::lam(
          root_name("y"),
          Expr::sort(Level::zero()),
          bvar(0),
          BinderInfo::Implicit,
        ),
        true,
      ),
      (
        "smart-constant-neighbour",
        Expr::cnst(root_name("Nat"), vec![]),
        Expr::cnst(root_name("Nat"), vec![]),
        true,
      ),
    ]
  }

  #[test]
  fn alpha_eq_raw_cases_match_lean() {
    for (label, a, b, expected) in controls() {
      assert_eq!(alpha_eq(&a, &b), expected, "{label}");
    }
  }

  #[test]
  fn motive_slots_use_canonical_universes_and_retain_raw_guards() {
    let root = Name(Arc::new(NameData::Anonymous(h(0))));
    let u = Name(Arc::new(NameData::Str(root.clone(), "u".into(), h(0))));
    let v = Name(Arc::new(NameData::Str(root.clone(), "v".into(), h(0))));
    let symbol = Name(Arc::new(NameData::Str(root, "F".into(), h(0))));
    let zero = Level(Arc::new(LevelData::Zero(h(0))));
    let one = Level(Arc::new(LevelData::Succ(zero.clone(), h(0))));
    let p = Level(Arc::new(LevelData::Param(u.clone(), h(0))));
    let q = Level(Arc::new(LevelData::Param(v.clone(), h(0))));
    let max = |a: &Level, b: &Level| {
      Level(Arc::new(LevelData::Max(a.clone(), b.clone(), h(0))))
    };
    let imax = |a: &Level, b: &Level| {
      Level(Arc::new(LevelData::Imax(a.clone(), b.clone(), h(0))))
    };
    let sort = |level: &Level| raw(ExprData::Sort(level.clone(), h(0)));
    let cnst =
      |levels: Vec<Level>| raw(ExprData::Const(symbol.clone(), levels, h(0)));
    let params = vec![u.clone(), v];
    let max00 = max(&zero, &zero);
    // These labels and cases mirror Tests/Ix/Compile/MotiveEq.lean.
    let controls = vec![
      ("zero-max00", vec![], sort(&zero), sort(&max00), true, false),
      (
        "commuting-parameters",
        params.clone(),
        sort(&max(&p, &q)),
        sort(&max(&q, &p)),
        true,
        false,
      ),
      (
        "idempotent-max",
        params.clone(),
        sort(&max(&p, &p)),
        sort(&p),
        true,
        false,
      ),
      (
        "imax-zero",
        params.clone(),
        sort(&imax(&p, &zero)),
        sort(&zero),
        true,
        false,
      ),
      (
        "imax-is-not-max",
        params.clone(),
        sort(&imax(&p, &q)),
        sort(&max(&p, &q)),
        false,
        false,
      ),
      ("unequal-constants", vec![], sort(&zero), sort(&one), false, false),
      (
        "distinct-parameters-with-colliding-caches",
        params.clone(),
        sort(&p),
        sort(&q),
        false,
        false,
      ),
      ("unknown-exact-parameter", vec![], sort(&p), sort(&p), true, true),
      (
        "unknown-semantic-alias",
        vec![],
        sort(&p),
        sort(&max(&p, &zero)),
        false,
        false,
      ),
      (
        "unknown-metavariable",
        params.clone(),
        sort(&Level(Arc::new(LevelData::Mvar(u.clone(), h(0))))),
        sort(&zero),
        false,
        false,
      ),
      (
        "constant-universe-alias",
        vec![],
        cnst(vec![max00.clone()]),
        cnst(vec![zero.clone()]),
        true,
        false,
      ),
      (
        "constant-universe-count",
        params.clone(),
        cnst(vec![p.clone()]),
        cnst(vec![p.clone(), q.clone()]),
        false,
        false,
      ),
      (
        "constant-universe-order",
        params,
        cnst(vec![p.clone(), q.clone()]),
        cnst(vec![q, p]),
        false,
        false,
      ),
      (
        "constant-name-collision",
        vec![],
        cnst(vec![zero.clone()]),
        raw(ExprData::Const(u, vec![zero.clone()], h(0))),
        false,
        false,
      ),
      (
        "paired-metadata",
        vec![],
        raw(ExprData::Mdata(vec![], sort(&max00), h(0))),
        raw(ExprData::Mdata(vec![], sort(&zero), h(0))),
        true,
        false,
      ),
      (
        "one-sided-metadata",
        vec![],
        raw(ExprData::Mdata(vec![], sort(&max00), h(0))),
        sort(&zero),
        false,
        false,
      ),
    ];
    for (label, params, left, right, expected, raw) in controls {
      assert_eq!(motive_eq(&params, &left, &right), expected, "{label}");
      assert_eq!(alpha_eq(&left, &right), raw, "raw alpha: {label}");
    }
  }

  #[test]
  fn alpha_eq_confirms_true_and_false_memo_hits() {
    let mut memo = AlphaMemo::default();
    let a = raw_bvar(0, 1);
    let b = raw_bvar(0, 2);
    assert!(alpha_eq_visit(&a, &b, &mut memo));
    assert_eq!(memo.len(), 1);
    assert!(alpha_eq_visit(&a.clone(), &b.clone(), &mut memo));

    // The successful pair has the same hashes as this unequal pair.
    let c = raw_bvar(1, 1);
    let d = raw_bvar(2, 2);
    assert!(!alpha_eq_visit(&c, &d, &mut memo));
    assert_eq!(memo.len(), 1);
    assert_eq!(memo.get(&(h(1), h(2))), Some(&(c.clone(), d.clone(), false)));
    assert!(!alpha_eq_visit(&c.clone(), &d.clone(), &mut memo));

    // Conversely a cached false result must not reject an equal neighbour.
    assert!(alpha_eq_visit(&a, &b, &mut memo));
    assert_eq!(memo.get(&(h(1), h(2))), Some(&(a, b, true)));
  }

  #[test]
  fn alpha_eq_memo_retains_owners_and_confirms_distinct_allocations() {
    let mut memo = AlphaMemo::default();
    let (original_a, original_b) = {
      let a = raw_bvar(0, 1);
      let b = raw_bvar(0, 2);
      assert!(alpha_eq_visit(&a, &b, &mut memo));
      let (saved_a, saved_b, _) = memo.get(&(h(1), h(2))).unwrap();
      assert!(Arc::ptr_eq(&saved_a.0, &a.0));
      assert!(Arc::ptr_eq(&saved_b.0, &b.0));
      (Arc::downgrade(&a.0), Arc::downgrade(&b.0))
    };
    // The entry keeps the original raw owners alive after the callers leave.
    assert!(original_a.upgrade().is_some());
    assert!(original_b.upgrade().is_some());
    let a = raw_bvar(0, 1);
    let b = raw_bvar(0, 2);
    assert!(!Arc::ptr_eq(&a.0, &original_a.upgrade().unwrap()));
    assert!(!Arc::ptr_eq(&b.0, &original_b.upgrade().unwrap()));
    assert!(alpha_eq_visit(&a, &b, &mut memo));
    let (saved_a, saved_b, _) = memo.get(&(h(1), h(2))).unwrap();
    assert!(Arc::ptr_eq(&saved_a.0, &original_a.upgrade().unwrap()));
    assert!(Arc::ptr_eq(&saved_b.0, &original_b.upgrade().unwrap()));
    memo.clear();
    assert!(original_a.upgrade().is_none());
    assert!(original_b.upgrade().is_none());
  }
}
