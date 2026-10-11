//! The term helpers, declarations and the monad state of the clique
//! transport (a port of `Ix/Compile/Clique/Basic.lean`).
//!
//! Every function mirrors its Lean original: the results are the same terms,
//! binder names and `mdata` included, because the transported constants are
//! compiled to bytes compared with the Lean compiler's. Errors are the Lean
//! texts: some reach the side-car record `_ix.clique` (a fallback's reason).

use rustc_hash::FxHashMap;

use ix_common::env::{
  BinderInfo, ConstantInfo, Expr, ExprData, Level, LevelData, Name, NameData,
};

use crate::compile::pass3::expr::{
  self as px, bvar, get_app_fn_args, lift_loose, lower_loose, nat, nat_usize,
  strip_mdata,
};

pub type Hash = blake3::Hash;
pub type R<T> = Result<T, String>;

// ---------------------------------------------------------------------------
// Causes
// ---------------------------------------------------------------------------

/// `Clique.Cause`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Cause {
  Shape,
  GuessLex,
  NoSpec,
}

impl Cause {
  pub fn tag(self) -> &'static str {
    match self {
      Cause::Shape => "SHAPE",
      Cause::GuessLex => "GUESSLEX",
      Cause::NoSpec => "NOSPEC",
    }
  }
}

// ---------------------------------------------------------------------------
// Declarations
// ---------------------------------------------------------------------------

/// `Clique.Decl`.
#[derive(Clone, Debug)]
pub struct Decl {
  pub name: Name,
  pub level_params: Vec<Name>,
  pub typ: Expr,
  pub value: Expr,
  pub is_thm: bool,
}

impl Decl {
  /// `Decl.ofConstantInfo?`.
  pub fn of_ci(ci: &ConstantInfo) -> Option<Decl> {
    match ci {
      ConstantInfo::DefnInfo(v) => Some(Decl {
        name: v.cnst.name.clone(),
        level_params: v.cnst.level_params.clone(),
        typ: v.cnst.typ.clone(),
        value: v.value.clone(),
        is_thm: false,
      }),
      ConstantInfo::ThmInfo(v) => Some(Decl {
        name: v.cnst.name.clone(),
        level_params: v.cnst.level_params.clone(),
        typ: v.cnst.typ.clone(),
        value: v.value.clone(),
        is_thm: true,
      }),
      ConstantInfo::OpaqueInfo(v) => Some(Decl {
        name: v.cnst.name.clone(),
        level_params: v.cnst.level_params.clone(),
        typ: v.cnst.typ.clone(),
        value: v.value.clone(),
        is_thm: false,
      }),
      _ => None,
    }
  }

  /// `Decl.same`: exact equality (content hashes cover binder names and
  /// `mdata`).
  pub fn same(&self, b: &Decl) -> bool {
    self.name == b.name
      && self.level_params == b.level_params
      && self.is_thm == b.is_thm
      && self.typ == b.typ
      && self.value == b.value
  }

  pub fn with_name(&self, name: Name) -> Decl {
    Decl { name, ..self.clone() }
  }
}

/// The environment lookup the transport reads (`const?`).
pub type ConstOf<'a> = &'a dyn Fn(&Name) -> Option<ConstantInfo>;

// ---------------------------------------------------------------------------
// Names
// ---------------------------------------------------------------------------

pub fn ln(s: &str) -> Name {
  px::dotted(s)
}

pub fn n_psum() -> Name {
  ln("PSum")
}
pub fn n_psum_inl() -> Name {
  ln("PSum.inl")
}
pub fn n_psum_inr() -> Name {
  ln("PSum.inr")
}
pub fn n_psum_cases_on() -> Name {
  ln("PSum.casesOn")
}
pub fn n_psigma() -> Name {
  ln("PSigma")
}
pub fn n_pprod() -> Name {
  ln("PProd")
}
pub fn n_pprod_mk() -> Name {
  ln("PProd.mk")
}
pub fn n_pprod_fst() -> Name {
  ln("PProd.fst")
}
pub fn n_pprod_snd() -> Name {
  ln("PProd.snd")
}
pub fn n_and() -> Name {
  ln("And")
}
pub fn n_and_intro() -> Name {
  ln("And.intro")
}

/// `Ix.Name.mkStr Ix.Name.mkAnon s`.
pub fn root(s: &str) -> Name {
  px::root_name(s)
}

pub fn mk_str(p: &Name, s: &str) -> Name {
  Name::str(p.clone(), s.to_string())
}

/// Lean's `toString` of an `Ix.Name` (`toStringAux`: numeric components as
/// `«n»`), the spelling of `{name}` in Lean's interpolated messages.
pub fn name_to_string(n: &Name) -> String {
  match n.as_data() {
    NameData::Anonymous(_) => String::new(),
    NameData::Str(p, s, _) => match p.as_data() {
      NameData::Anonymous(_) => s.clone(),
      _ => format!("{}.{}", name_to_string(p), s),
    },
    NameData::Num(p, k, _) => match p.as_data() {
      NameData::Anonymous(_) => format!("«{}»", k.0),
      _ => format!("{}.«{}»", name_to_string(p), k.0),
    },
  }
}

/// `Array String` as Lean's `toString` prints it: `#[a, b]`.
pub fn arr_str(xs: &[String]) -> String {
  format!("#[{}]", xs.join(", "))
}

/// `Array Nat` as Lean prints it.
pub fn arr_nat(xs: &[usize]) -> String {
  arr_str(&xs.iter().map(|x| x.to_string()).collect::<Vec<_>>())
}

/// `List String` as Lean's `toString` prints it: `[a, b]`.
pub fn list_str(xs: &[String]) -> String {
  format!("[{}]", xs.join(", "))
}

// ---------------------------------------------------------------------------
// Levels, as Lean's `MetaM` builds them
// ---------------------------------------------------------------------------

pub fn level_is_zero(l: &Level) -> bool {
  matches!(l.as_data(), LevelData::Zero(_))
}

pub fn level_offset(l: &Level) -> usize {
  match l.as_data() {
    LevelData::Succ(u, _) => level_offset(u) + 1,
    _ => 0,
  }
}

pub fn level_base(l: &Level) -> Level {
  match l.as_data() {
    LevelData::Succ(u, _) => level_base(u),
    _ => l.clone(),
  }
}

pub fn level_is_explicit(l: &Level) -> bool {
  level_is_zero(&level_base(l))
}

/// Lean's `mkLevelMax'`.
pub fn mk_level_max_prime(u: &Level, v: &Level) -> Level {
  let subsumes = |u: &Level, v: &Level| -> bool {
    if level_is_explicit(v) && level_offset(u) >= level_offset(v) {
      true
    } else {
      match u.as_data() {
        LevelData::Max(u1, u2, _) => v == u1 || v == u2,
        _ => false,
      }
    }
  };
  if u == v {
    u.clone()
  } else if level_is_zero(u) {
    v.clone()
  } else if level_is_zero(v) {
    u.clone()
  } else if subsumes(u, v) {
    u.clone()
  } else if subsumes(v, u) {
    v.clone()
  } else if level_base(u) == level_base(v) {
    if level_offset(u) >= level_offset(v) { u.clone() } else { v.clone() }
  } else {
    Level::max(u.clone(), v.clone())
  }
}

pub fn lvl_one() -> Level {
  Level::succ(Level::zero())
}

/// `pairLevel`.
pub fn pair_level(u: &Level, v: &Level) -> Level {
  mk_level_max_prime(&mk_level_max_prime(&lvl_one(), u), v)
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

// ---------------------------------------------------------------------------
// Term helpers
// ---------------------------------------------------------------------------

pub fn mk_app_n(f: Expr, args: &[Expr]) -> Expr {
  px::mk_app_n(f, args)
}

pub fn cnst(n: &Name, us: &[Level]) -> Expr {
  Expr::cnst(n.clone(), us.to_vec())
}

pub fn fvar(n: &Name) -> Expr {
  Expr::fvar(n.clone())
}

pub fn proj(s: &Name, i: usize, x: Expr) -> Expr {
  Expr::proj(s.clone(), nat(i), x)
}

pub fn sort0() -> Expr {
  Expr::sort(Level::zero())
}

/// `constApp?`: head constant and arguments (through `mdata` at the head).
pub fn const_app(e: &Expr) -> Option<(Name, Vec<Level>, Vec<Expr>)> {
  let (h, args) = get_app_fn_args(&strip_mdata(e));
  match h.as_data() {
    ExprData::Const(n, us, _) => Some((n.clone(), us.clone(), args)),
    _ => None,
  }
}

pub fn is_app_of_arity(e: &Expr, n: &Name, k: usize) -> bool {
  match const_app(e) {
    Some((m, _, args)) => m == *n && args.len() == k,
    None => false,
  }
}

/// `stripAllMdata`.
pub fn strip_all_mdata(e: &Expr) -> Expr {
  fn visit(e: &Expr, memo: &mut FxHashMap<Hash, Expr>) -> Expr {
    let memo_key = px::key(e);
    if let Some(result) = memo.get(&memo_key) {
      return result.clone();
    }
    let result = {
      match e.as_data() {
        ExprData::Mdata(_, x, _) => visit(x, memo),
        ExprData::App(f, a, _) => Expr::app(visit(f, memo), visit(a, memo)),
        ExprData::Lam(n, t, b, bi, _) => {
          Expr::lam(n.clone(), visit(t, memo), visit(b, memo), bi.clone())
        },
        ExprData::ForallE(n, t, b, bi, _) => {
          Expr::all(n.clone(), visit(t, memo), visit(b, memo), bi.clone())
        },
        ExprData::LetE(n, t, v, b, nd, _) => Expr::letE(
          n.clone(),
          visit(t, memo),
          visit(v, memo),
          visit(b, memo),
          *nd,
        ),
        ExprData::Proj(s, i, x, _) => {
          Expr::proj(s.clone(), i.clone(), visit(x, memo))
        },
        _ => e.clone(),
      }
    };
    memo.insert(memo_key, result.clone());
    result
  }

  visit(e, &mut FxHashMap::default())
}

/// `eqUpTo`: equality up to binder names, binder info and `mdata`, with the
/// constant (and projection structure) names of `b` mapped by `map_b`.
pub fn eq_up_to(map_b: &dyn Fn(&Name) -> Name, a: &Expr, b: &Expr) -> bool {
  match (a.as_data(), b.as_data()) {
    (ExprData::Mdata(_, x, _), _) => eq_up_to(map_b, x, b),
    (_, ExprData::Mdata(_, y, _)) => eq_up_to(map_b, a, y),
    (ExprData::Bvar(i, _), ExprData::Bvar(j, _)) => i == j,
    (ExprData::Fvar(x, _), ExprData::Fvar(y, _)) => x == y,
    (ExprData::Mvar(x, _), ExprData::Mvar(y, _)) => x == y,
    (ExprData::Sort(u, _), ExprData::Sort(v, _)) => u == v,
    (ExprData::Const(x, us, _), ExprData::Const(y, vs, _)) => {
      *x == map_b(y) && us == vs
    },
    (ExprData::App(f, x, _), ExprData::App(g, y, _)) => {
      eq_up_to(map_b, f, g) && eq_up_to(map_b, x, y)
    },
    (ExprData::Lam(_, t, b1, _, _), ExprData::Lam(_, t2, b2, _, _))
    | (ExprData::ForallE(_, t, b1, _, _), ExprData::ForallE(_, t2, b2, _, _)) => {
      eq_up_to(map_b, t, t2) && eq_up_to(map_b, b1, b2)
    },
    (
      ExprData::LetE(_, t, v, b1, _, _),
      ExprData::LetE(_, t2, v2, b2, _, _),
    ) => {
      eq_up_to(map_b, t, t2)
        && eq_up_to(map_b, v, v2)
        && eq_up_to(map_b, b1, b2)
    },
    (ExprData::Lit(x, _), ExprData::Lit(y, _)) => x == y,
    (ExprData::Proj(s, i, x, _), ExprData::Proj(s2, i2, y, _)) => {
      *s == map_b(s2) && i == i2 && eq_up_to(map_b, x, y)
    },
    _ => false,
  }
}

/// `Clique.alphaEq` (`eqUpTo id`): `mdata` is skipped on either side.
pub fn alpha_eq(a: &Expr, b: &Expr) -> bool {
  if a.get_hash() == b.get_hash() {
    return true;
  }
  alpha_eq_go(a, b)
}

fn alpha_eq_go(a: &Expr, b: &Expr) -> bool {
  fn visit(
    a: &Expr,
    b: &Expr,
    memo: &mut FxHashMap<(Hash, Hash), bool>,
  ) -> bool {
    let memo_key = (px::key(a), px::key(b));
    if let Some(result) = memo.get(&memo_key) {
      return *result;
    }
    let result = (|| {
      if a.get_hash() == b.get_hash() {
        return true;
      }
      match (a.as_data(), b.as_data()) {
        (ExprData::Mdata(_, x, _), _) => visit(x, b, memo),
        (_, ExprData::Mdata(_, y, _)) => visit(a, y, memo),
        (ExprData::Bvar(i, _), ExprData::Bvar(j, _)) => i == j,
        (ExprData::Fvar(x, _), ExprData::Fvar(y, _)) => x == y,
        (ExprData::Mvar(x, _), ExprData::Mvar(y, _)) => x == y,
        (ExprData::Sort(u, _), ExprData::Sort(v, _)) => u == v,
        (ExprData::Const(x, us, _), ExprData::Const(y, vs, _)) => {
          x == y && us == vs
        },
        (ExprData::App(f, x, _), ExprData::App(g, y, _)) => {
          visit(f, g, memo) && visit(x, y, memo)
        },
        (ExprData::Lam(_, t, b1, _, _), ExprData::Lam(_, t2, b2, _, _))
        | (
          ExprData::ForallE(_, t, b1, _, _),
          ExprData::ForallE(_, t2, b2, _, _),
        ) => visit(t, t2, memo) && visit(b1, b2, memo),
        (
          ExprData::LetE(_, t, v, b1, _, _),
          ExprData::LetE(_, t2, v2, b2, _, _),
        ) => visit(t, t2, memo) && visit(v, v2, memo) && visit(b1, b2, memo),
        (ExprData::Lit(x, _), ExprData::Lit(y, _)) => x == y,
        (ExprData::Proj(s, i, x, _), ExprData::Proj(s2, i2, y, _)) => {
          s == s2 && i == i2 && visit(x, y, memo)
        },
        _ => false,
      }
    })();
    memo.insert(memo_key, result);
    result
  }

  visit(a, b, &mut FxHashMap::default())
}

/// `substBVar0Same`: loose `bvar 0` of `body` replaced by `t`, which lives
/// in the same context (no variable is lowered).
pub fn subst_bvar0_same(body: &Expr, t: &Expr) -> Expr {
  fn go(
    e: &Expr,
    t: &Expr,
    d: usize,
    memo: &mut FxHashMap<(Hash, usize), Expr>,
  ) -> Expr {
    let memo_key = (px::key(e), d);
    if let Some(result) = memo.get(&memo_key) {
      return result.clone();
    }
    let result = {
      match e.as_data() {
        ExprData::Bvar(i, _) => {
          if nat_usize(i) == d {
            lift_loose(t, d, 0)
          } else {
            e.clone()
          }
        },
        ExprData::App(f, a, _) => {
          Expr::app(go(f, t, d, memo), go(a, t, d, memo))
        },
        ExprData::Lam(n, ty, b, bi, _) => Expr::lam(
          n.clone(),
          go(ty, t, d, memo),
          go(b, t, d + 1, memo),
          bi.clone(),
        ),
        ExprData::ForallE(n, ty, b, bi, _) => Expr::all(
          n.clone(),
          go(ty, t, d, memo),
          go(b, t, d + 1, memo),
          bi.clone(),
        ),
        ExprData::LetE(n, ty, v, b, nd, _) => Expr::letE(
          n.clone(),
          go(ty, t, d, memo),
          go(v, t, d, memo),
          go(b, t, d + 1, memo),
          *nd,
        ),
        ExprData::Proj(s, i, x, _) => {
          Expr::proj(s.clone(), i.clone(), go(x, t, d, memo))
        },
        ExprData::Mdata(m, x, _) => Expr::mdata(m.clone(), go(x, t, d, memo)),
        _ => e.clone(),
      }
    };
    memo.insert(memo_key, result.clone());
    result
  }
  go(body, t, 0, &mut FxHashMap::default())
}

/// `Canon.looseAtLeast`: every loose bound variable is `>= k`.
pub fn loose_all_at_least(e: &Expr, d: usize) -> bool {
  fn go(
    e: &Expr,
    k: usize,
    d: usize,
    memo: &mut FxHashMap<(Hash, usize), bool>,
  ) -> bool {
    let memo_key = (px::key(e), k);
    if let Some(result) = memo.get(&memo_key) {
      return *result;
    }
    let result = {
      match e.as_data() {
        ExprData::Bvar(i, _) => {
          let i = nat_usize(i);
          i < k || i - k >= d
        },
        ExprData::App(f, a, _) => go(f, k, d, memo) && go(a, k, d, memo),
        ExprData::Lam(_, t, b, _, _) | ExprData::ForallE(_, t, b, _, _) => {
          go(t, k, d, memo) && go(b, k + 1, d, memo)
        },
        ExprData::LetE(_, t, v, b, _, _) => {
          go(t, k, d, memo) && go(v, k, d, memo) && go(b, k + 1, d, memo)
        },
        ExprData::Proj(_, _, s, _) | ExprData::Mdata(_, s, _) => {
          go(s, k, d, memo)
        },
        _ => true,
      }
    };
    memo.insert(memo_key, result);
    result
  }
  go(e, 0, d, &mut FxHashMap::default())
}

/// `lower?`.
pub fn lower_opt(e: &Expr, k: usize) -> Option<Expr> {
  if loose_all_at_least(e, k) { Some(lower_loose(e, k, 0)) } else { None }
}

pub fn lift(e: &Expr, n: usize) -> Expr {
  lift_loose(e, n, 0)
}

pub type Binder = (Name, Expr, BinderInfo);

/// `peelLams`: peel `n` leading `λ`s (through `mdata`).
pub fn peel_lams(n: usize, e: &Expr) -> (Vec<Binder>, Expr) {
  let mut acc = Vec::new();
  let mut cur = e.clone();
  for _ in 0..n {
    let s = strip_mdata(&cur);
    match s.as_data() {
      ExprData::Lam(nm, t, b, bi, _) => {
        acc.push((nm.clone(), t.clone(), bi.clone()));
        cur = b.clone();
      },
      _ => return (acc, s),
    }
  }
  (acc, cur)
}

/// `Canon.peelForalls`.
pub fn peel_foralls(n: usize, e: &Expr) -> (Vec<Binder>, Expr) {
  px::peel_foralls(n, e)
}

pub fn mk_lams(bs: &[Binder], body: Expr) -> Expr {
  bs.iter().rev().fold(body, |acc, (nm, t, bi)| {
    Expr::lam(nm.clone(), t.clone(), acc, bi.clone())
  })
}

pub fn mk_foralls(bs: &[Binder], body: Expr) -> Expr {
  bs.iter().rev().fold(body, |acc, (nm, t, bi)| {
    Expr::all(nm.clone(), t.clone(), acc, bi.clone())
  })
}

pub fn lam_arity(e: &Expr) -> usize {
  match e.as_data() {
    ExprData::Lam(_, _, b, _, _) => lam_arity(b) + 1,
    ExprData::Mdata(_, x, _) => lam_arity(x),
    _ => 0,
  }
}

pub fn forall_arity(e: &Expr) -> usize {
  px::forall_arity(e)
}

/// `constOccurrences`: pre-order first occurrences (a tree walk, as Lean's).
pub fn const_occurrences(p: &dyn Fn(&Name) -> bool, e: &Expr) -> Vec<Name> {
  fn go(
    e: &Expr,
    p: &dyn Fn(&Name) -> bool,
    acc: &mut Vec<Name>,
    seen: &mut rustc_hash::FxHashSet<Name>,
    nodes: &mut rustc_hash::FxHashSet<Hash>,
  ) {
    if !nodes.insert(px::key(e)) {
      return;
    }

    match e.as_data() {
      ExprData::Const(n, _, _) => {
        if p(n) && seen.insert(n.clone()) {
          acc.push(n.clone());
        }
      },
      ExprData::App(f, a, _) => {
        go(f, p, acc, seen, nodes);
        go(a, p, acc, seen, nodes);
      },
      ExprData::Lam(_, t, b, _, _) | ExprData::ForallE(_, t, b, _, _) => {
        go(t, p, acc, seen, nodes);
        go(b, p, acc, seen, nodes);
      },
      ExprData::LetE(_, t, v, b, _, _) => {
        go(t, p, acc, seen, nodes);
        go(v, p, acc, seen, nodes);
        go(b, p, acc, seen, nodes);
      },
      ExprData::Proj(_, _, x, _) | ExprData::Mdata(_, x, _) => {
        go(x, p, acc, seen, nodes)
      },
      _ => {},
    }
  }
  let mut acc = Vec::new();
  let mut seen = rustc_hash::FxHashSet::default();
  go(e, p, &mut acc, &mut seen, &mut rustc_hash::FxHashSet::default());
  acc
}

/// `renameConsts` (projection structure names are left alone).
pub fn rename_consts(m: &dyn Fn(&Name) -> Option<Name>, e: &Expr) -> Expr {
  fn visit(
    m: &dyn Fn(&Name) -> Option<Name>,
    e: &Expr,
    memo: &mut FxHashMap<Hash, Expr>,
  ) -> Expr {
    let memo_key = px::key(e);
    if let Some(result) = memo.get(&memo_key) {
      return result.clone();
    }
    let result = {
      match e.as_data() {
        ExprData::Const(n, us, _) => match m(n) {
          Some(n2) => Expr::cnst(n2, us.clone()),
          None => e.clone(),
        },
        ExprData::App(f, a, _) => {
          Expr::app(visit(m, f, memo), visit(m, a, memo))
        },
        ExprData::Lam(n, t, b, bi, _) => {
          Expr::lam(n.clone(), visit(m, t, memo), visit(m, b, memo), bi.clone())
        },
        ExprData::ForallE(n, t, b, bi, _) => {
          Expr::all(n.clone(), visit(m, t, memo), visit(m, b, memo), bi.clone())
        },
        ExprData::LetE(n, t, v, b, nd, _) => Expr::letE(
          n.clone(),
          visit(m, t, memo),
          visit(m, v, memo),
          visit(m, b, memo),
          *nd,
        ),
        ExprData::Proj(s, i, x, _) => {
          Expr::proj(s.clone(), i.clone(), visit(m, x, memo))
        },
        ExprData::Mdata(d, x, _) => Expr::mdata(d.clone(), visit(m, x, memo)),
        _ => e.clone(),
      }
    };
    memo.insert(memo_key, result.clone());
    result
  }

  visit(m, e, &mut FxHashMap::default())
}

/// `mentions`.
pub fn mentions(n: &Name, e: &Expr) -> bool {
  fn visit(n: &Name, e: &Expr, memo: &mut FxHashMap<Hash, bool>) -> bool {
    let memo_key = px::key(e);
    if let Some(result) = memo.get(&memo_key) {
      return *result;
    }
    let result = {
      match e.as_data() {
        ExprData::Const(m, _, _) => m == n,
        ExprData::App(f, a, _) => visit(n, f, memo) || visit(n, a, memo),
        ExprData::Lam(_, t, b, _, _) | ExprData::ForallE(_, t, b, _, _) => {
          visit(n, t, memo) || visit(n, b, memo)
        },
        ExprData::LetE(_, t, v, b, _, _) => {
          visit(n, t, memo) || visit(n, v, memo) || visit(n, b, memo)
        },
        ExprData::Proj(_, _, x, _) | ExprData::Mdata(_, x, _) => {
          visit(n, x, memo)
        },
        _ => false,
      }
    };
    memo.insert(memo_key, result);
    result
  }

  visit(n, e, &mut FxHashMap::default())
}

/// `mentionsFVar`.
pub fn mentions_fvar(x: &Name, e: &Expr) -> bool {
  fn visit(x: &Name, e: &Expr, memo: &mut FxHashMap<Hash, bool>) -> bool {
    let memo_key = px::key(e);
    if let Some(result) = memo.get(&memo_key) {
      return *result;
    }
    let result = {
      match e.as_data() {
        ExprData::Fvar(y, _) => x == y,
        ExprData::App(f, a, _) => visit(x, f, memo) || visit(x, a, memo),
        ExprData::Lam(_, t, b, _, _) | ExprData::ForallE(_, t, b, _, _) => {
          visit(x, t, memo) || visit(x, b, memo)
        },
        ExprData::LetE(_, t, v, b, _, _) => {
          visit(x, t, memo) || visit(x, v, memo) || visit(x, b, memo)
        },
        ExprData::Proj(_, _, e, _) | ExprData::Mdata(_, e, _) => {
          visit(x, e, memo)
        },
        _ => false,
      }
    };
    memo.insert(memo_key, result);
    result
  }

  visit(x, e, &mut FxHashMap::default())
}

pub fn is_bvar(e: &Expr, i: usize) -> bool {
  matches!(e.as_data(), ExprData::Bvar(j, _) if nat_usize(j) == i)
}

pub fn bvar_idx(e: &Expr) -> Option<usize> {
  match e.as_data() {
    ExprData::Bvar(j, _) => Some(nat_usize(j)),
    _ => None,
  }
}

pub fn mk_bvar(i: usize) -> Expr {
  bvar(i)
}

// ---------------------------------------------------------------------------
// Permutations
// ---------------------------------------------------------------------------

pub fn is_perm(s: &[usize]) -> bool {
  let n = s.len();
  (0..n).all(|p| s.iter().filter(|&&x| x == p).count() == 1)
}

/// `invPerm`: `inv[p]` = Lean index at canonical position `p`.
pub fn inv_perm(s: &[usize]) -> Vec<usize> {
  (0..s.len()).map(|p| s.iter().position(|&x| x == p).unwrap_or(p)).collect()
}

/// `permute`: reorder `xs` (by Lean index) into canonical order.
pub fn permute<T: Clone>(s: &[usize], xs: &[T]) -> Vec<T> {
  inv_perm(s).into_iter().map(|i| xs[i].clone()).collect()
}

pub fn id_perm(m: usize) -> Vec<usize> {
  (0..m).collect()
}

/// `reorder`: new position `p` holds `xs[perm[p]]`.
pub fn reorder<T: Clone>(perm: &[usize], xs: &[T]) -> Vec<T> {
  perm.iter().map(|&i| xs[i].clone()).collect()
}

/// Lean's `qsort` on the identity with a key comparison `lt`: the same
/// result as any sort when the keys are distinct (fixed-parameter positions
/// are distinct, checked before every use).
pub fn sort_idx_by_key(m: usize, key: &dyn Fn(usize) -> usize) -> Vec<usize> {
  let mut v: Vec<usize> = (0..m).collect();
  v.sort_by_key(|&a| key(a));
  v
}

pub fn eq_sorted(xs: &[usize]) -> bool {
  xs.windows(2).all(|w| w[0] <= w[1])
}

pub fn no_dups(xs: &[usize]) -> bool {
  let mut v = xs.to_vec();
  v.sort_unstable();
  v.dedup();
  v.len() == xs.len()
}

// ---------------------------------------------------------------------------
// The transport monad's state
// ---------------------------------------------------------------------------

/// The key of the structural memo (`TState.cacheOwn`): the term, the
/// context (each binder type with its ownership) and the ownership mode
/// (`StructLayout::check_ownership`). Lean keys by a 64-bit mix of the
/// hashes and the mode and checks all three on a hit; this keys by the full
/// content.
pub type OwnKey = (Hash, Hash, bool);

/// `TState`.
#[derive(Default)]
pub struct Tm {
  pub next: usize,
  pub log: Vec<String>,
  pub fallbacks: Vec<String>,
  pub cache_own: FxHashMap<OwnKey, Expr>,
}

pub fn fvar_root() -> Name {
  root("_clq_fvar")
}

impl Tm {
  pub fn fresh(&mut self) -> Name {
    let n = Name::num(fvar_root(), nat(self.next));
    self.next += 1;
    n
  }
  pub fn trace(&mut self, s: String) {
    self.log.push(s);
  }
}

/// `defaultFuel`.
pub const DEFAULT_FUEL: usize = 1_000_000;

/// An opened binder (`Image.Local`).
pub use crate::compile::pass3::expr::Local;

pub fn local(fvar: Name, user_name: Name, typ: Expr, bi: BinderInfo) -> Local {
  Local { fvar, user_name, typ, bi }
}

pub fn inst_locals(e: &Expr, xs: &[Expr]) -> Expr {
  px::inst_locals(e, xs)
}

pub fn abstract_fvars(xs: &[Name], e: &Expr) -> Expr {
  px::abstract_fvars(xs, e)
}

pub fn mk_lambda(xs: &[Local], b: &Expr) -> Expr {
  px::mk_lambda(xs, b)
}

pub fn mk_forall(xs: &[Local], b: &Expr) -> Expr {
  px::mk_forall(xs, b)
}

pub fn instantiate_rev(b: &Expr, args: &[Expr]) -> Expr {
  px::instantiate_rev(b, args)
}

pub fn exprs(ls: &[Local]) -> Vec<Expr> {
  px::exprs(ls)
}

/// `Array.extract` (clamped).
pub fn extract<T: Clone>(xs: &[T], a: usize, b: usize) -> Vec<T> {
  let b = b.min(xs.len());
  if a >= b { Vec::new() } else { xs[a..b].to_vec() }
}

pub fn nm_default() -> BinderInfo {
  BinderInfo::Default
}
