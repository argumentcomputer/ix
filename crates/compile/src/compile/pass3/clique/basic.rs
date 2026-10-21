//! The declarations, names, level and term helpers and the state of the
//! clique transport (a port of `Ix/Compile/Pass/Clique/Basic.lean`, and of
//! the walks over distinct subterms of `Dag.lean`).
//!
//! Every function mirrors its Lean original: the results are the same terms,
//! binder names and `mdata` included, because the transported constants are
//! compiled to bytes compared with the Lean compiler's. Errors are the Lean
//! texts.
//!
//! `Dag.lean`'s de Bruijn and locally nameless helpers (`liftLoose`,
//! `lowerLoose`, `instantiateRev`, `instLocals`, `abstractFVars`,
//! `mkLambda`, `mkForall`) are [`crate::compile::pass3::expr`]'s, re-exported
//! here with the other shared helpers the transport uses. Its one
//! visited-set walk, `foldDistinct`, is [`fold_distinct`]: the constant fold
//! [`fold_consts`] and [`mentions_fvar`] are folds over it.
//!
//! Everything here is total: an index out of range is a refusal
//! ([`tm_idx`], or `None`), never a default value. Where a Lean memo or
//! visited set is keyed by an expression's hash (run-local key faithfulness,
//! see `Dag.lean`), the Rust one is an [`ExactMemo`], which confirms a hit by
//! raw equality; the results agree whenever that premise holds.

use std::ops::ControlFlow;

use rustc_hash::{FxHashMap, FxHashSet};

use ix_common::env::{
  ConstantInfo, Expr, ExprData, Level, LevelData, Name, NameComponent,
};

use crate::compile::pass3::expr::{
  ExactMemo, get_app_fn_args, key, nat, nat_usize, strip_mdata,
};

pub use crate::compile::pass3::expr::{
  Binder, Hash, Local, abstract_fvars, bvar, dotted, exprs, forall_arity,
  inst_locals, instantiate_rev, is_always_zero, lift_loose, lower_loose,
  lvl_one, mk_app_n, mk_forall, mk_lambda, peel_foralls,
};
pub use crate::compile::pass3::names::{
  mk_str, n_and, n_and_intro, n_pprod, n_pprod_mk, root_name,
};

/// The transport's `Except String`: an error is a grammar failure (or an
/// exhausted bound), which the caller turns into the faithful fallback.
pub type R<T> = Result<T, String>;

// ---------------------------------------------------------------------------
// Causes
// ---------------------------------------------------------------------------

/// The non-canonical causes the transport itself can decide (`Cause`). The
/// test fixture `Tests.Ix.Compile.NonCanonical` has the full enum (with the
/// measurement-only `pending*` causes); [`Cause::tag`] agrees with it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Cause {
  /// The grammar check failed; the fallback carries Lean's packing.
  Shape,
  /// GuessLex picked a different measure in another presentation (decided
  /// by the caller, who sees both presentations; the transport never
  /// reports it on its own).
  GuessLex,
  /// A theorem clique without a specification whose order could not be
  /// determined.
  NoSpec,
}

impl Cause {
  /// `Cause.tag`.
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

/// A definition or theorem of a clique's encoding (`Decl`; the transport
/// neither needs nor produces other kinds).
#[derive(Clone, Debug)]
pub struct Decl {
  pub name: Name,
  pub level_params: Vec<Name>,
  pub typ: Expr,
  pub value: Expr,
  pub is_thm: bool,
}

impl Decl {
  /// `Decl.ofConstantInfo?`: definitions, theorems and opaques.
  pub fn of_constant_info(ci: &ConstantInfo) -> Option<Decl> {
    let (cnst, value, is_thm) = match ci {
      ConstantInfo::DefnInfo(v) => (&v.cnst, &v.value, false),
      ConstantInfo::ThmInfo(v) => (&v.cnst, &v.value, true),
      ConstantInfo::OpaqueInfo(v) => (&v.cnst, &v.value, false),
      _ => return None,
    };
    Some(Decl {
      name: cnst.name.clone(),
      level_params: cnst.level_params.clone(),
      typ: cnst.typ.clone(),
      value: value.clone(),
      is_thm,
    })
  }
}

/// The environment lookup the transport reads (Lean's `const?`).
pub type ConstOf<'a> = &'a dyn Fn(&Name) -> Option<ConstantInfo>;

// ---------------------------------------------------------------------------
// Names of the constants the encodings use
// ---------------------------------------------------------------------------
//
// The `PProd`/`And` names are the shared table's (`pass3::names`, Lean's
// `Ix.Compile.LibraryNames`), re-exported above; the sums are the
// transport's own.

pub fn n_psum() -> Name {
  dotted("PSum")
}
pub fn n_psum_inl() -> Name {
  dotted("PSum.inl")
}
pub fn n_psum_inr() -> Name {
  dotted("PSum.inr")
}
pub fn n_psum_cases_on() -> Name {
  dotted("PSum.casesOn")
}
pub fn n_psigma() -> Name {
  dotted("PSigma")
}
/// `LibraryNames.nPProdFst` (not in `pass3::names`, which has only the
/// names the image generator builds with).
pub fn n_pprod_fst() -> Name {
  mk_str(&n_pprod(), "fst")
}
/// `LibraryNames.nPProdSnd`.
pub fn n_pprod_snd() -> Name {
  mk_str(&n_pprod(), "snd")
}

// ---------------------------------------------------------------------------
// Lean's spelling of values in messages
// ---------------------------------------------------------------------------

/// Lean's `toString` of an `Ix.Name` (`toStringAux`: numeric components as
/// `«n»`), the spelling of `{name}` in Lean's interpolated messages.
pub fn name_to_string(n: &Name) -> String {
  let parts: Vec<String> = n
    .components()
    .into_iter()
    .map(|c| match c {
      NameComponent::Str(s) => s,
      NameComponent::Num(k) => format!("«{}»", k.0),
    })
    .collect();
  parts.join(".")
}

/// `Array String` as Lean's `toString` prints it: `#[a, b]`.
pub fn arr_str(xs: &[String]) -> String {
  format!("#[{}]", xs.join(", "))
}

/// `Array Nat` as Lean's `toString` prints it.
pub fn arr_nat(xs: &[usize]) -> String {
  arr_str(&xs.iter().map(ToString::to_string).collect::<Vec<_>>())
}

/// `List String` as Lean's `toString` prints it: `[a, b]`.
pub fn list_str(xs: &[String]) -> String {
  format!("[{}]", xs.join(", "))
}

// ---------------------------------------------------------------------------
// Universe levels, as Lean's `MetaM` builds them
// ---------------------------------------------------------------------------

/// `Level.isZero`.
pub fn level_is_zero(l: &Level) -> bool {
  matches!(l.as_data(), LevelData::Zero(_))
}

/// `succⁿ u ↦ n` (`Lean.Level.getOffset`).
pub fn level_offset(l: &Level) -> usize {
  let mut n = 0;
  let mut cur = l;
  while let LevelData::Succ(u, _) = cur.as_data() {
    n += 1;
    cur = u;
  }
  n
}

/// `succⁿ u ↦ u` (`Lean.Level.getLevelOffset`).
pub fn level_base(l: &Level) -> Level {
  let mut cur = l;
  while let LevelData::Succ(u, _) = cur.as_data() {
    cur = u;
  }
  cur.clone()
}

/// `succⁿ zero` (`Lean.Level.isExplicit`).
pub fn level_is_explicit(l: &Level) -> bool {
  level_is_zero(&level_base(l))
}

/// Lean's `mkLevelMax'` (`mkLevelMaxCore`): the simplifying `max` that
/// `instantiateLevelParams` uses, hence the one behind every level
/// `getLevel` returns for an instantiated `Sort (max (max 1 u) v)`.
pub fn mk_level_max_prime(u: &Level, v: &Level) -> Level {
  let subsumes = |u: &Level, v: &Level| -> bool {
    if level_is_explicit(v) && level_offset(u) >= level_offset(v) {
      return true;
    }
    match u.as_data() {
      LevelData::Max(u1, u2, _) => v == u1 || v == u2,
      _ => false,
    }
  };
  if u == v {
    u.clone()
  } else if level_is_zero(u) {
    v.clone()
  } else if level_is_zero(v) || subsumes(u, v) {
    u.clone()
  } else if subsumes(v, u) {
    v.clone()
  } else if level_base(u) == level_base(v) {
    if level_offset(u) >= level_offset(v) { u.clone() } else { v.clone() }
  } else {
    Level::max(u.clone(), v.clone())
  }
}

/// The level of `PSum α β`, `PProd α β` or `PSigma β` at `α : Sort u`,
/// `β : Sort v` (`pairLevel`): their declared sort `Sort (max (max 1 u) v)`
/// instantiated as `getLevel` instantiates it.
pub fn pair_level(u: &Level, v: &Level) -> Level {
  mk_level_max_prime(&mk_level_max_prime(&lvl_one(), u), v)
}

// ---------------------------------------------------------------------------
// Term helpers
// ---------------------------------------------------------------------------

/// `Expr.mkConst n us`.
pub fn cnst(n: &Name, us: &[Level]) -> Expr {
  Expr::cnst(n.clone(), us.to_vec())
}

/// `Expr.mkFVar n`.
pub fn fvar(n: &Name) -> Expr {
  Expr::fvar(n.clone())
}

/// `Expr.mkProj s i x`.
pub fn proj(s: &Name, i: usize, x: Expr) -> Expr {
  Expr::proj(s.clone(), nat(i), x)
}

/// `Sort 0`.
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

/// `isAppOfArity`: `e` is an application of the constant `n` to exactly `k`
/// arguments.
pub fn is_app_of_arity(e: &Expr, n: &Name, k: usize) -> bool {
  match const_app(e) {
    Some((m, _, args)) => m == *n && args.len() == k,
    None => false,
  }
}

/// `stripAllMdata`: strip `mdata` everywhere (memoised by the subterm:
/// proofs are shared DAGs).
pub fn strip_all_mdata(e: &Expr) -> Expr {
  fn go(e: &Expr, memo: &mut ExactMemo<(), Expr>) -> Expr {
    if let ExprData::Mdata(_, x, _) = e.as_data() {
      return go(x, memo);
    }
    if let Some(r) = memo.get(e, ()) {
      return r;
    }
    let r = match e.as_data() {
      ExprData::App(f, a, _) => Expr::app(go(f, memo), go(a, memo)),
      ExprData::Lam(n, t, b, bi, _) => {
        Expr::lam(n.clone(), go(t, memo), go(b, memo), bi.clone())
      },
      ExprData::ForallE(n, t, b, bi, _) => {
        Expr::all(n.clone(), go(t, memo), go(b, memo), bi.clone())
      },
      ExprData::LetE(n, t, v, b, nd, _) => {
        Expr::letE(n.clone(), go(t, memo), go(v, memo), go(b, memo), *nd)
      },
      ExprData::Proj(s, i, x, _) => {
        Expr::proj(s.clone(), i.clone(), go(x, memo))
      },
      _ => return e.clone(),
    };
    memo.insert(e, (), r.clone());
    r
  }
  go(e, &mut ExactMemo::default())
}

/// The clique transport's term comparison (`alphaEqSkipMdata`): equality
/// up to binder names, binder info, let flags and `mdata`, walking distinct
/// pairs of subterms.
///
/// It differs from the image generator's
/// [`alpha_eq`](crate::compile::pass3::expr::alpha_eq) (Lean's
/// `Image.alphaEq`) in three ways: `mdata` is skipped on
/// **either** side (`alpha_eq` only pairs an `mdata` node with an `mdata`
/// node); names and levels are compared by their stored hashes (the `BEq`
/// instances of `Ix.Name` and `Ix.Level`), not by raw equality; and two
/// subterms with equal hashes are equal at once (the hash shortcut), as are
/// pairs already visited, where `alpha_eq` lets no hash decide (it confirms
/// every fast return and memo hit by raw equality). The shortcut and the
/// visited hits rely on run-local expression-key faithfulness (equal keys
/// denote the same full expression), independently of constructor
/// consistency; this is an implementation premise, not a theorem. The first
/// differing pair ends the walk.
pub fn alpha_eq_skip_mdata(a: &Expr, b: &Expr) -> bool {
  fn levels_eq(us: &[Level], vs: &[Level]) -> bool {
    us.len() == vs.len()
      && us.iter().zip(vs).all(|(u, v)| u.get_hash() == v.get_hash())
  }
  fn go(a: &Expr, b: &Expr, seen: &mut FxHashSet<(Hash, Hash)>) -> bool {
    let pair = (key(a), key(b));
    if pair.0 == pair.1 || !seen.insert(pair) {
      return true;
    }
    match (a.as_data(), b.as_data()) {
      (ExprData::Mdata(_, x, _), _) => go(x, b, seen),
      (_, ExprData::Mdata(_, y, _)) => go(a, y, seen),
      (ExprData::Bvar(i, _), ExprData::Bvar(j, _)) => i == j,
      (ExprData::Fvar(x, _), ExprData::Fvar(y, _))
      | (ExprData::Mvar(x, _), ExprData::Mvar(y, _)) => {
        x.get_hash() == y.get_hash()
      },
      (ExprData::Sort(u, _), ExprData::Sort(v, _)) => {
        u.get_hash() == v.get_hash()
      },
      (ExprData::Const(x, us, _), ExprData::Const(y, vs, _)) => {
        x.get_hash() == y.get_hash() && levels_eq(us, vs)
      },
      (ExprData::App(f, x, _), ExprData::App(g, y, _)) => {
        go(f, g, seen) && go(x, y, seen)
      },
      (ExprData::Lam(_, t, x, _, _), ExprData::Lam(_, t2, y, _, _))
      | (ExprData::ForallE(_, t, x, _, _), ExprData::ForallE(_, t2, y, _, _)) => {
        go(t, t2, seen) && go(x, y, seen)
      },
      (
        ExprData::LetE(_, t, v, x, _, _),
        ExprData::LetE(_, t2, v2, y, _, _),
      ) => go(t, t2, seen) && go(v, v2, seen) && go(x, y, seen),
      (ExprData::Lit(x, _), ExprData::Lit(y, _)) => x == y,
      (ExprData::Proj(s, i, x, _), ExprData::Proj(s2, i2, y, _)) => {
        s.get_hash() == s2.get_hash() && i == i2 && go(x, y, seen)
      },
      _ => false,
    }
  }
  go(a, b, &mut FxHashSet::default())
}

/// `substBVar0Same`: replace loose `bvar 0` of `body` by `t`, where `t`
/// lives in the same context as `body` (so its own `bvar 0` is the same
/// binder): no variable is lowered. Used to instantiate a motive `λ x. M` at
/// `pre(z)` under a new binder `z`.
pub fn subst_bvar0_same(body: &Expr, t: &Expr) -> Expr {
  fn go(
    e: &Expr,
    t: &Expr,
    d: usize,
    memo: &mut ExactMemo<usize, Expr>,
  ) -> Expr {
    if let Some(r) = memo.get(e, d) {
      return r;
    }
    let r = match e.as_data() {
      ExprData::Bvar(i, _) => {
        if nat_usize(i) == d {
          lift_loose(t, d, 0)
        } else {
          e.clone()
        }
      },
      ExprData::App(f, a, _) => Expr::app(go(f, t, d, memo), go(a, t, d, memo)),
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
      _ => return e.clone(),
    };
    memo.insert(e, d, r.clone());
    r
  }
  go(body, t, 0, &mut ExactMemo::default())
}

/// `looseAllAtLeast` (`Dag.looseAtLeast`): every loose bound variable of `e`
/// is `>= k` (so `e` can be lowered by `k`).
pub fn loose_all_at_least(e: &Expr, k: usize) -> bool {
  fn go(
    e: &Expr,
    d: usize,
    k: usize,
    memo: &mut ExactMemo<usize, bool>,
  ) -> bool {
    if let Some(r) = memo.get(e, d) {
      return r;
    }
    let r = match e.as_data() {
      ExprData::Bvar(i, _) => {
        let i = nat_usize(i);
        i < d || i - d >= k
      },
      ExprData::App(f, a, _) => go(f, d, k, memo) && go(a, d, k, memo),
      ExprData::Lam(_, t, b, _, _) | ExprData::ForallE(_, t, b, _, _) => {
        go(t, d, k, memo) && go(b, d + 1, k, memo)
      },
      ExprData::LetE(_, t, v, b, _, _) => {
        go(t, d, k, memo) && go(v, d, k, memo) && go(b, d + 1, k, memo)
      },
      ExprData::Proj(_, _, s, _) | ExprData::Mdata(_, s, _) => {
        go(s, d, k, memo)
      },
      _ => return true,
    };
    memo.insert(e, d, r);
    r
  }
  go(e, 0, k, &mut ExactMemo::default())
}

/// `lower?`: lower `e` by `k` when it does not mention the `k` innermost
/// binders.
pub fn lower_opt(e: &Expr, k: usize) -> Option<Expr> {
  if loose_all_at_least(e, k) { Some(lower_loose(e, k, 0)) } else { None }
}

/// `peelLams`: peel up to `n` leading `λ`s (through `mdata`), keeping the
/// binders; on fewer, the rest with its `mdata` stripped.
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

/// `mkLams`: `λ bs, body`, binders outermost first.
pub fn mk_lams(bs: &[Binder], body: Expr) -> Expr {
  bs.iter().rev().fold(body, |acc, (nm, t, bi)| {
    Expr::lam(nm.clone(), t.clone(), acc, bi.clone())
  })
}

/// `Canon.mkForalls`: `∀ bs, body`, binders outermost first (not in
/// [`crate::compile::pass3::expr`]).
pub fn mk_foralls(bs: &[Binder], body: Expr) -> Expr {
  bs.iter().rev().fold(body, |acc, (nm, t, bi)| {
    Expr::all(nm.clone(), t.clone(), acc, bi.clone())
  })
}

/// `lamArity`: the number of leading `λ`s (through `mdata`).
pub fn lam_arity(e: &Expr) -> usize {
  let mut n = 0;
  let mut cur = e;
  loop {
    match cur.as_data() {
      ExprData::Lam(_, _, b, _, _) => {
        n += 1;
        cur = b;
      },
      ExprData::Mdata(_, x, _) => cur = x,
      _ => return n,
    }
  }
}

/// `e` is `bvar i`.
pub fn is_bvar(e: &Expr, i: usize) -> bool {
  matches!(e.as_data(), ExprData::Bvar(j, _) if nat_usize(j) == i)
}

/// The index of `e` when it is a bound variable.
pub fn bvar_idx(e: &Expr) -> Option<usize> {
  match e.as_data() {
    ExprData::Bvar(j, _) => Some(nat_usize(j)),
    _ => None,
  }
}

// ---------------------------------------------------------------------------
// Walks over distinct subterms
// ---------------------------------------------------------------------------

/// `Dag.foldDistinct`: fold `visit` over the distinct subterms of `e`. Each
/// distinct subterm is visited once, before its children, in
/// first-occurrence pre-order with the function before the argument (binder
/// domain before body; `let` type, value, body), the order of Lean's
/// `Expr.getUsedConstants`. A subterm met again is skipped with everything
/// below it. `visit` returning [`ControlFlow::Break`] ends the walk with
/// that value.
pub fn fold_distinct<S>(
  e: &Expr,
  init: S,
  mut visit: impl FnMut(S, &Expr) -> ControlFlow<S, S>,
) -> S {
  let mut acc = init;
  let mut seen: ExactMemo<(), ()> = ExactMemo::default();
  // An explicit stack, children pushed in reverse: the same order as the
  // recursive pre-order walk, since a subtree is finished before its right
  // sibling is popped.
  let mut stack = vec![e];
  while let Some(x) = stack.pop() {
    if seen.get(x, ()).is_some() {
      continue;
    }
    seen.insert(x, (), ());
    acc = match visit(acc, x) {
      ControlFlow::Break(b) => return b,
      ControlFlow::Continue(b) => b,
    };
    match x.as_data() {
      ExprData::App(f, a, _) => stack.extend([a, f]),
      ExprData::Lam(_, t, b, _, _) | ExprData::ForallE(_, t, b, _, _) => {
        stack.extend([b, t])
      },
      ExprData::LetE(_, t, v, b, _, _) => stack.extend([b, v, t]),
      ExprData::Proj(_, _, s, _) | ExprData::Mdata(_, s, _) => stack.push(s),
      _ => {},
    }
  }
  acc
}

/// `foldConsts`: fold `f` over the constants of `e`, each distinct constant
/// name once, at its first occurrence in [`fold_distinct`]'s order.
/// Projection structure names are not constants here. `f` returning
/// [`ControlFlow::Break`] ends the walk with that value.
pub fn fold_consts<S>(
  e: &Expr,
  init: S,
  mut f: impl FnMut(S, &Name) -> ControlFlow<S, S>,
) -> S {
  let mut names: FxHashSet<Name> = FxHashSet::default();
  fold_distinct(e, init, |acc, x| match x.as_data() {
    ExprData::Const(n, _, _) if !names.contains(n) => {
      let step = f(acc, n);
      if step.is_continue() {
        names.insert(n.clone());
      }
      step
    },
    _ => ControlFlow::Continue(acc),
  })
}

/// `constOccurrences`: the constants satisfying `p`, each once, in
/// first-occurrence pre-order.
pub fn const_occurrences(p: &dyn Fn(&Name) -> bool, e: &Expr) -> Vec<Name> {
  fold_consts(e, Vec::new(), |mut out, n| {
    if p(n) {
      out.push(n.clone());
    }
    ControlFlow::Continue(out)
  })
}

/// `mentions`: `e` mentions the constant `n`.
pub fn mentions(n: &Name, e: &Expr) -> bool {
  fold_consts(e, false, |_, m| {
    if n == m { ControlFlow::Break(true) } else { ControlFlow::Continue(false) }
  })
}

/// `Dag.mentionsFVar`: `e` mentions the free variable `x`.
pub fn mentions_fvar(x: &Name, e: &Expr) -> bool {
  fold_distinct(e, false, |_, y| match y.as_data() {
    ExprData::Fvar(z, _) if x == z => ControlFlow::Break(true),
    _ => ControlFlow::Continue(false),
  })
}

/// `renameConsts`: rename constants (projection structure names are left
/// alone), caching only within this call, where the renaming is fixed.
pub fn rename_consts(m: &dyn Fn(&Name) -> Option<Name>, e: &Expr) -> Expr {
  fn go(
    m: &dyn Fn(&Name) -> Option<Name>,
    e: &Expr,
    memo: &mut ExactMemo<(), Expr>,
  ) -> Expr {
    if let ExprData::Const(n, us, _) = e.as_data() {
      return match m(n) {
        Some(n2) => Expr::cnst(n2, us.clone()),
        None => e.clone(),
      };
    }
    if let Some(r) = memo.get(e, ()) {
      return r;
    }
    let r = match e.as_data() {
      ExprData::App(f, a, _) => Expr::app(go(m, f, memo), go(m, a, memo)),
      ExprData::Lam(n, t, b, bi, _) => {
        Expr::lam(n.clone(), go(m, t, memo), go(m, b, memo), bi.clone())
      },
      ExprData::ForallE(n, t, b, bi, _) => {
        Expr::all(n.clone(), go(m, t, memo), go(m, b, memo), bi.clone())
      },
      ExprData::LetE(n, t, v, b, nd, _) => Expr::letE(
        n.clone(),
        go(m, t, memo),
        go(m, v, memo),
        go(m, b, memo),
        *nd,
      ),
      ExprData::Proj(s, i, x, _) => {
        Expr::proj(s.clone(), i.clone(), go(m, x, memo))
      },
      ExprData::Mdata(d, x, _) => Expr::mdata(d.clone(), go(m, x, memo)),
      _ => return e.clone(),
    };
    memo.insert(e, (), r.clone());
    r
  }
  go(m, e, &mut ExactMemo::default())
}

// ---------------------------------------------------------------------------
// Permutations and arrays
// ---------------------------------------------------------------------------

/// `isPerm`: `s` is a permutation of `0..s.len()`, given as `s[i]` = the
/// canonical position of Lean's member `i`.
pub fn is_perm(s: &[usize]) -> bool {
  (0..s.len()).all(|p| s.iter().filter(|&&x| x == p).count() == 1)
}

/// `invPerm`: the inverse permutation, `inv[p]` = the Lean index at
/// canonical position `p`; `None` when `s` is not a permutation (every
/// position `p < s.len()` occurs in `s` exactly when `s` is one).
pub fn inv_perm(s: &[usize]) -> Option<Vec<usize>> {
  (0..s.len()).map(|p| s.iter().position(|&x| x == p)).collect()
}

/// `permute`: reorder `xs` (indexed by Lean index) into canonical order;
/// `None` when `s` is not a permutation or `xs` is not of its size.
pub fn permute<T: Clone>(s: &[usize], xs: &[T]) -> Option<Vec<T>> {
  if xs.len() != s.len() {
    return None;
  }
  inv_perm(s)?.into_iter().map(|i| xs.get(i).cloned()).collect()
}

/// Lean's `Array.extract`: `xs[a..b]`, clamped to the array.
pub fn extract<T: Clone>(xs: &[T], a: usize, b: usize) -> Vec<T> {
  xs.get(a..b.min(xs.len())).map_or_else(Vec::new, <[T]>::to_vec)
}

/// Lean's `xs == xs.qsort (· < ·)`: `xs` is sorted.
pub fn eq_sorted(xs: &[usize]) -> bool {
  xs.is_sorted()
}

/// `xs` has no repeated element.
pub fn no_dups(xs: &[usize]) -> bool {
  let mut seen = FxHashSet::default();
  xs.iter().all(|x| seen.insert(*x))
}

// ---------------------------------------------------------------------------
// The transport monad's state
// ---------------------------------------------------------------------------

/// The key of the structural memo (`TState.cacheOwn`): the term, the
/// context (each binder type with its ownership) and the ownership mode.
/// Lean keys by a 64-bit mix of the hashes and the mode and checks all three
/// on a hit; this keys by the full hashes.
pub type OwnKey = (Hash, Hash, bool);

/// The transport's state (`TState`): a fresh-variable counter, the trace
/// (for the tests' logs), the grammar failures that took a local fallback,
/// and the structural memo. The transport monad `TM` is `&mut TState` with
/// an [`R`] result.
#[derive(Default)]
pub struct TState {
  pub next: usize,
  pub log: Vec<String>,
  /// grammar failures that took a local fallback (`partial_fixpoint`'s
  /// composition), for the caller to record
  pub fallbacks: Vec<String>,
  /// the structural `Φ`, which depends on the binder context, on which bound
  /// variables are the recursion's own `below` dictionaries and on the
  /// ownership mode
  pub cache_own: FxHashMap<OwnKey, Expr>,
}

/// `fvarRoot`: the reserved root of the transport's free variables, which
/// no input mentions.
pub fn fvar_root() -> Name {
  root_name("_clq_fvar")
}

impl TState {
  /// `freshFVar`.
  pub fn fresh_fvar(&mut self) -> Name {
    let n = Name::num(fvar_root(), nat(self.next));
    self.next += 1;
    n
  }

  /// `trace`.
  pub fn trace(&mut self, s: String) {
    self.log.push(s);
  }
}

/// `TM.idx`: total array access in the transport. Out of range is a named
/// error (a refusal, which the caller turns into the faithful fallback),
/// never a default.
pub fn tm_idx<'a, T>(xs: &'a [T], i: usize, what: &str) -> R<&'a T> {
  xs.get(i).ok_or_else(|| {
    format!("clique: {what}: index {i} out of range (size {})", xs.len())
  })
}

/// The memo of one WF walk (`TransportMemoM`'s state): fuel and binder depth
/// are part of the key, so caching preserves even the small-fuel refusal
/// paths.
pub type TransportMemo = ExactMemo<(usize, usize), Expr>;

/// `memoTransport`: cache a state-neutral WF visit only. These walkers
/// otherwise change only [`TState::next`] (via [`TState::fresh_fvar`]); an
/// allocating visit is repeated in full, so both the fresh-name stream and
/// the result are preserved. An error is not cached.
pub fn memo_transport(
  tm: &mut TState,
  memo: &mut TransportMemo,
  e: &Expr,
  fuel: usize,
  depth: usize,
  act: impl FnOnce(&mut TState, &mut TransportMemo) -> R<Expr>,
) -> R<Expr> {
  if let Some(out) = memo.get(e, (fuel, depth)) {
    return Ok(out);
  }
  let before = tm.next;
  let out = act(tm, memo)?;
  if tm.next == before {
    memo.insert(e, (fuel, depth), out.clone());
  }
  Ok(out)
}

#[cfg(test)]
mod tests {
  use std::cell::Cell;
  use std::ops::ControlFlow;

  use ix_common::env::{BinderInfo, DataValue, Expr, Level, Name};

  use super::{
    TState, TransportMemo, alpha_eq_skip_mdata, bvar, cnst, const_occurrences,
    dotted, fold_distinct, fvar, inv_perm, is_perm, memo_transport, mentions,
    mentions_fvar, mk_level_max_prime, name_to_string, pair_level, permute,
    strip_all_mdata, subst_bvar0_same, tm_idx,
  };
  use crate::compile::pass3::expr::nat;

  fn c(s: &str) -> Expr {
    cnst(&dotted(s), &[])
  }

  fn md(x: Expr) -> Expr {
    Expr::mdata(vec![(dotted("k"), DataValue::OfBool(true))], x)
  }

  #[test]
  fn permutations() {
    let s = [2, 0, 1];
    assert!(is_perm(&s));
    // `inv[p]` is the Lean index at canonical position `p`
    assert_eq!(inv_perm(&s), Some(vec![1, 2, 0]));
    assert_eq!(permute(&s, &["a", "b", "c"]), Some(vec!["b", "c", "a"]));
    // not a permutation: a repeated and a missing position
    assert!(!is_perm(&[0, 0, 1]));
    assert_eq!(inv_perm(&[0, 0, 1]), None);
    assert_eq!(permute(&[0, 0, 1], &["a", "b", "c"]), None);
    assert_eq!(inv_perm(&[0, 3]), None);
    // size mismatch
    assert_eq!(permute(&[1, 0], &["a", "b", "c"]), None);
    assert_eq!(permute::<&str>(&[], &[]), Some(vec![]));
  }

  #[test]
  fn fold_order_and_dedup_on_a_shared_dag() {
    // `x` is shared: `F (G x) (λ (_ : H) x) x`, with `x = A B`
    let x = Expr::app(c("A"), c("B"));
    let lam = Expr::lam(dotted("y"), c("H"), x.clone(), BinderInfo::Default);
    let e = Expr::app(
      Expr::app(Expr::app(c("F"), Expr::app(c("G"), x.clone())), lam),
      x.clone(),
    );
    // first-occurrence pre-order, function before argument, domain first
    let names = const_occurrences(&|_| true, &e);
    let want: Vec<Name> =
      ["F", "G", "A", "B", "H"].into_iter().map(dotted).collect();
    assert_eq!(names, want);
    assert_eq!(const_occurrences(&|n| *n != dotted("G"), &e).len(), 4);
    // each distinct subterm is visited once: `x`'s 3 nodes once, not 3 times
    let visits = fold_distinct(&e, 0usize, |n, _| ControlFlow::Continue(n + 1));
    assert_eq!(visits, 11);
    // early stop
    let seen = Cell::new(0);
    let hit = fold_distinct(&e, false, |_, y| {
      seen.set(seen.get() + 1);
      if *y == c("G") {
        ControlFlow::Break(true)
      } else {
        ControlFlow::Continue(false)
      }
    });
    assert!(hit);
    assert_eq!(seen.get(), 6);
    assert!(mentions(&dotted("H"), &e));
    assert!(!mentions(&dotted("Z"), &e));
    let f = dotted("_clq_fvar");
    assert!(mentions_fvar(&f, &Expr::app(c("A"), fvar(&f))));
    assert!(!mentions_fvar(&f, &e));
  }

  #[test]
  fn alpha_eq_skips_mdata_on_either_side() {
    let a = Expr::app(c("F"), bvar(0));
    let b = Expr::app(md(c("F")), md(bvar(0)));
    assert!(alpha_eq_skip_mdata(&a, &b));
    assert!(alpha_eq_skip_mdata(&md(b.clone()), &a));
    assert!(crate::compile::pass3::expr::alpha_eq(&a, &a));
    assert!(!crate::compile::pass3::expr::alpha_eq(&a, &b));
    // binder names and info are metadata
    let l1 = Expr::lam(dotted("x"), c("T"), bvar(0), BinderInfo::Default);
    let l2 = Expr::lam(dotted("y"), md(c("T")), bvar(0), BinderInfo::Implicit);
    assert!(alpha_eq_skip_mdata(&l1, &l2));
    assert!(!alpha_eq_skip_mdata(&a, &Expr::app(c("F"), bvar(1))));
    assert!(!alpha_eq_skip_mdata(
      &c("F"),
      &cnst(&dotted("F"), &[Level::zero()])
    ));
    assert_eq!(strip_all_mdata(&b), a);
  }

  #[test]
  fn substitution_and_levels() {
    // `λ z. (bvar 1) z` with `bvar 0 ↦ c`, under the binder: `λ z. c z`
    let body = Expr::lam(
      dotted("z"),
      c("T"),
      Expr::app(bvar(1), bvar(0)),
      BinderInfo::Default,
    );
    let want = Expr::lam(
      dotted("z"),
      c("T"),
      Expr::app(c("C"), bvar(0)),
      BinderInfo::Default,
    );
    assert_eq!(subst_bvar0_same(&body, &c("C")), want);
    let one = Level::succ(Level::zero());
    let u = Level::param(dotted("u"));
    assert_eq!(pair_level(&Level::zero(), &Level::zero()), one);
    assert_eq!(
      mk_level_max_prime(&one, &Level::succ(u.clone())),
      Level::succ(u)
    );
  }

  #[test]
  fn state_helpers() {
    let mut tm = TState::default();
    let a = tm.fresh_fvar();
    assert_eq!(name_to_string(&a), "_clq_fvar.«0»");
    assert_eq!(tm.next, 1);
    assert_eq!(tm_idx(&[1, 2], 1, "x"), Ok(&2));
    assert_eq!(
      tm_idx(&[1, 2], 2, "x"),
      Err("clique: x: index 2 out of range (size 2)".to_string())
    );
    // a state-neutral visit is cached, an allocating one is not
    let mut memo = TransportMemo::default();
    let e = c("E");
    let calls = Cell::new(0);
    for _ in 0..2 {
      let out = memo_transport(&mut tm, &mut memo, &e, 3, 0, |_, _| {
        calls.set(calls.get() + 1);
        Ok(c("O"))
      });
      assert_eq!(out, Ok(c("O")));
    }
    assert_eq!(calls.get(), 1);
    for _ in 0..2 {
      let out = memo_transport(&mut tm, &mut memo, &e, 4, 0, |tm, _| {
        Ok(Expr::fvar(tm.fresh_fvar()))
      });
      assert!(out.is_ok());
    }
    assert_eq!(tm.next, 3);
    assert_eq!(name_to_string(&Name::num(dotted("a.b"), nat(2))), "a.b.«2»");
  }
}
