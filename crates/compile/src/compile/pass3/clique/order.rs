//! Pass 1's classes and canonical order of a clique's specifications, and
//! the order of a theorem clique by its statements: a port of
//! `Ix.Compile.Canon.cliqueClasses` (`Ix/Compile/Canon/Clique.lean`), with
//! the parts of `Canon/Order.lean` and `Canon/Classes.lean` it runs on
//! definitions (`compareExpr`, `compareDef`, `compareConst`,
//! `sortClasses`), and of `Ix.Compile.Pass.Clique.statementOrder`
//! (`Clique/Order.lean`).
//!
//! Every comparison, the order in which the refinement makes it (and so the
//! first error raised), the cache and every error text are Lean's.
//!
//! **Not the compiler's comparator.** `compile.rs`'s `compare_expr`,
//! `compare_defn`, `compare_const` and `sort_consts` take a
//! `&CompileState`: an external constant's address comes from
//! `CompileState::resolve_addr`, not from a caller's lookup (the recovery's
//! lookup also answers for placeholder names no state holds), and an
//! unresolved one is a `CompileError::MissingConstant` tagged with its
//! caller, not Lean's `CmpError` text. Its block sort is also not Lean's
//! refinement step by step: a top-down merge sort where Lean runs
//! `List.sortByM` (a natural merge sort, which compares other pairs, so
//! another error can come first), no name-hash re-sort of a group, and no
//! fuel. The stateless parts are reused: levels go through
//! [`compare_level`] (Lean `compareLevel`: `toUniv`, `Ixon.canonUniv`,
//! `compareUniv`, parameters by position), contract metadata through
//! [`semantic_contract::has_metadata`] and [`semantic_contract::read`], and
//! strengths through [`SOrd`] (`try_compare` is `SOrder.cmpM`, `try_zip` is
//! `SOrder.zipM`).
//!
//! **The rules.**
//! * Seed ([`Rules`]; the default is Lean's `{}`, `Rules.compiler`):
//!   [`Seed::ByNameHash`] sorts the members by the blake3 hash of the name
//!   (Rust `Name`'s `Ord`, Lean `nameCompare`), stably as Lean's insertion
//!   sort; [`Seed::AllOrder`] keeps the caller's order.
//! * A round sorts every class of two or more members with `List.sortByM`
//!   under the context mapping each member to its class index
//!   (`MutConst.ctx`), groups adjacent equal members with `List.groupByM`
//!   (each member against its predecessor; Lean's accumulator leaves the
//!   last group reversed), and re-sorts each group by name hash. The
//!   refinement stops when a round leaves the number of classes unchanged;
//!   the fuel is the member count plus one; Lean's guards follow.
//! * Definitions compare by level-parameter count, type, then value (the
//!   kind is `defn` for every member, `CliqueMember.toMutConst`; a pinned
//!   choice is the value applied to its literal, so it compares last).
//! * Expressions: metavariables, then free variables, are errors; `mdata`
//!   is stripped unless it is a semantic contract, which compares by
//!   `orderKey` and sorts after any non-contract term; then the constructor
//!   order `bvar < sort < const < app < lam < forallE < letE < lit < proj`;
//!   binder names and binder information are ignored; a `let` compares its
//!   type, value, body, then its nondependency bit (`false < true`).
//! * Referenced names (constant heads after their levels, projection
//!   structures): the same name (raw `==`, Lean `ExactKey.nameEq`) is
//!   strongly equal; two in-block names compare by class index, weakly;
//!   in-block sorts before external; two external names by the caller's
//!   address, a missing one an error (the left one first).
//! * Only strong results are cached, by name pair (raw equality, Lean's
//!   `ExactName`); a hit for the swapped pair is returned reversed.
//!
//! **Where the two could still part.** Level parameters are found by raw
//! name equality in [`compare_level`], Lean's `toUniv` by `Name`'s `==` (the
//! stored hash): only two names sharing a stored hash tell them apart. A
//! contract field of `2^64` or more is "semantic contract field is too
//! large" in [`semantic_contract::read`], where Lean reads the `Nat` and
//! fails with another text.

use std::cmp::Ordering;

use bignat::Nat;
use rustc_hash::FxHashMap;

use ix_common::address::Address;
use ix_common::env::{Expr, ExprData, Level, Literal, Name};
use ix_common::strong_ordering::SOrd;
use ixon::CompileError;

use super::basic::R;
use crate::compile::compare_level;
use crate::semantic_contract;

// ---------------------------------------------------------------------------
// Rules
// ---------------------------------------------------------------------------

/// `Seed`: where the refinement starts.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Seed {
  /// One class sorted by the blake3 hash of the name.
  #[default]
  ByNameHash,
  /// The caller's order (a clique's member order), kept stably.
  AllOrder,
}

/// `Rules`: the seed of the refinement. `Rules::default()` is Lean's `{}`
/// (`Rules.compiler`), which the clique order runs.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Rules {
  pub seed: Seed,
}

/// External constants' compiled addresses (`addr? : Name → Option Address`).
pub type AddrOf<'a> = &'a dyn Fn(&Name) -> Option<Address>;

// ---------------------------------------------------------------------------
// Cliques
// ---------------------------------------------------------------------------

/// `CliqueKind`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CliqueKind {
  Structural,
  WellFounded,
  PartialFixpoint,
  /// Theorems and Prop-valued definitions: no specification.
  NoSpec,
  Partial,
  Unsafe,
}

impl CliqueKind {
  /// `CliqueKind.name`.
  pub fn name(self) -> &'static str {
    match self {
      CliqueKind::Structural => "structural",
      CliqueKind::WellFounded => "well-founded",
      CliqueKind::PartialFixpoint => "partial_fixpoint",
      CliqueKind::NoSpec => "theorem / Prop (no specification)",
      CliqueKind::Partial => "partial",
      CliqueKind::Unsafe => "unsafe",
    }
  }
}

/// `CliqueMember`: one member's recursive specification.
#[derive(Clone, Debug)]
pub struct CliqueMember {
  pub name: Name,
  pub level_params: Vec<Name>,
  pub typ: Expr,
  pub value: Expr,
  /// The pinned recursive-argument position (structural recursion).
  pub rec_arg_pos: Option<Nat>,
}

/// `Clique`: a clique in Lean's order.
#[derive(Clone, Debug)]
pub struct Clique {
  pub kind: CliqueKind,
  pub members: Vec<CliqueMember>,
}

impl Clique {
  /// `Clique.names`.
  pub fn names(&self) -> Vec<Name> {
    self.members.iter().map(|m| m.name.clone()).collect()
  }
}

/// The definition the comparator sorts (`CliqueMember.toMutConst`'s
/// `MutConst.defn`). Its kind, hints, safety and `all` are the same for
/// every member, so these are the fields compared.
#[derive(Clone, Debug)]
pub struct MutDef {
  pub name: Name,
  pub level_params: Vec<Name>,
  pub typ: Expr,
  pub value: Expr,
}

impl CliqueMember {
  /// `CliqueMember.toMutConst`: the value applied to the pinned choice,
  /// which the comparator reaches after the value.
  pub fn to_mut_const(&self) -> MutDef {
    let value = match &self.rec_arg_pos {
      Some(p) => {
        Expr::app(self.value.clone(), Expr::lit(Literal::NatVal(p.clone())))
      },
      None => self.value.clone(),
    };
    MutDef {
      name: self.name.clone(),
      level_params: self.level_params.clone(),
      typ: self.typ.clone(),
      value,
    }
  }
}

// ---------------------------------------------------------------------------
// The comparator
// ---------------------------------------------------------------------------

/// `CmpCtx`: the external addresses and every in-block name's class index.
struct CmpCtx<'a> {
  addr: AddrOf<'a>,
  mut_ctx: &'a FxHashMap<Name, usize>,
}

/// `CmpError.render` of the errors [`compare_level`] and
/// [`semantic_contract::read`] raise.
fn cmp_error_text(e: CompileError) -> String {
  match e {
    CompileError::UnknownUnivParam { param, .. } => {
      format!("unknown universe parameter {param}")
    },
    CompileError::UnsupportedExpr { desc } => desc,
    e => e.to_string(),
  }
}

/// `compareLevel`.
fn level(xl: &[Name], yl: &[Name], x: &Level, y: &Level) -> R<SOrd> {
  compare_level(x, y, xl, yl).map_err(cmp_error_text)
}

/// `compareExternal`: two external names, by compiled address.
fn compare_external(c: &CmpCtx<'_>, x: &Name, y: &Name) -> R<SOrd> {
  match ((c.addr)(x), (c.addr)(y)) {
    (Some(ax), Some(ay)) => Ok(SOrd::cmp(&ax, &ay)),
    (None, _) => Err(format!("no compiled address for {}", x.pretty())),
    (_, None) => Err(format!("no compiled address for {}", y.pretty())),
  }
}

/// `compareRef`: two referenced names.
fn compare_ref(c: &CmpCtx<'_>, x: &Name, y: &Name) -> R<SOrd> {
  if x == y {
    return Ok(SOrd::eq(true));
  }
  match (c.mut_ctx.get(x), c.mut_ctx.get(y)) {
    (Some(nx), Some(ny)) => Ok(SOrd::weak_cmp(nx, ny)),
    (Some(_), None) => Ok(SOrd::lt(true)),
    (None, Some(_)) => Ok(SOrd::gt(true)),
    (None, None) => compare_external(c, x, y),
  }
}

/// The constructor order of `compareExpr` (metavariables, free variables
/// and `mdata` are decided before it is read).
fn rank(e: &Expr) -> u8 {
  match e.as_data() {
    ExprData::Bvar(..) => 0,
    ExprData::Sort(..) => 1,
    ExprData::Const(..) => 2,
    ExprData::App(..) => 3,
    ExprData::Lam(..) => 4,
    ExprData::ForallE(..) => 5,
    ExprData::LetE(..) => 6,
    ExprData::Lit(..) => 7,
    ExprData::Proj(..) => 8,
    ExprData::Fvar(..) | ExprData::Mvar(..) | ExprData::Mdata(..) => 9,
  }
}

/// `compareExpr`: the name-irrelevant structural order on expressions.
fn compare_expr(
  c: &CmpCtx<'_>,
  xl: &[Name],
  yl: &[Name],
  x: &Expr,
  y: &Expr,
) -> R<SOrd> {
  use semantic_contract::{has_metadata, read};
  match (x.as_data(), y.as_data()) {
    (ExprData::Mvar(..), _) | (_, ExprData::Mvar(..)) => {
      Err("metavariable in comparison".into())
    },
    (ExprData::Fvar(..), _) | (_, ExprData::Fvar(..)) => {
      Err("fvar in comparison".into())
    },
    (ExprData::Mdata(dx, xi, _), ExprData::Mdata(dy, yi, _)) => {
      if !has_metadata(dx) {
        compare_expr(c, xl, yl, xi, y)
      } else if !has_metadata(dy) {
        compare_expr(c, xl, yl, x, yi)
      } else {
        let cx = read(dx).map_err(cmp_error_text)?;
        let cy = read(dy).map_err(cmp_error_text)?;
        let o = SOrd::cmp(&cx.order_key(), &cy.order_key());
        if o.ordering != Ordering::Equal {
          Ok(o)
        } else {
          compare_expr(c, xl, yl, xi, yi)
        }
      }
    },
    (ExprData::Mdata(d, xi, _), _) => {
      if has_metadata(d) {
        Ok(SOrd::gt(true))
      } else {
        compare_expr(c, xl, yl, xi, y)
      }
    },
    (_, ExprData::Mdata(d, yi, _)) => {
      if has_metadata(d) {
        Ok(SOrd::lt(true))
      } else {
        compare_expr(c, xl, yl, x, yi)
      }
    },
    (ExprData::Bvar(i, _), ExprData::Bvar(j, _)) => Ok(SOrd::cmp(i, j)),
    (ExprData::Sort(u, _), ExprData::Sort(v, _)) => level(xl, yl, u, v),
    (ExprData::Const(xn, xls, _), ExprData::Const(yn, yls, _)) => {
      let us = SOrd::try_zip(|a, b| level(xl, yl, a, b), xls, yls)?;
      if us.ordering != Ordering::Equal {
        Ok(us)
      } else {
        compare_ref(c, xn, yn)
      }
    },
    (ExprData::App(xf, xa, _), ExprData::App(yf, ya, _)) => {
      compare_expr(c, xl, yl, xf, yf)?
        .try_compare(|| compare_expr(c, xl, yl, xa, ya))
    },
    (ExprData::Lam(_, xt, xb, ..), ExprData::Lam(_, yt, yb, ..))
    | (ExprData::ForallE(_, xt, xb, ..), ExprData::ForallE(_, yt, yb, ..)) => {
      compare_expr(c, xl, yl, xt, yt)?
        .try_compare(|| compare_expr(c, xl, yl, xb, yb))
    },
    (
      ExprData::LetE(_, xt, xv, xb, xnd, _),
      ExprData::LetE(_, yt, yv, yb, ynd, _),
    ) => compare_expr(c, xl, yl, xt, yt)?.try_compare(|| {
      compare_expr(c, xl, yl, xv, yv)?.try_compare(|| {
        compare_expr(c, xl, yl, xb, yb)?.try_compare(|| Ok(SOrd::cmp(xnd, ynd)))
      })
    }),
    (ExprData::Lit(a, _), ExprData::Lit(b, _)) => Ok(SOrd::cmp(a, b)),
    (ExprData::Proj(xn, xi, xs, _), ExprData::Proj(yn, yi, ys, _)) => {
      compare_ref(c, xn, yn)?.try_compare(|| {
        SOrd::cmp(xi, yi).try_compare(|| compare_expr(c, xl, yl, xs, ys))
      })
    },
    _ => Ok(SOrd::cmp(&rank(x), &rank(y))),
  }
}

/// `compareDef` (the kind compares equal: every member is a `defn`).
fn compare_def(c: &CmpCtx<'_>, x: &MutDef, y: &MutDef) -> R<SOrd> {
  let (xl, yl) = (&x.level_params, &y.level_params);
  SOrd::cmp(&xl.len(), &yl.len()).try_compare(|| {
    compare_expr(c, xl, yl, &x.typ, &y.typ)?
      .try_compare(|| compare_expr(c, xl, yl, &x.value, &y.value))
  })
}

/// `CmpState`: the strong results, by the name pair in the orientation they
/// were computed in. Lean keys the unordered pair and records the left
/// name; an entry is written only on a miss for both orientations, so the
/// two agree.
#[derive(Default)]
struct CmpState {
  cache: FxHashMap<(Name, Name), Ordering>,
}

impl CmpState {
  /// `cacheGet`: a hit computed for the swapped pair is returned reversed.
  fn get(&self, x: &Name, y: &Name) -> Option<Ordering> {
    if let Some(o) = self.cache.get(&(x.clone(), y.clone())) {
      return Some(*o);
    }
    self.cache.get(&(y.clone(), x.clone())).map(|o| o.reverse())
  }
}

/// `compareConst`: the comparison the refinement sorts by, cached.
fn compare_const(
  st: &mut CmpState,
  addr: AddrOf<'_>,
  mut_ctx: &FxHashMap<Name, usize>,
  x: &MutDef,
  y: &MutDef,
) -> R<Ordering> {
  if let Some(o) = st.get(&x.name, &y.name) {
    return Ok(o);
  }
  let so = compare_def(&CmpCtx { addr, mut_ctx }, x, y)?;
  if so.strong {
    st.cache.insert((x.name.clone(), y.name.clone()), so.ordering);
  }
  Ok(so.ordering)
}

// ---------------------------------------------------------------------------
// `List.sortByM` and `List.groupByM` (`Ix/Common.lean`)
// ---------------------------------------------------------------------------

type CmpFn<'f, T> = dyn FnMut(&T, &T) -> R<Ordering> + 'f;

/// `List.sequencesM` (with `descendingM` and `ascendingM`): the maximal
/// strictly descending runs (reversed) and non-descending runs, left to
/// right. A run that reaches the end of the input is followed by an empty
/// run, as Lean's `sequencesM []`.
fn sequences<T: Clone>(cmp: &mut CmpFn<'_, T>, xs: &[T]) -> R<Vec<Vec<T>>> {
  let mut runs = Vec::new();
  let mut rest = xs;
  loop {
    let [a, b, tail @ ..] = rest else {
      runs.push(rest.to_vec());
      return Ok(runs);
    };
    let descending = cmp(a, b)? == Ordering::Greater;
    let mut run = vec![a.clone()];
    let mut last = b;
    let mut tail = tail;
    rest = loop {
      let Some((next, more)) = tail.split_first() else { break tail };
      if (cmp(last, next)? == Ordering::Greater) != descending {
        break tail;
      }
      run.push(last.clone());
      last = next;
      tail = more;
    };
    run.push(last.clone());
    if descending {
      run.reverse();
    }
    runs.push(run);
  }
}

/// `List.mergeM`: the left element first unless it is greater.
fn merge<T>(cmp: &mut CmpFn<'_, T>, a: Vec<T>, b: Vec<T>) -> R<Vec<T>> {
  let mut out = Vec::with_capacity(a.len() + b.len());
  let mut a = a.into_iter().peekable();
  let mut b = b.into_iter().peekable();
  while let (Some(x), Some(y)) = (a.peek(), b.peek()) {
    if cmp(x, y)? == Ordering::Greater {
      out.extend(b.next());
    } else {
      out.extend(a.next());
    }
  }
  out.extend(a);
  out.extend(b);
  Ok(out)
}

/// `List.mergePairsM`.
fn merge_pairs<T>(cmp: &mut CmpFn<'_, T>, runs: Vec<Vec<T>>) -> R<Vec<Vec<T>>> {
  let mut out = Vec::with_capacity(runs.len().div_ceil(2));
  let mut it = runs.into_iter();
  while let Some(a) = it.next() {
    match it.next() {
      Some(b) => out.push(merge(cmp, a, b)?),
      None => out.push(a),
    }
  }
  Ok(out)
}

/// `List.sortByM`: `sequencesM`, then `mergeAllM` (merge rounds, fuelled by
/// the number of runs).
fn sort_by_m<T: Clone>(cmp: &mut CmpFn<'_, T>, xs: &[T]) -> R<Vec<T>> {
  let mut runs = sequences(cmp, xs)?;
  let mut fuel = runs.len();
  while fuel > 0 && runs.len() != 1 {
    fuel -= 1;
    runs = merge_pairs(cmp, runs)?;
  }
  Ok(runs.into_iter().flatten().collect())
}

/// `List.groupByM`: adjacent elements share a group while `eq current
/// previous` holds. Lean's accumulator keeps the open group most recent
/// first and reverses each group as it closes, so the last group is left
/// reversed.
fn group_by_m<T>(
  eq: &mut dyn FnMut(&T, &T) -> R<bool>,
  xs: Vec<T>,
) -> R<Vec<Vec<T>>> {
  let mut groups = Vec::new();
  let mut open: Vec<T> = Vec::new();
  for a in xs {
    let same = match open.last() {
      Some(previous) => eq(&a, previous)?,
      None => true,
    };
    if same {
      open.push(a);
    } else {
      groups.push(std::mem::replace(&mut open, vec![a]));
    }
  }
  if !open.is_empty() {
    open.reverse();
    groups.push(open);
  }
  Ok(groups)
}

// ---------------------------------------------------------------------------
// Classes
// ---------------------------------------------------------------------------

/// `SortStats`: the statistics of one refinement.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct SortStats {
  pub rounds: usize,
}

/// `sortByName`: by name hash, stably.
fn sort_by_name(mut xs: Vec<&MutDef>) -> Vec<&MutDef> {
  xs.sort_by(|a, b| a.name.cmp(&b.name));
  xs
}

/// `MutConst.ctx` over definitions: each member's class index (a later
/// class wins for a repeated name).
fn mut_ctx(classes: &[Vec<&MutDef>]) -> FxHashMap<Name, usize> {
  let mut ctx = FxHashMap::default();
  for (j, class) in classes.iter().enumerate() {
    for m in class {
      ctx.insert(m.name.clone(), j);
    }
  }
  ctx
}

/// `refineClass`.
fn refine_class<'a>(
  st: &mut CmpState,
  addr: AddrOf<'_>,
  ctx: &FxHashMap<Name, usize>,
  class: &[&'a MutDef],
) -> R<Vec<Vec<&'a MutDef>>> {
  match class {
    [] => Err("empty class in sortConsts".into()),
    [x] => Ok(vec![vec![*x]]),
    xs => {
      let sorted = sort_by_m(
        &mut |a: &&MutDef, b: &&MutDef| compare_const(st, addr, ctx, a, b),
        xs,
      )?;
      let groups = group_by_m(
        &mut |a: &&MutDef, b: &&MutDef| {
          Ok(compare_const(st, addr, ctx, a, b)? == Ordering::Equal)
        },
        sorted,
      )?;
      Ok(groups.into_iter().map(sort_by_name).collect())
    },
  }
}

/// `sortClasses` over definitions: the classes of `sources` in canonical
/// order, each class's first member its representative, from the seed
/// `rules.seed`. No members, no classes.
pub fn sort_classes<'a>(
  rules: Rules,
  addr: AddrOf<'_>,
  sources: &'a [MutDef],
) -> R<(Vec<Vec<&'a MutDef>>, SortStats)> {
  if sources.is_empty() {
    return Ok((Vec::new(), SortStats::default()));
  }
  let members: Vec<&MutDef> = sources.iter().collect();
  let seed = match rules.seed {
    Seed::ByNameHash => sort_by_name(members),
    Seed::AllOrder => members,
  };
  let mut st = CmpState::default();
  let mut classes = vec![seed];
  let mut rounds = 0;
  let mut fuel = sources.len() + 1;
  let classes = loop {
    if fuel == 0 {
      return Err("sortConsts did not converge".into());
    }
    fuel -= 1;
    let ctx = mut_ctx(&classes);
    let mut refined = Vec::new();
    for class in &classes {
      refined.extend(refine_class(&mut st, addr, &ctx, class)?);
    }
    rounds += 1;
    if classes.len() == refined.len() {
      break refined;
    }
    classes = refined;
  };
  if classes.iter().any(Vec::is_empty) {
    return Err("empty class after sortConsts".into());
  }
  if sources.len() < classes.len() {
    return Err("too many classes after sortConsts".into());
  }
  Ok((classes, SortStats { rounds }))
}

/// `classNames`.
pub fn class_names(classes: &[Vec<&MutDef>]) -> Vec<Vec<Name>> {
  classes
    .iter()
    .map(|class| class.iter().map(|m| m.name.clone()).collect())
    .collect()
}

/// `cliqueClasses`: the classes and canonical order of a clique, as names.
pub fn clique_classes(
  rules: Rules,
  addr: AddrOf<'_>,
  c: &Clique,
) -> R<(Vec<Vec<Name>>, SortStats)> {
  let defs: Vec<MutDef> =
    c.members.iter().map(CliqueMember::to_mut_const).collect();
  let (classes, st) = sort_classes(rules, addr, &defs)?;
  Ok((class_names(&classes), st))
}

/// `statementOrder`: the canonical order of a theorem clique by its
/// statements, each compared as its own value. `σ[i]` is the canonical
/// position of Lean's member `i`, or `None` when two statements tie (a
/// class of two or more). An error is the comparator's, or a member the
/// classes do not contain.
pub fn statement_order(
  rules: Rules,
  addr: AddrOf<'_>,
  members: &[CliqueMember],
) -> R<Option<Vec<usize>>> {
  let c = Clique {
    kind: CliqueKind::NoSpec,
    members: members
      .iter()
      .map(|m| CliqueMember {
        value: m.typ.clone(),
        rec_arg_pos: None,
        ..m.clone()
      })
      .collect(),
  };
  let (classes, _) = clique_classes(rules, addr, &c)?;
  if classes.iter().any(|class| class.len() >= 2) {
    return Ok(None);
  }
  // `Array.contains` reads `Name`'s `==`: the stored hash.
  let sigma: Option<Vec<usize>> = c
    .members
    .iter()
    .map(|m| {
      classes.iter().position(|class| {
        class.iter().any(|n| n.get_hash() == m.name.get_hash())
      })
    })
    .collect();
  match sigma {
    Some(sigma) => Ok(Some(sigma)),
    None => Err("statementOrder: a member is in no class".into()),
  }
}

#[cfg(test)]
mod tests {
  //! The expected strings are Lean's: `Ix.Compile.Canon.cliqueClasses {}`
  //! and `Ix.Compile.Pass.Clique.statementOrder {}` evaluated on the same
  //! terms, with `addr? n = some n.getHash`, printed as
  //! `#[#[..]] rounds=n` (or `error: ..`).

  use bignat::Nat;

  use ix_common::address::Address;
  use ix_common::env::{BinderInfo, Expr, Level, Name};

  use super::{
    AddrOf, Clique, CliqueKind, CliqueMember, R, Rules, Seed, SortStats,
    clique_classes, statement_order,
  };
  use crate::compile::pass3::clique::basic::{bvar, dotted, root_name};

  /// `addr? n = some n.getHash`.
  fn by_hash() -> impl Fn(&Name) -> Option<Address> {
    |n: &Name| Some(Address::from_blake3_hash(*n.get_hash()))
  }

  fn nowhere(_: &Name) -> Option<Address> {
    None
  }

  fn nat_t() -> Expr {
    Expr::cnst(root_name("Nat"), vec![])
  }

  fn bool_t() -> Expr {
    Expr::cnst(root_name("Bool"), vec![])
  }

  fn arrow(a: Expr, b: Expr) -> Expr {
    Expr::all(root_name("x"), a, b, BinderInfo::Default)
  }

  fn lam1(t: Expr, b: Expr) -> Expr {
    Expr::lam(root_name("x"), t, b, BinderInfo::Default)
  }

  fn nat_to_nat() -> Expr {
    arrow(nat_t(), nat_t())
  }

  fn id_nat() -> Expr {
    lam1(nat_t(), bvar(0))
  }

  /// `fun x : Nat => f x`.
  fn call(f: Name) -> Expr {
    lam1(nat_t(), Expr::app(Expr::cnst(f, vec![]), bvar(0)))
  }

  fn mem(name: &str, typ: Expr, value: Expr) -> CliqueMember {
    CliqueMember {
      name: root_name(name),
      level_params: vec![],
      typ,
      value,
      rec_arg_pos: None,
    }
  }

  fn arr(xs: &[String]) -> String {
    format!("#[{}]", xs.join(", "))
  }

  fn show(r: &R<(Vec<Vec<Name>>, SortStats)>) -> String {
    match r {
      Ok((classes, st)) => {
        let classes: Vec<String> = classes
          .iter()
          .map(|c| arr(&c.iter().map(Name::pretty).collect::<Vec<_>>()))
          .collect();
        format!("{} rounds={}", arr(&classes), st.rounds)
      },
      Err(e) => format!("error: {e}"),
    }
  }

  fn run_with(
    rules: Rules,
    addr: AddrOf<'_>,
    members: Vec<CliqueMember>,
  ) -> String {
    let c = Clique { kind: CliqueKind::Structural, members };
    show(&clique_classes(rules, addr, &c))
  }

  fn run(members: Vec<CliqueMember>) -> String {
    run_with(Rules::default(), &by_hash(), members)
  }

  #[test]
  fn equal_specifications_are_one_class_in_name_hash_order() {
    let f = || mem("f", nat_to_nat(), id_nat());
    let g = || mem("g", nat_to_nat(), id_nat());
    let h = || mem("h", nat_to_nat(), id_nat());
    assert_eq!(run(vec![f(), g()]), "#[#[f, g]] rounds=1");
    // The hashes order `h < f < g`, whatever the input order or seed.
    assert_eq!(run(vec![h(), g(), f()]), "#[#[h, f, g]] rounds=1");
    assert_eq!(run(vec![f(), g(), h()]), "#[#[h, f, g]] rounds=1");
    let all_order = Rules { seed: Seed::AllOrder };
    assert_eq!(
      run_with(all_order, &by_hash(), vec![h(), g(), f()]),
      "#[#[h, f, g]] rounds=1"
    );
  }

  #[test]
  fn recursive_references_classify_by_structure() {
    // `f` calls `g` and `g` calls `f`: one class at the fixed point.
    assert_eq!(
      run(vec![
        mem("f", nat_to_nat(), call(root_name("g"))),
        mem("g", nat_to_nat(), call(root_name("f"))),
      ]),
      "#[#[f, g]] rounds=1"
    );
    // `a` calls itself, `b` calls `c`, `c` calls `Nat.succ`: round 1 splits
    // `c` off (in-block before external), round 2 splits `a` from `b`.
    let a = || mem("a", nat_to_nat(), call(root_name("a")));
    let b = || mem("b", nat_to_nat(), call(root_name("c")));
    let c = || mem("c", nat_to_nat(), call(dotted("Nat.succ")));
    assert_eq!(run(vec![a(), b(), c()]), "#[#[a], #[b], #[c]] rounds=3");
    assert_eq!(run(vec![c(), b(), a()]), "#[#[a], #[b], #[c]] rounds=3");
  }

  #[test]
  fn pinned_choice_compares_last() {
    let mut f = mem("f", nat_to_nat(), id_nat());
    f.rec_arg_pos = Some(Nat::from(1u64));
    let mut g = mem("g", nat_to_nat(), id_nat());
    g.rec_arg_pos = Some(Nat::from(0u64));
    assert_eq!(run(vec![f, g]), "#[#[g], #[f]] rounds=2");
  }

  #[test]
  fn non_dep_splits_classes_but_binder_names_do_not() {
    let sort1 = || Expr::sort(Level::succ(Level::zero()));
    let let_val = |binder: &str, nd| {
      Expr::letE(
        root_name(binder),
        sort1(),
        Expr::sort(Level::zero()),
        bvar(0),
        nd,
      )
    };
    assert_eq!(
      run(vec![
        mem("let", sort1(), let_val("x", false)),
        mem("have", sort1(), let_val("x", true)),
        mem("neighbour", sort1(), let_val("y", false)),
      ]),
      "#[#[let, neighbour], #[have]] rounds=2"
    );
  }

  #[test]
  fn external_and_projection_references() {
    let bool_id = || lam1(bool_t(), bvar(0));
    assert_eq!(
      run(vec![
        mem("f", nat_to_nat(), id_nat()),
        mem("g", arrow(bool_t(), bool_t()), bool_id()),
      ]),
      "#[#[f], #[g]] rounds=2"
    );
    let proj = |s: &str| {
      lam1(nat_t(), Expr::proj(root_name(s), Nat::from(0u64), bvar(0)))
    };
    assert_eq!(
      run(vec![
        mem("f", nat_to_nat(), proj("g")),
        mem("g", nat_to_nat(), proj("Prod"))
      ]),
      "#[#[f], #[g]] rounds=2"
    );
  }

  #[test]
  fn levels_compare_by_position_after_canon_univ() {
    let u = || Level::param(root_name("u"));
    let v = || Level::param(root_name("v"));
    let uv = || vec![root_name("u"), root_name("v")];
    let with_levels = |name: &str, ls: Vec<Name>, typ: Expr| CliqueMember {
      level_params: ls,
      ..mem(name, typ, nat_t())
    };
    assert_eq!(
      run(vec![
        with_levels("f", uv(), Expr::sort(Level::max(u(), v()))),
        with_levels("g", uv(), Expr::sort(Level::max(v(), u()))),
      ]),
      "#[#[f, g]] rounds=1"
    );
    assert_eq!(
      run(vec![
        with_levels("f", vec![root_name("u")], Expr::sort(u())),
        with_levels("g", vec![root_name("v")], Expr::sort(v())),
      ]),
      "#[#[f, g]] rounds=1"
    );
  }

  #[test]
  fn errors_are_lean_texts() {
    let bool_id = || lam1(bool_t(), bvar(0));
    let f = || mem("f", nat_to_nat(), id_nat());
    let no_addr: AddrOf<'_> = &nowhere;
    // The seed puts `f` before `g` and `h` before `f`; the left name of the
    // first comparison is reported.
    let g = mem("g", arrow(bool_t(), bool_t()), bool_id());
    assert_eq!(
      run_with(Rules::default(), no_addr, vec![g, f()]),
      "error: no compiled address for Nat"
    );
    let h = mem("h", arrow(bool_t(), bool_t()), bool_id());
    assert_eq!(
      run_with(Rules::default(), no_addr, vec![h, f()]),
      "error: no compiled address for Bool"
    );
    assert_eq!(
      run(vec![
        mem("f", nat_to_nat(), Expr::fvar(root_name("y"))),
        mem("g", nat_to_nat(), id_nat()),
      ]),
      "error: fvar in comparison"
    );
    assert_eq!(
      run(vec![
        mem("f", Expr::sort(Level::param(root_name("u"))), nat_t()),
        mem("g", Expr::sort(Level::zero()), nat_t()),
      ]),
      "error: unknown universe parameter u"
    );
    assert_eq!(run(vec![]), "#[] rounds=0");
  }

  /// `∀ n : Nat, Eq.{1} Nat (s n) (s n)`.
  fn statement(s: &dyn Fn(Expr) -> Expr) -> Expr {
    let eq = Expr::cnst(root_name("Eq"), vec![Level::succ(Level::zero())]);
    let body =
      Expr::app(Expr::app(Expr::app(eq, nat_t()), s(bvar(0))), s(bvar(0)));
    Expr::all(root_name("n"), nat_t(), body, BinderInfo::Default)
  }

  #[test]
  fn statement_order_ties_and_orders() {
    let refl = || statement(&|e| e);
    let succ =
      || statement(&|e| Expr::app(Expr::cnst(dotted("Nat.succ"), vec![]), e));
    let rules = Rules::default();
    // The values differ, the statements tie.
    let tie = [mem("t1", refl(), id_nat()), mem("t2", refl(), nat_t())];
    assert_eq!(statement_order(rules, &by_hash(), &tie), Ok(None));
    let ordered = [mem("t1", refl(), id_nat()), mem("t2", succ(), id_nat())];
    assert_eq!(
      statement_order(rules, &by_hash(), &ordered),
      Ok(Some(vec![0, 1]))
    );
    let reversed = [mem("t2", succ(), id_nat()), mem("t1", refl(), id_nat())];
    assert_eq!(
      statement_order(rules, &by_hash(), &reversed),
      Ok(Some(vec![1, 0]))
    );
    let missing = [
      mem("t1", nat_to_nat(), id_nat()),
      mem("t2", arrow(bool_t(), bool_t()), id_nat()),
    ];
    assert_eq!(
      statement_order(rules, &nowhere, &missing),
      Err("no compiled address for Nat".to_string())
    );
  }
}
