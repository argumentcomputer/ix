//! Pass 1's classes over a definition clique's specifications (a port of the
//! parts of `Ix/Compile/Canon/{Order,Classes,Clique}.lean` that
//! `Clique.cliqueOrder` runs: `Rules.phaseA`, definitions only).
//!
//! The Rust compiler's own block sort (`compile.rs` `sort_consts`) is not
//! reused: the clique order compares with a caller-supplied address lookup
//! (the specification placeholders have fixed addresses), seeds and
//! re-sorts classes by name hash (`Representative.leastNameHash`), and stops
//! when the number of classes is stable, all as the Lean module does.

use std::cmp::Ordering;

use rustc_hash::FxHashMap;

use ix_common::address::Address;
use ix_common::env::{Expr, ExprData, Level, Name};

use super::basic::R;
use crate::compile::pass3::expr::nat_usize;

/// A specification as the definition the comparator sorts.
#[derive(Clone, Debug)]
pub struct Member {
  pub name: Name,
  pub level_params: Vec<Name>,
  pub typ: Expr,
  pub value: Expr,
}

pub type AddrOf<'a> = &'a dyn Fn(&Name) -> Option<Address>;

#[derive(Clone, Copy, Debug)]
struct So {
  strong: bool,
  ord: Ordering,
}

fn so(strong: bool, ord: Ordering) -> R<So> {
  Ok(So { strong, ord })
}

/// `SOrder.cmpM`.
fn cmp_m(x: R<So>, y: impl FnOnce() -> R<So>) -> R<So> {
  let x = x?;
  match (x.strong, x.ord) {
    (true, Ordering::Equal) => y(),
    (false, Ordering::Equal) => Ok(So { strong: false, ord: y()?.ord }),
    _ => Ok(x),
  }
}

/// `SOrder.zipM`.
fn zip_m<T>(f: &dyn Fn(&T, &T) -> R<So>, xs: &[T], ys: &[T]) -> R<So> {
  match (xs.split_first(), ys.split_first()) {
    (None, None) => so(true, Ordering::Equal),
    (None, Some(_)) => so(true, Ordering::Less),
    (Some(_), None) => so(true, Ordering::Greater),
    (Some((x, xr)), Some((y, yr))) => {
      let a = f(x, y)?;
      if a.ord == Ordering::Equal {
        cmp_m(Ok(a), || zip_m(f, xr, yr))
      } else {
        Ok(a)
      }
    },
  }
}

struct Cmp<'a> {
  addr: AddrOf<'a>,
  mut_ctx: &'a FxHashMap<Name, usize>,
}

fn compare_level(xl: &[Name], yl: &[Name], x: &Level, y: &Level) -> R<So> {
  match crate::compile::compare_level(x, y, xl, yl) {
    Ok(s) => so(true, s.ordering),
    Err(e) => Err(format!("{e:?}")),
  }
}

fn compare_external(c: &Cmp<'_>, x: &Name, y: &Name) -> R<So> {
  match ((c.addr)(x), (c.addr)(y)) {
    (Some(ax), Some(ay)) => so(true, ax.cmp(&ay)),
    (None, _) => Err(format!("no compiled address for {}", x.pretty())),
    (_, None) => Err(format!("no compiled address for {}", y.pretty())),
  }
}

fn compare_ref(c: &Cmp<'_>, x: &Name, y: &Name) -> R<So> {
  if x == y {
    return so(true, Ordering::Equal);
  }
  match (c.mut_ctx.get(x), c.mut_ctx.get(y)) {
    (Some(nx), Some(ny)) => so(false, nx.cmp(ny)),
    (Some(_), None) => so(true, Ordering::Less),
    (None, Some(_)) => so(true, Ordering::Greater),
    (None, None) => compare_external(c, x, y),
  }
}

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
    _ => 9,
  }
}

/// `compareExpr`.
fn compare_expr(
  c: &Cmp<'_>,
  xl: &[Name],
  yl: &[Name],
  x: &Expr,
  y: &Expr,
) -> R<So> {
  use crate::semantic_contract as sc;
  match (x.as_data(), y.as_data()) {
    (ExprData::Mvar(..), _) | (_, ExprData::Mvar(..)) => {
      Err("metavariable in comparison".into())
    },
    (ExprData::Fvar(..), _) | (_, ExprData::Fvar(..)) => {
      Err("fvar in comparison".into())
    },
    (ExprData::Mdata(dx, xi, _), ExprData::Mdata(dy, yi, _)) => {
      if sc::has_metadata(dx) {
        if sc::has_metadata(dy) {
          let cx = sc::read(dx).map_err(|e| format!("{e:?}"))?;
          let cy = sc::read(dy).map_err(|e| format!("{e:?}"))?;
          let o = cx.order_key().cmp(&cy.order_key());
          if o != Ordering::Equal {
            so(true, o)
          } else {
            compare_expr(c, xl, yl, xi, yi)
          }
        } else {
          compare_expr(c, xl, yl, x, yi)
        }
      } else {
        compare_expr(c, xl, yl, xi, y)
      }
    },
    (ExprData::Mdata(d, xi, _), _) => {
      if sc::has_metadata(d) {
        so(true, Ordering::Greater)
      } else {
        compare_expr(c, xl, yl, xi, y)
      }
    },
    (_, ExprData::Mdata(d, yi, _)) => {
      if sc::has_metadata(d) {
        so(true, Ordering::Less)
      } else {
        compare_expr(c, xl, yl, x, yi)
      }
    },
    (ExprData::Bvar(i, _), ExprData::Bvar(j, _)) => {
      so(true, nat_usize(i).cmp(&nat_usize(j)))
    },
    (ExprData::Sort(u, _), ExprData::Sort(v, _)) => compare_level(xl, yl, u, v),
    (ExprData::Const(xn, xls, _), ExprData::Const(yn, yls, _)) => {
      let us =
        zip_m(&|a: &Level, b: &Level| compare_level(xl, yl, a, b), xls, yls)?;
      if us.ord != Ordering::Equal { Ok(us) } else { compare_ref(c, xn, yn) }
    },
    (ExprData::App(xf, xa, _), ExprData::App(yf, ya, _)) => {
      cmp_m(compare_expr(c, xl, yl, xf, yf), || compare_expr(c, xl, yl, xa, ya))
    },
    (ExprData::Lam(_, xt, xb, _, _), ExprData::Lam(_, yt, yb, _, _))
    | (
      ExprData::ForallE(_, xt, xb, _, _),
      ExprData::ForallE(_, yt, yb, _, _),
    ) => {
      cmp_m(compare_expr(c, xl, yl, xt, yt), || compare_expr(c, xl, yl, xb, yb))
    },
    (
      ExprData::LetE(_, xt, xv, xb, xnd, _),
      ExprData::LetE(_, yt, yv, yb, ynd, _),
    ) => cmp_m(compare_expr(c, xl, yl, xt, yt), || {
      cmp_m(compare_expr(c, xl, yl, xv, yv), || {
        cmp_m(compare_expr(c, xl, yl, xb, yb), || so(true, xnd.cmp(ynd)))
      })
    }),
    (ExprData::Lit(a, _), ExprData::Lit(b, _)) => so(true, a.cmp(b)),
    (ExprData::Proj(xn, xi, xs, _), ExprData::Proj(yn, yi, ys, _)) => {
      cmp_m(compare_ref(c, xn, yn), || {
        cmp_m(so(true, nat_usize(xi).cmp(&nat_usize(yi))), || {
          compare_expr(c, xl, yl, xs, ys)
        })
      })
    },
    _ => so(true, rank(x).cmp(&rank(y))),
  }
}

/// `compareDef` (both definitions of kind `defn`).
fn compare_def(c: &Cmp<'_>, x: &Member, y: &Member) -> R<So> {
  cmp_m(so(true, x.level_params.len().cmp(&y.level_params.len())), || {
    cmp_m(
      compare_expr(c, &x.level_params, &y.level_params, &x.typ, &y.typ),
      || compare_expr(c, &x.level_params, &y.level_params, &x.value, &y.value),
    )
  })
}

/// The comparison cache (`CmpState.cache`, `portFixes`: reversed hits
/// flipped).
#[derive(Default)]
struct Cache {
  map: FxHashMap<(Name, Name), (Ordering, Name)>,
}

fn cache_key(x: &Name, y: &Name) -> (Name, Name) {
  if x < y { (x.clone(), y.clone()) } else { (y.clone(), x.clone()) }
}

fn compare_const(
  cache: &mut Cache,
  addr: AddrOf<'_>,
  mut_ctx: &FxHashMap<Name, usize>,
  x: &Member,
  y: &Member,
) -> R<Ordering> {
  if let Some((o, left)) = cache.map.get(&cache_key(&x.name, &y.name)) {
    if *left == x.name || *o == Ordering::Equal {
      return Ok(*o);
    }
    return Ok(o.reverse());
  }
  let c = Cmp { addr, mut_ctx };
  let s = compare_def(&c, x, y)?;
  if s.strong {
    cache.map.insert(cache_key(&x.name, &y.name), (s.ord, x.name.clone()));
  }
  Ok(s.ord)
}

type CmpFn<'b> = dyn FnMut(&Member, &Member) -> R<Ordering> + 'b;

// Lean's `List.sortByM` (a natural merge sort), step by step.
fn merge(
  cmp: &mut CmpFn<'_>,
  a: Vec<Member>,
  b: Vec<Member>,
) -> R<Vec<Member>> {
  let mut out = Vec::with_capacity(a.len() + b.len());
  let (mut i, mut j) = (0, 0);
  while i < a.len() && j < b.len() {
    if cmp(&a[i], &b[j])? == Ordering::Greater {
      out.push(b[j].clone());
      j += 1;
    } else {
      out.push(a[i].clone());
      i += 1;
    }
  }
  out.extend_from_slice(&a[i..]);
  out.extend_from_slice(&b[j..]);
  Ok(out)
}

fn sequences(cmp: &mut CmpFn<'_>, xs: &[Member]) -> R<Vec<Vec<Member>>> {
  if xs.len() < 2 {
    return Ok(vec![xs.to_vec()]);
  }
  let (a, b) = (&xs[0], &xs[1]);
  if cmp(a, b)? == Ordering::Greater {
    descending(cmp, b.clone(), vec![a.clone()], &xs[2..])
  } else {
    ascending(cmp, b.clone(), vec![a.clone()], &xs[2..])
  }
}

/// `descendingM a as xs` (`as` holds the run, most recent first).
fn descending(
  cmp: &mut CmpFn<'_>,
  a: Member,
  run: Vec<Member>,
  xs: &[Member],
) -> R<Vec<Vec<Member>>> {
  match xs.split_first() {
    Some((b, bs)) => {
      if cmp(&a, b)? == Ordering::Greater {
        let mut r = vec![a];
        r.extend(run);
        descending(cmp, b.clone(), r, bs)
      } else {
        let rest = sequences(cmp, xs)?;
        let mut r = vec![a];
        r.extend(run);
        let mut out = vec![r];
        out.extend(rest);
        Ok(out)
      }
    },
    None => {
      let rest = sequences(cmp, &[])?;
      let mut r = vec![a];
      r.extend(run);
      let mut out = vec![r];
      out.extend(rest);
      Ok(out)
    },
  }
}

/// `ascendingM a as xs` (`run` holds the prefix in order).
fn ascending(
  cmp: &mut CmpFn<'_>,
  a: Member,
  run: Vec<Member>,
  xs: &[Member],
) -> R<Vec<Vec<Member>>> {
  match xs.split_first() {
    Some((b, bs)) => {
      if cmp(&a, b)? != Ordering::Greater {
        let mut r = run;
        r.push(a);
        ascending(cmp, b.clone(), r, bs)
      } else {
        let rest = sequences(cmp, xs)?;
        let mut r = run;
        r.push(a);
        let mut out = vec![r];
        out.extend(rest);
        Ok(out)
      }
    },
    None => {
      let rest = sequences(cmp, &[])?;
      let mut r = run;
      r.push(a);
      let mut out = vec![r];
      out.extend(rest);
      Ok(out)
    },
  }
}

fn merge_pairs(
  cmp: &mut CmpFn<'_>,
  xs: Vec<Vec<Member>>,
) -> R<Vec<Vec<Member>>> {
  let mut out = Vec::new();
  let mut it = xs.into_iter();
  loop {
    match (it.next(), it.next()) {
      (Some(a), Some(b)) => out.push(merge(cmp, a, b)?),
      (Some(a), None) => {
        out.push(a);
        break;
      },
      _ => break,
    }
  }
  Ok(out)
}

fn sort_by_m(cmp: &mut CmpFn<'_>, xs: &[Member]) -> R<Vec<Member>> {
  let mut runs = sequences(cmp, xs)?;
  let mut fuel = runs.len();
  loop {
    if fuel == 0 {
      return Ok(runs.into_iter().flatten().collect());
    }
    if runs.len() == 1 {
      return Ok(runs.pop().unwrap());
    }
    fuel -= 1;
    runs = merge_pairs(cmp, runs)?;
  }
}

fn sort_by_name(xs: &mut [Member]) {
  xs.sort_by(|a, b| a.name.cmp(&b.name));
}

fn ctx_of(classes: &[Vec<Member>]) -> FxHashMap<Name, usize> {
  let mut m = FxHashMap::default();
  for (j, c) in classes.iter().enumerate() {
    for x in c {
      m.insert(x.name.clone(), j);
    }
  }
  m
}

/// `sortClasses Rules.phaseA` over definitions.
pub fn sort_classes(
  addr: AddrOf<'_>,
  sources: &[Member],
) -> R<Vec<Vec<Member>>> {
  if sources.is_empty() {
    return Ok(Vec::new());
  }
  let mut seed = sources.to_vec();
  sort_by_name(&mut seed);
  let mut cache = Cache::default();
  let mut classes: Vec<Vec<Member>> = vec![seed];
  let mut fuel = sources.len() + 1;
  loop {
    if fuel == 0 {
      return Err("sortConsts did not converge".into());
    }
    fuel -= 1;
    let ctx = ctx_of(&classes);
    let mut refined: Vec<Vec<Member>> = Vec::new();
    for c in &classes {
      match c.len() {
        0 => return Err("empty class in sortConsts".into()),
        1 => refined.push(c.clone()),
        _ => {
          let sorted = {
            let mut f = |a: &Member, b: &Member| {
              compare_const(&mut cache, addr, &ctx, a, b)
            };
            sort_by_m(&mut f, c)?
          };
          // `groupAdjacent`: each element compared with its predecessor
          let mut groups: Vec<Vec<Member>> = Vec::new();
          let mut cur: Vec<Member> = vec![sorted[0].clone()];
          for k in 1..sorted.len() {
            let eq = compare_const(
              &mut cache,
              addr,
              &ctx,
              &sorted[k],
              &sorted[k - 1],
            )? == Ordering::Equal;
            if eq {
              cur.push(sorted[k].clone());
            } else {
              groups.push(std::mem::replace(&mut cur, vec![sorted[k].clone()]));
            }
          }
          groups.push(cur);
          for mut g in groups {
            sort_by_name(&mut g);
            refined.push(g);
          }
        },
      }
    }
    let done = classes.len() == refined.len();
    classes = refined;
    if done {
      break;
    }
  }
  if classes.iter().any(|c| c.is_empty()) {
    return Err("empty class after sortConsts".into());
  }
  if sources.len() < classes.len() {
    return Err("too many classes after sortConsts".into());
  }
  Ok(classes)
}

/// `cliqueClasses`: the class names in canonical order.
pub fn clique_classes(
  addr: AddrOf<'_>,
  members: &[Member],
) -> R<Vec<Vec<Name>>> {
  let cls = sort_classes(addr, members)?;
  Ok(cls.into_iter().map(|c| c.into_iter().map(|m| m.name).collect()).collect())
}

/// `statementOrder`.
pub fn statement_order(
  addr: AddrOf<'_>,
  members: &[Member],
) -> R<Option<Vec<usize>>> {
  let ms: Vec<Member> = members
    .iter()
    .map(|m| Member { value: m.typ.clone(), ..m.clone() })
    .collect();
  let cls = clique_classes(addr, &ms)?;
  if cls.iter().any(|c| c.len() >= 2) {
    return Ok(None);
  }
  Ok(Some(
    ms.iter()
      .map(|m| cls.iter().position(|c| c.contains(&m.name)).unwrap_or(0))
      .collect(),
  ))
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::compile::pass3::expr::{bvar, root_name};

  #[test]
  fn non_dep_splits_classes_but_binder_names_do_not() {
    let typ = Expr::sort(Level::succ(Level::zero()));
    let make = |name: &str, binder: &str, flag| Member {
      name: root_name(name),
      level_params: vec![],
      typ: typ.clone(),
      value: Expr::letE(
        root_name(binder),
        typ.clone(),
        Expr::sort(Level::zero()),
        bvar(0),
        flag,
      ),
    };
    let a = make("let", "x", false);
    let b = make("have", "x", true);
    let neighbour = make("neighbour", "y", false);
    let addr: AddrOf<'_> = &|_| None;
    let reference =
      clique_classes(addr, &[a.clone(), b.clone(), neighbour.clone()]).unwrap();
    assert_eq!(reference.iter().map(Vec::len).collect::<Vec<_>>(), vec![2, 1]);
    assert!(reference[0].contains(&a.name));
    assert!(reference[0].contains(&neighbour.name));
    assert_eq!(reference[1], vec![b.name.clone()]);
    assert_eq!(clique_classes(addr, &[b, neighbour, a]).unwrap(), reference);
  }
}
