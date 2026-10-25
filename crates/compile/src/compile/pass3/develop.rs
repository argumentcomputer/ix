//! Pass 3: the development of an image as hereditary substitution. A port of
//! `Ix/Compile/Image/Develop.lean`.
//!
//! `hinst v k e` substitutes `v` for the loose variable `bvar k` of `e` and
//! contracts exactly the redexes the substitution forms at the substituted
//! positions, hereditarily: beta at an application whose head became a
//! lambda, projection of a `PProd.mk`/`And.intro`, and eta at a binder whose
//! body became `x a1 ... an y` with `x` directly substituted. A lambda under
//! immediate semantic metadata retains its binder. Nothing else is reduced
//! (never iota). Every traversal is memoised per node, as on the Lean
//! side; the results are those of the plain recursions.
//!
//! Every node the development builds is shared (`DevState::share`, Lean
//! `TotalMemo.share`): a node equal to one built before is that node, so a
//! term met again is the same allocation and the tables confirm their hits
//! at `same_raw`'s pointer test. The tables are carried across the
//! developments of a rewrite (`instantiate_with`).

use rustc_hash::FxHashMap;

use ix_common::env::{Expr, ExprData, Name};

use super::expr::{
  ExactMemo, Hash, abstract_fvars, bvar, get_app_fn_args, key, nat_usize,
};
use super::names::{n_and, n_and_intro, n_pprod, n_pprod_mk};

/// How the head of a substituted term was formed.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Created {
  No,
  Direct,
  Reduced,
}

/// `.proj S i (S.mk a b x y)` to `x`/`y` for `PProd` and `And`.
fn proj_ctor(s: &Name, i: usize, e: &Expr) -> Option<Expr> {
  let (h, args) = get_app_fn_args(e);
  match h.as_data() {
    ExprData::Const(c, _, _) => {
      if args.len() == 4
        && i < 2
        && ((*s == n_pprod() && *c == n_pprod_mk())
          || (*s == n_and() && *c == n_and_intro()))
      {
        args.get(2 + i).cloned()
      } else {
        None
      }
    },
    _ => None,
  }
}

/// The substitution table: `(v, e, k)` to `hinst v k e`, keyed by the two
/// expressions' hashes and confirmed by raw equality of both (the Lean side's
/// `hinst` table confirms its hits the same way). It is keyed without the
/// remaining fuel: a successful result does not depend on the fuel that
/// reached it.
#[derive(Default)]
struct InstMemo {
  map: FxHashMap<(Hash, Hash, usize), (Expr, Expr, (Expr, Created))>,
}

impl InstMemo {
  fn get(&self, v: &Expr, e: &Expr, k: usize) -> Option<(Expr, Created)> {
    match self.map.get(&(key(v), key(e), k)) {
      Some((sv, se, r)) if sv.same_raw(v) && se.same_raw(e) => Some(r.clone()),
      _ => None,
    }
  }

  fn insert(&mut self, v: &Expr, e: &Expr, k: usize, r: (Expr, Created)) {
    self.map.insert((key(v), key(e), k), (v.clone(), e.clone(), r));
  }
}

/// The fuel-free tables (values of total functions of their keys) and the
/// substitution table, every hit confirmed by raw equality (`ExactMemo`).
#[derive(Default)]
pub struct DevState {
  range: ExactMemo<(), usize>,
  lifted: ExactMemo<(usize, usize), Expr>,
  lowered: ExactMemo<(usize, usize), Expr>,
  occurs: ExactMemo<usize, bool>,
  insts: InstMemo,
  /// The development's nodes, one per digest (`share`; Lean `DevState.nodes`):
  /// a node the development builds again is the node it built first, so the
  /// tables above confirm their hits by pointer (`same_raw`'s first test).
  nodes: FxHashMap<Hash, Expr>,
}

impl DevState {
  /// `e`, or the table's node at `e`'s digest when it equals `e` (raw
  /// equality). A free digest takes `e`; a digest holding a different term
  /// keeps it.
  fn share(&mut self, e: Expr) -> Expr {
    match self.nodes.entry(*e.get_hash()) {
      std::collections::hash_map::Entry::Occupied(o) => {
        if o.get().same_raw(&e) { o.get().clone() } else { e }
      },
      std::collections::hash_map::Entry::Vacant(v) => {
        v.insert(e.clone());
        e
      },
    }
  }

  /// `mk_app_n(f, args)`, every application node shared.
  fn share_app_n(&mut self, f: Expr, args: &[Expr]) -> Expr {
    let mut acc = f;
    for a in args {
      acc = self.share(Expr::app(acc, a.clone()));
    }
    acc
  }

  /// One more than the largest loose bound variable of `e`.
  fn loose_range(&mut self, e: &Expr) -> usize {
    if let Some(r) = self.range.get(e, ()) {
      return r;
    }
    let r = match e.as_data() {
      ExprData::Bvar(i, _) => nat_usize(i).saturating_add(1),
      ExprData::App(f, a, _) => {
        let x = self.loose_range(f);
        let y = self.loose_range(a);
        x.max(y)
      },
      ExprData::Lam(_, t, b, _, _) | ExprData::ForallE(_, t, b, _, _) => {
        let x = self.loose_range(t);
        let y = self.loose_range(b).saturating_sub(1);
        x.max(y)
      },
      ExprData::LetE(_, t, v, b, _, _) => {
        let x = self.loose_range(t);
        let y = self.loose_range(v);
        let z = self.loose_range(b).saturating_sub(1);
        x.max(y).max(z)
      },
      ExprData::Proj(_, _, s, _) | ExprData::Mdata(_, s, _) => {
        self.loose_range(s)
      },
      _ => 0,
    };
    self.range.insert(e, (), r);
    r
  }

  fn lift(&mut self, e: &Expr, n: usize, c: usize) -> Expr {
    if n == 0 || self.loose_range(e) <= c {
      return e.clone();
    }
    if let Some(r) = self.lifted.get(e, (n, c)) {
      return r.clone();
    }
    let r = match e.as_data() {
      ExprData::Bvar(i, _) => {
        let i = nat_usize(i);
        if i >= c { self.share(bvar(i + n)) } else { e.clone() }
      },
      ExprData::App(f, a, _) => {
        let f2 = self.lift(f, n, c);
        let a2 = self.lift(a, n, c);
        self.share(Expr::app(f2, a2))
      },
      ExprData::Lam(nm, t, b, bi, _) => {
        let t2 = self.lift(t, n, c);
        let b2 = self.lift(b, n, c + 1);
        self.share(Expr::lam(nm.clone(), t2, b2, bi.clone()))
      },
      ExprData::ForallE(nm, t, b, bi, _) => {
        let t2 = self.lift(t, n, c);
        let b2 = self.lift(b, n, c + 1);
        self.share(Expr::all(nm.clone(), t2, b2, bi.clone()))
      },
      ExprData::LetE(nm, t, v, b, nd, _) => {
        let t2 = self.lift(t, n, c);
        let v2 = self.lift(v, n, c);
        let b2 = self.lift(b, n, c + 1);
        self.share(Expr::letE(nm.clone(), t2, v2, b2, *nd))
      },
      ExprData::Proj(nm, i, s, _) => {
        let s2 = self.lift(s, n, c);
        self.share(Expr::proj(nm.clone(), i.clone(), s2))
      },
      ExprData::Mdata(md, x, _) => {
        let x2 = self.lift(x, n, c);
        self.share(Expr::mdata(md.clone(), x2))
      },
      _ => e.clone(),
    };
    self.lifted.insert(e, (n, c), r.clone());
    r
  }

  fn lower(&mut self, e: &Expr, n: usize, c: usize) -> Expr {
    if n == 0 || self.loose_range(e) <= c {
      return e.clone();
    }
    if let Some(r) = self.lowered.get(e, (n, c)) {
      return r.clone();
    }
    let r = match e.as_data() {
      ExprData::Bvar(i, _) => {
        let i = nat_usize(i);
        if i >= c + n { self.share(bvar(i - n)) } else { e.clone() }
      },
      ExprData::App(f, a, _) => {
        let f2 = self.lower(f, n, c);
        let a2 = self.lower(a, n, c);
        self.share(Expr::app(f2, a2))
      },
      ExprData::Lam(nm, t, b, bi, _) => {
        let t2 = self.lower(t, n, c);
        let b2 = self.lower(b, n, c + 1);
        self.share(Expr::lam(nm.clone(), t2, b2, bi.clone()))
      },
      ExprData::ForallE(nm, t, b, bi, _) => {
        let t2 = self.lower(t, n, c);
        let b2 = self.lower(b, n, c + 1);
        self.share(Expr::all(nm.clone(), t2, b2, bi.clone()))
      },
      ExprData::LetE(nm, t, v, b, nd, _) => {
        let t2 = self.lower(t, n, c);
        let v2 = self.lower(v, n, c);
        let b2 = self.lower(b, n, c + 1);
        self.share(Expr::letE(nm.clone(), t2, v2, b2, *nd))
      },
      ExprData::Proj(nm, i, s, _) => {
        let s2 = self.lower(s, n, c);
        self.share(Expr::proj(nm.clone(), i.clone(), s2))
      },
      ExprData::Mdata(md, x, _) => {
        let x2 = self.lower(x, n, c);
        self.share(Expr::mdata(md.clone(), x2))
      },
      _ => e.clone(),
    };
    self.lowered.insert(e, (n, c), r.clone());
    r
  }

  fn occurs(&mut self, e: &Expr, k: usize) -> bool {
    if self.loose_range(e) <= k {
      return false;
    }
    if let Some(r) = self.occurs.get(e, k) {
      return r;
    }
    let r = match e.as_data() {
      ExprData::Bvar(i, _) => nat_usize(i) == k,
      ExprData::App(f, a, _) => self.occurs(f, k) || self.occurs(a, k),
      ExprData::Lam(_, t, b, _, _) | ExprData::ForallE(_, t, b, _, _) => {
        self.occurs(t, k) || self.occurs(b, k + 1)
      },
      ExprData::LetE(_, t, v, b, _, _) => {
        self.occurs(t, k) || self.occurs(v, k) || self.occurs(b, k + 1)
      },
      ExprData::Proj(_, _, s, _) | ExprData::Mdata(_, s, _) => {
        self.occurs(s, k)
      },
      _ => false,
    };
    self.occurs.insert(e, k, r);
    r
  }

  /// `e[bvar k := v]`, contracting the redexes formed at the substituted
  /// positions.
  pub fn hinst(
    &mut self,
    fuel: usize,
    v: &Expr,
    k: usize,
    e: &Expr,
  ) -> Result<(Expr, Created), String> {
    if fuel == 0 {
      return Err(develop_exhausted());
    }
    let fuel = fuel - 1;
    if self.loose_range(e) <= k {
      return Ok((e.clone(), Created::No));
    }
    if let Some(r) = self.insts.get(v, e, k) {
      return Ok(r);
    }
    let r = match e.as_data() {
      ExprData::Bvar(i, _) => {
        let i = nat_usize(i);
        if i == k {
          (self.lift(v, k, 0), Created::Direct)
        } else if i > k {
          (self.share(bvar(i - 1)), Created::No)
        } else {
          (e.clone(), Created::No)
        }
      },
      ExprData::App(..) => {
        let (h, args) = get_app_fn_args(e);
        let mut args2 = Vec::with_capacity(args.len());
        for a in &args {
          args2.push(self.hinst(fuel, v, k, a)?.0);
        }
        let (h2, c) = self.hinst(fuel, v, k, &h)?;
        match (c, h2.as_data()) {
          (Created::No, _) => (self.share_app_n(h2, &args2), Created::No),
          (_, ExprData::Lam(..)) => {
            (self.happ(fuel, &h2, &args2)?, Created::Reduced)
          },
          (c, _) => (self.share_app_n(h2, &args2), c),
        }
      },
      ExprData::Proj(s, i, x, _) => {
        let (x2, c) = self.hinst(fuel, v, k, x)?;
        match c {
          Created::No => {
            (self.share(Expr::proj(s.clone(), i.clone(), x2)), Created::No)
          },
          _ => match proj_ctor(s, nat_usize(i), &x2) {
            Some(f) => (f, Created::Reduced),
            None => {
              (self.share(Expr::proj(s.clone(), i.clone(), x2)), Created::No)
            },
          },
        }
      },
      ExprData::Lam(n, t, b, bi, _) => {
        let (t2, _) = self.hinst(fuel, v, k, t)?;
        let (b2, c) = self.hinst(fuel, v, k + 1, b)?;
        let mut out = None;
        if c == Created::Direct
          && let ExprData::App(f, a, _) = b2.as_data()
          && let ExprData::Bvar(z, _) = a.as_data()
          && nat_usize(z) == 0
          && !self.occurs(f, 0)
        {
          out = Some((self.lower(f, 1, 0), Created::Direct));
        }
        match out {
          Some(o) => o,
          None => {
            (self.share(Expr::lam(n.clone(), t2, b2, bi.clone())), Created::No)
          },
        }
      },
      ExprData::ForallE(n, t, b, bi, _) => {
        let (t2, _) = self.hinst(fuel, v, k, t)?;
        let (b2, _) = self.hinst(fuel, v, k + 1, b)?;
        (self.share(Expr::all(n.clone(), t2, b2, bi.clone())), Created::No)
      },
      ExprData::LetE(n, t, x, b, nd, _) => {
        let (t2, _) = self.hinst(fuel, v, k, t)?;
        let (x2, _) = self.hinst(fuel, v, k, x)?;
        let (b2, _) = self.hinst(fuel, v, k + 1, b)?;
        (self.share(Expr::letE(n.clone(), t2, x2, b2, *nd)), Created::No)
      },
      ExprData::Mdata(md, x, _) => {
        // Protect the binder of a semantic frame under its own full key;
        // an unwrapped lambda's cached result may already be eta-reduced.
        let (x2, c) = match x.as_data() {
          ExprData::Lam(n, t, b, bi, _)
            if crate::semantic_contract::has_metadata(md) =>
          {
            let inner_fuel =
              fuel.checked_sub(1).ok_or_else(develop_exhausted)?;
            let (t2, _) = self.hinst(inner_fuel, v, k, t)?;
            let (b2, _) = self.hinst(inner_fuel, v, k + 1, b)?;
            (self.share(Expr::lam(n.clone(), t2, b2, bi.clone())), Created::No)
          },
          _ => self.hinst(fuel, v, k, x)?,
        };
        (self.share(Expr::mdata(md.clone(), x2)), c)
      },
      _ => (e.clone(), Created::No),
    };
    self.insts.insert(v, e, k, r.clone());
    Ok(r)
  }

  /// `f a1 ... an` with the beta-redexes at the head contracted
  /// hereditarily.
  pub fn happ(
    &mut self,
    fuel: usize,
    f: &Expr,
    args: &[Expr],
  ) -> Result<Expr, String> {
    if fuel == 0 {
      return Err(develop_exhausted());
    }
    let fuel = fuel - 1;
    match (f.as_data(), args.split_first()) {
      (ExprData::Lam(_, _, b, _, _), Some((a, rest))) => {
        let (b2, _) = self.hinst(fuel, a, 0, b)?;
        self.happ(fuel, &b2, rest)
      },
      _ => Ok(self.share_app_n(f.clone(), args)),
    }
  }
}

/// The bound on the recursion depth of the development (Lean `developFuel`).
/// A development that exhausts it is an error naming the bound, never a
/// partial result.
pub const DEVELOP_FUEL: usize = 1 << 16;

/// The error of an exhausted development, word for word the Lean side's
/// (`developExhausted`).
pub fn develop_exhausted() -> String {
  format!(
    "development: recursion depth bound developFuel = {DEVELOP_FUEL} exhausted"
  )
}

/// The developed application `f args`.
pub fn instantiate(f: &Expr, args: &[Expr]) -> Result<Expr, String> {
  DevState::default().happ(DEVELOP_FUEL, f, args)
}

/// `instantiate` with the tables of an earlier development carried over (Lean
/// `instantiateWith`): each is keyed by its exact inputs, and a successful
/// result does not depend on the fuel that reached it.
pub fn instantiate_with(
  st: &mut DevState,
  f: &Expr,
  args: &[Expr],
) -> Result<Expr, String> {
  st.happ(DEVELOP_FUEL, f, args)
}

/// `e[xs := vs]` for free variables, developed.
pub fn subst_fvars(xs: &[Name], vs: &[Expr], e: &Expr) -> Result<Expr, String> {
  if xs.len() != vs.len() {
    return Err("substFVars: arity mismatch".into());
  }
  let mut st = DevState::default();
  let mut acc = abstract_fvars(xs, e);
  for v in vs.iter().rev() {
    acc = st.hinst(DEVELOP_FUEL, v, 0, &acc)?.0;
  }
  Ok(acc)
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::semantic_contract::{decode, inspect};
  use ix_common::env::{BinderInfo, DataValue};
  use std::sync::Arc;

  #[test]
  fn semantic_lambda_placement_cache_and_fuel() {
    let name = |root, field| Name::str(Name::str(Name::anon(), root), field);
    let ty = Expr::cnst(Name::str(Name::anon(), "Nat".into()), vec![]);
    let g = Expr::cnst(name("Nat".into(), "succ".into()), vec![]);
    let lam =
      |body| Expr::lam(Name::anon(), ty.clone(), body, BinderInfo::Default);
    let contract = decode(0, 1).unwrap();
    let raw = lam(Expr::app(bvar(1), bvar(0)));
    let frame = contract.attach(raw.clone());
    let kept = lam(Expr::app(g.clone(), bvar(0)));
    let expected = contract.attach(kept.clone());
    let mut warm = DevState::default();
    let (out, tag) = warm.hinst(4, &g, 0, &frame).unwrap();
    assert!(out.same_raw(&expected));
    assert_eq!(tag, Created::No);
    assert!(inspect(&frame).unwrap() && inspect(&out).unwrap());
    let size = warm.insts.map.len();
    assert!(warm.hinst(1, &g, 0, &frame).unwrap().0.same_raw(&expected));
    assert_eq!(warm.insts.map.len(), size);
    assert!(warm.hinst(16, &g, 0, &raw).unwrap().0.same_raw(&g));
    let mut plain_warm = DevState::default();
    assert!(plain_warm.hinst(3, &g, 0, &raw).unwrap().0.same_raw(&g));
    for fuel in 0..4 {
      assert_eq!(
        DevState::default().hinst(fuel, &g, 0, &frame).unwrap_err(),
        develop_exhausted()
      );
    }
    assert_eq!(warm.hinst(0, &g, 0, &frame).unwrap_err(), develop_exhausted());
    for fuel in 1..3 {
      assert_eq!(
        plain_warm.hinst(fuel, &g, 0, &frame).unwrap_err(),
        develop_exhausted()
      );
    }
    assert!(plain_warm.hinst(3, &g, 0, &frame).unwrap().0.same_raw(&expected));
    let function_ty =
      Expr::all(Name::anon(), ty.clone(), ty.clone(), BinderInfo::Default);
    let f =
      Expr::lam(Name::anon(), function_ty, frame.clone(), BinderInfo::Default);
    let mut state = DevState::default();
    for _ in 0..2 {
      assert!(
        instantiate_with(&mut state, &f, std::slice::from_ref(&g))
          .unwrap()
          .same_raw(&expected)
      );
    }
    for (root, field) in [("native", "hint"), ("_ix", "inline")] {
      let md =
        vec![(name(root.into(), field.into()), DataValue::OfNat(0u64.into()))];
      for (input, output) in [(&raw, &g), (&frame, &expected)] {
        let e = Expr::mdata(md.clone(), input.clone());
        let expected = Expr::mdata(md.clone(), output.clone());
        assert!(
          DevState::default()
            .hinst(16, &g, 0, &e)
            .unwrap()
            .0
            .same_raw(&expected)
        );
      }
    }
    let nested =
      contract.attach(lam(contract.attach(lam(Expr::app(bvar(2), bvar(0))))));
    let nested_out = contract.attach(lam(expected));
    assert!(
      DevState::default()
        .hinst(16, &g, 0, &nested)
        .unwrap()
        .0
        .same_raw(&nested_out)
    );
    assert!(inspect(&nested_out).unwrap());
    let mut bad_data = contract.metadata();
    bad_data.pop();
    let bad =
      Expr(Arc::new(ExprData::Mdata(bad_data.clone(), raw, *frame.get_hash())));
    let malformed = Expr::mdata(bad_data, kept);
    assert!(!bad.same_raw(&frame));
    assert!(warm.hinst(16, &g, 0, &bad).unwrap().0.same_raw(&malformed));
    assert!(
      matches!(inspect(&malformed), Err(ixon::CompileError::UnsupportedExpr { desc })
      if desc == "malformed semantic contract frame")
    );
  }
}
